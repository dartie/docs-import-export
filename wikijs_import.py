#!/usr/bin/env python3
"""
import_to_wikijs.py
-------------------
Recursively imports a tree of Markdown files into Wiki.js via its GraphQL API.
Attachments (images and other assets referenced in the markdown) are uploaded
to the Wiki.js asset manager and the local references are rewritten to the
canonical Wiki.js URL before the page is created.

Requirements:
    pip install requests

Usage:
    python import_to_wikijs.py \
        --url   http://192.168.1.80:3000 \
        --token YOUR_API_TOKEN \
        --root  ./knowledge-base \
        [--locale en] \
        [--dry-run] \
        [--overwrite]
"""

import argparse
import mimetypes
import re
import sys
import time
from pathlib import Path

import requests

# ---------------------------------------------------------------------------
# GraphQL queries / mutations
# ---------------------------------------------------------------------------

GQL_PAGE_CREATE = """
mutation CreatePage(
  $content: String!, $description: String!, $editor: String!,
  $isPublished: Boolean!, $isPrivate: Boolean!, $locale: String!,
  $path: String!, $tags: [String]!, $title: String!
) {
  pages {
    create(
      content: $content, description: $description, editor: $editor,
      isPublished: $isPublished, isPrivate: $isPrivate, locale: $locale,
      path: $path, tags: $tags, title: $title
    ) {
      responseResult { succeeded errorCode slug message }
      page { id path title }
    }
  }
}
"""

GQL_PAGE_UPDATE = """
mutation UpdatePage(
  $id: Int!, $content: String!, $description: String!, $editor: String!,
  $isPublished: Boolean!, $isPrivate: Boolean!, $locale: String!,
  $path: String!, $tags: [String]!, $title: String!
) {
  pages {
    update(
      id: $id, content: $content, description: $description, editor: $editor,
      isPublished: $isPublished, isPrivate: $isPrivate, locale: $locale,
      path: $path, tags: $tags, title: $title
    ) {
      responseResult { succeeded errorCode slug message }
      page { id path title }
    }
  }
}
"""

GQL_PAGE_BY_PATH = """
query GetPage($path: String!, $locale: String!) {
  pages {
    singleByPath(path: $path, locale: $locale) { id path title }
  }
}
"""

GQL_ASSET_FOLDERS = """
query ListFolders($parentFolderId: Int!) {
  assets {
    folders(parentFolderId: $parentFolderId) { id slug name }
  }
}
"""

GQL_ASSET_FOLDER_CREATE = """
mutation CreateFolder($slug: String!, $parentFolderId: Int!) {
  assets {
    createFolder(slug: $slug, parentFolderId: $parentFolderId) {
      responseResult { succeeded errorCode slug message }
    }
  }
}
"""

# ---------------------------------------------------------------------------
# Utility helpers
# ---------------------------------------------------------------------------

_SLUG_CLEAN = re.compile(r"[^a-z0-9\-]")


def slugify(text: str) -> str:
    text = text.lower().replace("_", "-").replace(" ", "-")
    text = _SLUG_CLEAN.sub("", text)
    text = re.sub(r"-{2,}", "-", text).strip("-")
    return text or "page"


def wikijs_path(file_path: Path, root: Path) -> str:
    """
    Convert a filesystem path to a Wiki.js page path.
    e.g.  root/3D_Printing/3D Printing.md  ->  3d-printing/3d-printing
    No leading slash, no .md extension.
    """
    rel = file_path.relative_to(root)
    parts = [slugify(p) for p in rel.with_suffix("").parts]
    # Treat index / readme as the parent folder page
    if parts and parts[-1] in ("index", "readme"):
        parts = parts[:-1]
    if not parts:
        parts = ["home"]
    return "/".join(parts)


def extract_title(content: str, filename: str) -> str:
    for line in content.splitlines():
        line = line.strip()
        if line.startswith("# "):
            return line[2:].strip()
    return Path(filename).stem.replace("-", " ").replace("_", " ").title()


def find_local_attachments(content: str, md_file: Path) -> list[tuple[str, Path]]:
    """
    Return [(original_ref, absolute_path)] for every local file referenced
    in the markdown.  Skips http(s) and anchor refs.
    """
    pattern = re.compile(r'!?\[.*?\]\((?!https?://)(?!#)([^)\s"\']+)')
    seen: set[str] = set()
    results = []
    for m in pattern.finditer(content):
        ref = m.group(1)
        if ref in seen:
            continue
        seen.add(ref)
        abs_path = (md_file.parent / ref).resolve()
        if abs_path.exists() and abs_path.is_file():
            results.append((ref, abs_path))
    return results


# ---------------------------------------------------------------------------
# Wiki.js API client
# ---------------------------------------------------------------------------

class WikiJS:
    def __init__(self, base_url: str, token: str, dry_run: bool = False):
        self.base_url   = base_url.rstrip("/")
        self.gql_url    = f"{self.base_url}/graphql"
        self.upload_url = f"{self.base_url}/u"
        self.session    = requests.Session()
        self.session.headers.update({"Authorization": f"Bearer {token}"})
        self.dry_run    = dry_run
        self._folder_cache: dict[str, int] = {"": 0}  # "" -> root (id=0)

    # ---- low-level GQL --------------------------------------------------

    def gql(self, query: str, variables: dict) -> dict:
        resp = self.session.post(
            self.gql_url,
            json={"query": query, "variables": variables},
            timeout=30,
        )
        if not resp.ok:
            snippet = resp.text[:500]
            raise requests.HTTPError(
                f"{resp.status_code} {resp.reason} | body: {snippet}",
                response=resp,
            )
        data = resp.json()
        if "errors" in data:
            raise RuntimeError(f"GraphQL errors: {data['errors']}")
        return data["data"]

    # ---- pages ----------------------------------------------------------

    def page_id(self, path: str, locale: str) -> int | None:
        try:
            data = self.gql(GQL_PAGE_BY_PATH, {"path": path, "locale": locale})
            page = (data.get("pages") or {}).get("singleByPath")
            return page["id"] if page else None
        except Exception:
            return None

    def create_page(self, path, title, content, locale,
                    description="", tags=None) -> bool:
        if self.dry_run:
            print(f"    [dry-run] CREATE  /{path}")
            return True
        try:
            data = self.gql(GQL_PAGE_CREATE, {
                "path": path, "title": title, "content": content,
                "locale": locale, "description": description,
                "editor": "markdown", "isPublished": True,
                "isPrivate": False, "tags": tags or [],
            })
            res = data["pages"]["create"]["responseResult"]
            if not res["succeeded"]:
                print(f"    ERROR create: {res['message']} (code {res['errorCode']})")
                return False
            return True
        except Exception as exc:
            print(f"    EXCEPTION during create: {exc}")
            return False

    def update_page(self, pid, path, title, content, locale,
                    description="", tags=None) -> bool:
        if self.dry_run:
            print(f"    [dry-run] UPDATE  /{path}  (id={pid})")
            return True
        try:
            data = self.gql(GQL_PAGE_UPDATE, {
                "id": pid, "path": path, "title": title, "content": content,
                "locale": locale, "description": description,
                "editor": "markdown", "isPublished": True,
                "isPrivate": False, "tags": tags or [],
            })
            res = data["pages"]["update"]["responseResult"]
            if not res["succeeded"]:
                print(f"    ERROR update: {res['message']} (code {res['errorCode']})")
                return False
            return True
        except Exception as exc:
            print(f"    EXCEPTION during update: {exc}")
            return False

    # ---- asset folders --------------------------------------------------

    def _list_children(self, parent_id: int) -> dict[str, int]:
        """Return {slug: id} of immediate child folders."""
        try:
            data = self.gql(GQL_ASSET_FOLDERS, {"parentFolderId": parent_id})
            return {
                f["slug"]: f["id"]
                for f in (data.get("assets") or {}).get("folders", [])
            }
        except Exception as exc:
            print(f"    WARNING: could not list folders (parent={parent_id}): {exc}")
            return {}

    def _ensure_single_folder(self, slug: str, parent_id: int) -> int:
        """
        Make sure one folder level exists. Returns its id.
        Falls back to parent_id on any error so the upload can still proceed.
        """
        slug = slugify(slug)

        # Already exists?
        children = self._list_children(parent_id)
        if slug in children:
            return children[slug]

        if self.dry_run:
            print(f"    [dry-run] mkdir '{slug}' under folder id={parent_id}")
            return parent_id

        # Attempt to create the folder. Wiki.js's createFolder mutation returns
        # only responseResult (no 'folder' sub-field), so we always re-list
        # afterwards to find the new folder's real id.
        try:
            data = self.gql(
                GQL_ASSET_FOLDER_CREATE,
                {"slug": slug, "parentFolderId": parent_id},
            )
            rr = data["assets"]["createFolder"].get("responseResult", {})
            if not rr.get("succeeded"):
                print(f"    WARNING: folder '{slug}' create reported failure: {rr.get('message', '?')}")
        except Exception as exc:
            # 400 / GraphQL errors often mean schema mismatch or already-exists;
            # we intentionally swallow and re-list below.
            print(f"    WARNING: folder create error for '{slug}': {type(exc).__name__}: {str(exc)[:120]}")

        # Re-list regardless — Wiki.js frequently creates the folder even when
        # it reports an error, and the old 'folder { id }' field doesn't exist.
        children = self._list_children(parent_id)
        if slug in children:
            return children[slug]

        print(f"    WARNING: folder '{slug}' missing after create attempt; uploading to parent (id={parent_id})")
        return parent_id

    def _resolve_folder(self, parts: list[str]) -> int:
        """
        Walk/create the full folder path and return the leaf folder id.
        Uses a local cache to avoid redundant API calls.
        """
        parts = [slugify(p) for p in parts if p.strip()]
        if not parts:
            return 0

        current_id = 0
        for depth, slug in enumerate(parts):
            cache_key = "/".join(parts[: depth + 1])
            if cache_key in self._folder_cache:
                current_id = self._folder_cache[cache_key]
            else:
                current_id = self._ensure_single_folder(slug, current_id)
                self._folder_cache[cache_key] = current_id

        return current_id

    # ---- asset upload ---------------------------------------------------

    def upload_asset(self, local_path: Path, folder_parts: list[str]) -> str | None:
        """
        Upload a file. Returns canonical URL (e.g. /assets/photos/img.png) or None.
        """
        folder_id   = self._resolve_folder(folder_parts)
        clean_parts = [slugify(p) for p in folder_parts if p.strip()]
        canonical   = "/" + "/".join(clean_parts + [local_path.name])

        if self.dry_run:
            print(f"    [dry-run] UPLOAD  {local_path.name}  ->  {canonical}")
            return canonical

        mime, _ = mimetypes.guess_type(str(local_path))
        mime = mime or "application/octet-stream"

        try:
            with open(local_path, "rb") as fh:
                resp = self.session.post(
                    self.upload_url,
                    data={"mediaUpload": f'{{"folderId":{folder_id}}}'},
                    files={"mediaUpload": (local_path.name, fh, mime)},
                    timeout=60,
                )
            if not resp.ok:
                print(f"    WARNING: upload {resp.status_code} — {resp.text[:200]}")
                return None
            return canonical
        except Exception as exc:
            print(f"    WARNING: upload exception ({exc})")
            return None


# ---------------------------------------------------------------------------
# Main import loop
# ---------------------------------------------------------------------------

def import_tree(root: Path, wiki: WikiJS, locale: str, overwrite: bool):
    md_files = sorted(root.rglob("*.md"))
    total    = len(md_files)
    print(f"Found {total} markdown file(s) under {root}\n")

    counts = {"created": 0, "updated": 0, "skipped": 0, "failed": 0}

    for i, md_file in enumerate(md_files, 1):
        rel       = md_file.relative_to(root)
        page_path = wikijs_path(md_file, root)
        print(f"[{i}/{total}] {rel}  ->  /{page_path}")

        try:
            content = md_file.read_text(encoding="utf-8", errors="replace")
        except Exception as exc:
            print(f"    ERROR reading file: {exc}")
            counts["failed"] += 1
            continue

        title = extract_title(content, md_file.name)

        # -- Attachments ---------------------------------------------------
        for ref, abs_path in find_local_attachments(content, md_file):
            try:
                rel_asset    = abs_path.relative_to(root)
                folder_parts = ["assets"] + list(rel_asset.parent.parts)
            except ValueError:
                folder_parts = ["assets"]

            url = wiki.upload_asset(abs_path, folder_parts)
            if url:
                print(f"    attachment: {ref}  ->  {url}")
                content = content.replace(ref, url)

        # -- Create / update page -----------------------------------------
        existing_id = wiki.page_id(page_path, locale)

        if existing_id:
            if overwrite:
                ok = wiki.update_page(existing_id, page_path, title, content, locale)
                print(f"    {'updated' if ok else 'FAILED'} (id={existing_id})")
                counts["updated" if ok else "failed"] += 1
            else:
                print(f"    skipped (already exists — use --overwrite to update)")
                counts["skipped"] += 1
        else:
            ok = wiki.create_page(page_path, title, content, locale)
            print(f"    {'created' if ok else 'FAILED'}")
            counts["created" if ok else "failed"] += 1

        time.sleep(0.15)

    print(
        f"\nDone.  created={counts['created']}  updated={counts['updated']}  "
        f"skipped={counts['skipped']}  failed={counts['failed']}"
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    p = argparse.ArgumentParser(
        description="Import a Markdown file tree into Wiki.js"
    )
    p.add_argument("--url",       required=True,  help="Wiki.js base URL, e.g. http://192.168.1.80:3000")
    p.add_argument("--token",     required=True,  help="Wiki.js API token")
    p.add_argument("--root",      required=True,  help="Root folder of the markdown tree")
    p.add_argument("--locale",    default="en",   help="Locale for all pages (default: en)")
    p.add_argument("--dry-run",   action="store_true", help="Preview without making changes")
    p.add_argument("--overwrite", action="store_true", help="Update pages that already exist")
    args = p.parse_args()

    root = Path(args.root).resolve()
    if not root.is_dir():
        print(f"ERROR: '{root}' is not a directory.", file=sys.stderr)
        sys.exit(1)

    wiki = WikiJS(args.url, args.token, dry_run=args.dry_run)

    if args.dry_run:
        print("*** DRY RUN — no changes will be made ***\n")

    import_tree(root, wiki, args.locale, args.overwrite)


if __name__ == "__main__":
    main()
