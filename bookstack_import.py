#!/usr/bin/env python3
"""
BookStack Markdown Importer / Exporter
=======================================
Import a structured tree of markdown files into BookStack,
or export BookStack content back to the same structure.

Directory Structure:
  root/
  ├── Book Name/
  │   ├── Chapter Name/
  │   │   ├── page.md
  │   │   ├── another-page.md
  │   │   └── attachments/
  │   │       └── diagram.pdf
  │   └── top-level-page.md
  └── Another Book/
      └── ...

Usage:
  # Import
  python bookstack.py import --url https://bookstack.example.com \\
      --token-id YOUR_ID --token-secret YOUR_SECRET --dir ./docs

  # Import (dry run)
  python bookstack.py import --url ... --token-id ... --token-secret ... \\
      --dir ./docs --dry-run

  # Export everything
  python bookstack.py export --url https://bookstack.example.com \\
      --token-id YOUR_ID --token-secret YOUR_SECRET --dir ./docs-export

  # Export a specific shelf only
  python bookstack.py export ... --shelf "My Shelf"

  # Export a specific book only
  python bookstack.py export ... --book "My Book"

Requirements:
  pip install requests
  pip install emoji  # optional, for :shortcode: conversion during import
"""

import argparse
import logging
import mimetypes
import re
import sys
import time
import unicodedata
from pathlib import Path
from urllib.parse import urlparse

import requests

try:
    import emoji as emoji_lib
    EMOJI_AVAILABLE = True
except ImportError:
    EMOJI_AVAILABLE = False

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("bookstack")


# ---------------------------------------------------------------------------
# Emoji helpers (import side)
# ---------------------------------------------------------------------------
def _convert_emoji_outside_inline_code(line: str) -> str:
    if not EMOJI_AVAILABLE:
        return line
    parts = re.split(r"(`[^`]+`)", line)
    return "".join(
        part if part.startswith("`") else emoji_lib.emojize(part, language="alias")
        for part in parts
    )


def preprocess_markdown(text: str) -> str:
    """Convert :shortcode: emoji outside fenced/inline code blocks."""
    result = []
    in_fenced = False
    fence_char = None

    for line in text.splitlines(keepends=True):
        stripped = line.lstrip()
        if not in_fenced:
            m = re.match(r"^(`{3,}|~{3,})", stripped)
            if m:
                in_fenced = True
                fence_char = m.group(1)[0]
                result.append(line)
                continue
        else:
            m = re.match(r"^(`{3,}|~{3,})\s*$", stripped)
            if m and stripped[0] == fence_char:
                in_fenced = False
                fence_char = None
                result.append(line)
                continue

        result.append(line if in_fenced else _convert_emoji_outside_inline_code(line))

    return "".join(result)


# ---------------------------------------------------------------------------
# Filesystem name helpers
# ---------------------------------------------------------------------------
def slugify(name: str) -> str:
    """Turn a BookStack name into a safe directory/file name."""
    # Normalise unicode, lower-case
    name = unicodedata.normalize("NFKD", name)
    name = name.encode("ascii", "ignore").decode("ascii")
    name = name.lower().strip()
    # Replace spaces and special chars with hyphens
    name = re.sub(r"[^\w\s-]", "", name)
    name = re.sub(r"[\s_]+", "-", name)
    name = re.sub(r"-+", "-", name).strip("-")
    return name or "untitled"


def infer_name(path: Path) -> str:
    """Convert a file/directory name to a human-readable title."""
    name = path.stem if path.is_file() else path.name
    name = re.sub(r"[-_]+", " ", name)
    name = re.sub(r"^\d+[\.\s]+", "", name)
    return name.strip().title()


# ---------------------------------------------------------------------------
# BookStack API client
# ---------------------------------------------------------------------------
class BookStackClient:
    def __init__(self, base_url: str, token_id: str, token_secret: str, dry_run: bool = False):
        self.base_url = base_url.rstrip("/")
        self.headers = {
            "Authorization": f"Token {token_id}:{token_secret}",
            "Content-Type": "application/json",
        }
        self.dry_run = dry_run
        self._cache: dict = {}

    # ------------------------------------------------------------------
    # Generic helpers
    # ------------------------------------------------------------------
    def _get(self, path: str, params: dict | None = None) -> dict:
        url = f"{self.base_url}/api/{path}"
        r = requests.get(url, headers=self.headers, params=params, timeout=30)
        r.raise_for_status()
        return r.json()

    def _get_binary(self, url: str) -> bytes:
        headers = {k: v for k, v in self.headers.items() if k != "Content-Type"}
        r = requests.get(url, headers=headers, timeout=60)
        r.raise_for_status()
        return r.content

    def _post(self, path: str, json: dict | None = None) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] POST /api/%s  %s", path, json)
            return {"id": 0, "name": "(dry-run)", "slug": "dry-run"}
        url = f"{self.base_url}/api/{path}"
        r = requests.post(url, headers=self.headers, json=json, timeout=30)
        r.raise_for_status()
        return r.json()

    def _put(self, path: str, json: dict | None = None) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] PUT /api/%s  %s", path, json)
            return {"id": 0}
        url = f"{self.base_url}/api/{path}"
        r = requests.put(url, headers=self.headers, json=json, timeout=30)
        r.raise_for_status()
        return r.json()

    def _post_multipart(self, path: str, data: dict, files: dict) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] POST (multipart) /api/%s  data=%s", path, data)
            return {"id": 0}
        url = f"{self.base_url}/api/{path}"
        headers = {k: v for k, v in self.headers.items() if k != "Content-Type"}
        r = requests.post(url, headers=headers, data=data, files=files, timeout=60)
        r.raise_for_status()
        return r.json()

    # ------------------------------------------------------------------
    # Pagination
    # ------------------------------------------------------------------
    def _list_all(self, path: str, params: dict | None = None) -> list[dict]:
        results, offset, count = [], 0, 500
        base_params = dict(params or {})
        while True:
            base_params.update({"count": count, "offset": offset})
            data = self._get(path, params=base_params)
            items = data.get("data", [])
            results.extend(items)
            if len(results) >= data.get("total", 0) or not items:
                break
            offset += count
        return results

    # ------------------------------------------------------------------
    # Shelves
    # ------------------------------------------------------------------
    def get_or_create_shelf(self, name: str) -> dict:
        key = f"shelf:{name}"
        if key in self._cache:
            return self._cache[key]
        for s in self._list_all("shelves"):
            if s["name"] == name:
                self._cache[key] = s
                return s
        log.info("Creating shelf: %s", name)
        shelf = self._post("shelves", {"name": name, "description": ""})
        self._cache[key] = shelf
        return shelf

    def list_shelves(self) -> list[dict]:
        return self._list_all("shelves")

    def get_shelf(self, shelf_id: int) -> dict:
        return self._get(f"shelves/{shelf_id}")

    # ------------------------------------------------------------------
    # Books
    # ------------------------------------------------------------------
    def list_books(self) -> list[dict]:
        return self._list_all("books")

    def get_book(self, book_id: int) -> dict:
        return self._get(f"books/{book_id}")

    def get_or_create_book(self, name: str, shelf_id: int | None = None) -> dict:
        key = f"book:{name}"
        if key in self._cache:
            return self._cache[key]
        for b in self._list_all("books"):
            if b["name"] == name:
                self._cache[key] = b
                if shelf_id:
                    self._assign_book_to_shelf(b["id"], shelf_id)
                return b
        log.info("Creating book: %s", name)
        book = self._post("books", {"name": name, "description": ""})
        if shelf_id and not self.dry_run:
            self._assign_book_to_shelf(book["id"], shelf_id)
        self._cache[key] = book
        return book

    def _assign_book_to_shelf(self, book_id: int, shelf_id: int):
        try:
            shelf = self._get(f"shelves/{shelf_id}")
            existing_ids = [b["id"] for b in shelf.get("books", [])]
            if book_id not in existing_ids:
                self._put(f"shelves/{shelf_id}", {"books": existing_ids + [book_id]})
        except Exception as exc:
            log.warning("Could not assign book %d to shelf %d: %s", book_id, shelf_id, exc)

    # ------------------------------------------------------------------
    # Chapters
    # ------------------------------------------------------------------
    def list_chapters(self, book_id: int) -> list[dict]:
        return self._list_all("chapters", params={"filter[book_id]": book_id})

    def get_or_create_chapter(self, name: str, book_id: int) -> dict:
        key = f"chapter:{book_id}:{name}"
        if key in self._cache:
            return self._cache[key]
        for c in self._list_all("chapters"):
            if c["name"] == name and c.get("book_id") == book_id:
                self._cache[key] = c
                return c
        log.info("  Creating chapter: %s", name)
        chapter = self._post("chapters", {"name": name, "book_id": book_id, "description": ""})
        self._cache[key] = chapter
        return chapter

    # ------------------------------------------------------------------
    # Pages
    # ------------------------------------------------------------------
    def list_pages(self, book_id: int) -> list[dict]:
        return self._list_all("pages", params={"filter[book_id]": book_id})

    def get_page(self, page_id: int) -> dict:
        return self._get(f"pages/{page_id}")

    def find_page(self, name: str, book_id: int, chapter_id: int | None) -> dict | None:
        for p in self._list_all("pages"):
            if p["name"] == name and p.get("book_id") == book_id:
                if chapter_id is None or p.get("chapter_id") == chapter_id:
                    return p
        return None

    def create_or_update_page(
        self,
        name: str,
        markdown: str,
        book_id: int,
        chapter_id: int | None = None,
    ) -> dict:
        existing = self.find_page(name, book_id, chapter_id)
        payload: dict = {"name": name, "markdown": markdown}
        if existing:
            log.info("    Updating page: %s", name)
            return self._put(f"pages/{existing['id']}", payload)
        else:
            log.info("    Creating page: %s", name)
            payload["book_id"] = book_id
            if chapter_id:
                payload["chapter_id"] = chapter_id
            return self._post("pages", payload)

    # ------------------------------------------------------------------
    # Attachments
    # ------------------------------------------------------------------
    def list_attachments(self, page_id: int) -> list[dict]:
        return self._list_all("attachments", params={"filter[uploaded_to]": page_id})

    def get_attachment(self, attachment_id: int) -> dict:
        return self._get(f"attachments/{attachment_id}")

    def upload_attachment(self, page_id: int, file_path: Path) -> dict:
        mime, _ = mimetypes.guess_type(str(file_path))
        mime = mime or "application/octet-stream"
        log.info("      Attaching file: %s", file_path.name)
        with open(file_path, "rb") as fh:
            return self._post_multipart(
                "attachments",
                data={"name": file_path.name, "uploaded_to": str(page_id)},
                files={"file": (file_path.name, fh, mime)},
            )

    def upload_image(self, page_id: int, file_path: Path) -> dict:
        mime, _ = mimetypes.guess_type(str(file_path))
        mime = mime or "image/png"
        log.info("      Uploading image: %s", file_path.name)
        with open(file_path, "rb") as fh:
            return self._post_multipart(
                "image-gallery",
                data={"type": "gallery", "uploaded_to": str(page_id)},
                files={"image": (file_path.name, fh, mime)},
            )


# ---------------------------------------------------------------------------
# Import helpers
# ---------------------------------------------------------------------------
IMAGE_EXTENSIONS = {".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp", ".bmp"}


def rewrite_image_links(markdown: str, page_dir: Path, client: BookStackClient, page_id: int) -> str:
    def replace_match(m: re.Match) -> str:
        alt, ref = m.group(1), m.group(2)
        if ref.startswith(("http://", "https://", "//", "data:")):
            return m.group(0)
        img_path = (page_dir / ref).resolve()
        if not img_path.exists():
            log.warning("      Image not found, skipping: %s", img_path)
            return m.group(0)
        try:
            result = client.upload_image(page_id, img_path)
            return f"![{alt}]({result.get('url', ref)})"
        except Exception as exc:
            log.warning("      Failed to upload image %s: %s", img_path.name, exc)
            return m.group(0)

    return re.sub(r"!\[([^\]]*)\]\(([^)]+)\)", replace_match, markdown)


def upload_attachments_dir(page_dir: Path, page_id: int, client: BookStackClient):
    attach_dir = page_dir / "attachments"
    if not attach_dir.is_dir():
        return
    for f in sorted(attach_dir.iterdir()):
        if f.is_file():
            try:
                client.upload_attachment(page_id, f)
            except Exception as exc:
                log.warning("      Failed to attach %s: %s", f.name, exc)


def process_page(md_file: Path, book_id: int, chapter_id: int | None, client: BookStackClient):
    name = infer_name(md_file)
    raw_md = md_file.read_text(encoding="utf-8")

    processed_md = preprocess_markdown(raw_md)
    if EMOJI_AVAILABLE and processed_md != raw_md:
        log.info("    Converted emoji shortcodes in: %s", name)

    page = client.create_or_update_page(name, processed_md, book_id, chapter_id)
    page_id: int = page.get("id", 0)

    if page_id and not client.dry_run:
        updated_md = rewrite_image_links(processed_md, md_file.parent, client, page_id)
        if updated_md != processed_md:
            client._put(f"pages/{page_id}", {"markdown": updated_md})
        upload_attachments_dir(md_file.parent, page_id, client)

    time.sleep(0.1)


def process_directory(root: Path, client: BookStackClient, shelf_id: int | None):
    if not root.is_dir():
        log.error("Root path is not a directory: %s", root)
        sys.exit(1)

    book_dirs = sorted([d for d in root.iterdir() if d.is_dir()])
    if not book_dirs:
        log.error("No book directories found under %s", root)
        sys.exit(1)

    for book_dir in book_dirs:
        book_name = infer_name(book_dir)
        log.info("Book: %s", book_name)
        book = client.get_or_create_book(book_name, shelf_id)
        book_id: int = book.get("id", 0)

        for entry in sorted(book_dir.iterdir()):
            if entry.name.startswith("."):
                continue
            if entry.is_dir() and entry.name.lower() == "attachments":
                continue
            if entry.is_dir():
                chapter_name = infer_name(entry)
                log.info("  Chapter: %s", chapter_name)
                chapter = client.get_or_create_chapter(chapter_name, book_id)
                chapter_id: int = chapter.get("id", 0)
                for md_file in sorted(entry.glob("*.md")):
                    process_page(md_file, book_id, chapter_id, client)
            elif entry.suffix.lower() == ".md":
                process_page(entry, book_id, None, client)





# ---------------------------------------------------------------------------
# Export helpers
# ---------------------------------------------------------------------------
def safe_filename(name: str) -> str:
    """Make a name safe for use as a filename, preserving readability."""
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "-", name)
    name = name.strip(". ")
    return name or "untitled"


def download_attachments(client: BookStackClient, page_id: int, dest_dir: Path, dry_run: bool):
    """Download all file attachments for a page into dest_dir/attachments/.

    BookStack serves uploaded attachments via the API endpoint (auth required):
      GET /api/attachments/{id}  →  redirects to the file or returns content
    External/linked attachments are saved as .url shortcut files.
    """
    attachments = client.list_attachments(page_id)
    if not attachments:
        return

    attach_dir = dest_dir / "attachments"
    if not dry_run:
        attach_dir.mkdir(parents=True, exist_ok=True)

    for att in attachments:
        try:
            detail = client.get_attachment(att["id"])
        except Exception as exc:
            log.warning("      Could not fetch attachment detail %s: %s", att.get("name"), exc)
            continue

        # External (linked) attachments — save as a .url shortcut file
        if detail.get("external"):
            fname = safe_filename(detail["name"]) + ".url"
            content = f"[InternetShortcut]\nURL={detail.get('path', detail.get('url', ''))}\n"
            log.info("      Saving linked attachment: %s", fname)
            if not dry_run:
                (attach_dir / fname).write_text(content, encoding="utf-8")
            continue

        # Uploaded file — BookStack serves it via the API with auth
        fname = safe_filename(detail["name"])
        log.info("      Downloading attachment: %s", fname)
        if not dry_run:
            try:
                # The correct authenticated endpoint for file downloads
                download_url = f"{client.base_url}/api/attachments/{detail['id']}"
                data = client._get_binary(download_url)
                (attach_dir / fname).write_bytes(data)
                log.info("      Saved attachment: %s (%d bytes)", fname, len(data))
            except Exception as exc:
                log.warning("      Failed to download attachment %s: %s", fname, exc)


def download_inline_images(
    client: BookStackClient,
    markdown: str,
    dest_dir: Path,
    dry_run: bool,
) -> str:
    """Find all inline images hosted on BookStack, download them locally,
    and rewrite the markdown to use relative paths so it renders offline.

    Handles URLs like:
      http://192.168.1.79/uploads/images/gallery/2026-03/image.jpg
      http://192.168.1.79/uploads/images/gallery/2026-03/scaled-...
    """
    images_dir = dest_dir / "images"
    downloaded: dict[str, str] = {}  # original URL → relative path

    def replace_match(m: re.Match) -> str:
        alt = m.group(1)
        url = m.group(2)

        # Only rewrite URLs pointing at our BookStack instance
        parsed = urlparse(url)
        base_parsed = urlparse(client.base_url)
        if parsed.netloc != base_parsed.netloc:
            return m.group(0)  # external image, leave as-is

        # Reuse already-downloaded file if same URL appears multiple times
        if url in downloaded:
            return f"![{alt}]({downloaded[url]})"

        # Derive a local filename from the URL path
        url_path = parsed.path.lstrip("/")
        fname = Path(url_path).name  # e.g. "printer-parts-pic.jpg"
        # Avoid collisions: prefix with a short hash if needed
        local_path = images_dir / fname
        counter = 1
        while local_path.exists() and local_path in [Path(v) for v in downloaded.values()]:
            stem = Path(fname).stem
            suffix = Path(fname).suffix
            local_path = images_dir / f"{stem}-{counter}{suffix}"
            counter += 1

        rel_path = f"images/{local_path.name}"
        downloaded[url] = rel_path

        log.info("      Downloading image: %s → %s", url, rel_path)
        if not dry_run:
            images_dir.mkdir(parents=True, exist_ok=True)
            try:
                data = client._get_binary(url)
                local_path.write_bytes(data)
            except Exception as exc:
                log.warning("      Failed to download image %s: %s", url, exc)
                return m.group(0)  # keep original URL on failure

        return f"![{alt}]({rel_path})"

    return re.sub(r"!\[([^\]]*)\]\(([^)]+)\)", replace_match, markdown)


def export_page(client: BookStackClient, page_summary: dict, dest_dir: Path, dry_run: bool):
    """Export a single page to a .md file.

    - Downloads images embedded in markdown and rewrites URLs to relative paths
    - Downloads file attachments into an attachments/ subdirectory
    """
    page = client.get_page(page_summary["id"])
    name = page.get("name", "untitled")
    markdown = page.get("markdown", "") or ""

    if not markdown.strip():
        log.warning("    Page '%s' has no markdown content (may be WYSIWYG-only)", name)

    fname = safe_filename(name) + ".md"
    log.info("    Exporting page: %s → %s", name, fname)

    if not dry_run:
        dest_dir.mkdir(parents=True, exist_ok=True)

    # Download embedded images and rewrite URLs to relative paths
    markdown = download_inline_images(client, markdown, dest_dir, dry_run)

    if not dry_run:
        (dest_dir / fname).write_text(markdown, encoding="utf-8")

    # Download file attachments
    download_attachments(client, page["id"], dest_dir, dry_run)

    time.sleep(0.05)


def export_book(client: BookStackClient, book_summary: dict, root_dir: Path, dry_run: bool):
    """Export a full book (chapters + pages) to a directory."""
    book_name = book_summary["name"]
    book_dir = root_dir / safe_filename(book_name)
    log.info("Book: %s → %s/", book_name, book_dir)

    # Fetch full book detail to get ordered contents
    book = client.get_book(book_summary["id"])
    contents = book.get("contents", [])

    # contents is a flat list of chapters and pages with a 'type' field
    # ordered by their position in the book
    chapters_seen: dict[int, Path] = {}

    for item in contents:
        itype = item.get("type")

        if itype == "chapter":
            chapter_name = item["name"]
            chapter_dir = book_dir / safe_filename(chapter_name)
            chapters_seen[item["id"]] = chapter_dir
            log.info("  Chapter: %s", chapter_name)

            # Pages inside this chapter
            for page_item in item.get("pages", []):
                export_page(client, page_item, chapter_dir, dry_run)

        elif itype == "page":
            # Top-level page (no chapter)
            export_page(client, item, book_dir, dry_run)


def export_all(client: BookStackClient, root_dir: Path, shelf_filter: str | None,
               book_filter: str | None, dry_run: bool):
    """Walk all books (optionally filtered) and export them."""
    if not dry_run:
        root_dir.mkdir(parents=True, exist_ok=True)

    all_books = client.list_books()

    # Filter by shelf
    if shelf_filter:
        shelves = client.list_shelves()
        target_shelf = next((s for s in shelves if s["name"] == shelf_filter), None)
        if not target_shelf:
            log.error("Shelf not found: %s", shelf_filter)
            sys.exit(1)
        shelf_detail = client.get_shelf(target_shelf["id"])
        shelf_book_ids = {b["id"] for b in shelf_detail.get("books", [])}
        all_books = [b for b in all_books if b["id"] in shelf_book_ids]
        log.info("Exporting shelf '%s' (%d books)", shelf_filter, len(all_books))

    # Filter by book name
    if book_filter:
        all_books = [b for b in all_books if b["name"] == book_filter]
        if not all_books:
            log.error("Book not found: %s", book_filter)
            sys.exit(1)

    if not all_books:
        log.warning("No books found to export.")
        return

    for book_summary in sorted(all_books, key=lambda b: b["name"]):
        export_book(client, book_summary, root_dir, dry_run)

    log.info("Export complete → %s", root_dir)


# ---------------------------------------------------------------------------
# Connectivity check (shared)
# ---------------------------------------------------------------------------
def connect(args) -> BookStackClient:
    client = BookStackClient(
        base_url=args.url,
        token_id=args.token_id,
        token_secret=args.token_secret,
        dry_run=getattr(args, "dry_run", False),
    )
    try:
        client._get("books", params={"count": 1})
        log.info("Connected to BookStack at %s", args.url)
    except requests.HTTPError as exc:
        log.error("API error (check token): %s", exc)
        sys.exit(1)
    except requests.exceptions.ConnectionError as exc:
        log.error(
            "Cannot connect to %s — check the URL and port are correct.\n"
            "  Hint: try 'curl %s/api/books?count=1' to verify.\n"
            "  Error: %s",
            args.url, args.url, exc,
        )
        sys.exit(1)
    return client


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="bookstack.py",
        description="Import or export BookStack content as a Markdown directory tree.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )

    # Shared arguments factory
    def add_common(sub):
        sub.add_argument("--url", required=True,
                         help="BookStack base URL, e.g. http://192.168.1.79")
        sub.add_argument("--token-id", required=True, help="API token ID")
        sub.add_argument("--token-secret", required=True, help="API token secret")
        sub.add_argument("--dir", required=True,
                         help="Local directory (source for import, destination for export)")
        sub.add_argument("--verbose", action="store_true", help="Enable debug logging")

    subs = p.add_subparsers(dest="command", metavar="{import,export}", required=True)

    # ---- import subcommand ------------------------------------------------
    imp = subs.add_parser(
        "import",
        help="Import a Markdown directory tree into BookStack",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    add_common(imp)
    imp.add_argument("--shelf", default=None,
                     help="Assign all imported books to this shelf (created if needed)")
    imp.add_argument("--dry-run", action="store_true",
                     help="Preview actions without modifying BookStack")

    # ---- export subcommand ------------------------------------------------
    exp = subs.add_parser(
        "export",
        help="Export BookStack content to a Markdown directory tree",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    add_common(exp)
    exp.add_argument("--shelf", default=None,
                     help="Export only books belonging to this shelf")
    exp.add_argument("--book", default=None,
                     help="Export only this book (by exact name)")
    exp.add_argument("--dry-run", action="store_true",
                     help="Preview what would be exported without writing files")

    return p


def main():
    parser = build_parser()
    args = parser.parse_args()

    if args.verbose:
        log.setLevel(logging.DEBUG)

    # ---- import -----------------------------------------------------------
    if args.command == "import":
        if args.dry_run:
            log.info("=== DRY RUN MODE – no changes will be made ===")

        if EMOJI_AVAILABLE:
            log.info("Emoji shortcode conversion: enabled")
        else:
            log.warning("Emoji shortcode conversion: disabled (pip install emoji to enable)")

        client = connect(args)

        shelf_id: int | None = None
        if args.shelf:
            shelf = client.get_or_create_shelf(args.shelf)
            shelf_id = shelf.get("id")

        process_directory(Path(args.dir), client, shelf_id)
        log.info("Import complete.")

    # ---- export -----------------------------------------------------------
    elif args.command == "export":
        if args.dry_run:
            log.info("=== DRY RUN MODE – no files will be written ===")

        client = connect(args)
        export_all(
            client=client,
            root_dir=Path(args.dir),
            shelf_filter=args.shelf,
            book_filter=args.book,
            dry_run=args.dry_run,
        )


if __name__ == "__main__":
    main()
