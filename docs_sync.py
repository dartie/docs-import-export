#!/usr/bin/env python3
r"""
docs_sync.py - Markdown import/export and bidirectional sync for BookStack & Wiki.js 3
======================================================================================

One script for moving documentation between a markdown directory tree, BookStack and
Wiki.js 3.  It can be used as two independent importers/exporters, or as a bridge that
copies content from one wiki to the other through a staging markdown bundle.

Directory layout
----------------
Every bundle is a plain markdown tree plus an optional ``.docsync.json`` manifest:

    bundle/
    |-- .docsync.json                 # exact titles, paths, tags, IDs, timestamps
    |-- Book Name/
    |   |-- Chapter Name/
    |   |   |-- Page Title.md
    |   |   `-- Page Title.assets/    # files referenced by that page
    |   |       `-- diagram.png
    |   `-- Top Level Page.md
    `-- Another Book/
        `-- ...

The manifest is what makes round-trips lossless for the things a markdown file cannot
carry: the exact (non-slugified) title, Wiki.js page path/locale, BookStack book and
chapter, tags, source IDs and update timestamps.  Import still works without it.

Asset convention
----------------
Export writes assets into ``<page-stem>.assets/`` next to the page and rewrites the
markdown to use relative links.  Import accepts that convention plus the older
``attachments/`` and ``images/`` directories produced by the existing scripts.

Requirements
------------
    pip install requests
    pip install markdown       # optional; gives high quality Wiki.js HTML renders

A Wiki.js *personal access token* is required for writes (pages and assets).  A system
API key can read, but Wiki.js refuses to save pages through one because a page records
an author.  Give the token at least ``pages:read``, ``pages:write``, ``assets:read`` and
``assets:write`` scopes.  BookStack uses a normal API token (Token ID + Secret).

Usage
-----
    # Markdown -> BookStack
    python docs_sync.py import --backend bookstack \
        --url https://bookstack.example.com \
        --token-id ID --token-secret SECRET --dir ./docs

    # BookStack -> Markdown
    python docs_sync.py export --backend bookstack \
        --url https://bookstack.example.com \
        --token-id ID --token-secret SECRET --dir ./docs-export

    # Markdown -> Wiki.js 3
    python docs_sync.py import --backend wikijs \
        --url https://wiki.example.com --token PERSONAL_TOKEN --dir ./docs

    # Wiki.js 3 -> Markdown
    python docs_sync.py export --backend wikijs \
        --url https://wiki.example.com --token PERSONAL_TOKEN --dir ./docs-export

    # Copy BookStack -> Wiki.js through a temporary markdown bundle
    python docs_sync.py sync-bookstack-to-wikijs \
        --bookstack-url https://bookstack.example.com \
        --bookstack-token-id ID --bookstack-token-secret SECRET \
        --wikijs-url https://wiki.example.com --wikijs-token PERSONAL_TOKEN

    # Copy Wiki.js -> BookStack
    python docs_sync.py sync-wikijs-to-bookstack \
        --wikijs-url https://wiki.example.com --wikijs-token PERSONAL_TOKEN \
        --bookstack-url https://bookstack.example.com \
        --bookstack-token-id ID --bookstack-token-secret SECRET

Subcommands
-----------
    import                      Markdown bundle -> wiki backend
    export                      wiki backend -> Markdown bundle
    sync-bookstack-to-wikijs    BookStack -> staging bundle -> Wiki.js
    sync-wikijs-to-bookstack    Wiki.js -> staging bundle -> BookStack
    sync                        generic --from/--to form of the two sync commands

Notes
-----
* ``--dry-run`` never changes the remote backend.  During a sync the source is still
  exported to the staging directory (so the target import has something to read), but
  the target import only logs what it would do.
* Imports update matching pages; they never delete pages that are absent from the
  bundle.  Deleting is deliberately left to a human.
* Wiki.js 3 does not render markdown on save.  This script renders it client-side and
  sends the result in ``render`` so that search, the table of contents and the page
  view stay correct.  Install the optional ``markdown`` package for the best results;
  a small built-in renderer is used otherwise.
"""

import argparse
import base64
import json
import logging
import mimetypes
import os
import re
import shutil
import sys
import tempfile
import time
import unicodedata
from datetime import datetime, timezone
from html import escape as html_escape
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import quote, unquote, urlparse

import requests

try:
    import markdown as markdown_lib
    MARKDOWN_AVAILABLE = True
except ImportError:
    markdown_lib = None
    MARKDOWN_AVAILABLE = False

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("docs_sync")

MANIFEST_NAME = ".docsync.json"
MANIFEST_VERSION = 1
DEFAULT_BOOK = "Imported"
IMAGE_EXTENSIONS = {".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp", ".bmp", ".avif"}
RETRY_STATUSES = {429, 500, 502, 503, 504}
UUID_RE = re.compile(r"^[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}$")


# ---------------------------------------------------------------------------
# Generic helpers
# ---------------------------------------------------------------------------
def slugify(text: str) -> str:
    """Turn a title/path segment into a safe Wiki.js-style path segment.

    Unlike the old scripts this keeps Unicode letters, because Wiki.js accepts them.
    """
    text = unicodedata.normalize("NFKC", text or "").strip().lower()
    text = re.sub(r"[\s_]+", "-", text)
    text = re.sub(r"[^\w-]", "", text, flags=re.UNICODE)
    text = re.sub(r"-+", "-", text).strip("-")
    return text or "page"


def safe_filename(name: str) -> str:
    """Make a readable name safe for a single filesystem path component."""
    name = (name or "").replace("\x00", "")
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "-", name)
    name = re.sub(r"\s+", " ", name).strip().strip(". ")
    return name or "untitled"


def humanize_name(name: str) -> str:
    """Turn a file/directory name into a readable title (without slugifying it)."""
    name = Path(str(name)).stem if str(name).lower().endswith(".md") else Path(str(name)).name
    name = re.sub(r"^\d+\.\s*", "", name)
    name = re.sub(r"^\d{1,3}[-_\s]+", "", name)
    name = name.replace("_", " ")
    name = re.sub(r"-(?!\d)|(?<!\d)-", " ", name)
    return name.strip().title() or "Untitled"


def content_title(content: str, fallback: str) -> str:
    """Use an explicit H1 near the start of the document, else the fallback title."""
    for line in content.splitlines()[:80]:
        stripped = line.strip()
        if stripped.startswith("# "):
            title = stripped[2:].strip()
            if title:
                return title
        elif stripped and not stripped.startswith(("<!--", "---")):
            # Stop at real body text; a late H1 is usually a section, not the title.
            break
    return fallback


def is_external_ref(ref: str) -> bool:
    lowered = ref.strip().lower()
    return lowered.startswith(
        ("http://", "https://", "//", "data:", "mailto:", "tel:", "javascript:", "ftp:", "#")
    )


def ref_path_and_suffix(ref: str) -> tuple[str, str]:
    """Return (decoded path, ?query#fragment) for a local-ish reference."""
    parsed = urlparse(ref)
    suffix = ""
    if parsed.query:
        suffix += "?" + parsed.query
    if parsed.fragment:
        suffix += "#" + parsed.fragment
    return unquote(parsed.path), suffix


def resolve_local_file(ref: str, page_dir: Path, bundle_root: Path) -> Path | None:
    """Resolve a markdown/HTML reference to a file inside the bundle, safely."""
    if is_external_ref(ref):
        return None
    path_part, _ = ref_path_and_suffix(ref)
    if not path_part:
        return None
    candidate = (bundle_root / path_part.lstrip("/")) if path_part.startswith("/") else (page_dir / path_part)
    try:
        candidate = candidate.resolve()
        candidate.relative_to(bundle_root.resolve())
    except (ValueError, OSError):
        return None
    if candidate.is_file():
        return candidate
    return None


def relative_ref(from_dir: Path, target: Path) -> str:
    """Return a URL-safe POSIX relative reference to a target file."""
    value = os.path.relpath(str(target), str(from_dir)).replace(os.sep, "/")
    # Encode spaces and other characters that would break markdown link syntax or
    # change meaning when parsed as a URL (notably "%", "#" and "?").
    return quote(value, safe="/-_.~")


def unique_strings(items) -> list[str]:
    seen, result = set(), []
    for item in items or []:
        value = str(item).strip()
        if value and value not in seen:
            seen.add(value)
            result.append(value)
    return result


def tags_from_bookstack(tags) -> list[str]:
    result = []
    for tag in tags or []:
        name = str(tag.get("name", "")).strip()
        value = str(tag.get("value", "")).strip()
        if not name and not value:
            continue
        result.append(f"{name}: {value}" if value else name)
    return unique_strings(result)


def tags_to_bookstack(tags) -> list[dict]:
    result = []
    for tag in unique_strings(tags):
        if ":" in tag:
            name, value = tag.split(":", 1)
            result.append({"name": name.strip(), "value": value.strip()})
        else:
            result.append({"name": tag, "value": ""})
    return result


def truncate(text: str, length: int, fallback: str = "Untitled") -> str:
    text = (text or "").strip()
    if not text:
        return fallback
    return text[:length]


def atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def atomic_write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_bytes(data)
    tmp.replace(path)


def load_manifest(root: Path) -> dict:
    path = root / MANIFEST_NAME
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("manifest is not a JSON object")
        return data
    except Exception as exc:
        log.warning("Could not read %s: %s", path, exc)
        return {}


# ---------------------------------------------------------------------------
# Markdown -> HTML (Wiki.js `render`)
# ---------------------------------------------------------------------------
def _escape_text(value: str) -> str:
    return html_escape(value, quote=False)


def _inline_markdown(text: str) -> str:
    """Small, dependency-free inline markdown renderer."""
    placeholders: dict[str, str] = {}

    def stash(value: str) -> str:
        key = f"\x00{len(placeholders)}\x00"
        placeholders[key] = value
        return key

    # Code spans first so their contents are not interpreted.
    text = re.sub(
        r"`([^`]+)`",
        lambda m: stash(f"<code>{_escape_text(m.group(1))}</code>"),
        text,
    )

    escaped = _escape_text(text)

    # Images, then links.
    escaped = re.sub(
        r"!\[([^\]]*)\]\(([^)\s]+)(?:\s+[\"']([^\"']*)[\"'])?\)",
        lambda m: (
            f'<img src="{m.group(2)}" alt="{m.group(1)}"'
            + (f' title="{m.group(3)}"' if m.group(3) else "")
            + ">"
        ),
        escaped,
    )
    escaped = re.sub(
        r"\[([^\]]+)\]\(([^)\s]+)(?:\s+[\"']([^\"']*)[\"'])?\)",
        lambda m: (
            f'<a href="{m.group(2)}"'
            + (f' title="{m.group(3)}"' if m.group(3) else "")
            + f">{m.group(1)}</a>"
        ),
        escaped,
    )
    escaped = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", escaped)
    escaped = re.sub(r"__([^_]+)__", r"<strong>\1</strong>", escaped)
    escaped = re.sub(r"(?<!\*)\*([^*\n]+)\*(?!\*)", r"<em>\1</em>", escaped)
    escaped = re.sub(r"(?<!_)_([^_\n]+)_(?!_)", r"<em>\1</em>", escaped)
    escaped = re.sub(r"~~([^~]+)~~", r"<del>\1</del>", escaped)

    for key, value in placeholders.items():
        escaped = escaped.replace(key, value)
    return escaped


def fallback_render_markdown(text: str) -> str:
    """A compact line-based markdown renderer used when `markdown` is not installed."""
    lines = text.splitlines()
    out: list[str] = []
    paragraph: list[str] = []
    in_fence = False
    fence_marker = ""
    fence_lang = ""
    fence_lines: list[str] = []
    in_list = False
    list_ordered = False
    list_counter = 1

    def flush_paragraph() -> None:
        if paragraph:
            out.append("<p>" + _inline_markdown(" ".join(paragraph)) + "</p>")
            paragraph.clear()

    def close_list() -> None:
        nonlocal in_list
        if in_list:
            out.append("</ol>" if list_ordered else "</ul>")
            in_list = False

    for line in lines:
        stripped = line.strip()

        if in_fence:
            if re.match(rf"^{re.escape(fence_marker)}{{3,}}\s*$", stripped):
                code = "\n".join(fence_lines)
                cls = f' class="language-{fence_lang}"' if fence_lang else ""
                out.append(f"<pre><code{cls}>{_escape_text(code)}</code></pre>")
                in_fence = False
                fence_lines = []
                fence_marker = ""
                fence_lang = ""
            else:
                fence_lines.append(line)
            continue

        fence_match = re.match(r"^(`{3,}|~{3,})\s*([\w+-]*)\s*$", stripped)
        if fence_match:
            flush_paragraph()
            close_list()
            in_fence = True
            fence_marker = fence_match.group(1)[0]
            fence_lang = fence_match.group(2) or ""
            continue

        if not stripped:
            flush_paragraph()
            close_list()
            continue

        if re.match(r"^<([a-zA-Z!/])", stripped):
            flush_paragraph()
            close_list()
            out.append(line)
            continue

        heading = re.match(r"^(#{1,6})\s+(.*)$", stripped)
        if heading:
            flush_paragraph()
            close_list()
            level = len(heading.group(1))
            out.append(f"<h{level}>{_inline_markdown(heading.group(2))}</h{level}>")
            continue

        if re.match(r"^(\*\s*){3,}$|^(-\s*){3,}$|^(_\s*){3,}$", stripped):
            flush_paragraph()
            close_list()
            out.append("<hr>")
            continue

        if stripped.startswith(">"):
            flush_paragraph()
            close_list()
            quote = re.sub(r"^>\s?", "", stripped)
            out.append(f"<blockquote><p>{_inline_markdown(quote)}</p></blockquote>")
            continue

        bullet = re.match(r"^[-+*]\s+(.*)$", stripped)
        ordered = re.match(r"^(\d+)\.\s+(.*)$", stripped)
        if bullet or ordered:
            flush_paragraph()
            want_ordered = bool(ordered)
            if not in_list or list_ordered != want_ordered:
                close_list()
                out.append("<ol>" if want_ordered else "<ul>")
                in_list = True
                list_ordered = want_ordered
                list_counter = 1
            item = bullet.group(1) if bullet else ordered.group(2)
            if ordered:
                out.append(f"<li>{_inline_markdown(item)}</li>")
                list_counter += 1
            else:
                out.append(f"<li>{_inline_markdown(item)}</li>")
            continue

        paragraph.append(stripped)

    if in_fence:
        code = "\n".join(fence_lines)
        out.append(f"<pre><code>{_escape_text(code)}</code></pre>")
    flush_paragraph()
    close_list()
    return "\n".join(out)


def render_markdown_to_html(text: str) -> str:
    if not text or not text.strip():
        return ""
    if MARKDOWN_AVAILABLE:
        try:
            renderer = markdown_lib.Markdown(
                extensions=["fenced_code", "tables", "sane_lists", "nl2br"],
                output_format="html5",
            )
            return renderer.convert(text)
        except Exception as exc:  # pragma: no cover - defensive around optional dep
            log.debug("markdown package failed (%s); using fallback renderer", exc)
    return fallback_render_markdown(text)


# ---------------------------------------------------------------------------
# HTML -> Markdown (BookStack WYSIWYG fallback)
# ---------------------------------------------------------------------------
class _HTMLToMarkdown(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.parts: list[str] = []
        self.list_stack: list[dict] = []
        self.href_stack: list[str] = []
        self.in_pre = False
        self.ignore_depth = 0

    def _append(self, value: str) -> None:
        if value:
            self.parts.append(value)

    def _newlines(self, count: int = 2) -> None:
        tail = "".join(self.parts[-3:])
        existing = len(tail) - len(tail.rstrip("\n"))
        if existing < count:
            self.parts.append("\n" * (count - existing))

    def handle_starttag(self, tag, attrs):
        tag = tag.lower()
        attrs = dict(attrs)
        if tag in ("script", "style", "noscript"):
            self.ignore_depth += 1
            return
        if self.ignore_depth:
            return
        if tag in ("h1", "h2", "h3", "h4", "h5", "h6"):
            self._newlines(2)
            self._append("#" * int(tag[1]) + " ")
        elif tag in ("p", "div", "section", "article", "header", "footer", "main"):
            self._newlines(2)
        elif tag == "br":
            self._append("  \n")
        elif tag == "hr":
            self._newlines(2)
            self._append("---")
            self._newlines(2)
        elif tag in ("strong", "b"):
            self._append("**")
        elif tag in ("em", "i"):
            self._append("*")
        elif tag in ("del", "s", "strike"):
            self._append("~~")
        elif tag == "code":
            if not self.in_pre:
                self._append("`")
        elif tag == "pre":
            self.in_pre = True
            self._newlines(2)
            self._append("```\n")
        elif tag == "blockquote":
            self._newlines(2)
            self._append("> ")
        elif tag == "a":
            href = attrs.get("href", "")
            self.href_stack.append(href)
            self._append("[")
        elif tag == "img":
            src = attrs.get("src", "")
            alt = attrs.get("alt", "")
            title = attrs.get("title", "")
            suffix = f' "{title}"' if title else ""
            self._append(f"![{alt}]({src}{suffix})")
        elif tag in ("ul", "ol"):
            self._newlines(1)
            self.list_stack.append({"ordered": tag == "ol", "counter": 1})
        elif tag == "li":
            indent = "  " * max(0, len(self.list_stack) - 1)
            marker = "- "
            if self.list_stack and self.list_stack[-1]["ordered"]:
                marker = f"{self.list_stack[-1]['counter']}. "
                self.list_stack[-1]["counter"] += 1
            self._newlines(1)
            self._append(indent + marker)
        elif tag in ("td", "th"):
            self._append(" | ")
        elif tag == "tr":
            self._newlines(1)
        elif tag in ("dt",):
            self._newlines(1)
        elif tag in ("dd",):
            self._newlines(1)
            self._append("  ")

    def handle_endtag(self, tag):
        tag = tag.lower()
        if tag in ("script", "style", "noscript"):
            self.ignore_depth = max(0, self.ignore_depth - 1)
            return
        if self.ignore_depth:
            return
        if tag in ("h1", "h2", "h3", "h4", "h5", "h6", "p", "div", "section", "article"):
            self._newlines(2)
        elif tag in ("strong", "b"):
            self._append("**")
        elif tag in ("em", "i"):
            self._append("*")
        elif tag in ("del", "s", "strike"):
            self._append("~~")
        elif tag == "code":
            if not self.in_pre:
                self._append("`")
        elif tag == "pre":
            self._newlines(1)
            self._append("```")
            self._newlines(2)
            self.in_pre = False
        elif tag == "a":
            href = self.href_stack.pop() if self.href_stack else ""
            self._append(f"]({href})" if href else "]")
        elif tag in ("ul", "ol"):
            if self.list_stack:
                self.list_stack.pop()
            self._newlines(1)
        elif tag == "li":
            self._newlines(1)
        elif tag == "blockquote":
            self._newlines(2)
        elif tag in ("table", "tr"):
            self._newlines(1)

    def handle_data(self, data):
        if self.ignore_depth:
            return
        if self.in_pre:
            self._append(data)
        else:
            self._append(re.sub(r"[ \t\r\n]+", " ", data))

    def markdown(self) -> str:
        text = "".join(self.parts)
        text = re.sub(r"[ \t]+\n", "\n", text)
        text = re.sub(r"\n{3,}", "\n\n", text)
        return text.strip() + ("\n" if text.strip() else "")


def html_to_markdown(html: str) -> str:
    if not html or not html.strip():
        return ""
    parser = _HTMLToMarkdown()
    try:
        parser.feed(html)
        parser.close()
        result = parser.markdown()
    except Exception as exc:
        log.debug("HTML parser failed (%s); falling back to tag stripping", exc)
        result = re.sub(r"<[^>]+>", "", html)
    return result


# ---------------------------------------------------------------------------
# Reference rewriting
# ---------------------------------------------------------------------------
MD_REF_RE = re.compile(
    r"(?P<prefix>!?\[[^\]]*\]\()\s*"
    r"(?:<(?P<angle>[^>\n]*)>|(?P<plain>[^)\n]*?))"
    r"(?P<suffix>(?:\s+(?:\"[^\"]*\"|'[^']*'))?\))"
)
HTML_ATTR_RE = re.compile(
    r'(?P<prefix>\b(?:src|href)\s*=\s*)(?P<quote>["\'])(?P<ref>.*?)(?P=quote)',
    re.IGNORECASE | re.DOTALL,
)


def rewrite_references(text: str, resolver) -> str:
    """Rewrite markdown links/images and HTML src/href attributes through resolver."""

    def replace_markdown(match: re.Match) -> str:
        ref = match.group("angle")
        if ref is None:
            ref = (match.group("plain") or "").strip()
        new_ref = resolver(ref)
        if new_ref is None:
            return match.group(0)
        if re.search(r"[\s()]", new_ref):
            new_ref = f"<{new_ref}>"
        return f"{match.group('prefix')}{new_ref}{match.group('suffix')}"

    def replace_html(match: re.Match) -> str:
        new_ref = resolver(match.group("ref"))
        if new_ref is None:
            return match.group(0)
        return f"{match.group('prefix')}{match.group('quote')}{new_ref}{match.group('quote')}"

    text = MD_REF_RE.sub(replace_markdown, text)
    text = HTML_ATTR_RE.sub(replace_html, text)
    return text


# ---------------------------------------------------------------------------
# BookStack API client
# ---------------------------------------------------------------------------
class BookStackClient:
    def __init__(self, base_url: str, token_id: str, token_secret: str,
                 dry_run: bool = False, timeout: int = 30):
        self.base_url = (base_url or "").rstrip("/")
        self.dry_run = dry_run
        self.timeout = timeout
        self.session = requests.Session()
        self.session.headers.update({
            "Authorization": f"Token {token_id}:{token_secret}",
            "Accept": "application/json",
            "User-Agent": "docs_sync/1.0",
        })
        self._cache: dict = {}
        self._book_pages: dict[int, dict[tuple, dict]] = {}

    # ---- low level ----------------------------------------------------
    def _request(self, method: str, path_or_url: str, **kwargs) -> requests.Response:
        url = path_or_url if path_or_url.startswith(("http://", "https://")) else f"{self.base_url}/api/{path_or_url.lstrip('/')}"
        headers = dict(self.session.headers)
        headers.update(kwargs.pop("headers", {}) or {})
        last_exc = None
        for attempt in range(3):
            try:
                response = self.session.request(method, url, headers=headers, timeout=self.timeout, **kwargs)
            except requests.RequestException as exc:
                last_exc = exc
                if attempt < 2:
                    time.sleep(2 ** attempt)
                    continue
                raise
            if response.status_code in RETRY_STATUSES and attempt < 2:
                retry_after = response.headers.get("Retry-After", "")
                try:
                    delay = max(0.5, float(retry_after))
                except ValueError:
                    delay = 2 ** attempt
                log.debug("BookStack %s %s -> %s, retrying in %.1fs", method, url, response.status_code, delay)
                time.sleep(delay)
                continue
            if response.status_code >= 400:
                snippet = response.text[:500].replace("\n", " ")
                raise RuntimeError(f"BookStack {method} {url} -> {response.status_code}: {snippet}")
            return response
        raise RuntimeError(f"BookStack request failed: {last_exc}")

    def _get(self, path: str, params: dict | None = None) -> dict:
        response = self._request("GET", path, params=params)
        if not response.content:
            return {}
        return response.json()

    def _post(self, path: str, payload: dict | None = None) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] POST /api/%s %s", path, json.dumps(payload or {})[:500])
            return {"id": 0, "name": (payload or {}).get("name", "(dry-run)")}
        response = self._request("POST", path, json=payload or {})
        return response.json() if response.content else {}

    def _put(self, path: str, payload: dict | None = None) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] PUT /api/%s %s", path, json.dumps(payload or {})[:500])
            return {"id": 0}
        response = self._request("PUT", path, json=payload or {})
        return response.json() if response.content else {}

    def _post_multipart(self, path: str, data: dict, files: dict) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] POST (multipart) /api/%s data=%s", path, data)
            return {"id": 0}
        response = self._request("POST", path, data=data, files=files)
        return response.json() if response.content else {}

    def download_url(self, url: str) -> bytes:
        if self.dry_run:
            return b""
        headers = {k: v for k, v in self.session.headers.items() if k.lower() != "content-type"}
        response = self._request("GET", url, headers=headers)
        return response.content

    def _list_all(self, path: str, params: dict | None = None) -> list[dict]:
        results: list[dict] = []
        offset = 0
        count = 500
        base_params = dict(params or {})
        while True:
            query = dict(base_params)
            query.update({"count": count, "offset": offset})
            data = self._get(path, params=query)
            items = data.get("data", []) or []
            results.extend(items)
            total = data.get("total", len(results))
            if not items or len(results) >= total:
                break
            offset += count
        return results

    # ---- shelves ------------------------------------------------------
    def list_shelves(self) -> list[dict]:
        return self._list_all("shelves")

    def get_shelf(self, shelf_id: int) -> dict:
        return self._get(f"shelves/{shelf_id}")

    def get_or_create_shelf(self, name: str) -> dict:
        key = f"shelf:{name}"
        if key in self._cache:
            return self._cache[key]
        for shelf in self.list_shelves():
            if shelf.get("name") == name:
                self._cache[key] = shelf
                return shelf
        log.info("Creating shelf: %s", name)
        shelf = self._post("shelves", {"name": name, "description": ""})
        self._cache[key] = shelf
        return shelf

    def assign_book_to_shelf(self, book_id: int, shelf_id: int) -> None:
        if not book_id or not shelf_id or self.dry_run:
            return
        try:
            shelf = self.get_shelf(shelf_id)
            existing = [b["id"] for b in shelf.get("books", [])]
            if book_id not in existing:
                self._put(f"shelves/{shelf_id}", {"books": existing + [book_id]})
        except Exception as exc:
            log.warning("Could not assign book %s to shelf %s: %s", book_id, shelf_id, exc)

    # ---- books --------------------------------------------------------
    def list_books(self) -> list[dict]:
        return self._list_all("books")

    def get_book(self, book_id: int) -> dict:
        return self._get(f"books/{book_id}")

    def get_or_create_book(self, name: str, shelf_id: int | None = None) -> dict:
        key = f"book:{name}"
        if key in self._cache:
            book = self._cache[key]
            if shelf_id:
                self.assign_book_to_shelf(book.get("id", 0), shelf_id)
            return book
        for book in self.list_books():
            if book.get("name") == name:
                self._cache[key] = book
                if shelf_id:
                    self.assign_book_to_shelf(book["id"], shelf_id)
                return book
        log.info("Creating book: %s", name)
        book = self._post("books", {"name": name, "description": ""})
        if shelf_id:
            self.assign_book_to_shelf(book.get("id", 0), shelf_id)
        self._cache[key] = book
        return book

    # ---- chapters -----------------------------------------------------
    def list_chapters(self, book_id: int) -> list[dict]:
        return self._list_all("chapters", params={"filter[book_id]": book_id})

    def get_or_create_chapter(self, name: str, book_id: int) -> dict:
        key = f"chapter:{book_id}:{name}"
        if key in self._cache:
            return self._cache[key]
        for chapter in self.list_chapters(book_id):
            if chapter.get("name") == name:
                self._cache[key] = chapter
                return chapter
        log.info("  Creating chapter: %s", name)
        chapter = self._post("chapters", {"name": name, "book_id": book_id, "description": ""})
        self._cache[key] = chapter
        return chapter

    # ---- pages --------------------------------------------------------
    def list_pages(self, book_id: int) -> list[dict]:
        return self._list_all("pages", params={"filter[book_id]": book_id})

    def get_page(self, page_id: int) -> dict:
        return self._get(f"pages/{page_id}")

    def _page_index(self, book_id: int) -> dict[tuple, dict]:
        if book_id not in self._book_pages:
            index = {}
            for page in self.list_pages(book_id):
                index[(page.get("chapter_id"), page.get("name"))] = page
            self._book_pages[book_id] = index
        return self._book_pages[book_id]

    def find_page(self, name: str, book_id: int, chapter_id: int | None) -> dict | None:
        if not book_id:
            return None
        return self._page_index(book_id).get((chapter_id, name))

    def remember_page(self, page: dict) -> None:
        book_id = page.get("book_id")
        if book_id:
            self._page_index(book_id)[(page.get("chapter_id"), page.get("name"))] = page

    def save_page(self, name: str, content: str, book_id: int, chapter_id: int | None = None,
                  html: bool = False, tags: list[dict] | None = None,
                  priority: int | None = None, existing: dict | None = None) -> dict:
        content_key = "html" if html else "markdown"
        payload: dict = {"name": name, content_key: content}
        if tags is not None:
            payload["tags"] = tags
        if priority is not None:
            payload["priority"] = priority
        if existing:
            if existing.get("book_id") and existing.get("book_id") != book_id:
                payload["book_id"] = book_id
            if existing.get("chapter_id") != chapter_id:
                payload["chapter_id"] = chapter_id
            log.info("    Updating page: %s", name)
            page = self._put(f"pages/{existing['id']}", payload)
            if page.get("id"):
                page.setdefault("name", name)
                page.setdefault("book_id", book_id)
                page.setdefault("chapter_id", chapter_id)
                self.remember_page(page)
            return page
        payload["book_id"] = book_id
        if chapter_id:
            payload["chapter_id"] = chapter_id
        log.info("    Creating page: %s", name)
        page = self._post("pages", payload)
        if page.get("id"):
            page.setdefault("name", name)
            page.setdefault("book_id", book_id)
            page.setdefault("chapter_id", chapter_id)
            self.remember_page(page)
        return page

    # ---- uploads ------------------------------------------------------
    def upload_attachment(self, page_id: int, file_path: Path) -> dict:
        mime, _ = mimetypes.guess_type(str(file_path))
        mime = mime or "application/octet-stream"
        log.info("      Attaching file: %s", file_path.name)
        with open(file_path, "rb") as handle:
            return self._post_multipart(
                "attachments",
                data={"name": file_path.name, "uploaded_to": str(page_id)},
                files={"file": (file_path.name, handle, mime)},
            )

    def upload_image(self, page_id: int, file_path: Path) -> dict:
        mime, _ = mimetypes.guess_type(str(file_path))
        mime = mime or "image/png"
        log.info("      Uploading image: %s", file_path.name)
        with open(file_path, "rb") as handle:
            return self._post_multipart(
                "image-gallery",
                data={"type": "gallery", "uploaded_to": str(page_id)},
                files={"image": (file_path.name, handle, mime)},
            )

    # ---- attachments --------------------------------------------------
    def list_attachments(self, page_id: int) -> list[dict]:
        return self._list_all("attachments", params={"filter[uploaded_to]": page_id})

    def get_attachment(self, attachment_id: int) -> dict:
        return self._get(f"attachments/{attachment_id}")

    def read_attachment(self, attachment_id: int) -> tuple[str, object]:
        """Return ("external", url) or ("file", bytes) for an attachment."""
        url = f"{self.base_url}/api/attachments/{attachment_id}"
        headers = {k: v for k, v in self.session.headers.items() if k.lower() != "content-type"}
        response = self._request("GET", url, headers=headers)
        content_type = response.headers.get("content-type", "").lower()
        if "json" in content_type:
            data = response.json()
            if data.get("external"):
                target = data.get("content") or data.get("path") or data.get("url") or ""
                return "external", target
            encoded = data.get("content") or ""
            if not encoded:
                raise RuntimeError(f"Attachment {attachment_id} returned no content")
            try:
                return "file", base64.b64decode(encoded, validate=False)
            except Exception:
                return "file", encoded.encode("utf-8")
        return "file", response.content


# ---------------------------------------------------------------------------
# Wiki.js 3 REST client
# ---------------------------------------------------------------------------
class WikiJSClient:
    def __init__(self, base_url: str, token: str, site: str = "current",
                 locale: str | None = None, dry_run: bool = False, timeout: int = 60):
        self.base_url = (base_url or "").rstrip("/")
        self.api_url = f"{self.base_url}/_api"
        self.token = token
        self.requested_site = site or "current"
        self.locale = locale
        self.dry_run = dry_run
        self.timeout = timeout
        self.site_id: str | None = None
        self.site_info: dict = {}
        self.session = requests.Session()
        self.session.headers.update({
            "Authorization": f"Bearer {token}",
            "Accept": "application/json",
            "User-Agent": "docs_sync/1.0",
        })
        self._tree_cache: dict[tuple, list[dict]] = {}

    # ---- low level ----------------------------------------------------
    def _request(self, method: str, path: str, params: dict | None = None,
                 json_body: dict | None = None, data: bytes | None = None,
                 headers: dict | None = None, expect_json: bool = True):
        url = path if path.startswith(("http://", "https://")) else f"{self.api_url}{path}"
        request_headers = dict(self.session.headers)
        request_headers.update(headers or {})
        last_exc = None
        for attempt in range(3):
            try:
                response = self.session.request(
                    method, url, params=params, json=json_body, data=data,
                    headers=request_headers, timeout=self.timeout,
                )
            except requests.RequestException as exc:
                last_exc = exc
                if attempt < 2:
                    time.sleep(2 ** attempt)
                    continue
                raise
            if response.status_code in RETRY_STATUSES and attempt < 2:
                retry_after = response.headers.get("Retry-After", "")
                try:
                    delay = max(0.5, float(retry_after))
                except ValueError:
                    delay = 2 ** attempt
                log.debug("Wiki.js %s %s -> %s, retrying in %.1fs", method, url, response.status_code, delay)
                time.sleep(delay)
                continue
            if response.status_code >= 400:
                snippet = response.text[:600].replace("\n", " ")
                if response.status_code == 401:
                    raise RuntimeError(
                        f"Wiki.js {method} {url} -> 401 Unauthorized. Check the personal access token. {snippet}"
                    )
                if response.status_code == 403 and "personal access token" in snippet.lower():
                    raise RuntimeError(
                        f"Wiki.js {method} {url} -> 403: this action needs a personal access token, "
                        f"not a system API key. {snippet}"
                    )
                raise RuntimeError(f"Wiki.js {method} {url} -> {response.status_code}: {snippet}")
            if response.status_code == 204 or not response.content:
                return {} if expect_json else b""
            if not expect_json:
                return response.content
            try:
                return response.json()
            except ValueError:
                return {}
        raise RuntimeError(f"Wiki.js request failed: {last_exc}")

    # ---- site ---------------------------------------------------------
    def resolve_site(self) -> dict:
        if self.site_id:
            return self.site_info
        target = (self.requested_site or "current").strip()
        if UUID_RE.match(target):
            self.site_info = {"id": target}
        elif target.lower() == "current":
            self.site_info = self._request("GET", "/sites/current")
        else:
            self.site_info = self._request("GET", f"/sites/{quote(target, safe='')}", params={"strict": "true"})
        self.site_id = self.site_info.get("id")
        if not self.site_id:
            raise RuntimeError("Could not determine the Wiki.js site ID; pass --site ID")
        if not self.locale:
            primary = (self.site_info.get("locales") or {}).get("primary")
            self.locale = primary or "en"
        return self.site_info

    @property
    def _site_path(self) -> str:
        self.resolve_site()
        return f"/sites/{self.site_id}"

    def _tree_locale(self, locale: str | None) -> str | None:
        return locale if locale is not None else self.locale

    # ---- tree ---------------------------------------------------------
    def list_tree(self, parent_path: str = "", types: str | None = "folder,page,asset",
                  locale: str | None = None) -> list[dict]:
        parent_path = (parent_path or "").strip("/")
        use_locale = self._tree_locale(locale)
        cache_key = (parent_path, types, use_locale)
        if cache_key in self._tree_cache:
            return self._tree_cache[cache_key]
        results: list[dict] = []
        offset = 0
        limit = 1000
        while True:
            params = {
                "limit": limit,
                "offset": offset,
                "orderBy": "title",
                "orderByDirection": "asc",
            }
            if parent_path:
                params["parentPath"] = parent_path
            if types:
                params["types"] = types
            if use_locale:
                params["locale"] = use_locale
            items = self._request("GET", f"{self._site_path}/tree", params=params) or []
            results.extend(items)
            if len(items) < limit:
                break
            offset += len(items)
        self._tree_cache[cache_key] = results
        return results

    def invalidate_tree(self, parent_path: str | None = None) -> None:
        if parent_path is None:
            self._tree_cache.clear()
            return
        parent_path = (parent_path or "").strip("/")
        for key in list(self._tree_cache):
            if key[0] == parent_path:
                del self._tree_cache[key]

    def walk_tree(self, locale: str | None = None):
        """Yield tree items depth-first, with folder paths resolved."""
        queue: list[str] = [""]
        visited: set[str] = set()
        while queue:
            folder = queue.pop(0)
            if folder in visited:
                continue
            visited.add(folder)
            for item in self.list_tree(folder, types="folder,page,asset", locale=locale):
                item = dict(item)
                item["_path"] = "/".join(
                    part for part in [item.get("folderPath", ""), item.get("fileName", "")] if part
                )
                yield item
                if item.get("type") == "folder":
                    queue.append(item["_path"])

    # ---- pages --------------------------------------------------------
    def get_page(self, page_id: str, with_content: bool = True) -> dict | None:
        params = {}
        if with_content:
            params["withContent"] = "true"
        if self.locale:
            params["locale"] = self.locale
        try:
            return self._request("GET", f"{self._site_path}/pages/{page_id}", params=params)
        except RuntimeError as exc:
            if "-> 404" in str(exc):
                return None
            raise

    def find_page_by_path(self, path: str, locale: str | None = None) -> dict | None:
        path = (path or "").strip("/")
        parent, _, name = path.rpartition("/")
        for item in self.list_tree(parent, types="page", locale=locale):
            if item.get("type") not in (None, "page"):
                continue
            if item.get("fileName") == name or (not parent and item.get("fileName") == path):
                return item
        return None

    def create_page(self, payload: dict) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] CREATE Wiki.js page /%s (%s)", payload.get("path"), payload.get("title"))
            return {"page": {"id": "dry-run", **payload}}
        result = self._request("POST", f"{self._site_path}/pages", json_body=payload)
        self.invalidate_tree((payload.get("path") or "").rsplit("/", 1)[0] if "/" in (payload.get("path") or "") else "")
        return result

    def update_page(self, page_id: str, payload: dict) -> dict:
        if self.dry_run:
            log.info("[DRY-RUN] UPDATE Wiki.js page /%s (id=%s)", payload.get("path"), page_id)
            return {"page": {"id": page_id, **payload}}
        result = self._request("PATCH", f"{self._site_path}/pages/{page_id}", json_body=payload)
        if "/" in (payload.get("path") or ""):
            self.invalidate_tree((payload.get("path") or "").rsplit("/", 1)[0])
        else:
            self.invalidate_tree("")
        return result

    # ---- assets -------------------------------------------------------
    def upload_asset(self, file_path: Path, folder_path: str, locale: str | None = None) -> dict | None:
        folder_path = "/".join(
            part for part in (folder_path or "").strip("/").split("/") if part and part not in (".", "..")
        )
        if self.dry_run:
            url = "/" + "/".join(part for part in [folder_path, file_path.name] if part)
            log.info("[DRY-RUN] UPLOAD Wiki.js asset %s -> %s", file_path.name, url)
            return {"folderPath": folder_path, "fileName": file_path.name}
        mime, _ = mimetypes.guess_type(str(file_path))
        mime = mime or "application/octet-stream"
        params = {"fileName": file_path.name}
        if folder_path:
            params["folderPath"] = folder_path
        if locale:
            params["locale"] = locale
        data = file_path.read_bytes()
        log.info("      Uploading asset: %s", file_path.name)
        result = self._request(
            "POST", f"{self._site_path}/assets", params=params, data=data,
            headers={"Content-Type": mime},
        )
        self.invalidate_tree(folder_path)
        return result.get("asset") if isinstance(result, dict) else None

    def find_asset(self, path: str, locale: str | None = None) -> dict | None:
        path = (path or "").strip("/")
        parent, _, name = path.rpartition("/")
        for item in self.list_tree(parent, types="asset", locale=locale):
            if item.get("type") not in (None, "asset"):
                continue
            if item.get("fileName") == name:
                return item
        return None

    def download_asset(self, asset_id: str) -> bytes:
        if self.dry_run:
            return b""
        return self._request("GET", f"{self._site_path}/assets/{asset_id}/content", expect_json=False)


# ---------------------------------------------------------------------------
# Bundle writer / reader
# ---------------------------------------------------------------------------
class BundleWriter:
    def __init__(self, root: Path, source: dict, dry_run: bool = False):
        self.root = root
        self.source = source
        self.dry_run = dry_run
        self.documents: dict[str, dict] = {}
        self.folders: dict[str, dict] = {}
        self._reserved: dict[str, set[str]] = {}

    def ensure_dir(self, rel_dir: Path | str, title: str | None = None) -> None:
        rel_dir = Path(rel_dir)
        if str(rel_dir) in ("", "."):
            return
        key = rel_dir.as_posix()
        if title and key not in self.folders:
            self.folders[key] = {"title": title}
        if not self.dry_run:
            (self.root / rel_dir).mkdir(parents=True, exist_ok=True)

    def _name_taken(self, parent_rel: Path, name: str) -> bool:
        key = Path(parent_rel).as_posix()
        if name.lower() in self._reserved.get(key, set()):
            return True
        return not self.dry_run and (self.root / parent_rel / name).exists()

    def _reserve_name(self, parent_rel: Path, name: str) -> str:
        parent_rel = Path(parent_rel)
        key = parent_rel.as_posix()
        reserved = self._reserved.setdefault(key, set())
        stem, suffix = os.path.splitext(name)
        candidate = name
        index = 2
        while self._name_taken(parent_rel, candidate):
            candidate = f"{stem}-{index}{suffix}" if suffix else f"{name}-{index}"
            index += 1
        reserved.add(candidate.lower())
        return candidate

    def reserve_dir(self, parent_rel: Path | str, title: str) -> Path:
        parent_rel = Path(parent_rel) if str(parent_rel) not in ("", ".") else Path()
        name = self._reserve_name(parent_rel, safe_filename(title))
        rel = parent_rel / name if str(parent_rel) not in ("", ".") else Path(name)
        self.ensure_dir(rel, title=title)
        return rel

    def ensure_path_dirs(self, rel_dir: Path | str, titles: dict[str, str] | None = None) -> Path:
        rel_dir = Path(rel_dir)
        if str(rel_dir) in ("", "."):
            return Path()
        titles = titles or {}
        current = Path()
        for part in rel_dir.parts:
            current = current / part
            self.ensure_dir(current, title=titles.get(current.as_posix()))
        return rel_dir

    def reserve_markdown(self, parent_rel: Path | str, filename_stem: str) -> Path:
        parent_rel = Path(parent_rel) if str(parent_rel) not in ("", ".") else Path()
        self.ensure_dir(parent_rel)
        name = self._reserve_name(parent_rel, safe_filename(filename_stem) + ".md")
        return parent_rel / name if str(parent_rel) not in ("", ".") else Path(name)

    def asset_dir_for(self, page_rel: Path) -> Path:
        return page_rel.parent / (page_rel.stem + ".assets")

    def reserve_asset(self, asset_dir_rel: Path, filename: str) -> Path:
        self.ensure_dir(asset_dir_rel)
        name = self._reserve_name(asset_dir_rel, safe_filename(filename))
        return asset_dir_rel / name

    def write_text(self, rel: Path, text: str) -> None:
        if self.dry_run:
            return
        atomic_write_text(self.root / rel, text)

    def write_bytes(self, rel: Path, data: bytes) -> None:
        if self.dry_run:
            return
        atomic_write_bytes(self.root / rel, data)

    def add_document(self, page_rel: Path, metadata: dict) -> None:
        self.documents[page_rel.as_posix()] = metadata

    def write_manifest(self) -> None:
        if self.dry_run:
            return
        manifest = {
            "version": MANIFEST_VERSION,
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "source": self.source,
            "folders": self.folders,
            "documents": self.documents,
        }
        atomic_write_text(
            self.root / MANIFEST_NAME,
            json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        )


class BundleReader:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.manifest = load_manifest(self.root)
        self.documents = self.manifest.get("documents") or {}
        self.folders = self.manifest.get("folders") or {}

    def document_meta(self, rel: Path) -> dict:
        return self.documents.get(rel.as_posix()) or {}

    def folder_title(self, key: str) -> str:
        key = (key or "").strip("/")
        entry = self.folders.get(key)
        if isinstance(entry, dict) and entry.get("title"):
            return entry["title"]
        return humanize_name(key.rsplit("/", 1)[-1] if key else "untitled")

    def markdown_files(self) -> list[Path]:
        files = []
        for path in sorted(self.root.rglob("*.md")):
            rel = path.relative_to(self.root)
            if any(part.startswith(".") for part in rel.parts):
                continue
            if any(part.lower().endswith(".assets") for part in rel.parts[:-1]):
                continue
            if path.is_file():
                files.append(rel)
        return files

    def missing_documents(self, seen: set[str]) -> list[str]:
        return sorted(set(self.documents) - seen)


# ---------------------------------------------------------------------------
# BookStack export: download images and attachments for one page
# ---------------------------------------------------------------------------
class BookStackExportResolver:
    def __init__(self, client: BookStackClient, page: dict, page_rel: Path,
                 asset_dir_rel: Path, writer: BundleWriter):
        self.client = client
        self.page = page
        self.page_rel = page_rel
        self.asset_dir_rel = asset_dir_rel
        self.writer = writer
        self.attachment_map: dict[str, str] = {}
        self.image_map: dict[str, str] = {}
        if not writer.dry_run:
            self._load_attachments()

    def _key_variants(self, ref: str) -> list[str]:
        ref = (ref or "").strip()
        variants = {ref}
        parsed = urlparse(ref)
        if parsed.path:
            variants.add(unquote(parsed.path))
            variants.add(unquote(parsed.path).rstrip("/"))
            variants.add(unquote(parsed.path) + ("#" + parsed.fragment if parsed.fragment else ""))
        return [value for value in variants if value]

    def _remember(self, mapping: dict[str, str], keys, value: str) -> None:
        for key in keys:
            if key:
                mapping[key] = value

    def _load_attachments(self) -> None:
        try:
            attachments = self.client.list_attachments(self.page["id"])
        except Exception as exc:
            log.warning("      Could not list attachments: %s", exc)
            return
        for attachment in attachments:
            try:
                detail = self.client.get_attachment(attachment["id"])
            except Exception as exc:
                log.warning("      Could not read attachment %s: %s", attachment.get("name"), exc)
                continue
            name = safe_filename(detail.get("name") or attachment.get("name") or "attachment")
            extension = detail.get("extension") or ""
            if extension and not name.lower().endswith("." + extension.lower()):
                name += "." + extension
            keys = self._key_variants(f"/attachments/{detail['id']}")
            keys += self._key_variants(detail.get("url", ""))
            keys += self._key_variants(detail.get("path", ""))
            if detail.get("external"):
                target = detail.get("content") or detail.get("path") or detail.get("url") or ""
                shortcut = self.writer.reserve_asset(self.asset_dir_rel, name + ".url")
                self.writer.write_text(shortcut, f"[InternetShortcut]\nURL={target}\n")
                self._remember(self.attachment_map, keys, target)
                continue
            try:
                kind, payload = self.client.read_attachment(detail["id"])
            except Exception as exc:
                log.warning("      Could not download attachment %s: %s", name, exc)
                continue
            if kind != "file" or not isinstance(payload, bytes):
                self._remember(self.attachment_map, keys, str(payload))
                continue
            target = self.writer.reserve_asset(self.asset_dir_rel, name)
            self.writer.write_bytes(target, payload)
            local = relative_ref(self.page_rel.parent, target)
            self._remember(self.attachment_map, keys, local)
            log.info("      Saved attachment: %s (%d bytes)", target.name, len(payload))

    def _bookstack_image_url(self, ref: str) -> str | None:
        parsed = urlparse(ref)
        base = urlparse(self.client.base_url)
        if parsed.scheme in ("http", "https"):
            if parsed.netloc != base.netloc:
                return None
            path = parsed.path
        elif ref.startswith("/"):
            path = parsed.path
        else:
            return None
        if not path.startswith(("/uploads/", "/attachments/", "/storage/")):
            return None
        return ref if parsed.scheme else f"{self.client.base_url}{path}"

    def resolve(self, ref: str) -> str | None:
        for key in self._key_variants(ref):
            if key in self.attachment_map:
                return self.attachment_map[key]
        if self.writer.dry_run:
            return None
        url = self._bookstack_image_url(ref)
        if not url:
            return None
        if url in self.image_map:
            return self.image_map[url]
        try:
            data = self.client.download_url(url)
        except Exception as exc:
            log.warning("      Could not download image %s: %s", url, exc)
            return None
        filename = Path(unquote(urlparse(url).path)).name or "image"
        target = self.writer.reserve_asset(self.asset_dir_rel, filename)
        self.writer.write_bytes(target, data)
        local = relative_ref(self.page_rel.parent, target)
        self.image_map[url] = local
        log.info("      Saved image: %s (%d bytes)", target.name, len(data))
        return local


def export_bookstack_page(client: BookStackClient, writer: BundleWriter, page_summary: dict,
                          dir_rel: Path, book_title: str, chapter_title: str | None,
                          book_id: int, chapter_id: int | None) -> None:
    page = client.get_page(page_summary["id"])
    title = page.get("name") or page_summary.get("name") or "Untitled"
    page_rel = writer.reserve_markdown(dir_rel, title)
    content = page.get("markdown") or ""
    if not content.strip():
        html = page.get("raw_html") or page.get("html") or ""
        content = html_to_markdown(html)
        if content.strip():
            log.info("      Converted WYSIWYG HTML to markdown: %s", title)
        else:
            log.warning("      Page has no usable content: %s", title)

    asset_dir_rel = writer.asset_dir_for(page_rel)
    resolver = BookStackExportResolver(client, page, page_rel, asset_dir_rel, writer)
    content = rewrite_references(content, resolver.resolve)
    writer.write_text(page_rel, content)
    writer.add_document(page_rel, {
        "title": title,
        "tags": tags_from_bookstack(page.get("tags")),
        "source_backend": "bookstack",
        "source_id": page.get("id"),
        "updated_at": page.get("updated_at"),
        "content_type": "markdown",
        "editor": page.get("editor"),
        "book": book_title,
        "chapter": chapter_title,
        "book_id": book_id,
        "chapter_id": chapter_id,
        "priority": page.get("priority"),
    })
    time.sleep(0.05)


def export_bookstack(client: BookStackClient, root: Path, dry_run: bool = False,
                     shelf_filter: str | None = None, book_filter: str | None = None) -> BundleWriter:
    source = {"backend": "bookstack", "base_url": client.base_url}
    writer = BundleWriter(root, source, dry_run=dry_run)
    books = client.list_books()

    if shelf_filter:
        shelves = client.list_shelves()
        target_shelf = next((s for s in shelves if s.get("name") == shelf_filter), None)
        if not target_shelf:
            raise RuntimeError(f"BookStack shelf not found: {shelf_filter}")
        shelf_detail = client.get_shelf(target_shelf["id"])
        allowed = {b["id"] for b in shelf_detail.get("books", [])}
        books = [b for b in books if b.get("id") in allowed]
        log.info("Exporting shelf '%s' (%d books)", shelf_filter, len(books))

    if book_filter:
        books = [b for b in books if b.get("name") == book_filter]
        if not books:
            raise RuntimeError(f"BookStack book not found: {book_filter}")

    for summary in sorted(books, key=lambda b: b.get("name", "")):
        book = client.get_book(summary["id"])
        book_title = book.get("name") or summary.get("name") or "Untitled Book"
        book_dir = writer.reserve_dir(Path(), book_title)
        log.info("Book: %s", book_title)

        for item in book.get("contents", []) or []:
            item_type = item.get("type")
            if item_type == "chapter":
                chapter_title = item.get("name") or "Untitled Chapter"
                chapter_dir = writer.reserve_dir(book_dir, chapter_title)
                log.info("  Chapter: %s", chapter_title)
                for page_summary in item.get("pages", []) or []:
                    export_bookstack_page(
                        client, writer, page_summary, chapter_dir, book_title,
                        chapter_title, book["id"], item.get("id"),
                    )
            elif item_type == "page":
                export_bookstack_page(
                    client, writer, item, book_dir, book_title,
                    None, book["id"], None,
                )

    writer.write_manifest()
    return writer


# ---------------------------------------------------------------------------
# Wiki.js export: download referenced and page-owned assets
# ---------------------------------------------------------------------------
class WikiJSExportResolver:
    def __init__(self, client: WikiJSClient, page: dict, page_path: str, page_rel: Path,
                 asset_dir_rel: Path, writer: BundleWriter, locale: str | None):
        self.client = client
        self.page = page
        self.page_path = page_path.strip("/")
        self.page_rel = page_rel
        self.asset_dir_rel = asset_dir_rel
        self.writer = writer
        self.locale = locale
        self.remote_map: dict[str, str] = {}

    def _remember(self, remote: str, local: str) -> None:
        remote = remote.strip("/")
        self.remote_map[remote] = local
        self.remote_map["/" + remote] = local

    def _store(self, remote: str, data: bytes, relative_under_assets: Path) -> str:
        parent = self.asset_dir_rel / relative_under_assets.parent
        target = self.writer.reserve_asset(parent, relative_under_assets.name)
        self.writer.write_bytes(target, data)
        local = relative_ref(self.page_rel.parent, target)
        self._remember(remote, local)
        log.info("      Saved asset: %s (%d bytes)", target.name, len(data))
        return local

    def _walk_own_assets(self, folder: str):
        queue = [folder.strip("/")]
        visited: set[str] = set()
        while queue:
            current = queue.pop(0)
            if current in visited:
                continue
            visited.add(current)
            for item in self.client.list_tree(current, types="folder,asset", locale=self.locale):
                item_path = "/".join(
                    part for part in [item.get("folderPath", ""), item.get("fileName", "")] if part
                )
                if item.get("type") == "folder":
                    queue.append(item_path)
                elif item.get("type") == "asset":
                    yield item_path, item

    def preload_own_assets(self) -> None:
        if self.writer.dry_run:
            return
        own_folder = f"{self.page_path}/assets" if self.page_path else "assets"
        try:
            for remote, item in self._walk_own_assets(own_folder):
                relative = remote[len(own_folder):].lstrip("/") or item.get("fileName", "asset")
                if remote in self.remote_map:
                    continue
                try:
                    data = self.client.download_asset(item["id"])
                except Exception as exc:
                    log.warning("      Could not download asset %s: %s", remote, exc)
                    continue
                self._store(remote, data, Path(relative))
        except Exception as exc:
            log.debug("No page asset folder for %s: %s", own_folder, exc)

    def _normalize_remote(self, ref: str) -> str | None:
        ref = (ref or "").strip()
        if not ref or ref.startswith("#") or ref.lower().startswith(("data:", "mailto:", "tel:", "javascript:")):
            return None
        parsed = urlparse(ref)
        base = urlparse(self.client.base_url)
        if parsed.scheme in ("http", "https"):
            if parsed.netloc != base.netloc:
                return None
            path = parsed.path
        elif ref.startswith("//"):
            return None
        elif ref.startswith("/_files/"):
            path = ref[len("/_files/"):]
        elif ref.startswith("/"):
            path = parsed.path
        elif ref.startswith(("./", "../")):
            import posixpath
            page_dir = self.page_path.rsplit("/", 1)[0] if "/" in self.page_path else ""
            path = posixpath.normpath(posixpath.join(page_dir, ref))
        else:
            return None
        path = unquote(path).lstrip("/")
        if not path or path.startswith("../") or "/../" in path:
            return None
        return path

    def resolve(self, ref: str) -> str | None:
        remote = self._normalize_remote(ref)
        if not remote:
            return None
        if remote in self.remote_map:
            return self.remote_map[remote]
        if self.writer.dry_run:
            return None
        item = self.client.find_asset(remote, locale=self.locale)
        if not item:
            return None
        try:
            data = self.client.download_asset(item["id"])
        except Exception as exc:
            log.warning("      Could not download asset %s: %s", remote, exc)
            return None
        return self._store(remote, data, Path(Path(remote).name or "asset"))


def export_wikijs_page(client: WikiJSClient, writer: BundleWriter, item: dict,
                       folder_titles: dict[str, str], locale: str | None) -> None:
    page = client.get_page(item["id"], with_content=True)
    if not page:
        log.warning("Could not fetch Wiki.js page %s", item.get("_path"))
        return
    path = (page.get("path") or item.get("_path") or "").strip("/")
    parts = [part for part in path.split("/") if part] or ["home"]
    title = page.get("title") or item.get("title") or parts[-1]
    dir_parts = parts[:-1]
    rel_dir = Path(*[safe_filename(part) for part in dir_parts]) if dir_parts else Path()
    local_titles: dict[str, str] = {}
    current = Path()
    for index, part in enumerate(dir_parts):
        current = current / safe_filename(part)
        wiki_key = "/".join(parts[: index + 1])
        local_titles[current.as_posix()] = folder_titles.get(wiki_key) or humanize_name(part)
    writer.ensure_path_dirs(rel_dir, local_titles)
    page_rel = writer.reserve_markdown(rel_dir, parts[-1])

    content = page.get("content") or ""
    content_type = (page.get("contentType") or "").lower()
    if "html" in content_type and content.strip():
        content = html_to_markdown(content)
    if not content.strip():
        log.warning("      Wiki.js page has no content: %s", title)

    asset_dir_rel = writer.asset_dir_for(page_rel)
    resolver = WikiJSExportResolver(client, page, path, page_rel, asset_dir_rel, writer, locale)
    resolver.preload_own_assets()
    content = rewrite_references(content, resolver.resolve)
    writer.write_text(page_rel, content)
    writer.add_document(page_rel, {
        "title": title,
        "path": path,
        "locale": page.get("locale") or locale,
        "description": page.get("description"),
        "tags": unique_strings(page.get("tags")),
        "source_backend": "wikijs",
        "source_id": page.get("id"),
        "updated_at": page.get("updatedAt"),
        "content_type": "markdown",
        "original_content_type": page.get("contentType"),
        "editor": page.get("editor"),
    })
    time.sleep(0.03)


def export_wikijs(client: WikiJSClient, root: Path, dry_run: bool = False) -> BundleWriter:
    client.resolve_site()
    locale = client.locale
    source = {
        "backend": "wikijs",
        "base_url": client.base_url,
        "site_id": client.site_id,
        "site_title": client.site_info.get("title"),
        "locale": locale,
    }
    writer = BundleWriter(root, source, dry_run=dry_run)

    folder_titles: dict[str, str] = {}
    pages: list[dict] = []
    for item in client.walk_tree(locale=locale):
        item_type = item.get("type")
        item_path = item.get("_path", "")
        if item_type == "folder":
            title = item.get("title") or humanize_name(item.get("fileName", ""))
            folder_titles[item_path] = title
            writer.folders[item_path] = {"title": title}
        elif item_type == "page":
            pages.append(item)
    log.info("Found %d Wiki.js page(s)", len(pages))

    for item in sorted(pages, key=lambda value: value.get("_path", "")):
        log.info("Page: /%s", item.get("_path", ""))
        export_wikijs_page(client, writer, item, folder_titles, locale)

    writer.write_manifest()
    return writer


# ---------------------------------------------------------------------------
# Import: upload local assets and rewrite references
# ---------------------------------------------------------------------------
class BookStackRefProcessor:
    def __init__(self, client: BookStackClient, page_id: int, page_dir: Path,
                 bundle_root: Path, dry_run: bool):
        self.client = client
        self.page_id = page_id
        self.page_dir = page_dir
        self.bundle_root = bundle_root
        self.dry_run = dry_run
        self.cache: dict[str, str | None] = {}

    def process(self, content: str) -> str:
        if self.dry_run or not self.page_id:
            return content
        return rewrite_references(content, self.resolve)

    def resolve(self, ref: str) -> str | None:
        path = resolve_local_file(ref, self.page_dir, self.bundle_root)
        if not path:
            return None
        key = str(path)
        if key in self.cache:
            return self.cache[key]
        try:
            if path.suffix.lower() in IMAGE_EXTENSIONS:
                try:
                    result = self.client.upload_image(self.page_id, path)
                    url = result.get("url")
                    if url:
                        self.cache[key] = url
                        return url
                except Exception as exc:
                    log.warning("      Image upload failed for %s (%s); trying as attachment", path.name, exc)
            result = self.client.upload_attachment(self.page_id, path)
            attachment_id = result.get("id")
            if not attachment_id:
                self.cache[key] = None
                return None
            url = f"{self.client.base_url}/attachments/{attachment_id}"
            self.cache[key] = url
            return url
        except Exception as exc:
            log.warning("      Could not upload %s: %s", path.name, exc)
            self.cache[key] = None
            return None


class WikiJSRefProcessor:
    def __init__(self, client: WikiJSClient, page_path: str, page_dir: Path,
                 bundle_root: Path, locale: str | None, dry_run: bool):
        self.client = client
        self.page_path = page_path.strip("/")
        self.page_dir = page_dir
        self.bundle_root = bundle_root
        self.locale = locale
        self.dry_run = dry_run
        self.cache: dict[str, str | None] = {}

    def process(self, content: str) -> str:
        return rewrite_references(content, self.resolve)

    def _asset_relative_parts(self, path: Path) -> list[str]:
        try:
            relative = path.relative_to(self.page_dir)
        except ValueError:
            relative = Path(path.name)
        parts = list(relative.parts)
        if len(parts) > 1:
            first = parts[0].lower()
            if first.endswith(".assets") or first in ("attachments", "images", "assets"):
                parts = parts[1:]
        return parts or [path.name]

    def resolve(self, ref: str) -> str | None:
        path = resolve_local_file(ref, self.page_dir, self.bundle_root)
        if not path:
            return None
        key = str(path)
        if key in self.cache:
            return self.cache[key]
        parts = self._asset_relative_parts(path)
        folder_parts = [self.page_path] if self.page_path else []
        folder_parts.append("assets")
        folder_parts.extend(slugify(part) for part in parts[:-1])
        folder_path = "/".join(part for part in folder_parts if part)
        try:
            asset = self.client.upload_asset(path, folder_path, locale=self.locale)
        except Exception as exc:
            log.warning("      Could not upload asset %s: %s", path.name, exc)
            self.cache[key] = None
            return None
        if not asset:
            self.cache[key] = None
            return None
        stored_folder = (asset.get("folderPath") or folder_path).strip("/")
        stored_name = asset.get("fileName") or path.name
        url = "/" + quote(
            "/".join(part for part in [stored_folder, stored_name] if part), safe="/-_.~"
        )
        self.cache[key] = url
        return url


# ---------------------------------------------------------------------------
# Import targets
# ---------------------------------------------------------------------------
def normalize_wikijs_path(path: str) -> str:
    parts = [slugify(part) for part in (path or "").strip("/").split("/") if part and part not in (".", "..")]
    return "/".join(parts) or "home"


class WikiJSImporter:
    def __init__(self, client: WikiJSClient, reader: BundleReader, path_prefix: str = "",
                 publish_state: str = "published", dry_run: bool = False):
        self.client = client
        self.reader = reader
        self.path_prefix = normalize_wikijs_path(path_prefix).strip("/") if path_prefix else ""
        self.publish_state = publish_state
        self.dry_run = dry_run
        self.used_paths: dict[str, str] = {}

    def _page_path(self, rel: Path, meta: dict, title: str) -> str:
        raw = ""
        if meta.get("path") and meta.get("source_backend") == "wikijs":
            raw = str(meta["path"])
        elif meta.get("book"):
            parts = [slugify(meta["book"])]
            chapter = str(meta.get("chapter") or "")
            parts.extend(slugify(part) for part in re.split(r"\s+/\s+|/", chapter) if part.strip())
            parts.append(slugify(title))
            raw = "/".join(parts)
        else:
            parts = list(rel.with_suffix("").parts)
            if parts and parts[-1].lower() in ("index", "readme"):
                parts = parts[:-1]
            raw = "/".join(slugify(part) for part in parts)
        if self.path_prefix:
            raw = self.path_prefix + "/" + raw
        path = normalize_wikijs_path(raw)
        if len(path) > 255:
            path = path[:255].rstrip("/") or "home"
        if path in self.used_paths and self.used_paths[path] != rel.as_posix():
            original = path
            index = 2
            while f"{original}-{index}" in self.used_paths:
                index += 1
            path = f"{original}-{index}"
            log.warning("      Duplicate Wiki.js path %s; using %s", original, path)
        self.used_paths[path] = rel.as_posix()
        return path

    def import_document(self, rel: Path, meta: dict, content: str) -> str:
        title = truncate(str(meta.get("title") or content_title(content, humanize_name(rel.stem))), 255)
        path = self._page_path(rel, meta, title)
        existing = None
        source_id = meta.get("source_id")
        if meta.get("source_backend") == "wikijs" and source_id and UUID_RE.match(str(source_id)):
            existing = self.client.get_page(str(source_id), with_content=False)
        if not existing:
            existing = self.client.find_page_by_path(path, locale=self.client.locale)

        if meta.get("content_type") == "html" and content.strip():
            content = html_to_markdown(content)

        page_dir = self.reader.root / rel.parent
        processor = WikiJSRefProcessor(
            self.client, path, page_dir, self.reader.root, self.client.locale, self.dry_run
        )
        content = processor.process(content)
        render = render_markdown_to_html(content)

        payload = {
            "path": path,
            "title": title,
            "editor": "markdown",
            "content": content,
            "render": render,
            "locale": self.client.locale,
            "publishState": self.publish_state,
            "reasonForChange": "docs_sync import",
        }
        if "tags" in meta:
            payload["tags"] = unique_strings(meta.get("tags"))
        description = meta.get("description")
        if description:
            payload["description"] = str(description)[:255]
        if existing:
            log.info("    Updating page: /%s", path)
            self.client.update_page(existing["id"], payload)
            return "updated"
        log.info("    Creating page: /%s", path)
        self.client.create_page(payload)
        return "created"


class BookStackImporter:
    def __init__(self, client: BookStackClient, reader: BundleReader, shelf_name: str | None = None,
                 book_override: str | None = None, default_book: str = DEFAULT_BOOK,
                 dry_run: bool = False):
        self.client = client
        self.reader = reader
        self.book_override = book_override
        self.default_book = default_book or DEFAULT_BOOK
        self.dry_run = dry_run
        self.shelf_id = None
        if shelf_name:
            self.shelf_id = self.client.get_or_create_shelf(shelf_name).get("id")

    def _chapter_from_dirs(self, dirs: tuple[str, ...]) -> str | None:
        if not dirs:
            return None
        titles = [self.reader.folder_title("/".join(dirs[: index + 1])) for index in range(len(dirs))]
        return " / ".join(titles) or None

    def _location(self, rel: Path, meta: dict) -> tuple[str, str | None]:
        if self.book_override:
            return self.book_override, self._chapter_from_dirs(rel.parent.parts)
        if meta.get("book"):
            return str(meta["book"]), (str(meta["chapter"]) if meta.get("chapter") else None)
        if meta.get("path") and meta.get("source_backend") == "wikijs":
            parts = [part for part in str(meta["path"]).strip("/").split("/") if part]
            if len(parts) <= 1:
                return self.default_book, None
            book = self.reader.folder_title(parts[0]) or humanize_name(parts[0])
            chapter_parts = []
            for index in range(1, len(parts) - 1):
                key = "/".join(parts[: index + 1])
                chapter_parts.append(self.reader.folder_title(key) or humanize_name(parts[index]))
            return book, (" / ".join(chapter_parts) or None)
        dirs = rel.parent.parts
        if not dirs:
            return self.default_book, None
        book = self.reader.folder_title(dirs[0]) or humanize_name(dirs[0])
        return book, self._chapter_from_dirs(dirs[1:])

    def import_document(self, rel: Path, meta: dict, content: str) -> str:
        title = truncate(str(meta.get("title") or content_title(content, humanize_name(rel.stem))), 255)
        book_title, chapter_title = self._location(rel, meta)
        book = self.client.get_or_create_book(book_title, self.shelf_id)
        book_id = book.get("id", 0)
        chapter_id = None
        if chapter_title:
            chapter = self.client.get_or_create_chapter(chapter_title, book_id)
            chapter_id = chapter.get("id")

        existing = None
        source_id = meta.get("source_id")
        if meta.get("source_backend") == "bookstack" and isinstance(source_id, int) and source_id:
            try:
                existing = self.client.get_page(source_id)
            except Exception as exc:
                log.debug("Source BookStack page %s no longer exists: %s", source_id, exc)
        if not existing:
            existing = self.client.find_page(title, book_id, chapter_id)

        html_mode = meta.get("content_type") == "html"
        tags = tags_to_bookstack(meta.get("tags")) if "tags" in meta else None
        priority = meta.get("priority") if isinstance(meta.get("priority"), int) else None
        page = self.client.save_page(
            title, content, book_id, chapter_id, html=html_mode,
            tags=tags, priority=priority, existing=existing,
        )
        action = "updated" if existing else "created"
        page_id = page.get("id", 0)
        if not self.dry_run and page_id:
            processor = BookStackRefProcessor(
                self.client, page_id, self.reader.root / rel.parent, self.reader.root, self.dry_run
            )
            updated = processor.process(content)
            if updated != content:
                self.client.save_page(
                    title, updated, book_id, chapter_id, html=html_mode,
                    tags=tags, priority=priority, existing=page,
                )
        return action


# ---------------------------------------------------------------------------
# Import driver
# ---------------------------------------------------------------------------
def run_import(reader: BundleReader, importer, dry_run: bool = False) -> dict:
    files = reader.markdown_files()
    log.info("Found %d markdown file(s) under %s", len(files), reader.root)
    counts = {"created": 0, "updated": 0, "failed": 0}
    seen: set[str] = set()
    for rel in files:
        seen.add(rel.as_posix())
        meta = reader.document_meta(rel)
        try:
            content = (reader.root / rel).read_text(encoding="utf-8", errors="replace")
        except Exception as exc:
            log.error("Could not read %s: %s", rel, exc)
            counts["failed"] += 1
            continue
        try:
            action = importer.import_document(rel, meta, content)
            counts[action] = counts.get(action, 0) + 1
        except Exception as exc:
            log.error("Failed to import %s: %s", rel, exc)
            counts["failed"] += 1

    missing = reader.missing_documents(seen)
    if missing:
        log.warning("%d manifest document(s) are absent from the bundle (ignored)", len(missing))
    log.info(
        "Import complete. created=%d updated=%d failed=%d",
        counts["created"], counts["updated"], counts["failed"],
    )
    return counts


# ---------------------------------------------------------------------------
# Connectivity helpers
# ---------------------------------------------------------------------------
def _required(value, flag: str):
    if not value:
        log.error("Missing required option: %s", flag)
        sys.exit(2)
    return value


def connect_bookstack(args, prefix: str = "") -> BookStackClient:
    url = _required(getattr(args, f"{prefix}url", None), f"--{prefix.replace('_', '-')}url")
    token_id = _required(getattr(args, f"{prefix}token_id", None), f"--{prefix.replace('_', '-')}token-id")
    token_secret = _required(
        getattr(args, f"{prefix}token_secret", None), f"--{prefix.replace('_', '-')}token-secret"
    )
    client = BookStackClient(url, token_id, token_secret, dry_run=getattr(args, "dry_run", False))
    try:
        client._get("books", params={"count": 1})
    except Exception as exc:
        log.error("Could not connect to BookStack at %s: %s", url, exc)
        sys.exit(1)
    log.info("Connected to BookStack at %s", url)
    return client


def connect_wikijs(args, prefix: str = "") -> WikiJSClient:
    url = _required(getattr(args, f"{prefix}url", None), f"--{prefix.replace('_', '-')}url")
    token = _required(getattr(args, f"{prefix}token", None), f"--{prefix.replace('_', '-')}token")
    site = getattr(args, f"{prefix}site", "current") or "current"
    locale = getattr(args, f"{prefix}locale", None)
    client = WikiJSClient(url, token, site=site, locale=locale, dry_run=getattr(args, "dry_run", False))
    try:
        client.resolve_site()
        client._request("GET", f"{client._site_path}/tree", params={"limit": 1})
    except Exception as exc:
        log.error("Could not connect to Wiki.js at %s: %s", url, exc)
        sys.exit(1)
    log.info(
        "Connected to Wiki.js at %s (site %s, locale %s)",
        url, client.site_id, client.locale,
    )
    return client


# ---------------------------------------------------------------------------
# Commands
# ---------------------------------------------------------------------------
def cmd_import(args) -> None:
    root = Path(args.dir)
    if not root.is_dir():
        log.error("Import directory is not a directory: %s", root)
        sys.exit(1)
    reader = BundleReader(root)
    if args.dry_run:
        log.info("=== DRY RUN: no remote changes will be made ===")

    if args.backend == "bookstack":
        client = connect_bookstack(args)
        importer = BookStackImporter(
            client, reader, shelf_name=args.shelf, book_override=args.book,
            default_book=args.default_book, dry_run=args.dry_run,
        )
    else:
        if not MARKDOWN_AVAILABLE:
            log.warning("Python 'markdown' package not installed; using the built-in renderer")
        client = connect_wikijs(args)
        importer = WikiJSImporter(
            client, reader, path_prefix=args.path_prefix,
            publish_state=args.publish_state, dry_run=args.dry_run,
        )
    run_import(reader, importer, dry_run=args.dry_run)


def cmd_export(args) -> None:
    root = Path(args.dir)
    if root.exists() and not root.is_dir():
        log.error("Export path is not a directory: %s", root)
        sys.exit(1)
    if not args.dry_run:
        root.mkdir(parents=True, exist_ok=True)
    if args.backend == "bookstack":
        client = connect_bookstack(args)
        export_bookstack(client, root, dry_run=args.dry_run,
                         shelf_filter=args.shelf, book_filter=args.book)
    else:
        client = connect_wikijs(args)
        export_wikijs(client, root, dry_run=args.dry_run)
    log.info("Export complete -> %s", root)


def cmd_sync(args) -> None:
    if args.command == "sync":
        source_backend = args.from_backend
        target_backend = args.to_backend
    elif args.command == "sync-bookstack-to-wikijs":
        source_backend, target_backend = "bookstack", "wikijs"
    else:
        source_backend, target_backend = "wikijs", "bookstack"

    if source_backend == target_backend:
        log.error("Source and target are both %s; nothing to sync", source_backend)
        sys.exit(2)

    if args.dry_run:
        log.info("=== DRY RUN: the target backend will not be changed ===")

    needed = {source_backend, target_backend}
    bookstack_client = connect_bookstack(args, "bookstack_") if "bookstack" in needed else None
    wikijs_client = connect_wikijs(args, "wikijs_") if "wikijs" in needed else None

    keep_staging = bool(args.dir or args.keep_staging)
    if args.dir:
        staging = Path(args.dir)
        staging.mkdir(parents=True, exist_ok=True)
        if any(staging.iterdir()):
            log.warning(
                "Staging directory %s is not empty; stale files in it will also be imported", staging
            )
    else:
        temp_parent = "/tmp/opencode" if Path("/tmp/opencode").is_dir() else None
        staging = Path(tempfile.mkdtemp(prefix="docs-sync-", dir=temp_parent))

    try:
        log.info("Exporting %s -> %s", source_backend, staging)
        if source_backend == "bookstack":
            export_bookstack(
                bookstack_client, staging, dry_run=False,
                shelf_filter=args.shelf, book_filter=args.book,
            )
        else:
            export_wikijs(wikijs_client, staging, dry_run=False)

        reader = BundleReader(staging)
        if target_backend == "bookstack":
            importer = BookStackImporter(
                bookstack_client, reader,
                shelf_name=(args.shelf if source_backend != "bookstack" else None),
                book_override=(args.book if source_backend != "bookstack" else None),
                default_book=args.default_book, dry_run=args.dry_run,
            )
        else:
            if not MARKDOWN_AVAILABLE:
                log.warning("Python 'markdown' package not installed; using the built-in renderer")
            importer = WikiJSImporter(
                wikijs_client, reader, path_prefix=args.path_prefix,
                publish_state=args.publish_state, dry_run=args.dry_run,
            )
        log.info("Importing bundle -> %s", target_backend)
        run_import(reader, importer, dry_run=args.dry_run)
    finally:
        if not keep_staging:
            shutil.rmtree(staging, ignore_errors=True)
        else:
            log.info("Staging bundle kept at %s", staging)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="docs_sync.py",
        description="Import/export Markdown, and sync between BookStack and Wiki.js 3.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    subparsers = parser.add_subparsers(dest="command", metavar="{import,export,sync,...}", required=True)

    def add_single_connection(sub):
        sub.add_argument("--url", required=True, help="Backend base URL")
        sub.add_argument("--token-id", default=None, help="BookStack API token ID")
        sub.add_argument("--token-secret", default=None, help="BookStack API token secret")
        sub.add_argument("--token", default=None, help="Wiki.js personal access token")
        sub.add_argument("--site", default="current", help="Wiki.js site ID or 'current' (default: current)")
        sub.add_argument("--locale", default=None, help="Wiki.js locale (default: site primary locale)")
        sub.add_argument("--dry-run", action="store_true", help="Preview without changing the remote backend")
        sub.add_argument("--verbose", action="store_true", help="Enable debug logging")

    def add_common_import_export(sub):
        sub.add_argument("--dir", required=True, help="Bundle directory (source for import, destination for export)")
        sub.add_argument("--shelf", default=None, help="BookStack shelf name (import target or export filter)")
        sub.add_argument("--book", default=None, help="BookStack book name (import target or export filter)")
        sub.add_argument("--default-book", default=DEFAULT_BOOK,
                         help=f"BookStack book for root-level markdown (default: {DEFAULT_BOOK})")
        sub.add_argument("--path-prefix", default="",
                         help="Prefix to add to every imported Wiki.js page path")
        sub.add_argument("--publish-state", default="published", choices=["draft", "published", "scheduled"],
                         help="Wiki.js publish state for imported pages (default: published)")

    imp = subparsers.add_parser(
        "import", help="Import a markdown bundle into a wiki backend",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    imp.add_argument("--backend", required=True, choices=["bookstack", "wikijs"], help="Target backend")
    add_single_connection(imp)
    add_common_import_export(imp)

    exp = subparsers.add_parser(
        "export", help="Export a wiki backend to a markdown bundle",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    exp.add_argument("--backend", required=True, choices=["bookstack", "wikijs"], help="Source backend")
    add_single_connection(exp)
    add_common_import_export(exp)

    def add_sync_connection(sub):
        sub.add_argument("--bookstack-url", default=None, help="BookStack base URL")
        sub.add_argument("--bookstack-token-id", default=None, help="BookStack API token ID")
        sub.add_argument("--bookstack-token-secret", default=None, help="BookStack API token secret")
        sub.add_argument("--wikijs-url", default=None, help="Wiki.js base URL")
        sub.add_argument("--wikijs-token", default=None, help="Wiki.js personal access token")
        sub.add_argument("--wikijs-site", default="current", help="Wiki.js site ID or 'current'")
        sub.add_argument("--wikijs-locale", default=None, help="Wiki.js locale")

    def add_sync_common(sub):
        sub.add_argument("--dir", default=None,
                         help="Keep the staging bundle in this directory (default: a temporary directory)")
        sub.add_argument("--shelf", default=None, help="BookStack shelf (source filter or target)")
        sub.add_argument("--book", default=None,
                         help="BookStack book (source filter when BookStack is the source; target book otherwise)")
        sub.add_argument("--default-book", default=DEFAULT_BOOK,
                         help=f"BookStack book for root-level Wiki.js pages (default: {DEFAULT_BOOK})")
        sub.add_argument("--path-prefix", default="", help="Prefix for imported Wiki.js page paths")
        sub.add_argument("--publish-state", default="published", choices=["draft", "published", "scheduled"],
                         help="Wiki.js publish state for imported pages")
        sub.add_argument("--keep-staging", action="store_true",
                         help="Keep the temporary staging directory for inspection")
        sub.add_argument("--dry-run", action="store_true", help="Export the source but do not change the target")
        sub.add_argument("--verbose", action="store_true", help="Enable debug logging")

    sync_bw = subparsers.add_parser(
        "sync-bookstack-to-wikijs", help="Copy BookStack content into Wiki.js 3",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    add_sync_connection(sync_bw)
    add_sync_common(sync_bw)

    sync_wb = subparsers.add_parser(
        "sync-wikijs-to-bookstack", help="Copy Wiki.js 3 content into BookStack",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    add_sync_connection(sync_wb)
    add_sync_common(sync_wb)

    sync_generic = subparsers.add_parser(
        "sync", help="Generic sync with --from/--to",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sync_generic.add_argument("--from", dest="from_backend", required=True, choices=["bookstack", "wikijs"])
    sync_generic.add_argument("--to", dest="to_backend", required=True, choices=["bookstack", "wikijs"])
    add_sync_connection(sync_generic)
    add_sync_common(sync_generic)

    return parser


def main(argv=None) -> None:
    parser = build_parser()
    args = parser.parse_args(argv)
    if getattr(args, "verbose", False):
        log.setLevel(logging.DEBUG)
    try:
        if args.command == "import":
            cmd_import(args)
        elif args.command == "export":
            cmd_export(args)
        else:
            cmd_sync(args)
    except KeyboardInterrupt:
        log.error("Interrupted")
        sys.exit(130)
    except (RuntimeError, requests.RequestException) as exc:
        log.error("%s", exc)
        sys.exit(1)


if __name__ == "__main__":
    main()
