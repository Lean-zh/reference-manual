#!/usr/bin/env python3
"""Localize generated browser UI for translated reference-manual chapters.

Verso's declaration hovers are stored in a site-wide JSON table.  To avoid
changing untranslated chapters, translated pages are redirected to cloned
hover entries.  API cards contribute their translated bodies to the clones;
incidental references retain signatures without importing English prose.
"""

from __future__ import annotations

import argparse
import html
import json
import re
from html.parser import HTMLParser
from pathlib import Path

TARGET_PAGES = (
    "Attributes/index.html",
    "Axioms/index.html",
    "Type-Classes/Basic-Classes/index.html",
    "Type-Classes/Class-Declarations/index.html",
    "Type-Classes/Deriving-Instances/index.html",
    "Type-Classes/Instance-Declarations/index.html",
    "Type-Classes/Instance-Synthesis/index.html",
    "Type-Classes/index.html",
    "Coercions/index.html",
    "Coercions/Coercion-Insertion/index.html",
    "Coercions/Coercing-Between-Types/index.html",
    "Coercions/Coercing-to-Sorts/index.html",
    "Coercions/Coercing-to-Function-Types/index.html",
    "Coercions/Implementation-Details/index.html",
)

HOVER_ATTR_RE = re.compile(r'data-verso-hover="([^"]+)"')
DOCSTRING_RE = re.compile(
    r'(?:<span class="sep"></span>)?<code class="docstring">.*?</code>', re.DOTALL
)
TITLE_REPLACEMENTS = (
    (re.compile(r'title="Documentation for ([^"]*)"'), r'title="文档：\1"'),
    (re.compile(r'title="Definition of ([^"]*)"'), r'title="定义：\1"'),
    (re.compile(r'title="Permalink"'), 'title="永久链接"'),
)
FORBIDDEN_TITLES = ("Documentation for ", "Definition of ", "Permalink")
NO_ADDITIONAL_DOCS = "<span>无附加文档。</span>"
VOID_TAGS = {
    "area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
    "param", "source", "track", "wbr",
}


class NamedDocsParser(HTMLParser):
    """Collect the translated body and declaration hover ID of each API card."""

    def __init__(self) -> None:
        super().__init__()
        self.depth = 0
        self.named_depth: int | None = None
        self.text_depth: int | None = None
        self.hover_id: str | None = None
        self.text: list[str] = []
        self.translations: dict[str, str] = {}

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag not in VOID_TAGS:
            self.depth += 1
        data = dict(attrs)
        classes = (data.get("class") or "").split()
        if self.named_depth is None and tag == "div" and "namedocs" in classes:
            self.named_depth = self.depth
            self.hover_id = None
            self.text = []
            return
        if self.named_depth is None:
            return
        if self.hover_id is None and data.get("data-verso-hover"):
            self.hover_id = data["data-verso-hover"]
        if self.text_depth is None and tag == "div" and "text" in classes:
            self.text_depth = self.depth

    def handle_endtag(self, tag: str) -> None:
        del tag
        if self.text_depth == self.depth:
            self.text_depth = None
        if self.named_depth == self.depth:
            text = " ".join("".join(self.text).split())
            if self.hover_id and text:
                self.translations.setdefault(self.hover_id, text)
            self.named_depth = None
            self.hover_id = None
            self.text = []
        self.depth -= 1

    def handle_data(self, data: str) -> None:
        if self.text_depth is not None:
            self.text.append(data)


def localize_generated_html(root: Path) -> tuple[int, int, int, int]:
    docs_path = root / "-verso-docs.json"
    if not docs_path.is_file():
        raise SystemExit(f"missing Verso hover table: {docs_path}")
    docs: dict[str, str] = json.loads(docs_path.read_text(encoding="utf-8"))

    page_text: dict[Path, str] = {}
    title_count = 0
    hover_ids: set[str] = set()
    translated_hovers: dict[str, str] = {}
    for rel in TARGET_PAGES:
        path = root / rel
        if not path.is_file():
            raise SystemExit(f"missing translated page: {path}")
        text = path.read_text(encoding="utf-8")
        parser = NamedDocsParser()
        parser.feed(text)
        translated_hovers.update(parser.translations)
        for pattern, replacement in TITLE_REPLACEMENTS:
            text, count = pattern.subn(replacement, text)
            title_count += count
        page_text[path] = text
        hover_ids.update(HOVER_ATTR_RE.findall(text))

    clones: dict[str, str] = {}
    redirects: dict[str, str] = {}
    translated_count = 0
    for hover_id in sorted(hover_ids):
        payload = docs.get(hover_id)
        if payload is None:
            raise SystemExit(f"hover id {hover_id!r} is absent from {docs_path}")
        if hover_id.startswith("zh-"):
            if not payload.strip():
                docs[hover_id] = NO_ADDITIONAL_DOCS
            continue
        translated = translated_hovers.get(hover_id)
        replacement = ""
        if translated:
            replacement = (
                '<span class="sep"></span><code class="docstring">'
                + html.escape(translated)
                + "</code>"
            )
        stripped, count = DOCSTRING_RE.subn(replacement, payload)
        if count == 0:
            continue
        if not stripped.strip():
            stripped = NO_ADDITIONAL_DOCS
        if translated:
            translated_count += 1
        clone_id = f"zh-{hover_id}"
        if clone_id in docs and docs[clone_id] != stripped:
            raise SystemExit(f"conflicting localized hover id: {clone_id}")
        clones[clone_id] = stripped
        redirects[hover_id] = clone_id

    for path, text in page_text.items():
        text = HOVER_ATTR_RE.sub(
            lambda match: f'data-verso-hover="{redirects.get(match.group(1), match.group(1))}"',
            text,
        )
        for forbidden in FORBIDDEN_TITLES:
            if f'title="{forbidden}' in text:
                raise SystemExit(f"unlocalized generated title in {path}: {forbidden}")
        path.write_text(text, encoding="utf-8")

    docs.update(clones)
    docs_path.write_text(
        json.dumps(docs, ensure_ascii=False, separators=(",", ":")), encoding="utf-8"
    )

    referenced = set()
    for path in page_text:
        referenced.update(HOVER_ATTR_RE.findall(path.read_text(encoding="utf-8")))
    missing = referenced.difference(docs)
    if missing:
        raise SystemExit(f"localized hover ids missing from table: {sorted(missing)[:5]}")
    empty = [hover_id for hover_id in referenced if not docs[hover_id].strip()]
    if empty:
        raise SystemExit(f"empty localized hover payloads: {sorted(empty)[:5]}")
    english_docstrings = sum(
        1
        for hover_id in referenced
        if DOCSTRING_RE.search(docs[hover_id])
        and not re.search(r"[\u3400-\u9fff]", docs[hover_id])
    )
    if english_docstrings:
        raise SystemExit(
            f"{english_docstrings} target-page hover docstrings remain unlocalized"
        )

    return title_count, len(redirects), translated_count, len(referenced)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path, help="generated html-multi directory")
    args = parser.parse_args()
    titles, hovers, translated, referenced = localize_generated_html(args.root)
    print(
        f"Localized generated UI: {titles} titles, {hovers} hover docstrings "
        f"({translated} translated, {hovers - translated} signature-only), "
        f"{referenced} referenced hover entries"
    )


if __name__ == "__main__":
    main()
