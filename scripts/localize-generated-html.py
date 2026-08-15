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
    "Run-Time-Code/index.html",
    "Run-Time-Code/Boxing/index.html",
    "Run-Time-Code/Reference-Counting/index.html",
    "Run-Time-Code/Multi-Threaded-Execution/index.html",
    "Run-Time-Code/Foreign-Function-Interface/index.html",
    "Terms/index.html",
    "Terms/Identifiers/index.html",
    "Terms/Function-Types/index.html",
    "Terms/Functions/index.html",
    "Terms/Function-Application/index.html",
    "Terms/Numeric-Literals/index.html",
    "Terms/Structures-and-Constructors/index.html",
    "Terms/Conditionals/index.html",
    "Terms/Pattern-Matching/index.html",
    "Terms/Holes/index.html",
    "Terms/Type-Ascription/index.html",
    "Terms/Quotation-and-Antiquotation/index.html",
    "Terms/do--Notation/index.html",
    "Terms/Proofs/index.html",
    "Tactic-Proofs/index.html",
    "Tactic-Proofs/Reading-Proof-States/index.html",
    "Tactic-Proofs/Running-Tactics/index.html",
    "Tactic-Proofs/Naming-Bound-Variables/index.html",
    "Tactic-Proofs/The-Tactic-Language/index.html",
    "Tactic-Proofs/Options/index.html",
    "Tactic-Proofs/Tactic-Reference/index.html",
    "Tactic-Proofs/Targeted-Rewriting-with--conv/index.html",
    "Tactic-Proofs/Custom-Tactics/index.html",
)

HOVER_ATTR_RE = re.compile(r'data-verso-hover="([^"]+)"')
VERSO_LINKS_RE = re.compile(r'data-verso-links="([^"]+)"')
NAMEDOCS_TEXT_RE = re.compile(
    r'(<div class="namedocs"[^>]*>.*?<div class="text">)(.*?)(</div>\s*</div>)',
    re.DOTALL,
)
DOCSTRING_RE = re.compile(
    r'(?:<span class="sep"></span>)?<code class="docstring">.*?</code>', re.DOTALL
)
TITLE_REPLACEMENTS = (
    (re.compile(r'title="Documentation for ([^"]*)"'), r'title="文档：\1"'),
    (re.compile(r'title="Definition of ([^"]*)"'), r'title="定义：\1"'),
    (re.compile(r'title="Permalink"'), 'title="永久链接"'),
)
GENERATED_UI_REPLACEMENTS = (
    ('<span class="label">tactic</span>', '<span class="label">策略</span>'),
    ('<span class="label">conv tactic</span>', '<span class="label">conv 策略</span>'),
    ('title="文档：tactic"', 'title="文档：策略"'),
    ('title="文档：conv tactic"', 'title="文档：conv 策略"'),
    ('title="文档：syntax"', 'title="文档：语法"'),
)
FORBIDDEN_TITLES = ("Documentation for ", "Definition of ", "Permalink")
NO_ADDITIONAL_DOCS = "<span>无附加文档。</span>"
NAMEDOCS_TRANSLATIONS_PATH = Path(__file__).with_name("tactic-namedocs-zh.json")
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


def normalized_visible_text(fragment: str) -> str:
    return " ".join(html.unescape(re.sub(r"<[^>]+>", " ", fragment)).split())


def load_namedocs_translations() -> dict[str, str]:
    if not NAMEDOCS_TRANSLATIONS_PATH.is_file():
        return {}
    records = json.loads(NAMEDOCS_TRANSLATIONS_PATH.read_text(encoding="utf-8"))
    translations: dict[str, str] = {}
    for record in records:
        source = record["source"]
        translation = record["translation"]
        if source in translations and translations[source] != translation:
            raise SystemExit(f"conflicting generated-doc translation: {source[:80]!r}")
        translations[source] = translation
    return translations


def localize_link_metadata(text: str) -> str:
    replacements = {
        "Documentation for tactic": "策略文档",
        "Documentation for syntax": "语法文档",
    }

    def replace(match: re.Match[str]) -> str:
        links = json.loads(html.unescape(match.group(1)))
        for link in links:
            link["long"] = replacements.get(link.get("long"), link.get("long"))
        encoded = html.escape(
            json.dumps(links, ensure_ascii=False, separators=(",", ":")), quote=True
        )
        return f'data-verso-links="{encoded}"'

    return VERSO_LINKS_RE.sub(replace, text)


def localize_tactic_namedocs(text: str, translations: dict[str, str]) -> str:
    missing: list[str] = []

    def replace(match: re.Match[str]) -> str:
        source = normalized_visible_text(match.group(2))
        translation = translations.get(source)
        if translation is None and (
            not re.search(r"[A-Za-z]{3}", source)
            or re.search(r"[\u3400-\u9fff]", source)
        ):
            return match.group(0)
        if translation is None:
            missing.append(source)
            return match.group(0)
        body = f"\n                  <p>{html.escape(translation)}</p>\n                  "
        return match.group(1) + body + match.group(3)

    localized = NAMEDOCS_TEXT_RE.sub(replace, text)
    if missing:
        raise SystemExit(
            f"{len(missing)} generated tactic docstrings lack translations; "
            f"first: {missing[0][:120]!r}"
        )
    return localized


def strip_english_inline_docstrings(text: str) -> str:
    def replace(match: re.Match[str]) -> str:
        return match.group(0) if re.search(r"[\u3400-\u9fff]", match.group(0)) else ""

    return DOCSTRING_RE.sub(replace, text)


def localize_generated_html(root: Path) -> tuple[int, int, int, int]:
    docs_path = root / "-verso-docs.json"
    if not docs_path.is_file():
        raise SystemExit(f"missing Verso hover table: {docs_path}")
    docs: dict[str, str] = json.loads(docs_path.read_text(encoding="utf-8"))

    page_text: dict[Path, str] = {}
    namedocs_translations = load_namedocs_translations()
    title_count = 0
    hover_ids: set[str] = set()
    translated_hovers: dict[str, str] = {}
    for rel in TARGET_PAGES:
        path = root / rel
        if not path.is_file():
            raise SystemExit(f"missing translated page: {path}")
        text = path.read_text(encoding="utf-8")
        text = text.replace(">Table of Contents<", ">目录<")
        text = localize_link_metadata(text)
        if rel.startswith("Tactic-Proofs/"):
            text = localize_tactic_namedocs(text, namedocs_translations)
        parser = NamedDocsParser()
        parser.feed(text)
        translated_hovers.update(parser.translations)
        text = strip_english_inline_docstrings(text)
        for pattern, replacement in TITLE_REPLACEMENTS:
            text, count = pattern.subn(replacement, text)
            title_count += count
        for source, replacement in GENERATED_UI_REPLACEMENTS:
            text = text.replace(source, replacement)
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
        if translated and not re.search(r"[\u3400-\u9fff]", translated):
            translated = None
        replacement = ""
        if translated:
            replacement = (
                '<span class="sep"></span><code class="docstring">'
                + html.escape(translated)
                + "</code>"
            )
        stripped, count = DOCSTRING_RE.subn(lambda _match: replacement, payload)
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
