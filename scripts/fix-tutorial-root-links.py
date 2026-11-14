#!/usr/bin/env python3
"""Give tutorial root sections the same page path as their generated HTML."""
from __future__ import annotations

import json
import html
import re
from pathlib import Path
import sys


def fix(saved_path: Path, xref_path: Path, html_root: Path | None = None) -> None:
    saved = json.loads(saved_path.read_text(encoding="utf-8"))
    xref = json.loads(xref_path.read_text(encoding="utf-8"))
    locations = {item["key"]: item["value"] for item in saved["traverseState"]["externalTags"]}
    sections = xref["Verso.Genre.Manual.section"]["contents"]
    count = 0
    for topic in saved["tutorials"]["topics"]:
        for tutorial in topic["tutorials"]:
            metadata = tutorial["metadata"]
            slug = metadata["slug"]
            tag = metadata["tag"]
            location = locations[metadata["id"]]
            if location["path"] not in ([], [slug]):
                raise SystemExit(f"unexpected tutorial root path: {tag}: {location['path']!r}")
            location["path"] = [slug]
            targets = sections[tag]
            if len(targets) != 1:
                raise SystemExit(f"ambiguous tutorial root: {tag}")
            targets[0]["address"] = f"/{slug}/"
            if html_root is not None:
                page = html_root / slug / "index.html"
                text = page.read_text(encoding="utf-8")
                if not re.search(r"\bid=[\"']" + re.escape(tag) + r"[\"']", text):
                    anchor = '<span id="' + html.escape(tag, quote=True) + '"></span>'
                    text, replaced = re.subn(r"(<body\b[^>]*>)", lambda m: m[1] + anchor, text, count=1)
                    if replaced != 1:
                        raise SystemExit(f"cannot place tutorial root anchor: {page}")
                    page.write_text(text, encoding="utf-8")
            count += 1
    saved_path.write_text(json.dumps(saved, ensure_ascii=False), encoding="utf-8")
    xref_path.write_text(json.dumps(xref, ensure_ascii=False), encoding="utf-8")
    print(f"Fixed {count} tutorial root links")


if __name__ == "__main__":
    if len(sys.argv) not in (3, 4):
        raise SystemExit("usage: fix-tutorial-root-links.py SAVED_TUTORIALS XREF_JSON [HTML_ROOT]")
    fix(Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]) if len(sys.argv) == 4 else None)
