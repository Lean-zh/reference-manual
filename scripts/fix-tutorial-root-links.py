#!/usr/bin/env python3
"""Give tutorial root sections the same page path as their generated HTML."""
from __future__ import annotations

import json
from pathlib import Path
import sys


def fix(saved_path: Path, xref_path: Path) -> None:
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
            count += 1
    saved_path.write_text(json.dumps(saved, ensure_ascii=False), encoding="utf-8")
    xref_path.write_text(json.dumps(xref, ensure_ascii=False), encoding="utf-8")
    print(f"Fixed {count} tutorial root links")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: fix-tutorial-root-links.py SAVED_TUTORIALS XREF_JSON")
    fix(Path(sys.argv[1]), Path(sys.argv[2]))
