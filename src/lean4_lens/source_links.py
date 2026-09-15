"""Exact source references saved by Lean's elaborator in its `.ilean` files."""

from __future__ import annotations

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True, order=True)
class SourceRef:
    start: int
    end: int
    name: str
    definition: bool = False


def user_name(name: str) -> str:
    """Use the same written names as the review-cone emitter for private declarations."""
    return re.sub(r"^_private\..*?\.\d+\.", "", name)


def read_source_refs(root: Path, module: str, source: str) -> tuple[SourceRef, ...]:
    """Read compiler ranges as Python offsets; missing or stale data never triggers name guessing."""
    relative = Path(module.replace(".", "/"))
    source_path = root / relative.with_suffix(".lean")
    paths = [root / ".lake/build/lib/lean" / relative.with_suffix(".ilean"),
             root / ".lake/build/lib" / relative.with_suffix(".ilean")]
    path = next((p for p in paths if p.is_file()), None)
    try:
        if path is None:
            raise ValueError("missing .ilean")
        if source_path.stat().st_mtime_ns > path.stat().st_mtime_ns:
            raise ValueError("source is newer than .ilean")
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("module") != module:
            raise ValueError(".ilean module does not match source")
        # LSP columns count UTF-16 code units, not Unicode characters or UTF-8 bytes.
        positions: list[dict[int, int]] = []
        offset = 0
        for line in source.splitlines(keepends=True):
            column = 0
            row = {0: offset}
            for ch in line:
                column += 2 if ord(ch) > 0xFFFF else 1
                offset += 1
                row[column] = offset
            positions.append(row)
        positions.append({0: offset})
        refs = set()
        for ident_json, info in data["references"].items():
            ident = json.loads(ident_json)
            if "c" not in ident:
                continue  # Local variables have no global link target.
            name = user_name(ident["c"]["n"])
            locations = [(loc, False) for loc in info["usages"]]
            if info.get("definition") is not None:
                locations.append((info["definition"], True))
            for loc, definition in locations:
                if len(loc) not in (4, 5) or any(type(n) is not int or n < 0 for n in loc[:4]):
                    raise ValueError("invalid reference position")
                start = positions[loc[0]][loc[1]]
                end = positions[loc[2]][loc[3]]
                if not 0 <= start < end <= len(source):
                    raise ValueError("invalid reference range")
                refs.add(SourceRef(start, end, name, definition))
        return tuple(sorted(refs))
    except (OSError, ValueError, KeyError, IndexError, TypeError) as exc:
        print(f"warning: source links omitted for {module}: {exc}; rebuild the module", file=sys.stderr)
        return ()
