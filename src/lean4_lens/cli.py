"""Output helpers for the commands here — muted labels, highlighted values,
aligned tables, in-place heartbeats, and the JSONL files commands write.

Colour is gated on a TTY and honours `NO_COLOR`.
"""

from __future__ import annotations

import json
import os
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

RULE_W = 60


def use_color() -> bool:
    return sys.stdout.isatty() and not os.environ.get("NO_COLOR")


def _c(s: str, code: str) -> str:
    return f"\033[{code}m{s}\033[0m" if use_color() else s


def dim(s: str) -> str:
    return _c(s, "2")


def bold(s: str) -> str:
    return _c(s, "1")


def cyan(s: str) -> str:
    return _c(s, "36")


def green(s: str) -> str:
    return _c(s, "32")


def yellow(s: str) -> str:
    return _c(s, "33")


def red(s: str) -> str:
    return _c(s, "31")


def rule(ch: str = "─") -> str:
    return dim(ch * RULE_W)


def kv_s(label: str, value: str, width: int = 14) -> str:
    """A muted left-aligned label + highlighted value, as a string."""
    return f"  {dim(label.ljust(width))}{value}"


def kv(label: str, value: str) -> None:
    """A muted left-aligned label + highlighted value (label column ljust(14), 2-space gutter)."""
    print(kv_s(label, value))


def wrote(path: Path | str, detail: str = "") -> None:
    """The one success line every command ends with: `● wrote <path>  (detail)`."""
    line = "  " + green("●") + dim("  wrote ") + bold(str(path))
    if detail:
        line += dim(f"  ({detail})")
    print(line)


def write_jsonl(path: Path, records: Iterable[dict[str, Any]]) -> None:
    """One JSON object per line, UTF-8, non-ASCII kept literal."""
    with open(path, "w", encoding="utf-8") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")


def heading(title: str) -> None:
    """A named section heading: blank line + bold-cyan title (cyan = titles, per cli-style.md)."""
    print()
    print("  " + bold(cyan(title)))


def table_header(cols: tuple[tuple[str, int], ...], caption: str | None = None) -> None:
    """Dim header row + separator for a `_COLS = ((name, width), ...)` declaration.

    `caption` (optional, keep <=~50 chars) prints a dim one-line description above the header.
    """
    print()
    if caption is not None:
        print("  " + dim(caption))
    names = "  ".join(name.rjust(w) for name, w in cols)
    seps = "  ".join("─" * w for _name, w in cols)
    print("  " + dim(names))
    print("  " + dim(seps))


def _inplace(payload: str) -> None:
    """Carriage-return + clear-line + `payload`, no newline — TTY only. The shared
    primitive behind every erasable line (heartbeat rows, status lines, the clear)."""
    if sys.stdout.isatty():
        sys.stdout.write("\r\033[2K" + payload)
        sys.stdout.flush()


def row(cells: tuple[str, ...]) -> None:
    """Emit one aligned table row. Each cell is pre-formatted to its `_COLS` width then
    coloured (ANSI has zero display width, so format BEFORE colouring)."""
    print("  " + "  ".join(cells))


def status(text: str) -> None:
    """Write an in-place (erasable) muted status line — TTY only, no newline."""
    _inplace("  " + dim(text))


def clear_transient() -> None:
    """Erase the in-place heartbeat/status line (TTY only) before writing permanent output."""
    _inplace("")
