"""Lean source text partitioned into code, comment, and string spans, so a scan
never mistakes a word inside a comment for code.
"""

from __future__ import annotations

from collections.abc import Iterator

Span = tuple[int, int, str]  # (lo, hi, kind); kind is "code" | "comment" | "string"


def iter_spans(text: str) -> Iterator[Span]:
    """Partition `text` into contiguous `(lo, hi, kind)` spans covering it
    exactly. Comments are `--` to end of line and `/- -/` (possibly nested,
    docstrings included); strings are `"…"` with backslash escapes; everything
    else is code. Unterminated comments/strings run to the end of the text."""
    i, n = 0, len(text)
    code_start = 0

    def code_upto(hi: int) -> list[Span]:
        return [(code_start, hi, "code")] if hi > code_start else []

    while i < n:
        if text.startswith("/-", i):
            yield from code_upto(i)
            start, depth, i = i, 1, i + 2
            while i < n and depth > 0:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            yield (start, i, "comment")
            code_start = i
        elif text.startswith("--", i):
            start = i
            yield from code_upto(i)
            while i < n and text[i] != "\n":
                i += 1
            yield (start, i, "comment")
            code_start = i
        elif text[i] == '"':
            yield from code_upto(i)
            start, i = i, i + 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" and i + 1 < n else 1
            i = min(i + 1, n)
            yield (start, i, "string")
            code_start = i
        else:
            i += 1
    yield from code_upto(n)


def blank_comments_and_strings(text: str) -> str:
    """`text` with every comment and string literal replaced by spaces, at the
    original length, so offsets into the result still index the source."""
    out = list(text)
    for lo, hi, kind in iter_spans(text):
        if kind != "code":
            for j in range(lo, hi):
                if out[j] != "\n":
                    out[j] = " "
    return "".join(out)
