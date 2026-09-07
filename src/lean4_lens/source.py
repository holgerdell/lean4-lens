"""Lean source text partitioned into code, comment, and string spans, so a scan
never mistakes a word inside a comment for code.
"""

from __future__ import annotations

import re
from collections.abc import Iterator

Span = tuple[int, int, str]  # (lo, hi, kind); kind is "code" | "comment" | "string"

# Character literals share the non-code "string" span kind. Require a complete
# literal and a token boundary: apostrophes also occur inside Lean identifiers.
_CHAR_LITERAL_RE = re.compile(r"""(?<![\w'?!])'(?:[^\\\r\n]|\\(?:[\\'"rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'""")


def iter_spans(text: str) -> Iterator[Span]:
    """Partition `text` into contiguous `(lo, hi, kind)` spans covering it
    exactly. Comments are `--` to end of line and `/- -/` (possibly nested,
    docstrings included); strings are `"…"` with backslash escapes; character
    literals are also "string" spans. Everything else is code. Unterminated
    comments/strings run to the end of the text."""
    i, n = 0, len(text)
    code_start = 0

    def code_upto(hi: int) -> list[Span]:
        return [(code_start, hi, "code")] if hi > code_start else []

    while i < n:
        if text[i] == "«":
            # Quoted identifiers are code, even when their names contain
            # comment delimiters or text that looks like a literal.
            end = text.find("»", i + 1)
            i = n if end == -1 else end + 1
        elif text.startswith("/-", i):
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
        elif text[i] == "'" and (literal := _CHAR_LITERAL_RE.match(text, i)):
            yield from code_upto(i)
            start, i = i, literal.end()
            yield (start, i, "string")
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
    """`text` with every comment, string and character literal blanked, at the
    original length, so offsets into the result still index the source."""
    out = list(text)
    for lo, hi, kind in iter_spans(text):
        if kind != "code":
            for j in range(lo, hi):
                if out[j] != "\n":
                    out[j] = " "
    return "".join(out)
