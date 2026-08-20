"""Survey heavy / potentially-removable Lean tactics across the live sources.

Scans every project `*.lean` file (comments and docstrings stripped) for a
curated set of heavy or perf-relevant tactics and prints a short summary table:
how often each is used, in how many files, and the file that carries the most.
It is a triage aid for build-time work — the count is a starting point, NOT a
verdict (async trace times lie; profile the declaration before swapping).

  lean4-lens heavy-tactics            # summary table (default)
  lean4-lens heavy-tactics ring_nf    # every ring_nf hit: file:line + code
  lean4-lens heavy-tactics --all      # also count decide/norm_num/omega

`decide`, `norm_num`, and `omega` are omitted from the default summary — they
are intrinsic to numeric certificates and not removable — but you can still list
their hits by naming one (`lean4-lens heavy-tactics decide`) or show them in the
table with `--all`.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections.abc import Iterable, Sequence
from pathlib import Path

from .cli import (
    bold,
    clear_transient,
    cyan,
    dim,
    green,
    kv,
    row,
    rule,
    table_header,
    yellow,
)
from .project import exit_no_lean_files, iter_lean_files, resolve_root_or_exit
from .source import blank_comments_and_strings

# Curated set of heavy / perf-relevant tactics, in rough order of removability
# interest. `omit` = intrinsic to the numeric certs, dropped from the default
# summary (still queryable by name or via --all).
TACTICS: tuple[tuple[str, bool], ...] = (
    ("nlinarith", False),
    ("ring_nf", False),
    ("ring", False),
    ("congr", False),
    ("positivity", False),
    ("field_simp", False),
    ("gcongr", False),
    ("interval_cases", False),
    ("fin_cases", False),
    ("simp_all", False),
    ("aesop", False),
    ("polyrith", False),
    ("measurability", False),
    ("native_decide", False),
    ("decide", True),
    ("norm_num", True),
    ("omega", True),
)

OMITTED = {name for name, omit in TACTICS if omit}


def _pat(words: Iterable[str]) -> re.Pattern[str]:
    """Word-boundary match for the given tactic tokens: not preceded by an
    identifier char or a dot (excludes `sum_congr`, `.congr`), not followed by
    one (excludes `congrArg`, `ring_nf` when matching `ring`)."""
    alt = "|".join(re.escape(w) for w in sorted(words, key=len, reverse=True))
    return re.compile(rf"(?<![\w.])({alt})(?![\w])")


ALL_TACTICS_RE = _pat(name for name, _ in TACTICS)


Hit = tuple[Path, int, str]  # file, 1-indexed line, original line text


def scan(root: Path, only: str | None = None) -> tuple[dict[str, list[Hit]], int]:
    """Return {tactic: [hits]} (at most one hit per line and tactic) and the
    number of files scanned. `only` restricts the scan to one tactic."""
    rx = _pat([only]) if only else ALL_TACTICS_RE
    hits: dict[str, list[Hit]] = {name: [] for name, _ in TACTICS}
    n_files = 0
    for path in iter_lean_files(root):
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        n_files += 1
        orig = text.split("\n")
        clean = blank_comments_and_strings(text).split("\n")
        for lineno, code in enumerate(clean, start=1):
            for name in {m.group(1) for m in rx.finditer(code)}:
                hits[name].append((path, lineno, orig[lineno - 1]))
    return hits, n_files


_COLS = (("tactic", 14), ("sites", 6), ("files", 6), ("top file", 34))


def _trunc(s: str, w: int) -> str:
    return s if len(s) <= w else "…" + s[-(w - 1) :]


def show_summary(hits: dict[str, list[Hit]], root: Path, n_files: int, show_omitted: bool) -> None:
    print()
    print("  " + bold(cyan("Heavy tactics")))
    print("  " + dim("removable / perf-relevant tactic usage in live Lean sources"))
    print(rule())
    kv("root", dim(str(root)))
    kv("files scanned", green(str(n_files)))

    visible = [name for name, omit in TACTICS if show_omitted or not omit]
    present = [n for n in visible if hits[n]]
    present.sort(key=lambda n: len(hits[n]), reverse=True)

    table_header(_COLS, caption="most-used first · run `… <tactic>` for line hits")
    for name in present:
        hl = hits[name]
        files = {h[0] for h in hl}
        top = max(files, key=lambda f: sum(1 for h in hl if h[0] == f))
        top_rel = _trunc(str(top.relative_to(root)), 34)
        row(
            (
                cyan(f"{name:>14}"),
                bold(f"{len(hl):>6}"),
                dim(f"{len(files):>6}"),
                dim(f"{top_rel:<34}"),
            )
        )

    print(rule())
    total = sum(len(hits[n]) for n in visible)
    kv("total sites", bold(green(str(total))))
    zero = [n for n in visible if not hits[n]]
    if zero:
        kv("0 sites", dim(", ".join(zero)))
    if not show_omitted:
        om = ", ".join(f"{n} ({len(hits[n])})" for n in OMITTED if hits[n])
        if om:
            kv("omitted", dim(om) + dim("  — pass a name or --all"))
    print()


def show_detail(hits: dict[str, list[Hit]], name: str, root: Path) -> None:
    hl = sorted(hits[name], key=lambda h: (str(h[0]), h[1]))
    rx = _pat([name])
    print()
    print("  " + bold(cyan(f"Heavy tactics · {name}")))
    print("  " + dim(f"{len(hl)} hit(s) in {len({h[0] for h in hl})} file(s)"))
    print(rule())
    for path, lineno, code in hl:
        loc = f"{path.relative_to(root)}:{lineno}"
        marked = rx.sub(lambda m: yellow(bold(m.group(0))), code.strip())
        print(f"  {dim(loc)}  {marked}")
    print(rule())
    kv("total", bold(green(str(len(hl)))))
    print()


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="lean4-lens heavy-tactics",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("tactic", nargs="?", help="show every hit (file:line + code) for this tactic")
    ap.add_argument("--all", action="store_true", help="include decide/norm_num/omega in the summary table")
    ap.add_argument(
        "--root", type=Path, default=None, help="project root to scan (default: nearest lakefile from the CWD)"
    )
    args = ap.parse_args(argv)

    known = [name for name, _ in TACTICS]
    if args.tactic and args.tactic not in known:
        print(f"unknown tactic {args.tactic!r}; known: {', '.join(known)}", file=sys.stderr)
        return 2

    root = resolve_root_or_exit(args.root)
    hits, n_files = scan(root, only=args.tactic)
    clear_transient()
    if n_files == 0:
        exit_no_lean_files(root)
    if args.tactic:
        show_detail(hits, args.tactic, root)
    else:
        show_summary(hits, root, n_files, args.all)
    return 0
