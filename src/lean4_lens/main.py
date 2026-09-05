"""The `lean4-lens` command: one entry point in front of the four tools."""

from __future__ import annotations

import sys
from collections.abc import Callable, Sequence

from . import build_times, dep_tree, heavy_tactics, review_cone
from .cli import bold, cyan, dim

COMMANDS: dict[str, tuple[Callable[[Sequence[str]], int], str]] = {
    "review-cone": (review_cone.main, "render the review cone as a standalone HTML document"),
    "emit-refs": (review_cone.dep_graph_main, "emit dep-graph.json, the data `refs` reads"),
    "dep-graph": (review_cone.dep_graph_main, "alias of emit-refs (one release)"),
    "refs": (dep_tree.main, "query the proof references: check gates, shows, exports"),
    "dep-tree": (dep_tree.main, "alias of refs (one release)"),
    "heavy-tactics": (heavy_tactics.main, "where the expensive tactics are used"),
    "build-times": (build_times.main, "per-module build time for a library"),
}


def usage() -> str:
    lines = ["", "  " + bold(cyan("lean4-lens")) + dim("  — analysis tools for a Lean 4 project"), ""]
    width = max(len(name) for name in COMMANDS)
    for name, (_, help_text) in COMMANDS.items():
        lines.append(f"    {cyan(name.ljust(width))}  {dim(help_text)}")
    lines += ["", "  " + dim("lean4-lens <command> --help for a command's own options"), ""]
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if not args or args[0] in ("-h", "--help", "help"):
        print(usage())
        return 0
    name, rest = args[0], args[1:]
    if name not in COMMANDS:
        print(f"unknown command {name!r}; known: {', '.join(COMMANDS)}", file=sys.stderr)
        return 2
    return COMMANDS[name][0](rest)
