"""Locate a Lean project and read the facts every tool here needs from it: the
root, the libraries, the package name, and which `.lean` files count as project
code.

Scan settings come from an optional `lean4-lens.toml` at the project root
(`[scan] skip_dirs`, `[scan] skip_files`); build trees and dot-directories are
always skipped.
"""

from __future__ import annotations

import os
import re
import sys
import tomllib
from collections.abc import Iterator
from dataclasses import dataclass, field
from pathlib import Path
from typing import NoReturn

from . import cli

CONFIG_NAME = "lean4-lens.toml"

# The elaborator-emitted dependency graph `lean4-lens dep-graph` writes and
# `lean4-lens dep-tree` reads. Not `review-cone*.json`: those answer the review
# document's question, and their statement-only refs go quiet on sorry-taint.
DEP_GRAPH_NAME = "dep-graph.json"

# Build output and tooling dirs are never project code, in any Lean project.
# Dot-dirs (`.lake`, `.git`, `.scratch`, …) are pruned generically, so they are
# not listed here.
_ALWAYS_SKIP_DIRS = frozenset({"build", "node_modules", "__pycache__"})

# `lakefile.lean` declares the build (`osTag`, …), not the mathematics. No
# library imports it, so no elaborator data can ever describe its decls.
_ALWAYS_SKIP_FILES = frozenset({"lakefile.lean"})


class RootNotFoundError(RuntimeError):
    pass


def find_root(start: Path | None = None) -> Path:
    """The Lean project root for `start` (default: the CWD).

    Walks up to the nearest lakefile; failing that, searches downward and
    accepts exactly one match. Raises `RootNotFoundError` on none or several.
    """
    base = (start or Path.cwd()).resolve()
    for d in [base, *base.parents]:
        if has_lakefile(d):
            return d

    found: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in dirnames if d not in _ALWAYS_SKIP_DIRS and not d.startswith(".")]
        if "lakefile.lean" in filenames or "lakefile.toml" in filenames:
            found.append(Path(dirpath))
    if len(found) == 1:
        return found[0]
    if not found:
        raise RootNotFoundError(f"no lakefile.lean/toml found under {base}; pass --root explicitly")
    candidates = "\n".join(f"  {p}" for p in sorted(found))
    raise RootNotFoundError(
        f"multiple lakefile roots found under {base}:\n{candidates}\npass --root explicitly to select one"
    )


def resolve_root(start: Path | None) -> Path:
    """`find_root`, except an explicitly named directory must exist."""
    if start is not None and not start.exists():
        raise RootNotFoundError(f"root directory not found: {start}")
    return find_root(start)


def resolve_root_or_exit(start: Path | None) -> Path:
    """`resolve_root`, reporting failure on stderr and exiting 2 — the shared
    front door for every subcommand's `--root`/`--project` argument."""
    try:
        return resolve_root(start)
    except RootNotFoundError as e:
        print(cli.red("✗ ") + str(e), file=sys.stderr)
        raise SystemExit(2) from e


def exit_no_lean_files(root: Path) -> NoReturn:
    """Report an empty scan and exit 2 — a gate that scanned nothing must not
    pass as clean."""
    print(
        cli.red("✗ no project .lean files under ")
        + cli.bold(str(root))
        + cli.dim("  — check [scan] skip_dirs/skip_files in lean4-lens.toml"),
        file=sys.stderr,
    )
    raise SystemExit(2)


def module_of(rel: Path | str) -> str:
    """The Lean module a project-relative source path defines:
    `Coloring/K3/Weights.lean` -> `Coloring.K3.Weights`."""
    return ".".join(Path(rel).with_suffix("").parts)


def module_path(module: str) -> Path:
    """`module_of`'s inverse, as a project-relative path."""
    return Path(module.replace(".", "/") + ".lean")


def has_lakefile(d: Path) -> bool:
    return (d / "lakefile.lean").is_file() or (d / "lakefile.toml").is_file()


def lakefile_path(root: Path) -> Path:
    """The project's lakefile, `.lean` flavour preferred."""
    lean = root / "lakefile.lean"
    return lean if lean.is_file() else root / "lakefile.toml"


def read_lib_names(root: Path) -> list[str]:
    """The `lean_lib` names declared in the project's lakefile (either flavour)."""
    lf = lakefile_path(root)
    if not lf.is_file():
        return []
    text = lf.read_text(encoding="utf-8")
    if lf.suffix == ".lean":
        names = re.findall(r"^\s*lean_lib\s+«?([^\s»]+)»?", text, re.M)
    else:
        names = [lib["name"] for lib in tomllib.loads(text).get("lean_lib", []) if isinstance(lib.get("name"), str)]
    return list(dict.fromkeys(names))


def read_package_name(root: Path) -> str | None:
    """The lake `package` name, for a default document title."""
    lf = lakefile_path(root)
    if not lf.is_file():
        return None
    text = lf.read_text(encoding="utf-8")
    if lf.suffix == ".lean":
        m = re.search(r"package\s+«?([^\s»]+)»?", text)
        return m.group(1) if m else None
    m = re.search(r'name\s*=\s*"([^"]+)"', text)
    return m.group(1) if m else None


@dataclass(frozen=True)
class ScanConfig:
    """Which files under a project root count as project code."""

    skip_dirs: frozenset[str] = field(default_factory=frozenset)
    skip_files: frozenset[str] = field(default_factory=frozenset)

    def skips(self, rel: Path) -> bool:
        """True if a project-relative `.lean` path is not project code."""
        parts = rel.parts
        dirs = parts[:-1]
        if any(p.startswith(".") for p in dirs):
            return True
        if set(dirs) & (self.skip_dirs | _ALWAYS_SKIP_DIRS):
            return True
        return parts[-1] in (self.skip_files | _ALWAYS_SKIP_FILES)


def read_scan_config(root: Path) -> ScanConfig:
    """The `[scan]` settings from `lean4-lens.toml`, or the defaults if absent."""
    path = root / CONFIG_NAME
    if not path.is_file():
        return ScanConfig()
    scan = tomllib.loads(path.read_text(encoding="utf-8")).get("scan", {})
    return ScanConfig(
        skip_dirs=frozenset(scan.get("skip_dirs", ())),
        skip_files=frozenset(scan.get("skip_files", ())),
    )


def iter_lean_files(root: Path, config: ScanConfig | None = None) -> Iterator[Path]:
    """Every `.lean` file that counts as project code, in sorted order."""
    cfg = read_scan_config(root) if config is None else config
    files: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        # Pruning is efficiency only (`.lake` alone holds thousands of files);
        # `cfg.skips` below stays the sole authority on what counts.
        dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in (cfg.skip_dirs | _ALWAYS_SKIP_DIRS)]
        files.extend(Path(dirpath) / f for f in filenames if f.endswith(".lean"))
    for path in sorted(files):
        if not cfg.skips(path.relative_to(root)):
            yield path
