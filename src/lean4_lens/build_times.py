#!/usr/bin/env python3
"""Measure per-module build time for a Lean package via `lake`.

For every module in the project's libraries, this recompiles just that file with
`lake env lean <path>` (imports served from cached oleans) and records the
wall-clock elaboration time. Running each module in isolation avoids the
core-stealing noise of a parallel `lake build`, giving a reproducible per-module
cost. Results are streamed to a JSONL file (one JSON object per line), then
rewritten sorted slowest→fastest.

Project-independent: the project root is the nearest lakefile (`.lean` or `.toml`)
walking up from --project/CWD, and the libraries to time are the `lean_lib` names
declared there (override with --lib / narrow with --exclude).

Prerequisite: a warm build so dependency oleans exist. By default the script runs
`lake build` once first; pass --no-build to skip that.

Usage:
    lean4-lens build-times
    lean4-lens build-times --project path/to/proj --runs 3 --no-build
    lean4-lens build-times --lib Coloring --lib Branching --exclude Old
    lean4-lens build-times --output /tmp/times.jsonl
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from collections.abc import Sequence
from pathlib import Path
from typing import Any

from . import cli
from .project import module_of, read_lib_names, read_scan_config, resolve_root_or_exit

_COLS = (("#", 8), ("seconds", 9), ("module", 44), ("status", 14))


def discover_modules(root: Path, libs: list[str], exclude: list[str]) -> list[Path]:
    """Package `.lean` files (relative to `root`, sorted) across `libs`.

    For each library `L`, includes the root aggregator `L.lean` and everything
    under `L/`. What counts as project code comes from `lean4-lens.toml`, exactly
    as for the other tools; `exclude` skips further directory components on top.
    """
    cfg = read_scan_config(root)
    paths: list[Path] = []
    for lib in libs:
        root_module = root / f"{lib}.lean"
        if root_module.is_file():
            paths.append(root_module)
        lib_dir = root / lib
        if lib_dir.is_dir():
            paths.extend(lib_dir.rglob("*.lean"))
    rels = sorted({p.relative_to(root) for p in paths}, key=lambda r: r.as_posix())
    return [r for r in rels if not cfg.skips(r) and not any(part in exclude for part in r.parts)]


def time_one(rel: Path, root: Path, runs: int) -> dict[str, Any]:
    """Time `lake env lean <rel>`; return the minimum wall time over `runs`."""
    best: float | None = None
    rc = 0
    err_tail = ""
    for _ in range(runs):
        start = time.perf_counter()
        proc = subprocess.run(
            ["lake", "env", "lean", rel.as_posix()],
            cwd=root,
            capture_output=True,
            text=True,
        )
        elapsed = time.perf_counter() - start
        rc = proc.returncode
        if rc != 0:
            err_tail = (proc.stderr or proc.stdout or "").strip()[-800:]
            best = elapsed if best is None else min(best, elapsed)
            break  # a failing module won't get faster; don't repeat
        best = elapsed if best is None else min(best, elapsed)
    record = {
        "module": module_of(rel),
        "path": rel.as_posix(),
        "seconds": round(best if best is not None else 0.0, 3),
        "runs": runs,
        "returncode": rc,
        "ok": rc == 0,
    }
    if rc != 0:
        record["error_tail"] = err_tail
    return record


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="lean4-lens build-times", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--project", type=Path, default=None, help="Lean project root (default: nearest lakefile from the CWD)."
    )
    parser.add_argument(
        "--lib",
        action="append",
        default=None,
        metavar="NAME",
        help="Library to time (repeatable). Default: every lean_lib in the lakefile.",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        metavar="DIR",
        help="Skip modules with this directory component (repeatable).",
    )
    parser.add_argument(
        "--output", type=Path, default=None, help="Output JSONL path (default: <project>/module_build_times.jsonl)."
    )
    parser.add_argument(
        "--runs", type=int, default=1, help="Timed runs per module; the minimum is reported (default: 1)."
    )
    parser.add_argument(
        "--no-build", action="store_true", help="Skip the initial `lake build` warm-up (assume oleans are current)."
    )
    args = parser.parse_args(argv)

    if args.runs < 1:
        parser.error("--runs must be >= 1")

    root = resolve_root_or_exit(args.project)

    libs = args.lib or read_lib_names(root)
    if not libs:
        print(cli.red("✗ no libraries found") + cli.dim("  (no lean_lib in the lakefile; pass --lib)"), file=sys.stderr)
        return 2

    modules = discover_modules(root, libs, args.exclude)
    if not modules:
        print(cli.red("✗ no package modules found") + cli.dim(f"  under libraries {libs}"), file=sys.stderr)
        return 2

    output = args.output or (root / "module_build_times.jsonl")

    cli.heading("MODULE BUILD TIMES")
    cli.kv("project", cli.dim(str(root)))
    cli.kv("libraries", cli.dim(", ".join(libs)))
    cli.kv("output", cli.dim(str(output)))

    if not args.no_build:
        # Warm the build so import closures have fresh oleans. Modules that do not
        # compile in isolation are recorded with "ok": false rather than aborting.
        cli.status("warming build (lake build) …")
        warm = subprocess.run(["lake", "build"], cwd=root)
        cli.clear_transient()
        if warm.returncode != 0:
            print(cli.red("✗ warm-up `lake build` failed") + " — fix the build first.", file=sys.stderr)
            return warm.returncode

    cli.table_header(_COLS, caption=f"per-module `lake env lean` wall time · {len(modules)} modules")
    output.parent.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, Any]] = []
    with output.open("w", encoding="utf-8") as fh:
        for i, rel in enumerate(modules, 1):
            cli.status(f"[{i}/{len(modules)}] timing {module_of(rel)} …")
            record = time_one(rel, root, args.runs)
            records.append(record)
            fh.write(json.dumps(record) + "\n")
            fh.flush()  # stream progress; survive interruption
            cli.clear_transient()
            idx = cli.dim(f"{i:>3}/{len(modules)}".rjust(8))
            secs = cli.green(f"{record['seconds']:>9.3f}")
            mod = cli.cyan(record["module"][:44].ljust(44))
            flag = cli.dim("ok".ljust(14)) if record["ok"] else cli.red("BUILD FAILED".ljust(14))
            cli.row((idx, secs, mod, flag))

    # Rewrite sorted slowest→fastest (the streamed file was in scan order).
    records.sort(key=lambda r: float(r["seconds"]), reverse=True)
    cli.write_jsonl(output, records)

    n_fail = sum(1 for r in records if not r["ok"])
    total = sum(r["seconds"] for r in records)
    print()
    detail = f"{len(records)} modules, {total:.1f}s total, sorted slowest→fastest"
    if n_fail:
        detail += f" · {n_fail} failed"
    cli.wrote(output, detail)
    return 0
