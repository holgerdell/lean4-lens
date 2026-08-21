# lean4-lens

Analysis tools for a Lean 4 project. Point them at a project and they report on
it: what a reviewer must read, what depends on what, where the expensive tactics
are, and what each module costs to build.

They are stdlib-only, and they find the project themselves (the nearest
lakefile, walking up) — `--project DIR` on any command names one instead.

They never modify your Lean sources, but they are not read-only: `review-cone`
and `dep-graph` emit their JSON next to the project (running `lake build`
first, unless `--no-build`), `build-times` writes `module_build_times.jsonl`
and drives `lake`, and `dep-tree dead` writes `dead_candidates.jsonl` into the
current directory. Every output path is overridable. Each command's `--help`
is the authoritative list of its options; the sections below give the shape.

## Install

```sh
uv tool install /path/to/lean4-lens     # or: uv run --project /path/to/lean4-lens lean4-lens
```

## Commands

```
lean4-lens review-cone     render the review cone as a standalone HTML document
lean4-lens dep-graph       emit dep-graph.json, the data `dep-tree` reads
lean4-lens dep-tree        query the dependency graph: reachability, taint, dead code
lean4-lens heavy-tactics   where the expensive tactics are used
lean4-lens build-times     per-module build time for a library
```

### review-cone

The review cone is the transitive set of statements a human must read to trust
that a formalization says what it claims — a concept following
[lean-atlas](https://github.com/NyxFoundation/lean-atlas). `lean4-lens
review-cone` builds the libraries (skip with `--no-build`), runs a Lean
elaborator script over them, and writes a standalone cross-linked HTML
document: every project reference an internal link, every mathlib reference a
link to the mathlib4 docs. `--json FILE` re-renders JSON emitted earlier and
skips the Lean run entirely.

### dep-graph

Runs the same Lean emitter but writes `dep-graph.json`: every project
declaration with the declarations its proof refers to. That file is what
`dep-tree` reads.

### dep-tree

Answers dependency questions over `dep-graph.json`, one subcommand each:

```
summary       counts + listings, and the CI gates
coverage      does the committed graph still describe the code?
reach         split every decl into used / unused, from a set of roots
dead          dead-code candidates: unreachable *and* referenced by nothing live
orphans       unreferenced decls (entry points, or dead)
sorry-paths   direct-sorry decls ranked by how much they block
rdeps         transitive reverse-deps of one decl
from          transitive deps of one decl
direct        immediate refs of one decl
dag           the whole DAG as `Name: dep1 dep2 …` lines
dot           GraphViz DOT, optionally the subgraph from one decl
json          the whole graph as JSON
```

`reach` and `dead` take root declarations as arguments, or `--root-file PATH`
for every decl in a file; with neither they fall back to the roots named in the
project's `review-cone*.toml`. Both can write their split as JSONL
(`--out-used` / `--out-unused`). `dead` writes `dead_candidates.jsonl` by
default (`--out` redirects it, `--no-out` skips it) and takes `--closure` for
the whole removable set in one pass, rather than only the globally-orphaned
decls.

References come from the elaborator only. A declaration the data misses gets no
edges and is reported, never guessed at.

`summary --fail-on-sorry` / `--fail-on-axioms` turn the report into a CI gate
(exit 1 on findings), and every scan-based command exits 2 when it finds no
project files at all — a gate that scanned nothing must not pass as clean.

### heavy-tactics

With no argument, a summary table: how often each curated tactic is used, in
how many files, and the file carrying the most. Name a tactic
(`lean4-lens heavy-tactics ring_nf`) for every hit as `file:line` plus the
source line. `decide`, `norm_num` and `omega` are intrinsic to numeric
certificates rather than removable, so they stay out of the default table;
`--all` includes them.

### build-times

Recompiles each module on its own with `lake env lean` and reports the
wall-clock cost, sorted slowest first, to the terminal and to
`module_build_times.jsonl` (`--output` redirects). Timing one module at a time
avoids the core-stealing noise of a parallel build. `--runs N` reports the
minimum of N timings; `--lib NAME` and `--exclude DIR` narrow what is measured;
`--no-build` skips the `lake build` warm-up when the oleans are already current.

## Project configuration

Both files are optional and live at the Lean project root.

`review-cone.toml` names the roots and the section layout of the review
document, plus the document's own `title` and `out` path (relative to the
project root; `--title`/`--out` override). Each `[[section]]` has a `title`
and a `decls` list; every named decl is a root, and the cone is the transitive
closure of them all.

Cone members no section claims land in the `[support]` catch-all: rendered
last in topological order, and kept out of the table of contents unless
`support.toc = true` (or `--toc-support`). A section-local `[section.titles]`
table gives individual decls a display title; a dotted Lean name must be
quoted, or TOML reads it as a nested table.

```toml
title = "My Formalization"
out = "docs/review-cone.html"

[[section]]
title = "Main results"
decls = ["main_theorem", "algorithm_correct"]

[section.titles]
"main_theorem" = "Correctness of the algorithm"

[support]
title = "Supporting declarations"
toc = false
```

A project may keep several review documents: every `review-cone*.toml` is a
config in its own right (`--config` selects one), each emitting JSON and HTML
named after itself. `dep-tree`'s default roots are the union of them all.

`lean4-lens.toml` says which files count as project code. Build trees and
dot-directories are always skipped, so most projects need nothing here.

```toml
[scan]
skip_dirs = ["Old", "attic", "Draft", "scripts"]
skip_files = ["Main.lean"]
```

## Development

```sh
uv run ruff check
uv run mypy
uv run pytest
```

`uv run pytest` uses one interpreter. To run the suite on every supported
Python — 3.11 through 3.14, plus the 3.15 release candidate as early warning —
use tox:

```sh
uv tool install tox --with tox-uv   # once
tox            # every version
tox -e py311   # one of them
```

### The Lean fixture projects

The emitter runs on Lean v4.19 and up; v4.18 and older lack the
`importModules` options it needs.

`tests/lean-v*` are tiny Lean projects, one per pinned toolchain — the oldest
supported release, three newer ones and the current release candidate — that
the emitter tests run against: the assertions that need real elaborator output
rather than fixture JSON. They depend on Lean core only, so each builds in a couple of seconds:

```sh
cd tests/lean-v4.33.0 && lake build
```

An unbuilt one skips (building it would make pytest download a toolchain), so a
fresh clone runs the fast tests and nothing else. Adding a version means copying
a directory and editing its `lean-toolchain`; regenerate its committed
`dep-graph.json` with `lean4-lens dep-graph` from inside it.

To point the same tests at a real project instead of the fixtures:

```sh
LEANLENS_TEST_PROJECT=/path/to/lean/project uv run pytest
```
