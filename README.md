# lean4-lens

Analysis tools for a Lean 4 project. Point them at a project and they report on
it: what a reviewer must read, what depends on what, where the expensive tactics
are, and what each module costs to build.

They are read-only and stdlib-only, and they find the project themselves (the
nearest lakefile, walking up).

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
review-cone` builds the libraries, runs a Lean elaborator script over them, and
writes a standalone cross-linked HTML document: every project reference an
internal link, every mathlib reference a link to the mathlib4 docs.

### dep-graph

Runs the same Lean emitter but writes `dep-graph.json`: every project
declaration with the declarations its proof refers to. That file is what
`dep-tree` reads.

### dep-tree

Answers dependency questions over `dep-graph.json`: reachability, reverse
dependencies, `sorry`/axiom taint, orphans, dead code. `coverage` reports
whether the committed graph still describes the code.

References come from the elaborator only. A declaration the data misses gets no
edges and is reported, never guessed at.

`summary --fail-on-sorry` / `--fail-on-axioms` turn the report into a CI gate
(exit 1 on findings), and every scan-based command exits 2 when it finds no
project files at all — a gate that scanned nothing must not pass as clean.

## Project configuration

Both files are optional and live at the Lean project root.

`review-cone.toml` names the roots and the section layout of the review
document, plus the document's own `title` and `out` path (relative to the
project root; `--title`/`--out` override). Each `[[section]]` has a `title`
and a `decls` list; every named decl is a root, and the cone is the transitive
closure of them all.

```toml
title = "My Formalization"
out = "docs/review-cone.html"

[[section]]
title = "Main results"
decls = ["main_theorem", "algorithm_correct"]
```

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

The emitter tests need a built Lean project and skip without one:

```sh
LEANLENS_TEST_PROJECT=/path/to/lean/project uv run pytest
```
