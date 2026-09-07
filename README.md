# lean4-lens

Analysis tools for a Lean 4 project, built around the **review cone**. Why that
is the thing worth building:

- ✅ Lean's type checker guarantees the *proofs* are correct
- ❓ It says nothing about whether the *statements* mean what they claim
- 👤 Only a human can close that gap — so the reading should be as small as possible
- 🎯 The review cone is exactly that: the transitive set of statements and definitions whose meaning can affect the headline results (following [lean-atlas](https://github.com/NyxFoundation/lean-atlas))

**What `lean4-lens review-cone` does:**

- 🔍 Computes the cone from the elaborator, so nothing is guessed from the text
- 📄 Renders it as one standalone, cross-linked HTML document a reviewer can read top to bottom
- 🏅 Badges every declaration verified / tainted / sorry, and says which extra axioms it leans on
- ⚙️ Takes its roots, sections and titles from one `review-cone.toml`

**The other commands, off the same elaborator data:**

- 🕸️ `refs` — what depends on what, what is unreachable, what a `sorry` blocks
- 🐢 `heavy-tactics` — where the expensive tactics are used
- ⏱️ `build-times` — what each module costs to build

They are stdlib-only, and they find the project themselves (the nearest
lakefile, walking up from the CWD; failing that, a single lakefile below it) —
`--project DIR` on any command names one instead.

## Install

```sh
uv tool install git+https://github.com/holgerdell/lean4-lens
```

Or run it without installing:

```sh
uvx --from git+https://github.com/holgerdell/lean4-lens lean4-lens --help
```

From a local checkout: `uv tool install /path/to/lean4-lens`, or
`uv run --project /path/to/lean4-lens lean4-lens`.

## review-cone

```sh
lean4-lens review-cone
```

That builds the project's libraries, runs a Lean elaborator script over them to
collect the cone from the roots named in `review-cone.toml`, and writes the
document. Each declaration appears with its own source, ordered so nothing is
read before what it depends on:

- every reference to another project declaration is an internal link, every
  mathlib or core reference a link to the mathlib4 docs;
- each entry carries a status badge — verified (sorry-free, standard axioms
  only), tainted (extra axioms, which are listed), or sorry — plus its file and
  line span and a "used by" line back to its consumers in the cone;
- a panel at the top summarises the whole cone's verification status and
  records the Lean and Mathlib versions it was checked against;
- headline results are grouped into the sections the config names; everything
  else the cone dragged in lands in a supporting catch-all, in topological
  order.

The elaborator run needs `lake` on PATH. Options: `--no-build` skips the
`lake build` warm-up, `--json FILE` re-renders JSON emitted earlier and skips
the Lean run entirely, `--config`, `--out` and `--title` override the config,
`--toc-support` lists the supporting declarations in the contents even when
the config hides them,
and `--lean-root` points the source snippets at a different tree.

### Configuring the document

`review-cone.toml` at the Lean project root is the whole control surface, and
`review-cone` requires it (`--config` names another file). It lists the roots
in the order they should be read, and the sections they are grouped into:

```toml
title = "My Formalization"
out = "docs/review-cone.html"

[[section]]
title = "Main results"
decls = ["main_theorem", "algorithm_correct"]

[section.titles]
"main_theorem" = "Correctness of the algorithm"

[section.labels]
"main_theorem" = "Theorem 1"

[section.summaries]
"main_theorem" = "For every input the algorithm returns a valid answer."

[support]
title = "Supporting declarations"
toc = false

[info]
heading = "Full source code"
text = "Complete Lean sources, including all proofs, are hosted at"
url = "https://example.org/my-formalization"
```

Every named decl is a root, and the cone is the transitive closure of them all.
A decl may be named in only one section. `title` and `out` (relative to the
project root) name the document itself; `--title`/`--out` override them, and
without them the document is written next to the project as
`<config-stem>.html`.

Per section: `titles` gives a decl a display title (shown as the heading, with
the kind and Lean name on a secondary line), `labels` replaces the kind and
Lean name with something like "Theorem 1", `summaries` puts a prose paragraph
above the decl's source, and `toc = false` keeps the section out of the
contents sidebar. A dotted Lean name must be
quoted, or TOML reads it as a nested table.

Cone members no section claims land in the `[support]` catch-all: rendered
last in topological order, and listed in the contents sidebar unless
`support.toc = false` (`--toc-support` overrides that).

The optional `[info]` table adds a panel under the verification panel pointing
a reader at the full sources. `url` is required; `heading` and `text` have the
defaults shown. Leave the table out and no panel is rendered.

A project may keep several review documents: every `review-cone*.toml` is a
config in its own right (`--config` selects one), each emitting JSON and HTML
named after itself. `refs`' default roots are the union of them all.

## The other commands

```
lean4-lens review-cone     render the review cone as a standalone HTML document
lean4-lens emit-refs       emit dep-graph.json, the data `refs` reads
lean4-lens refs            query the proof references: check gates, shows, exports
lean4-lens heavy-tactics   where the expensive tactics are used
lean4-lens build-times     per-module build time for a library
```

`dep-graph` and `dep-tree` stay as aliases of `emit-refs` and `refs` for one
release. Each command's `--help` is the authoritative list of its options; the
sections below give the shape.

These commands never modify your Lean sources, but they are not read-only:
`review-cone` and `emit-refs` write their JSON next to the project (running
`lake build` first, unless `--no-build`), `build-times` writes
`module_build_times.jsonl` and drives `lake`, and `refs show dead` writes
`dead_candidates.jsonl` into the current directory. Every output path is
overridable.

### emit-refs

Runs the same Lean emitter as `review-cone`, but over every project
declaration and writing `dep-graph.json`: each declaration with the
declarations its proof refers to. That file is what `refs` reads.

Chain: first `lake build`, then `lean4-lens emit-refs --no-build`, then
`lean4-lens refs check data-complete`.

### refs

Answers proof-reference questions. It takes the declarations from the project's
own sources and every edge from `dep-graph.json`:

```
check data-complete   does the committed graph still describe the code?
check taint-status    counts + listings, and the CI gates
show direct-deps      immediate refs of one decl
show deps             transitive deps of one decl
show used-by          transitive reverse-deps of one decl
show reach            split every decl into used / unused, from a set of roots
show dead             dead-code candidates: unreachable *and* referenced by nothing live
show sorry-impact     direct-sorry decls ranked by how much they block
export                the whole graph as JSON, DOT, or text
```

`show dead --global` lists globally unreferenced decls (the old `orphans`
question). `export --format json|dot|text` merges the old `json` / `dot` /
`dag` outputs; `--from NAME` limits any format to one decl's cone. The old
flat names (`summary`, `coverage`, `from`, `direct`, `rdeps`, `dag`, `dot`,
`json`, `reach`, `dead`, `sorry-paths`, `orphans`) stay as hidden aliases for
one release.

`show reach` and `show dead` take root declarations as arguments, or
`--root-file PATH` for every decl in a file; with neither they fall back to the
roots named in the project's `review-cone*.toml`. Both can write their split as
JSONL (`--out-used` / `--out-unused`). `show dead` writes
`dead_candidates.jsonl` by default (`--out` redirects it, `--no-out` skips it)
and takes `--closure` for the whole removable set in one pass, rather than only
the globally-orphaned decls, plus `--global` to ignore roots entirely.

References come from the elaborator only. A declaration the data misses gets no
edges and is reported, never guessed at.

`check taint-status --fail-on-sorry` / `--fail-on-axioms` turn the report into
a CI gate (exit 1 on findings), and every scan-based command exits 2 when it
finds no project files at all — a gate that scanned nothing must not pass as
clean.

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

### Which files count as project code

The optional `lean4-lens.toml`, also at the Lean project root, says which files
the scanning commands (`refs`, `heavy-tactics`) treat as project code. Build
trees and dot-directories are always skipped, so most projects need nothing
here.

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
`dep-graph.json` with `lean4-lens emit-refs` from inside it.

To point the same tests at a real project instead of the fixtures:

```sh
LEANLENS_TEST_PROJECT=/path/to/lean/project uv run pytest
```
