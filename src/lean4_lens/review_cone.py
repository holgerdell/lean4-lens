"""Generate a project's *review cone* as a standalone, cross-linked HTML document.

The review cone is the transitive set of statements a human must read to trust
that the formalization says what it claims. This tool is end-to-end and
project-independent:

  1. finds the Lean project root (nearest lakefile, walking up from --project/CWD);
  2. reads `review-cone.toml` (the project's config; see below) for the roots and
     the section layout;
  3. builds the libraries and runs the Lean emitter — seeded with the config's
     roots — to emit the cone JSON;
  4. renders that JSON to HTML: each project declaration with its source snippet,
     every project reference an internal link, every mathlib/core reference a link
     to the mathlib4 docs.

The config (`review-cone.toml`, auto-detected in the project root; --config
overrides) is the sole control surface. It lists an ordered set of `[[section]]`
blocks, each with a `title` and a `decls` list of Lean names. EVERY named decl is
a *root*: the cone is the transitive closure of them all, and named decls render
in their section in the order written. Every other cone member falls into the
implicit `[support]` catch-all (rendered last, topologically sorted, listed in
the sidebar contents unless `support.toc = false`; --toc-support forces it on).
Optional display titles and prose summaries live in section-local
`[section.titles]` / `[section.summaries]` tables; the document's
own `title` and `out` path (relative to the project root) are top-level keys,
overridable with --title/--out. There is no in-source attribute and no
paper/LaTeX coupling.

Usage:
    lean4-lens review-cone                          # full pipeline in the current project
    lean4-lens review-cone --project path/to/proj   # a specific project
    lean4-lens review-cone --config path/to.toml    # a specific config
    lean4-lens review-cone --json cone.json         # render an existing JSON, skip the Lean run
    lean4-lens review-cone --no-build --toc-support --out out.html --title "My Formalization"

`lean4-lens emit-refs` shares this file's Lean emitter to write `dep-graph.json`
for `lean4-lens refs` — data, not a document.
"""

from __future__ import annotations

import argparse
import graphlib
import heapq
import html
import json
import os
import re
import shutil
import subprocess
import sys
import urllib.parse
from collections import Counter, defaultdict
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from . import cli
from .cone_config import DEFAULT_CONFIG_NAME, ReviewConeConfig, load_config
from .project import (
    DEP_GRAPH_NAME,
    RootNotFoundError,
    module_path,
    read_lib_names,
    read_package_name,
    resolve_root,
    resolve_root_or_exit,
)
from .source import blank_comments_and_strings, iter_spans

# The elaborator half of this tool, shipped as package data and handed to
# `lake env lean --run`.
REVIEW_CONE_LEAN = Path(__file__).resolve().parent / "data" / "review_cone.lean"


@dataclass
class ConeDecl:
    """One project declaration in the cone, as review_cone.lean emitted it,
    plus the source snippet the renderer reads for it."""

    name: str
    module: str
    kind: str
    start_line: int
    end_line: int
    status: str
    axioms: list[str]
    refs: list[str]
    is_root: bool
    # None marks JSON written before the emitter reported `autoName`; the
    # renderer then falls back to Lean's `inst` naming convention.
    auto_name: bool | None
    snippet: str = ""
    truncated: bool = False

    @classmethod
    def from_json(cls, d: dict[str, Any]) -> ConeDecl:
        return cls(
            name=d["name"],
            module=d.get("module", ""),
            kind=d.get("kind", ""),
            start_line=d.get("startLine", 0),
            end_line=d.get("endLine", 0),
            status=d.get("status", ""),
            axioms=d.get("axioms", []),
            refs=d.get("refs", []),
            is_root=d.get("isRoot", False),
            auto_name=d.get("autoName"),
        )


@dataclass(frozen=True)
class MathlibDecl:
    """One mathlib/core reference in the cone: a name and its docs URL."""

    name: str
    url: str


# --------------------------------------------------------------------------- #
# The driver                                                                  #
# --------------------------------------------------------------------------- #
def elide_middle(s: str, head: int = 3000, tail: int = 1200) -> str:
    """Shorten `s` from the middle. A crash names its cause at the top of the
    backtrace and only reaches the thread entry point at the bottom, so clipping
    to the tail alone keeps the least useful end."""
    if len(s) <= head + tail:
        return s
    return f"{s[:head]}\n… [{len(s) - head - tail} chars elided] …\n{s[-tail:]}"


def run_review_cone(
    root: Path, libs: list[str], roots: list[str], out_json: Path, build: bool, *, deps: bool = False
) -> None:
    """Build the libraries, then run review_cone.lean to emit JSON. `deps`
    selects the dependency graph's data rather than the review document's, and
    ignores `roots` (see `REVIEW_CONE_DEPS` in review_cone.lean)."""
    if build:
        print("  " + cli.dim(f"lake build {' '.join(libs)} …"))
        warm = subprocess.run(["lake", "build", *libs], cwd=root, capture_output=True, text=True)
        if warm.returncode != 0:
            # Build failed, but lake still writes .olean files for every module
            # that itself compiled cleanly — only the broken modules (and
            # anything that transitively imports them) are missing theirs.
            # review_cone.lean's libModules/pruneAndImport already skip modules
            # with no compiled .olean, so a partial cone is still worth emitting:
            # warn and continue rather than aborting the whole pipeline.
            body = (warm.stdout + warm.stderr).strip()
            if body:
                print(body)
            print(
                cli.red("⚠ lake build failed") + " — continuing with a partial cone (modules that failed to"
                " build, or depend on one that did, are skipped below)."
            )
        else:
            # Success: drop warning noise (stale-manifest notice, per-decl
            # `sorry` warnings, the `⚠` replay markers they trigger) and print
            # only the remaining signal (progress/completion lines).
            for line in warm.stdout.splitlines():
                stripped = line.strip()
                if stripped.startswith("warning:"):
                    continue
                if stripped.startswith("⚠"):
                    continue
                if stripped:
                    print(line)
    env = {
        **os.environ,
        "REVIEW_CONE_OUT": str(out_json),
        "REVIEW_CONE_LIBS": ",".join(libs),
        "REVIEW_CONE_ROOTS": ",".join(roots),
    }
    if deps:
        env["REVIEW_CONE_DEPS"] = "1"
    cli.status("running review_cone.lean …")
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(REVIEW_CONE_LEAN)],
        cwd=root,
        capture_output=True,
        text=True,
        env=env,
    )
    cli.clear_transient()
    if proc.returncode != 0:
        # Show both streams (labeled) — `stderr or stdout` used to silently
        # drop stdout whenever stderr held anything, even just a warning.
        parts = []
        if proc.stdout.strip():
            parts.append("stdout:\n" + proc.stdout.strip())
        if proc.stderr.strip():
            parts.append("stderr:\n" + proc.stderr.strip())
        body = elide_middle("\n\n".join(parts) or "(no output on stdout or stderr)")
        raise SystemExit(cli.red("✗ review_cone.lean failed") + f" (exit {proc.returncode})\n" + body)


# --------------------------------------------------------------------------- #
# HTML rendering                                                              #
# --------------------------------------------------------------------------- #
def toolchain_info(lean_root: Path) -> str:
    """Lean/Mathlib versions the statements were checked with (provenance)."""
    bits = []
    tc = lean_root / "lean-toolchain"
    if tc.exists():
        m = re.search(r"lean4:(\S+)", tc.read_text(encoding="utf-8"))
        if m:
            bits.append(f"Lean {m.group(1)}")
    mf = lean_root / "lake-manifest.json"
    if mf.exists():
        try:
            for pkg in json.loads(mf.read_text(encoding="utf-8")).get("packages", []):
                if pkg.get("name") == "mathlib":
                    rev = pkg.get("inputRev") or pkg.get("rev") or ""
                    if rev:
                        bits.append(f"Mathlib {rev[:12]}")
                    break
        except (OSError, json.JSONDecodeError):
            pass
    return ", ".join(bits)


def git_revision(lean_root: Path) -> str:
    """Short revision of the checkout the snippets were read from, suffixed
    `-dirty` when the tree has uncommitted changes; "" outside a checkout."""

    def git(*args: str) -> str | None:
        try:
            r = subprocess.run(["git", "-C", str(lean_root), *args], capture_output=True, text=True, timeout=5)
        except (OSError, subprocess.TimeoutExpired):
            return None
        return r.stdout if r.returncode == 0 else None

    rev = git("rev-parse", "--short", "HEAD")
    if not rev:
        return ""
    status = git("status", "--porcelain")
    return rev.strip() + ("-dirty" if status else "")


_SMALL_NUMS = [
    "zero",
    "one",
    "two",
    "three",
    "four",
    "five",
    "six",
    "seven",
    "eight",
    "nine",
    "ten",
    "eleven",
    "twelve",
]


def spell(n: int) -> str:
    """Spell out small counts (0-12) in running prose; keep larger ones numeric."""
    return _SMALL_NUMS[n] if 0 <= n < len(_SMALL_NUMS) else str(n)


def anchor_id(name: str) -> str:
    # Encode every non-ASCII-alphanumeric char by codepoint so distinct names
    # (e.g. ...μ vs ...ℱ) never collide onto the same anchor.
    return "d-" + "".join(ch if (ch.isascii() and ch.isalnum()) else f"_{ord(ch)}" for ch in name)


# `native_decide` mints one throwaway axiom per use, named after the
# declaration that used it, so the raw list is unreadable at any scale.
NATIVE_DECIDE_AX_RE = re.compile(r"\._native\.native_decide\.ax(_\d+)*$")


def summarize_axioms(axioms: list[str]) -> list[str]:
    """The axiom names to show, with the per-use `native_decide` axioms folded
    into one `native_decide (×n)` entry that keeps their first position."""
    out: list[str] = []
    native = 0
    for a in axioms:
        if NATIVE_DECIDE_AX_RE.search(a):
            if not native:
                out.append("")  # placeholder, filled in once the count is known
            native += 1
        else:
            out.append(a)
    if native:
        label = "native_decide" if native == 1 else f"native_decide (×{native})"
        out[out.index("")] = label
    return out


def status_badge(d: ConeDecl) -> str:
    st = d.status
    if st == "verified":
        return (
            "<span class='badge verified' title='kernel-checked: sorry-free, standard axioms only'>"
            "✓ Kernel-checked</span>"
        )
    if st == "tainted":
        ax = ", ".join(summarize_axioms(d.axioms))
        return (
            f"<span class='badge tainted' title='sorry-free but depends on extra axioms'>"
            f"⚠ Tainted</span><span class='axioms'>{html.escape(ax)}</span>"
        )
    if st == "sorry":
        return "<span class='badge sorry' title='depends on sorryAx'>✗ Sorry</span>"
    return ""


def render_decl(d: ConeDecl, body_html: str, title: str = "", label: str = "", summary: str = "") -> str:
    """One declaration's entry — every decl renders through this, in whatever
    section it lands. With a display title from `[section.titles]` the heading
    is that title and `<kind> <name> [badge]` follows on a secondary line;
    without one the heading is `<kind> <name> [badge]` itself. A label from
    `[section.labels]` ("Theorem 1") replaces the kind and the name, which the
    source body below already shows. A summary from `[section.summaries]` is a
    prose paragraph placed before the source body."""
    name = d.name
    if label:
        head_html = f"<strong class='label'>{html.escape(label)}</strong>"
    else:
        head_html = f"<span class='head'>{html.escape(d.kind)}</span> <strong class='self'>{html.escape(name)}</strong>"
    head_line = f"{head_html} {status_badge(d)}"
    if title:
        heading = f"<h3 id='{anchor_id(name)}'>{html.escape(title)}</h3><div class='subhead'>{head_line}</div>"
    else:
        heading = f"<h3 id='{anchor_id(name)}'>{head_line}</h3>"
    summary_html = f"<p class='summary'>{html.escape(summary)}</p>" if summary else ""
    return f"<div class='entry'>{heading}{summary_html}{body_html}</div>"


_OPENERS = "([{⟨⦃"
_CLOSERS = ")]}⟩⦄"


def _statement_value_split(block: list[str]) -> tuple[int, int] | None:
    """Locate the proof-introducing `:=` in a theorem's source lines.

    Returns `(line_index, column)` of the first `:=` at bracket depth 0 that is
    not inside a comment or string literal — the boundary between statement and
    proof — or `None` if there is none. Comments (so the leading docstring is
    ignored) and strings are blanked first; a `:=` nested inside `()[]{}⟨⟩⦃⦄`
    belongs to the statement.
    """
    depth = 0
    for idx, ln in enumerate(blank_comments_and_strings("\n".join(block)).split("\n")):
        for i, c in enumerate(ln):
            if c in _OPENERS:
                depth += 1
            elif c in _CLOSERS:
                depth -= 1
            elif c == ":" and depth == 0 and ln[i : i + 2] == ":=":
                return idx, i
    return None


def read_snippet(
    lean_root: Path,
    d: ConeDecl,
    max_lines: int = 60,
    cache: dict[str, list[str]] | None = None,
) -> tuple[str, bool]:
    module, name = d.module, d.name
    start, end = d.start_line, d.end_line
    if start <= 0:
        return "", False
    lines = cache.get(module) if cache is not None else None
    if lines is None:
        path = lean_root / module_path(module)
        if not path.exists():
            return "", False
        lines = path.read_text(encoding="utf-8").splitlines()
        if cache is not None:
            cache[module] = lines
    # Include `open … in` / `omit … in` / `set_option … in` prefix lines, which
    # the recorded declaration range excludes but the statement needs to parse.
    first = start - 1
    while first > 0:
        prev = lines[first - 1].strip()
        if prev.endswith(" in") and prev.startswith(("open ", "omit ", "set_option ")):
            first -= 1
        else:
            break
    block = lines[first:end]
    # Guard against a stale review-cone.json: the sliced range must actually
    # contain the declaration it claims to show. Exempt machine-chosen names
    # (the emitter's `autoName`, e.g. an anonymous instance): the range is
    # genuinely their declaration site, they are just never spelled out under
    # the name Lean chose for them, so the text can never match.
    last = name.split(".")[-1] if name else ""
    auto_name = d.auto_name
    if auto_name is None:
        # pre-autoName JSON: guess by Lean's `mkInstanceName` prefix convention
        auto_name = last.startswith("inst")
    if name and last not in "\n".join(block) and not auto_name:
        print(f"warning: stale line range for {name} in {module}; snippet omitted (re-run review_cone)")
        return "", False
    truncated = False
    # For theorems, the statement ends at the proof-introducing `:=` — drop the
    # proof body, whether a tactic block (`:= by ...`) or a term (`:= fun …`).
    # That `:=` is the one at bracket depth 0: a `:=` inside binders (autoparams
    # `(h : P := by …)`), a set-builder `{u | let x := …}`, or a comment/string
    # belongs to the statement, not the proof, and must not truncate it.
    if d.kind == "theorem":
        cut = _statement_value_split(block)
        if cut is not None:
            c_idx, c_col = cut
            block = block[: c_idx + 1]
            block[-1] = block[-1][:c_col].rstrip()
            if not block[-1].strip():
                block = block[:-1]
    if len(block) > max_lines:
        block = block[:max_lines]
        truncated = True
    snippet = "\n".join(block)
    # Strip `\label{...}` cross-referencing plumbing from the docstring; if that
    # leaves the docstring empty, drop it entirely rather than collapsing it.
    snippet = re.sub(r"[ \t]*\\label\{[^}]*\}[ \t]*\n?", "", snippet)
    snippet = re.sub(r"^[ \t]*/--\s*-/[ \t]*\n?", "", snippet, flags=re.M)
    snippet = re.sub(r"^([ \t]*)/--[ \t]*\n\s*", r"\1/-- ", snippet, flags=re.M)
    return snippet, truncated


# Lean identifier-ish chunk: anything that is not whitespace or a structural
# delimiter (including floor and ceiling brackets). `^` is included so `f^[n]` (iterate notation) doesn't glue its
# caret onto the preceding identifier and break the link lookup.
_DELIM_RE = re.compile(r"([\s(){}\[\],;⟨⟩«»⌊⌋⌈⌉^])")


@dataclass(frozen=True)
class Indexes:
    """The document-wide name-resolution tables the linkifier consults."""

    # A None value marks a structure-field projection: it resolves, but its
    # link target is the parent structure (see `proj_target`), and it has no
    # cone entry of its own.
    proj_full: dict[str, ConeDecl | None]
    mlib_full: dict[str, MathlibDecl]
    proj_final: dict[str, str]  # globally-unique final component -> full name
    mlib_final: dict[str, str]
    proj_target: dict[str, str]  # full name -> anchor target (fields -> struct)
    field_by_final: dict[str, list[str]]  # field's final component -> its full names
    prop_fields: set[str]  # full names of the fields that hold a proof, not data


@dataclass(frozen=True)
class LinkCtx:
    """`Indexes` plus the decl being rendered: its own name (bold, not linked)
    and its refs' final-component tables, which disambiguate shared names."""

    idx: Indexes
    define_name: str
    define_final: str
    local_final: dict[str, str]
    local_qual_final: dict[str, str]
    binders: frozenset[str] = frozenset()


# Names bound by a binder group: `(Vertex : Type*)`, `{V : Type*}`, `[inst : C]`,
# `⦃x y : α⦄` in a declaration's header, and `∀ x : α` / `∃ n : ℕ` anywhere.
_NAMES = r"((?:[A-Za-z_][A-Za-z0-9_'!?]*\s+)*[A-Za-z_][A-Za-z0-9_'!?]*)"
_GROUP_BINDER_RE = re.compile(r"[({\[⦃]\s*" + _NAMES + r"\s*:(?!=)")
_QUANT_BINDER_RE = re.compile(r"[∀∃]\s*" + _NAMES + r"\s*:(?!=)")
_HEADER_END_RE = re.compile(r":=|\bwhere\b|\|")


def _header(code: str) -> str:
    """The binder list of a declaration: the code up to the bracket-depth-0
    colon that introduces its type, or to `:=` / `where` / `|` if that comes
    first. A `(x : T)` past that point is a type ascription, not a binder."""
    depth = 0
    for i, ch in enumerate(code):
        if ch in _OPENERS:
            depth += 1
        elif ch in _CLOSERS:
            depth -= 1
        elif depth == 0 and ch == ":" and not code.startswith(":=", i):
            return code[:i]
    m = _HEADER_END_RE.search(code)
    return code[: m.start()] if m else code


def local_binders(src: str) -> frozenset[str]:
    """Names bound locally in `src`. A bare use of one must not resolve to an
    unrelated project decl that shares its final component."""
    code = "".join(text for text, is_code in split_code_comments(src) if is_code)
    names: set[str] = set()
    for m in _GROUP_BINDER_RE.finditer(_header(code)):
        names.update(m.group(1).split())
    for m in _QUANT_BINDER_RE.finditer(code):
        names.update(m.group(1).split())
    return frozenset(names)


def build_indexes(
    project: list[ConeDecl],
    mathlib: list[MathlibDecl],
    field_of: dict[str, str],
    prop_fields: set[str] | None = None,
) -> Indexes:
    proj_full: dict[str, ConeDecl | None] = {d.name: d for d in project}
    # structure-field projections resolve too, but their link target is the
    # parent structure (they are not emitted as their own entries).
    proj_target: dict[str, str] = {d.name: d.name for d in project}
    for fld, struct in field_of.items():
        proj_full.setdefault(fld, None)
        proj_target[fld] = struct
    mlib_full: dict[str, MathlibDecl] = {d.name: d for d in mathlib}
    field_by_final: dict[str, list[str]] = defaultdict(list)
    for fld in field_of:
        field_by_final[fld.split(".")[-1]].append(fld)

    def unique_final(names: list[str]) -> dict[str, str]:
        cnt = Counter(n.split(".")[-1] for n in names)
        return {f: n for n in names if cnt[f := n.split(".")[-1]] == 1}

    return Indexes(
        proj_full=proj_full,
        mlib_full=mlib_full,
        proj_final=unique_final(list(proj_full)),
        mlib_final=unique_final(list(mlib_full)),
        proj_target=proj_target,
        field_by_final=field_by_final,
        prop_fields=prop_fields or set(),
    )


def linkify_chunk(chunk: str, ctx: LinkCtx) -> str:
    """Wrap a single source chunk in a hyperlink if it names a known decl.
    `ctx` carries the indexes and the name being *defined* (bold, not linked)."""
    proj_full, mlib_full = ctx.idx.proj_full, ctx.idx.mlib_full
    proj_final, mlib_final, proj_target = ctx.idx.proj_final, ctx.idx.mlib_final, ctx.idx.proj_target
    define_name, define_final = ctx.define_name, ctx.define_final
    local_final, local_qual_final = ctx.local_final, ctx.local_qual_final

    def proj_link(full: str, text: str) -> str:
        if full == define_name or text == define_name:
            return f'<strong class="self">{html.escape(text)}</strong>'
        target = proj_target.get(full, full)
        if target == define_name:
            return html.escape(text)  # a field of the decl being rendered: linking would point here
        if target != full:  # a structure field: the link lands on the parent structure
            return (
                f'<a class="proj field" href="#{anchor_id(target)}" title="field of {html.escape(target)}">'
                f"{html.escape(text)}</a>"
            )
        return f'<a class="proj" href="#{anchor_id(target)}">{html.escape(text)}</a>'

    def mlib_link(full: str, text: str) -> str:
        url = mlib_full[full].url
        return f'<a class="mlib" href="{html.escape(url)}" target="_blank" rel="noopener">{html.escape(text)}</a>'

    def resolve_final(seg: str, dotted: bool = False) -> tuple[str, str] | None:
        """Resolve a final component to (kind, full_name). Prefer this decl's own
        resolved refs (disambiguates names shared across modules), then fall back
        to globally-unique final components. For a dot-notation access (`x.seg`),
        prefer a qualified ref ending in `.seg`."""
        full = None
        if dotted:
            full = local_qual_final.get(seg)
        if full is None:
            full = local_final.get(seg)
        if full is None:
            if seg in proj_final:
                full = proj_final[seg]
            elif seg in mlib_final:
                full = mlib_final[seg]
        if full is None:
            return None
        return ("proj" if full in proj_full else "mlib"), full

    # 0. the declaration's own name (bare or qualified) -> bold self.
    if chunk == define_name or chunk == define_final:
        return f'<strong class="self">{html.escape(chunk)}</strong>'

    # 1. exact full-name match; `TemporalGraph.{0}` tokenizes as `TemporalGraph.`
    #    followed by the universe braces, so a trailing dot is linked too.
    if chunk in proj_full:
        return proj_link(chunk, chunk)
    if chunk in mlib_full:
        return mlib_link(chunk, chunk)
    if chunk.endswith(".") and chunk[:-1] in proj_full:
        return proj_link(chunk[:-1], chunk[:-1]) + "."

    # 2. dotted chunk (dot-notation chain): the head segment is a term/namespace
    #    qualifier — never linked here. Only the projection/method segments after
    #    the head are link candidates.
    if "." in chunk:
        segs = chunk.split(".")
        rendered = [html.escape(segs[0])]
        for seg in segs[1:]:
            r = resolve_final(seg, dotted=True) if seg else None
            if r:
                kind, full = r
                rendered.append(proj_link(full, seg) if kind == "proj" else mlib_link(full, seg))
            else:
                rendered.append(html.escape(seg))
        return ".".join(rendered)

    # 3. bare token matched by final component — unless it is a local binder
    if chunk in ctx.binders:
        return html.escape(chunk)
    r = resolve_final(chunk)
    if r:
        kind, full = r
        return proj_link(full, chunk) if kind == "proj" else mlib_link(full, chunk)
    return html.escape(chunk)


def split_code_comments(src: str) -> list[tuple[str, bool]]:
    """Split Lean source into (text, is_code) spans. Block comments `/- … -/`
    (incl. docstrings `/-- … -/`, nested) and line comments `--` are is_code=False;
    string literals stay in the code spans (their words may still be linkified)."""
    spans: list[tuple[str, bool]] = []
    for lo, hi, kind in iter_spans(src):
        is_code = kind != "comment"
        if spans and spans[-1][1] == is_code:
            spans[-1] = (spans[-1][0] + src[lo:hi], is_code)
        else:
            spans.append((src[lo:hi], is_code))
    return spans


# The left-hand side of a `where` field assignment: a field name, then its
# binders, then `:=`. Matched per line, so it cannot span a term.
_FIELD_LHS_RE = re.compile(r"^(\s*)([A-Za-z_][A-Za-z0-9_'!?]*)((?:\s+(?:_|[A-Za-z_][A-Za-z0-9_'!?]*))*\s*:=)")


def linkify_code(text: str, ctx: LinkCtx) -> str:
    out = []
    for part in _DELIM_RE.split(text):
        if part == "" or _DELIM_RE.fullmatch(part):
            out.append(html.escape(part))
        else:
            out.append(linkify_chunk(part, ctx))
    return "".join(out)


def struct_of_where_block(src: str, idx: Indexes) -> str | None:
    """The structure a `where` block builds, guessed from the field names it
    assigns: each unambiguous one votes for its structure, and the winner names
    the block. `None` when nothing votes."""
    votes: Counter[str] = Counter()
    for line in src.splitlines():
        m = _FIELD_LHS_RE.match(line)
        if m is None:
            continue
        fulls = idx.field_by_final.get(m.group(2), [])
        if len(fulls) == 1:
            votes[idx.proj_target.get(fulls[0], fulls[0])] += 1
    return votes.most_common(1)[0][0] if votes else None


def linkify_code_line(line: str, ctx: LinkCtx, struct: str | None) -> tuple[str, bool]:
    """One line of code, and whether it assigns a proof field. A field assignment
    names a field of `struct`, the structure being built, so its left-hand side
    links there — never to an unrelated decl that happens to share the name. With
    no `struct`, only a name that is a field of exactly one structure is linked."""
    m = _FIELD_LHS_RE.match(line)
    if m is None:
        return linkify_code(line, ctx), False
    name = m.group(2)
    fulls = ctx.idx.field_by_final.get(name, [])
    if struct is not None:
        target = struct
    elif len(fulls) == 1:
        target = ctx.idx.proj_target.get(fulls[0], fulls[0])
    else:
        return linkify_code(line, ctx), False
    if target == ctx.define_name:
        return linkify_code(line, ctx), False
    link = f'<a class="proj" href="#{anchor_id(target)}">{html.escape(name)}</a>'
    rendered = html.escape(m.group(1)) + link + html.escape(m.group(3)) + linkify_code(line[m.end() :], ctx)
    return rendered, f"{target}.{name}" in ctx.idx.prop_fields


def linkify_code_block(text: str, ctx: LinkCtx, struct: str | None) -> str:
    """A run of code lines. A proof field's assignment is greyed, and so are the
    lines its proof continues onto — the ones indented deeper than it."""
    out = []
    proof_indent: int | None = None
    for line in text.splitlines(keepends=True):
        indent = len(line) - len(line.rstrip("\n").lstrip())
        rendered, is_proof = linkify_code_line(line, ctx, struct)
        if is_proof:
            proof_indent = indent
        elif proof_indent is not None and (line.strip() == "" or indent <= proof_indent):
            proof_indent = None
        out.append(f'<span class="proof">{rendered}</span>' if is_proof or proof_indent is not None else rendered)
    return "".join(out)


def linkify(src: str, ctx: LinkCtx) -> str:
    struct = struct_of_where_block(src, ctx.idx)
    out = []
    for text, is_code in split_code_comments(src):
        if not is_code:
            out.append(f'<span class="cmt">{html.escape(text)}</span>')
            continue
        out.append(linkify_code_block(text, ctx, struct))
    return "".join(out)


CSS = """
:root {
  --font-sans: -apple-system, system-ui, sans-serif;
  --font-mono: ui-monospace, monospace;
  --font-code: 'JuliaMono','DejaVu Sans Mono', ui-monospace, monospace;
  --fs-xs: .72rem; --fs-sm: .8rem; --fs-base: .9rem; --fs-lg: 1.1rem;
  --fs-xl: 1.5rem; --fs-2xl: 1.6rem;
  --lh: 1.4; --fw-semibold: 600;
  --radius-sm: 4px; --radius: 6px; --radius-lg: 8px;
  --gray-100: #eee; --gray-400: #6b6b6b; --gray-500: #777; --gray-600: #555;
  --gray-700: #444; --gray-900: #1a1a1a;
  --link-proj: #0b6bcb; --link-mlib: #8a5a00; --self: #b21f66; --cmt: #5f6368;
  --pre-bg: #f7f7f9; --pre-border: #e3e3e8; --code-ax-bg: rgba(0,0,0,.05);
  --white: #fff;
  --ok: #1a7a1a; --ok-bg: #e3f5e3; --ok-panel-bg: #eef8ee; --ok-panel-border: #b6e0b6;
  --ok-pill-bg: #cdeccd; --ok-pill-fg: #145214;
  --warn: #9a6700; --warn-bg: #fdf0d5; --warn-icon: #b8860b;
  --warn-panel-bg: #fdf6e3; --warn-panel-border: #ecd9a6;
  --warn-pill-bg: #f3e4bd; --warn-pill-fg: #7a5200;
  --bad: #b21f1f; --bad-bg: #fbe1e1; --bad-icon: #c62828;
  --bad-panel-bg: #fdecec; --bad-panel-border: #f0bcbc;
  --bad-pill-bg: #f6cccc; --bad-pill-fg: #8a1515;
  --info-panel-bg: #eef4fb; --info-panel-border: #c3dbf3;
}
@media (prefers-reduced-motion: no-preference) { html { scroll-behavior: smooth; } }
body { font-family: var(--font-sans); max-width: 1240px; overflow-wrap: anywhere;
       margin: 2rem auto; padding: 0 1rem; color: var(--gray-900); line-height: var(--lh); }
h1 { font-size: var(--fs-2xl); } h2 { margin-top: 2.5rem; border-bottom: 2px solid var(--gray-100); }
main h2:first-child { margin-top: 0; }
.layout { display: grid; grid-template-columns: 280px minmax(0, 1fr); gap: 2rem; align-items: start; }
.side { position: sticky; top: 0; max-height: 100vh; overflow-y: auto; padding: .5rem .5rem .5rem 0;
        font-size: var(--fs-sm); border-right: 1px solid var(--gray-100); }
.side h2 { font-size: var(--fs-base); border: 0; margin-top: 0; }
.side details > summary { display: none; }
.side ul { list-style: none; padding-left: 0; margin: .2rem 0 .6rem; }
.side li { margin: .12rem 0; }
.side li a { display: block; padding: .1rem .4rem; border-radius: var(--radius-sm); color: var(--link-proj);
             text-decoration: none; box-shadow: inset 3px 0 0 transparent; }
.side li a:hover { text-decoration: underline; }
.side li a.current { background: var(--info-panel-bg); color: var(--gray-900);
                     box-shadow: inset 3px 0 0 var(--link-proj); }
.side .kind { font-family: var(--font-mono); font-size: var(--fs-xs); color: var(--gray-500); }
@media (max-width: 860px) {
  .layout { display: block; }
  .side { position: static; max-height: none; border: 0; }
  .side details > summary { display: list-item; cursor: pointer; font-weight: var(--fw-semibold); padding: .4rem 0; }
}
.entry { margin: 2.2rem 0; padding: .5rem 0; }
.entry h3 { margin: .2rem 0; font-size: var(--fs-lg); }
.subhead { font-family: var(--font-mono); font-size: var(--fs-sm); margin: .1rem 0 .4rem; color: var(--gray-700); }
.summary { margin: .3rem 0 .5rem; font-size: var(--fs-base); }
.prov { font-size: var(--fs-sm); color: var(--gray-600); }
.desc { color: var(--gray-600); font-size: var(--fs-base); margin: .2rem 0 .1rem; }
.codeblock { margin: .6rem 0 1rem; }
.codeblock pre { margin: 0; }
.foot { display: flex; flex-wrap: wrap; justify-content: space-between; gap: .2rem 1.5rem;
        font-size: var(--fs-sm); color: var(--gray-600); margin: .3rem 0 0; }
.code-meta { font-family: var(--font-mono); font-size: var(--fs-sm); order: 2; margin-left: auto; }
a.src { color: var(--link-proj); }
pre { background: var(--pre-bg); border: 1px solid var(--pre-border); border-radius: var(--radius);
      padding: .7rem .9rem; overflow-x: auto; font-size: var(--fs-base);
      font-family: var(--font-code); }
pre code { font-family: inherit; }
a.proj { color: var(--link-proj); }
a.mlib { color: var(--link-mlib); }
a.proj, a.mlib, a.src { text-decoration: underline; text-decoration-color: rgba(0,0,0,.25);
                        text-underline-offset: .18em; }
a.proj:hover, a.mlib:hover, a.src:hover { text-decoration-color: currentColor; }
pre a.proj, pre a.mlib { text-decoration: none; }
pre a.proj:hover, pre a.mlib:hover { text-decoration: underline; }
a.field { text-decoration-style: dotted; }
.sample { text-decoration: underline; }
.proj.sample { color: var(--link-proj); }
.mlib.sample { color: var(--link-mlib); }
a:focus-visible, pre:focus-visible { outline: 3px solid #ffbf47; outline-offset: 2px; }
strong.self { color: var(--self); }
strong.label { font-weight: var(--fw-semibold); }
.cmt { color: var(--cmt); font-style: italic; }
.proof, .proof a { color: var(--gray-400); }
.head { color: var(--gray-500); font-size: var(--fs-sm); }
.paperref { font-size: var(--fs-sm); color: var(--gray-500); }
.tocgroup { font-weight: var(--fw-semibold); color: var(--gray-700); margin: .4rem 0 .15rem; }
.paper { margin-top: 1.6rem; }
.paper > h3 { font-size: var(--fs-lg); margin: .3rem 0; }
.badge { display: inline-block; font-size: var(--fs-xs); font-weight: var(--fw-semibold);
         border-radius: var(--radius-sm); padding: 0 .45rem; margin-left: .5rem; vertical-align: middle; }
.badge.verified { background: var(--ok-bg); color: var(--ok); }
.badge.tainted { background: var(--warn-bg); color: var(--warn); }
.badge.sorry { background: var(--bad-bg); color: var(--bad); }
.axioms { font-size: var(--fs-xs); color: var(--warn); font-family: var(--font-mono); margin-left: .35rem; }
.mlist { column-count: 2; font-size: var(--fs-base); } .mlist a { color: var(--link-mlib); }
.trunc { color: var(--gray-400); font-style: italic; }
.usedby { margin: 0; flex: 1 1 60%; }
.usedby-label { font-weight: var(--fw-semibold); margin-right: .3rem; }
.usedby details { display: inline; }
.usedby summary { display: inline; cursor: pointer; list-style: none; }
.usedby summary::-webkit-details-marker { display: none; }
.usedby summary::after { content: ' ▸'; font-size: .8em; }
.usedby details[open] summary::after { content: ' ▾'; }
.usedby details[open] summary { display: block; margin-bottom: .15rem; }
.subtitle { font-size: var(--fs-lg); color: var(--gray-600); margin: -.4rem 0 1.2rem; }
.vpanel { display: flex; gap: .85rem; align-items: flex-start; border-radius: var(--radius-lg);
          border: 1px solid; padding: .8rem 1rem; margin: 1.4rem 0; }
.vpanel.ok { background: var(--ok-panel-bg); border-color: var(--ok-panel-border); }
.vpanel.warn { background: var(--warn-panel-bg); border-color: var(--warn-panel-border); }
.vpanel.sorry { background: var(--bad-panel-bg); border-color: var(--bad-panel-border); }
.vpanel.info { background: var(--info-panel-bg); border-color: var(--info-panel-border); }
.vpanel-icon { font-size: var(--fs-xl); line-height: var(--lh); flex: none; width: 1.9rem;
               height: 1.9rem; display: flex; align-items: center;
               justify-content: center; border-radius: 50%; color: var(--white); }
.vpanel.ok .vpanel-icon { background: var(--ok); }
.vpanel.warn .vpanel-icon { background: var(--warn-icon); }
.vpanel.sorry .vpanel-icon { background: var(--bad-icon); }
.vpanel.info .vpanel-icon { background: var(--link-proj); }
.vpanel-head { font-weight: var(--fw-semibold); font-size: var(--fs-lg); }
.vpanel-pills { margin: .35rem 0 .1rem; }
.vpanel-sub { font-size: var(--fs-base); color: var(--gray-700); margin-top: .2rem; }
.vpanel-foot { font-size: var(--fs-xs); color: var(--gray-500); font-family: var(--font-mono);
               margin-top: .5rem; }
.pill { display: inline-block; font-size: var(--fs-sm); font-weight: var(--fw-semibold);
        border-radius: 20px; padding: .1rem .6rem; margin-right: .4rem; }
.pill.verified { background: var(--ok-pill-bg); color: var(--ok-pill-fg); }
.pill.tainted { background: var(--warn-pill-bg); color: var(--warn-pill-fg); }
.pill.sorry { background: var(--bad-pill-bg); color: var(--bad-pill-fg); }
code.ax { background: var(--code-ax-bg); border-radius: var(--radius-sm); padding: 0 .3rem;
          margin: 0 .12rem; font-size: .8em; }
"""


HUMAN_REVIEW_NOTE = (
    "<div class='vpanel-sub'><strong>Correspondence with the intended mathematics requires human review.</strong>"
    " That review is what this document is for.</div>"
)


def render(
    data: dict[str, Any],
    lean_root: Path,
    title_override: str | None,
    package: str | None,
    config: ReviewConeConfig,
    show_support_toc: bool,
    src_prefix: str = "",
) -> str:
    """`src_prefix` is the path from the output document's directory to
    `lean_root`, so each entry's source location can link to its file."""
    project = [ConeDecl.from_json(d) for d in data["project"]]
    mathlib = sorted((MathlibDecl(d["name"], d.get("url", "")) for d in data["mathlib"]), key=lambda d: d.name.lower())
    field_of = data.get("fieldOf", {})
    idx = build_indexes(project, mathlib, field_of, set(data.get("propFields", [])))
    proj_full, proj_target = idx.proj_full, idx.proj_target

    # Config drives the layout: `title_map` and `label_map` supply display
    # titles and headline labels (the union of all `[section.titles]` and
    # `[section.labels]`).
    title_map: dict[str, str] = {}
    label_map: dict[str, str] = {}
    summary_map: dict[str, str] = {}
    for sec in config["sections"]:
        title_map.update(sec["titles"])
        label_map.update(sec["labels"])
        summary_map.update(sec["summaries"])

    # Read each decl's source once; the cache reads each *module* once.
    module_lines: dict[str, list[str]] = {}
    for d in project:
        d.snippet, d.truncated = read_snippet(lean_root, d, cache=module_lines)

    # Reverse dependency map: for each project decl, who in the cone uses it.
    # A ref to a structure field counts as a use of the parent struct
    # (proj_target normalizes fields -> struct, same as the linkifier).
    used_by: dict[str, set[str]] = {}
    for d in project:
        dname = d.name
        for r in d.refs:
            target = proj_target.get(r)
            if target is None or target == dname:
                continue
            used_by.setdefault(target, set()).add(dname)

    def used_by_html(d: ConeDecl) -> str:
        """A long list of users collapses to a count behind a disclosure."""
        users = used_by.get(d.name)
        if not users:
            return ""
        items = ", ".join(
            f"<a class='proj' href='#{anchor_id(n)}'>{html.escape(n)}</a>" for n in sorted(users, key=str.lower)
        )
        label = "<span class='usedby-label'>Used by</span>"
        if len(users) > 3:
            return (
                f"<div class='usedby'><details><summary>{label} {len(users)} declarations</summary>"
                f"{items}</details></div>"
            )
        return f"<div class='usedby'>{label} {items}</div>"

    # --- Reading order: topological build-up (dependencies first) -------------
    def dep_edges(d: ConeDecl) -> list[str]:
        return [r for r in d.refs if r in proj_full and r != d.name]

    def topo_sort(decls: list[ConeDecl], key: Callable[[ConeDecl], str]) -> list[ConeDecl]:
        """Dependencies-first order within `decls`; `key` breaks ties. A cycle
        (should not occur) degrades to emitting all of `decls` sorted by `key`."""
        pool = {d.name: d for d in decls}
        # Equal keys fall back to the caller's `decls` order (a stable sort
        # would do the same), so the heap carries the position, not the name.
        pos = {d.name: i for i, d in enumerate(decls)}
        sorter: graphlib.TopologicalSorter[str] = graphlib.TopologicalSorter()
        for nm, d in pool.items():
            sorter.add(nm, *(r for r in dep_edges(d) if r in pool))
        try:
            sorter.prepare()
        except graphlib.CycleError:
            return sorted(decls, key=key)
        heap = [(key(pool[nm]), pos[nm], nm) for nm in sorter.get_ready()]
        heapq.heapify(heap)
        out: list[ConeDecl] = []
        while heap:
            _, _, nm = heapq.heappop(heap)
            out.append(pool[nm])
            sorter.done(nm)
            for r in sorter.get_ready():
                heapq.heappush(heap, (key(pool[r]), pos[r], r))
        return out

    # --- Partition the cone into the configured sections ----------------------
    # Each [[section]] takes its named decls in authored order; a name with no
    # cone entry of its own (e.g. it redirects to a parent structure) is warned
    # and skipped. Every unplaced cone member falls into the support catch-all,
    # topologically sorted (dependencies first, so it reads with no forward refs).
    placed: set[str] = set()
    section_entries: list[tuple[str, bool, list[ConeDecl]]] = []
    for sec in config["sections"]:
        entries: list[ConeDecl] = []
        for name in sec["decls"]:
            # `proj_full` holds None for a field redirected to its parent
            # structure — no cone entry of its own, same as a missing name.
            entry = proj_full.get(name)
            if entry is None:
                msg = f"warning: config root {name!r} has no cone entry (redirected to a parent?); skipped in layout"
                print(cli.yellow(msg), file=sys.stderr)
                continue
            if name not in placed:
                placed.add(name)
                entries.append(entry)
        section_entries.append((sec["title"], sec["toc"], entries))
    support = topo_sort([d for d in project if d.name not in placed], key=lambda d: d.name.lower())
    support_title = config["support"]["title"]

    def _body(d: ConeDecl) -> str:
        name = d.name
        local_by_final: dict[str, set[str]] = {}
        local_by_qfinal: dict[str, set[str]] = {}
        for r in d.refs:
            if r in proj_full or r in idx.mlib_full:
                local_by_final.setdefault(r.split(".")[-1], set()).add(r)
                if "." in r:  # qualified refs only, for dot-notation access
                    local_by_qfinal.setdefault(r.split(".")[-1], set()).add(r)
        ctx = LinkCtx(
            idx=idx,
            define_name=name,
            define_final=name.split(".")[-1],
            local_final={f: next(iter(s)) for f, s in local_by_final.items() if len(s) == 1},
            local_qual_final={f: next(iter(s)) for f, s in local_by_qfinal.items() if len(s) == 1},
            binders=local_binders(d.snippet),
        )
        snippet = d.snippet
        body = linkify(snippet, ctx) if snippet else "<span class='trunc'>(source not found)</span>"
        tag = " <span class='trunc'>… (truncated)</span>" if d.truncated else ""
        file_disp = module_path(d.module).as_posix()
        href = html.escape(f"{src_prefix}{urllib.parse.quote(file_disp)}#L{d.start_line}")
        meta = (
            f"<span class='code-meta'><a class='src' href='{href}' title='open source file'>"
            f"{html.escape(file_disp)}</a> · {d.start_line}–{d.end_line}</span>"
        )
        return (
            f"<div class='codeblock'><pre tabindex='0'><code>{body}{tag}</code></pre></div>"
            f"<div class='foot'>{meta}{used_by_html(d)}</div>"
        )

    st_counts = Counter(d.status for d in project)
    n_total = len(project)
    n_verified = st_counts.get("verified", 0)
    n_tainted = st_counts.get("tainted", 0)
    n_sorry = st_counts.get("sorry", 0)
    # The emitter publishes the axiom list its verdicts used; the literal trio
    # is a fallback for JSON written before `standardAxioms` existed.
    std_axioms = data.get("standardAxioms", ["propext", "Classical.choice", "Quot.sound"])
    axiom_chips = "".join(f"<code class='ax'>{a}</code>" for a in std_axioms)

    tcinfo = toolchain_info(lean_root)
    foot_bits = tcinfo.split(", ") if tcinfo else []
    foot_bits.append("checked by <code>#print axioms</code> on the full build")
    footer = " · ".join(html.escape(b) if "<" not in b else b for b in foot_bits)

    panel_tail = f"<div class='vpanel-foot'>{footer}</div>{HUMAN_REVIEW_NOTE}</div></section>"
    all_verified = n_verified == n_total and n_total > 0
    if all_verified:
        panel = (
            "<section class='vpanel ok'><div class='vpanel-icon'>✓</div>"
            "<div class='vpanel-body'>"
            f"<div class='vpanel-head'>All {n_total} declarations kernel-checked</div>"
            "<div class='vpanel-sub'>Standard axioms only; no <code>sorry</code> dependencies: "
            f"{axiom_chips}</div>"
            f"{panel_tail}"
        )
    else:
        icon = "✗" if n_sorry else ("⚠" if n_tainted else "✓")
        cls = "sorry" if n_sorry else ("warn" if n_tainted else "ok")
        pills = []
        if n_verified:
            pills.append(f"<span class='pill verified'>{n_verified} kernel-checked</span>")
        if n_tainted:
            pills.append(f"<span class='pill tainted'>{n_tainted} tainted</span>")
        if n_sorry:
            pills.append(f"<span class='pill sorry'>{n_sorry} with sorry</span>")
        panel = (
            f"<section class='vpanel {cls}'><div class='vpanel-icon'>{icon}</div>"
            "<div class='vpanel-body'>"
            f"<div class='vpanel-head'>Verification status &mdash; {n_total} declarations</div>"
            f"<div class='vpanel-pills'>{''.join(pills)}</div>"
            "<div class='vpanel-sub'>Kernel-checked = sorry-free, standard axioms "
            f"({axiom_chips}) only. Tainted = sorry-free but uses extra axioms "
            "(listed by the badge). Sorry = depends on <code>sorryAx</code>.</div>"
            f"{panel_tail}"
        )

    def toc_label(d: ConeDecl) -> str:
        parts = [p for p in (label_map.get(d.name), title_map.get(d.name) or d.name) if p]
        return html.escape(" — ".join(parts))

    ptitle = title_override or (f"the {package}" if package else "this Lean project")
    title = "Lean 4 formalization of " + ptitle
    named_titles = [t for t, _, entries in section_entries if entries]  # headings that actually render, in order
    n_headline = sum(len(entries) for _, _, entries in section_entries)
    # With nothing left over, the sentence just ends after the sections.
    support_prose = (
        f"; the {spell(len(support))} remaining <em>{html.escape(support_title.lower())}</em> "
        "follow in <em>topological order</em>, each after everything it depends on"
        if support
        else ""
    )

    def _em(t: str) -> str:
        return f"<em>{html.escape(t)}</em>"

    if len(named_titles) > 1:
        order_prose = ", ".join(_em(t) for t in named_titles[:-1]) + " then " + _em(named_titles[-1])
    elif named_titles:
        order_prose = _em(named_titles[0])
    else:
        order_prose = ""
    parts = [
        "<!doctype html><html lang='en'><head><meta charset='utf-8'>",
        "<meta name='viewport' content='width=device-width, initial-scale=1'>",
        f"<title>{html.escape(title)}</title>",
        f"<style>{CSS}</style></head><body>",
        f"<h1>Lean 4 formalization of <em>{html.escape(ptitle)}</em></h1>",
        "<p>Lean's type checker guarantees the proofs are logically correct, but "
        "not that the theorem <em>statements</em> actually express the intended "
        "mathematics &mdash; a formalization can type-check yet fail to capture the "
        "intended meaning. Closing that gap is the human reviewer's job. The "
        "declarations collected here are the <strong>review cone</strong> (following "
        "<a class='proj' href='https://github.com/NyxFoundation/lean-atlas' "
        "target='_blank' rel='noopener'>lean-atlas</a>): the transitive set of statements and "
        "definitions whose meaning can affect what the results say &mdash; the "
        "minimal set one must read to trust the formalization. The proofs themselves "
        "can be taken on trust, since the checker guarantees them.</p>",
        f"<p>The {spell(n_headline)} results are grouped into sections"
        + (f" &mdash; {order_prose}" if order_prose else "")
        + support_prose
        + ". The defined name is <strong class='self'>bold pink</strong> at its definition. "
        "<span class='proj sample'>Blue links</span> jump within this document; "
        "<span class='mlib sample'>brown links</span> open the mathlib4 docs.</p>",
    ]
    parts.append(panel)
    info = config["info"]
    if info is not None:
        url = html.escape(info["url"])
        parts.append(
            "<section class='vpanel info'><div class='vpanel-icon'>\u2139</div>"
            "<div class='vpanel-body'>"
            f"<div class='vpanel-head'>{html.escape(info['heading'])}</div>"
            f"<div class='vpanel-sub'>{html.escape(info['text'])} "
            f"<a class='proj' href='{url}' target='_blank' rel='noopener'>{url}</a></div>"
            "</div></section>"
        )
    rev = git_revision(lean_root)
    if rev:
        parts.append(f"<p class='prov'>Generated from repository revision <code>{html.escape(rev)}</code>.</p>")

    # Sidebar contents: every section that opts in, then the support catch-all.
    # A sticky column on wide screens; a disclosure (closed by default) on narrow.
    def nav_item(d: ConeDecl, label: str) -> str:
        return f"<li><a href='#{anchor_id(d.name)}'><span class='kind'>{html.escape(d.kind)}</span> {label}</a></li>"

    toc_sections = [(t, e) for t, in_toc, e in section_entries if e and in_toc]
    nav = []
    for sec_title, entries in toc_sections:
        nav.append(f"<div class='tocgroup'>{html.escape(sec_title)} ({len(entries)})</div><ul>")
        nav.extend(nav_item(d, toc_label(d)) for d in entries)
        nav.append("</ul>")
    if support and show_support_toc:
        nav.append(
            f"<div class='tocgroup'>{html.escape(support_title)} ({len(support)}), in dependency order</div><ul>"
        )
        nav.extend(nav_item(d, html.escape(d.name)) for d in support)
        nav.append("</ul>")
    n_nav = sum(len(e) for _, e in toc_sections) + (len(support) if show_support_toc else 0)
    if nav:
        parts.append(
            "<div class='layout'><nav class='side' aria-label='Contents'><details open>"
            f"<summary>Contents ({n_nav} declarations)</summary><h2 id='contents'>Contents</h2>"
            + "".join(nav)
            + "</details></nav>"
        )
    parts.append("<main>")
    for sec_title, _, entries in section_entries:
        if not entries:
            continue
        parts.append(f"<h2>{html.escape(sec_title)}</h2>")
        for d in entries:
            parts.append(
                render_decl(
                    d, _body(d), title_map.get(d.name, ""), label_map.get(d.name, ""), summary_map.get(d.name, "")
                )
            )
    if support:
        parts.append(f"<h2>{html.escape(support_title)}</h2>")
        for d in support:
            parts.append(render_decl(d, _body(d)))
    parts.append("</main>")
    if nav:
        parts.append("</div>" + SIDEBAR_JS)
    parts.append("</body></html>")
    return "".join(parts)


# Marks the sidebar entry of the declaration currently in view, keeps that entry
# visible by scrolling the sidebar alone, and folds the contents on narrow
# screens (reopening it whenever the wide layout returns).
SIDEBAR_JS = """<script>
(function(){
  const links=[...document.querySelectorAll('.side a[href^="#"]')];
  const byId=new Map(links.map(a=>[a.getAttribute('href').slice(1),a]));
  const heads=[...byId.keys()].map(id=>document.getElementById(id)).filter(Boolean);
  const side=document.querySelector('.side');
  let current=null;
  function setCurrent(id){
    if(id===current) return; current=id;
    links.forEach(a=>{a.classList.remove('current'); a.removeAttribute('aria-current');});
    const a=byId.get(id); if(!a) return;
    a.classList.add('current'); a.setAttribute('aria-current','location');
    if(side.scrollHeight>side.clientHeight){
      const r=a.getBoundingClientRect(), sr=side.getBoundingClientRect();
      if(r.top<sr.top) side.scrollTop+=r.top-sr.top-8;
      else if(r.bottom>sr.bottom) side.scrollTop+=r.bottom-sr.bottom+8;
    }
  }
  function update(){
    if(!heads.length) return;
    const y=window.scrollY+Math.min(120,window.innerHeight/4);
    let best=heads[0];
    for(const h of heads){ if(h.offsetTop<=y) best=h; else break; }
    setCurrent(best.id);
  }
  window.addEventListener('scroll',update,{passive:true}); window.addEventListener('resize',update); update();
  const det=side.querySelector('details'), mq=window.matchMedia('(max-width: 860px)');
  function layout(){ if(mq.matches){ if(!det.dataset.touched) det.open=false; } else det.open=true; }
  det.addEventListener('toggle',()=>{ if(mq.matches) det.dataset.touched='1'; });
  mq.addEventListener('change',layout); layout();
})();
</script>"""


def main(argv: Sequence[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="lean4-lens review-cone", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument(
        "--project", type=Path, default=None, help="Lean project root (default: nearest lakefile from the CWD)."
    )
    ap.add_argument(
        "--json", type=Path, default=None, help="Render an existing review-cone.json and skip the Lean run."
    )
    ap.add_argument("--out", type=Path, default=None, help="Output HTML path (default: <project>/<config-stem>.html).")
    ap.add_argument(
        "--title", type=str, default=None, help="Document title (default: derived from the lake package name)."
    )
    ap.add_argument(
        "--lean-root",
        type=Path,
        default=None,
        help="Source root for snippets (default: the JSON's projectRoot / the project).",
    )
    ap.add_argument("--no-build", action="store_true", help="Skip `lake build` before running the emitter.")
    ap.add_argument(
        "--config",
        type=Path,
        default=None,
        help=f"Layout config (default: <project>/{DEFAULT_CONFIG_NAME}). Lists the roots and sections.",
    )
    ap.add_argument(
        "--toc-support",
        action="store_true",
        help="List the supporting declarations in the contents even if the config sets support.toc = false.",
    )
    args = ap.parse_args(argv)

    if shutil.which("lake") is None and args.json is None:
        ap.error("`lake` not found on PATH — build tooling required (or pass --json to render only)")

    # Locate the project. Always attempt discovery (it is cheap and also supplies
    # the default config/output locations) — even in --json render-only mode, so a
    # `review-cone.toml` in the project is still auto-detected.
    start = (args.project or Path.cwd()).resolve()
    try:
        project_root: Path | None = resolve_root(args.project)
    except RootNotFoundError:
        project_root = None
    if project_root is None and args.json is None:
        print(
            cli.red("✗ no lakefile.lean/.toml found") + cli.dim(f"  from {start} upward — pass --project"),
            file=sys.stderr,
        )
        return 1

    cli.heading("REVIEW CONE")

    # The config (required) supplies the roots and the section layout.
    if args.config is not None:
        config_path = args.config
    elif project_root is not None:
        config_path = project_root / DEFAULT_CONFIG_NAME
    else:
        print(
            cli.red("✗ no config: pass --config") + cli.dim("  (no project root to default review-cone.toml from)"),
            file=sys.stderr,
        )
        return 1
    config = load_config(config_path)  # ConfigError (SystemExit) on any problem
    cli.kv("config", cli.dim(str(config_path)))

    # 1–3. Produce the JSON (unless one was supplied).
    if args.json is not None:
        json_path = args.json
        if not json_path.is_file():
            print(
                cli.red("✗ input not found: ") + str(json_path) + cli.dim("  — run review_cone first, or drop --json"),
                file=sys.stderr,
            )
            return 1
    else:
        assert project_root is not None
        cli.kv("project", cli.dim(str(project_root)))
        libs = read_lib_names(project_root)
        if not libs:
            print(cli.red("✗ no lean_lib found in the lakefile"), file=sys.stderr)
            return 1
        cli.kv("libraries", cli.dim(", ".join(libs)))
        # Derive the JSON name from the config so multiple cones (multiple
        # configs) in one project don't clobber each other's JSON.
        json_path = project_root / (config_path.stem + ".json")
        run_review_cone(project_root, libs, config["roots"], json_path, build=not args.no_build)

    data = json.loads(json_path.read_text(encoding="utf-8"))

    # Resolve the source root for snippets: --lean-root, else the project we
    # found, else the JSON's own `projectRoot` — which the emitter records
    # relative to the project root, so it resolves against the JSON's directory.
    if args.lean_root is not None:
        lean_root = args.lean_root
    elif project_root is not None:
        lean_root = project_root
    else:
        lean_root = (json_path.resolve().parent / data.get("projectRoot", ".")).resolve()

    package = read_package_name(project_root) if project_root is not None else None
    show_support_toc = config["support"]["toc"] or args.toc_support

    # Output: --out beats the config's `out` (resolved against the project
    # root) beats the default name.
    doc_root = project_root or lean_root
    out_path = args.out or (doc_root / config["out"] if config["out"] else doc_root / f"{config_path.stem}.html")
    src_prefix = os.path.relpath(lean_root.resolve(), out_path.resolve().parent).replace(os.sep, "/")
    src_prefix = "" if src_prefix == "." else src_prefix + "/"
    html_str = render(data, lean_root, args.title or config["title"], package, config, show_support_toc, src_prefix)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(html_str, encoding="utf-8")

    n_root = sum(1 for d in data["project"] if d.get("isRoot"))
    cli.clear_transient()
    cli.wrote(out_path, f"{len(data['project'])} project, {len(data['mathlib'])} mathlib, {n_root} roots")
    return 0


def dep_graph_main(argv: Sequence[str] | None = None) -> int:
    """CLI for `lean4-lens emit-refs` (alias `dep-graph` for one release): run
    the same Lean emitter in dependency mode — every project decl with its
    proof refs — for `lean4-lens refs`."""
    ap = argparse.ArgumentParser(
        prog="lean4-lens emit-refs",
        description=(
            f"Emit {DEP_GRAPH_NAME} — every project decl with its proof refs — "
            "for `lean4-lens refs`. Chain: `lake build`, then `emit-refs --no-build`, "
            "then `refs check data-complete`."
        ),
    )
    ap.add_argument(
        "--project", type=Path, default=None, help="Lean project root (default: nearest lakefile from the CWD)."
    )
    ap.add_argument(
        "--out", type=Path, default=Path(DEP_GRAPH_NAME), help=f"Output path (default: <project>/{DEP_GRAPH_NAME})."
    )
    ap.add_argument("--no-build", action="store_true", help="Skip `lake build` before running the emitter.")
    args = ap.parse_args(argv)

    if shutil.which("lake") is None:
        ap.error("`lake` not found on PATH — build tooling required")
    project_root = resolve_root_or_exit(args.project)

    cli.heading("EMIT REFS")
    libs = read_lib_names(project_root)
    if not libs:
        print(cli.red("✗ no lean_lib found in the lakefile"), file=sys.stderr)
        return 1
    out_json = args.out if args.out.is_absolute() else project_root / args.out
    run_review_cone(project_root, libs, [], out_json, build=not args.no_build, deps=True)
    cli.clear_transient()
    cli.wrote(out_json, "every project decl, proof refs included")
    return 0
