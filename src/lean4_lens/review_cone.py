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
implicit `[support]` catch-all (rendered last, topologically sorted, hidden from
the table of contents unless `support.toc = true` or --toc-support). Optional
display titles live in a section-local `[section.titles]` table; the document's
own `title` and `out` path (relative to the project root) are top-level keys,
overridable with --title/--out. There is no in-source attribute and no
paper/LaTeX coupling.

Usage:
    lean4-lens review-cone                          # full pipeline in the current project
    lean4-lens review-cone --project path/to/proj   # a specific project
    lean4-lens review-cone --config path/to.toml    # a specific config
    lean4-lens review-cone --json cone.json         # render an existing JSON, skip the Lean run
    lean4-lens review-cone --no-build --toc-support --out out.html --title "My Formalization"

`lean4-lens dep-graph` shares this file's Lean emitter to write `dep-graph.json`
for `lean4-lens dep-tree` — data, not a document.
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
from collections import Counter
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


def anchor_id(name: str) -> str:
    # Encode every non-ASCII-alphanumeric char by codepoint so distinct names
    # (e.g. ...μ vs ...ℱ) never collide onto the same anchor.
    return "d-" + "".join(ch if (ch.isascii() and ch.isalnum()) else f"_{ord(ch)}" for ch in name)


def status_badge(d: ConeDecl) -> str:
    st = d.status
    if st == "verified":
        return "<span class='badge verified' title='sorry-free; standard axioms only'>✓ Verified</span>"
    if st == "tainted":
        ax = ", ".join(d.axioms)
        return (
            f"<span class='badge tainted' title='sorry-free but depends on extra axioms'>"
            f"⚠ Tainted</span><span class='axioms'>{html.escape(ax)}</span>"
        )
    if st == "sorry":
        return "<span class='badge sorry' title='depends on sorryAx'>✗ Sorry</span>"
    return ""


def render_decl(d: ConeDecl, body_html: str, title: str = "") -> str:
    """One declaration's entry — every decl renders through this, in whatever
    section it lands: `<kind> <name> (optional title) [badge]`, then the source
    body. The optional display title comes from the config's `[section.titles]`."""
    name = d.name
    title_html = f" <span class='title'>({html.escape(title)})</span>" if title else ""
    return (
        f"<div class='entry'><h3 id='{anchor_id(name)}'>"
        f"<span class='head'>{html.escape(d.kind)}</span> "
        f"<strong class='self'>{html.escape(name)}</strong>"
        f"{title_html} {status_badge(d)}</h3>"
        f"{body_html}</div>"
    )


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
# delimiter. `^` is included so `f^[n]` (iterate notation) doesn't glue its
# caret onto the preceding identifier and break the link lookup.
_DELIM_RE = re.compile(r"([\s(){}\[\],;⟨⟩«»^])")


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


@dataclass(frozen=True)
class LinkCtx:
    """`Indexes` plus the decl being rendered: its own name (bold, not linked)
    and its refs' final-component tables, which disambiguate shared names."""

    idx: Indexes
    define_name: str
    define_final: str
    local_final: dict[str, str]
    local_qual_final: dict[str, str]


def build_indexes(project: list[ConeDecl], mathlib: list[MathlibDecl], field_of: dict[str, str]) -> Indexes:
    proj_full: dict[str, ConeDecl | None] = {d.name: d for d in project}
    # structure-field projections resolve too, but their link target is the
    # parent structure (they are not emitted as their own entries).
    proj_target: dict[str, str] = {d.name: d.name for d in project}
    for fld, struct in field_of.items():
        proj_full.setdefault(fld, None)
        proj_target[fld] = struct
    mlib_full: dict[str, MathlibDecl] = {d.name: d for d in mathlib}

    def unique_final(names: list[str]) -> dict[str, str]:
        cnt = Counter(n.split(".")[-1] for n in names)
        return {f: n for n in names if cnt[f := n.split(".")[-1]] == 1}

    return Indexes(
        proj_full=proj_full,
        mlib_full=mlib_full,
        proj_final=unique_final(list(proj_full)),
        mlib_final=unique_final(list(mlib_full)),
        proj_target=proj_target,
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
        return f'<a class="proj" href="#{anchor_id(target)}">{html.escape(text)}</a>'

    def mlib_link(full: str, text: str) -> str:
        url = mlib_full[full].url
        return f'<a class="mlib" href="{html.escape(url)}" target="_blank">{html.escape(text)}</a>'

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

    # 1. exact full-name match
    if chunk in proj_full:
        return proj_link(chunk, chunk)
    if chunk in mlib_full:
        return mlib_link(chunk, chunk)

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

    # 3. bare token matched by final component
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


def linkify(src: str, ctx: LinkCtx) -> str:
    out = []
    for text, is_code in split_code_comments(src):
        if not is_code:
            out.append(f'<span class="cmt">{html.escape(text)}</span>')
            continue
        for part in _DELIM_RE.split(text):
            if part == "" or _DELIM_RE.fullmatch(part):
                out.append(html.escape(part))
            else:
                out.append(linkify_chunk(part, ctx))
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
  --gray-100: #eee; --gray-400: #999; --gray-500: #777; --gray-600: #555;
  --gray-700: #444; --gray-900: #1a1a1a;
  --link-proj: #0b6bcb; --link-mlib: #8a5a00; --self: #b21f66; --cmt: #9aa0a6;
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
}
body { font-family: var(--font-sans); max-width: 1000px;
       margin: 2rem auto; padding: 0 1rem; color: var(--gray-900); line-height: var(--lh); }
h1 { font-size: var(--fs-2xl); } h2 { margin-top: 2.5rem; border-bottom: 2px solid var(--gray-100); }
.entry { margin: 1.5rem 0; padding: .5rem 0; border-top: 1px solid var(--gray-100); }
.entry h3 { margin: .2rem 0; font-size: var(--fs-lg); }
.desc { color: var(--gray-600); font-size: var(--fs-base); margin: .2rem 0 .1rem; }
.codeblock { margin: .6rem 0 1rem; }
.codeblock pre { margin: 0; }
.code-meta { display: block; text-align: right; padding: .25rem .1rem 0 0;
             font-family: var(--font-mono); font-size: var(--fs-xs); color: var(--gray-400); }
pre { background: var(--pre-bg); border: 1px solid var(--pre-border); border-radius: var(--radius);
      padding: .7rem .9rem; overflow-x: auto; font-size: var(--fs-base);
      font-family: var(--font-code); }
a.proj { color: var(--link-proj); text-decoration: none; }
a.proj:hover { text-decoration: underline; }
a.mlib { color: var(--link-mlib); text-decoration: none; }
a.mlib:hover { text-decoration: underline; }
strong.self { color: var(--self); }
.cmt { color: var(--cmt); font-style: italic; }
.head { font-weight: var(--fw-semibold); }
.title { font-weight: var(--fw-semibold); }
.paperref { font-size: var(--fs-sm); color: var(--gray-500); }
.toc { columns: 2; font-size: var(--fs-base); } .toc a { text-decoration: none; color: var(--link-proj); }
.tocgroup { break-after: avoid; font-weight: var(--fw-semibold); color: var(--gray-700); margin: .4rem 0 .15rem; }
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
.usedby { font-size: var(--fs-sm); color: var(--gray-600); margin-top: .1rem; }
.usedby-label { font-weight: var(--fw-semibold); margin-right: .3rem; }
.subtitle { font-size: var(--fs-lg); color: var(--gray-600); margin: -.4rem 0 1.2rem; }
.vpanel { display: flex; gap: .85rem; align-items: flex-start; border-radius: var(--radius-lg);
          border: 1px solid; padding: .8rem 1rem; margin: 1.4rem 0; }
.vpanel.ok { background: var(--ok-panel-bg); border-color: var(--ok-panel-border); }
.vpanel.warn { background: var(--warn-panel-bg); border-color: var(--warn-panel-border); }
.vpanel.sorry { background: var(--bad-panel-bg); border-color: var(--bad-panel-border); }
.vpanel-icon { font-size: var(--fs-xl); line-height: var(--lh); flex: none; width: 1.9rem;
               height: 1.9rem; display: flex; align-items: center;
               justify-content: center; border-radius: 50%; color: var(--white); }
.vpanel.ok .vpanel-icon { background: var(--ok); }
.vpanel.warn .vpanel-icon { background: var(--warn-icon); }
.vpanel.sorry .vpanel-icon { background: var(--bad-icon); }
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


def render(
    data: dict[str, Any],
    lean_root: Path,
    title_override: str | None,
    package: str | None,
    config: ReviewConeConfig,
    show_support_toc: bool,
) -> str:
    project = [ConeDecl.from_json(d) for d in data["project"]]
    mathlib = sorted((MathlibDecl(d["name"], d.get("url", "")) for d in data["mathlib"]), key=lambda d: d.name.lower())
    field_of = data.get("fieldOf", {})
    idx = build_indexes(project, mathlib, field_of)
    proj_full, proj_target = idx.proj_full, idx.proj_target

    # Config drives the layout: `title_map` supplies display titles (union of
    # all `[section.titles]`).
    title_map: dict[str, str] = {}
    for sec in config["sections"]:
        title_map.update(sec["titles"])

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
        users = used_by.get(d.name)
        if not users:
            return ""
        items = ", ".join(
            f"<a class='proj' href='#{anchor_id(n)}'>{html.escape(n)}</a>" for n in sorted(users, key=str.lower)
        )
        return f"<div class='usedby'><span class='usedby-label'>Used by:</span> {items}</div>"

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
    section_entries: list[tuple[str, list[ConeDecl]]] = []
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
        section_entries.append((sec["title"], entries))
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
        )
        snippet = d.snippet
        body = linkify(snippet, ctx) if snippet else "<span class='trunc'>(source not found)</span>"
        tag = " <span class='trunc'>… (truncated)</span>" if d.truncated else ""
        file_disp = module_path(d.module).as_posix()
        meta = (
            f"<span class='code-meta'><span class='code-file'>{html.escape(file_disp)}</span>"
            f" · {d.start_line}–{d.end_line}</span>"
        )
        return f"<div class='codeblock'><pre>{body}{tag}</pre>{meta}</div>"

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

    all_verified = n_verified == n_total and n_total > 0
    if all_verified:
        panel = (
            "<section class='vpanel ok'><div class='vpanel-icon'>✓</div>"
            "<div class='vpanel-body'>"
            f"<div class='vpanel-head'>All {n_total} declarations fully verified</div>"
            "<div class='vpanel-sub'>Sorry-free, and depending only on the standard "
            f"axioms {axiom_chips}</div>"
            f"<div class='vpanel-foot'>{footer}</div></div></section>"
        )
    else:
        icon = "✗" if n_sorry else ("⚠" if n_tainted else "✓")
        cls = "sorry" if n_sorry else ("warn" if n_tainted else "ok")
        pills = []
        if n_verified:
            pills.append(f"<span class='pill verified'>{n_verified} verified</span>")
        if n_tainted:
            pills.append(f"<span class='pill tainted'>{n_tainted} tainted</span>")
        if n_sorry:
            pills.append(f"<span class='pill sorry'>{n_sorry} with sorry</span>")
        panel = (
            f"<section class='vpanel {cls}'><div class='vpanel-icon'>{icon}</div>"
            "<div class='vpanel-body'>"
            f"<div class='vpanel-head'>Verification status &mdash; {n_total} declarations</div>"
            f"<div class='vpanel-pills'>{''.join(pills)}</div>"
            "<div class='vpanel-sub'>Verified = sorry-free, standard axioms "
            f"({axiom_chips}) only. Tainted = sorry-free but uses extra axioms "
            "(listed by the badge). Sorry = depends on <code>sorryAx</code>.</div>"
            f"<div class='vpanel-foot'>{footer}</div></div></section>"
        )

    def toc_label(d: ConeDecl) -> str:
        t = title_map.get(d.name)
        return html.escape(t) if t else html.escape(d.name)

    ptitle = title_override or (f"the {package}" if package else "this Lean project")
    title = "Review cone — " + ptitle
    named_titles = [t for t, entries in section_entries if entries]  # headings that actually render, in order

    def _em(t: str) -> str:
        return f"<em>{html.escape(t)}</em>"

    if len(named_titles) > 1:
        order_prose = ", ".join(_em(t) for t in named_titles[:-1]) + " then " + _em(named_titles[-1])
    elif named_titles:
        order_prose = _em(named_titles[0])
    else:
        order_prose = ""
    parts = [
        "<!doctype html><html><head><meta charset='utf-8'>",
        f"<title>{html.escape(title)}</title>",
        f"<style>{CSS}</style></head><body>",
        f"<h1>Review cone of <em>{html.escape(ptitle)}</em></h1>",
        "<p>Lean's type checker guarantees the proofs are logically correct, but "
        "not that the theorem <em>statements</em> actually express the intended "
        "mathematics &mdash; a formalization can type-check yet fail to capture the "
        "intended meaning. Closing that gap is the human reviewer's job. The "
        "declarations collected here are the <strong>review cone</strong> (following "
        "<a class='proj' href='https://github.com/NyxFoundation/lean-atlas' "
        "target='_blank'>lean-atlas</a>): the transitive set of statements and "
        "definitions whose meaning can affect what the results say &mdash; the "
        "minimal set one must read to trust the formalization. The proofs themselves "
        "can be taken on trust, since the checker guarantees them.</p>",
        "<p>The cone is grouped into sections"
        + (f" &mdash; {order_prose}" if order_prose else "")
        + f"; the remaining <em>{html.escape(support_title.lower())}</em> follow in "
        "<em>topological order</em>, each after everything it depends on. The "
        "defined name is <strong class='self'>bold pink</strong> at its definition. "
        "<a class='proj' href='#'>Blue links</a> jump within this document; "
        "<a class='mlib' href='#'>brown links</a> open the mathlib4 docs.</p>",
    ]
    parts.append(panel)

    parts.append("<h2>Contents</h2><div class='toc'>")
    for sec_title, entries in section_entries:
        if not entries:
            continue
        parts.append(f"<div class='tocgroup'>{html.escape(sec_title)} ({len(entries)})</div>")
        for d in entries:
            parts.append(f"<a href='#{anchor_id(d.name)}'>{toc_label(d)}</a><br>")
    if support and show_support_toc:
        parts.append(f"<div class='tocgroup'>{html.escape(support_title)} ({len(support)})</div>")
        for d in support:
            parts.append(f"<a href='#{anchor_id(d.name)}'>{html.escape(d.name)}</a><br>")
    parts.append("</div>")

    for sec_title, entries in section_entries:
        if not entries:
            continue
        parts.append(f"<h2>{html.escape(sec_title)}</h2>")
        for d in entries:
            parts.append(render_decl(d, _body(d) + used_by_html(d), title_map.get(d.name, "")))
    if support:
        parts.append(f"<h2>{html.escape(support_title)}</h2>")
        for d in support:
            parts.append(render_decl(d, _body(d) + used_by_html(d)))

    parts.append("</body></html>")
    return "".join(parts)


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
    ap.add_argument("--out", type=Path, default=None, help="Output HTML path (default: <project>/review-cone.html).")
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
        help="List the supporting declarations in the ToC (off by default; forces them on, ignoring support.toc).",
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
    html_str = render(data, lean_root, args.title or config["title"], package, config, show_support_toc)

    # Output: --out beats the config's `out` (resolved against the project
    # root) beats the default name.
    doc_root = project_root or lean_root
    out_path = args.out or (doc_root / config["out"] if config["out"] else doc_root / "review-cone.html")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(html_str, encoding="utf-8")

    n_root = sum(1 for d in data["project"] if d.get("isRoot"))
    cli.clear_transient()
    cli.wrote(out_path, f"{len(data['project'])} project, {len(data['mathlib'])} mathlib, {n_root} roots")
    return 0


def dep_graph_main(argv: Sequence[str] | None = None) -> int:
    """CLI for `lean4-lens dep-graph`: run the same Lean emitter in dependency
    mode — every project decl with its proof refs — for `lean4-lens dep-tree`."""
    ap = argparse.ArgumentParser(
        prog="lean4-lens dep-graph",
        description=f"Emit {DEP_GRAPH_NAME} — every project decl with its proof refs — for `lean4-lens dep-tree`.",
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

    cli.heading("DEP GRAPH")
    libs = read_lib_names(project_root)
    if not libs:
        print(cli.red("✗ no lean_lib found in the lakefile"), file=sys.stderr)
        return 1
    out_json = args.out if args.out.is_absolute() else project_root / args.out
    run_review_cone(project_root, libs, [], out_json, build=not args.no_build, deps=True)
    cli.clear_transient()
    cli.wrote(out_json, "every project decl, proof refs included")
    return 0
