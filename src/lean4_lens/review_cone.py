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
import tempfile
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


def module_emitter_supported(root: Path) -> bool:
    """Conservative version gate for module syntax and cached exported axioms.

    Unknown/custom toolchains retain the legacy emitter. Respect elan's override.
    """
    toolchain = os.environ.get("ELAN_TOOLCHAIN")
    if toolchain is None:
        path = root / "lean-toolchain"
        toolchain = path.read_text(encoding="utf-8").strip() if path.is_file() else ""
    match = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc\d+)?", toolchain)
    return bool(match and (int(match[1]), int(match[2])) >= (4, 32))


def emitter_source(root: Path, *, deps: bool) -> str:
    """Use public compiler imports on modern Lean; retain private proof data for deps."""
    source = REVIEW_CONE_LEAN.read_text(encoding="utf-8")
    if module_emitter_supported(root):
        source = source.replace("-- MODULE_HEADER", "module", 1)
        source = source.replace("unsafe def main :", "public unsafe def main :", 1)
        if not deps:
            source = source.replace("-- IMPORT_LEVEL", "(level := if privateOnly then .private else .server)", 1)
    return source


def run_emitter_process(command: list[str], root: Path, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    """Stream progress while retaining both streams for failure diagnostics.

    Spool stdout to disk so a verbose emitter cannot fill an unread pipe.
    """
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as stdout:
        with subprocess.Popen(command, cwd=root, env=env, stdout=stdout, stderr=subprocess.PIPE, text=True) as proc:
            assert proc.stderr is not None
            errors = []
            for line in proc.stderr:
                errors.append(line)
                print(line, end="", file=sys.stderr, flush=True)
            code = proc.wait()
        stdout.seek(0)
        return subprocess.CompletedProcess(command, code, stdout.read(), "".join(errors))


def run_review_cone(
    root: Path, libs: list[str], roots: list[str], out_json: Path, build: bool, *,
    deps: bool = False, imports: list[str] | None = None
) -> None:
    """Build the libraries (or explicit imports), then emit Lean-derived JSON. `deps`
    selects the dependency graph's data rather than the review document's, and
    ignores `roots` (see `REVIEW_CONE_DEPS` in review_cone.lean). `imports`
    narrows entry modules only; `libs` still classifies all project declarations.
    """
    if deps and imports is not None:
        raise ValueError("dependency graphs require all project modules")
    targets = imports if imports is not None else libs
    if build:
        print("  " + cli.dim(f"lake build {' '.join(targets)} …"))
        warm = subprocess.run(["lake", "build", *targets], cwd=root, capture_output=True, text=True)
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
    env.pop("REVIEW_CONE_DEPS", None)
    env.pop("REVIEW_CONE_IMPORTS", None)
    if deps:
        env["REVIEW_CONE_DEPS"] = "1"
    if imports is not None:
        env["REVIEW_CONE_IMPORTS"] = ",".join(imports)
    cli.status("running review_cone.lean …")
    with tempfile.TemporaryDirectory(prefix="lean4-lens-") as tmp:
        emitter = Path(tmp) / "review_cone.lean"
        emitter.write_text(emitter_source(root, deps=deps), encoding="utf-8")
        proc = run_emitter_process(["lake", "env", "lean", "--run", str(emitter)], root, env)
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


def prose_html(text: str) -> str:
    """Escape authored prose, supporting paragraphs and inline code only."""
    paragraphs = []
    for paragraph in re.split(r"\n\s*\n", text.strip()):
        if not paragraph:
            continue
        pieces = re.split(r"(`[^`]+`)", paragraph)
        body = "".join(
            f"<code>{html.escape(piece[1:-1])}</code>" if i % 2 else html.escape(piece)
            for i, piece in enumerate(pieces)
        )
        paragraphs.append(f"<p class='summary'>{body}</p>")
    return "".join(paragraphs)


def split_docstring(snippet: str) -> tuple[str, str]:
    """Move only a leading declaration docstring into the prose column.

    Use the Lean scanner so nested comments cannot consume declaration code.
    Field docs and comments within the definition stay with their source.
    """
    prefix = ""
    for lo, hi, kind in iter_spans(snippet):
        piece = snippet[lo:hi]
        if not piece.strip():
            continue
        if kind == "comment" and piece.startswith("/--"):
            return piece[3:-2].strip(), prefix + snippet[hi:].lstrip("\n\r")
        # `open … in` / `set_option … in` lines may precede the docstring.
        if kind == "code" and not prefix and all(
            ln.strip().endswith(" in") and ln.split()[0] in ("open", "set_option")
            for ln in piece.strip().splitlines()
        ):
            prefix = piece
            continue
        break
    return "", snippet


def render_decl(
    d: ConeDecl, body_html: str, title: str = "", label: str = "", summary: str = "", source_html: str = ""
) -> str:
    """A shared title row, then readable prose beside always-visible Lean."""
    heading = " — ".join(part for part in (label, title) if part) or d.name
    # Success is stated once for the document. Exceptions remain visible locally.
    badge = status_badge(d) if d.status != "verified" else ""
    return (
        f"<article class='entry entry-pair' id='{anchor_id(d.name)}'>"
        f"<div class='entry-heading'><h3>{html.escape(heading)}{badge}</h3>{source_html}</div>"
        f"<div class='annotation'>{prose_html(summary)}</div>"
        f"<div class='lean'>{body_html}</div></article>"
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
    # Some cached module-interface exports classify theorem constants as axioms.
    # The source keyword still identifies which value is a proof, not a definition.
    source_theorem = re.search(
        r"^\s*(?:(?:private|protected|noncomputable)\s+)*theorem\b",
        blank_comments_and_strings("\n".join(block)), re.M,
    )
    if d.kind == "theorem" or (d.kind == "axiom" and source_theorem):
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
  --page-bg: #faf9f6; --section-bg: #f0f1ec; --text: #242a30;
  --muted: #65736c; --accent: #183f33; --link: #245c58;
  --rule: #dfe3db; --font-heading: Georgia, serif;
  --font-code: 'JuliaMono', 'DejaVu Sans Mono', ui-monospace, monospace;
  font: 16px/1.65 system-ui, sans-serif; color: var(--text); background: var(--page-bg);
}
* { box-sizing: border-box; }
body { max-width: 1480px; padding: 22px 56px 64px; margin: auto; overflow-wrap: anywhere; }
a { color: var(--link); text-underline-offset: 3px; }
a:focus-visible, summary:focus-visible, pre:focus-visible { outline: 3px solid #b87a39; outline-offset: 3px; }
summary { cursor: pointer; }
h1 { font: 400 30px/1.25 var(--font-heading); margin: 8px 0 12px; }
.intro { font-size: 15px; margin: 0 0 12px; }
.about, .verification { font-size: 13px; margin: 10px 0; }
.about p { max-width: 85ch; }
.verification > summary { color: var(--accent); }
.prov { color: var(--muted); font-size: 12px; }
.contents { display: flex; flex-wrap: wrap; gap: 12px 26px; padding: 14px 0 26px; }
.contents a { font-size: 13px; text-decoration: none; }
.contents a:hover { text-decoration: underline; }
.review-section { background: var(--section-bg); }
.review-section + .review-section { margin-top: 80px; }
.section-heading { padding: 28px 24px 22px; scroll-margin-top: 16px; }
.section-title { display: flex; align-items: baseline; gap: 12px; font-family: var(--font-heading); }
.section-title h2 { font: 400 25px/1.4 var(--font-heading); color: var(--accent); margin: 0; }
.section-count { font-size: 12px; color: #72837a; }
.section-description { margin: 6px 0 0; font-size: 13px; color: var(--muted); }
.entry-pair { position: relative; display: grid; grid-template-columns: minmax(0,44%) minmax(0,56%); }
.entry-pair > * { min-width: 0; }
.entry-pair + .entry-pair::before {
  content: ''; position: absolute; top: 0; left: 24px; right: 24px; height: 1px; background: var(--rule);
}
.entry-heading { grid-column: 1 / -1; display: flex; align-items: baseline; gap: 14px; padding: 24px 24px 20px; }
.entry-heading h3 { font: 500 19px/1.4 var(--font-heading); margin: 0; }
.heading-source { margin-left: auto; font-size: 11px; text-align: right; max-width: 55%; }
.heading-source a { color: var(--muted); text-decoration: none; }
.heading-source a:hover { color: var(--link); text-decoration: underline; }
.annotation { padding: 0 24px 28px; font: 17px/1.7 var(--font-heading); }
.summary { margin: 0 0 16px; }
.summary:last-child { margin-bottom: 0; }
.summary code { font: .85em/1.6 var(--font-code); }
.lean { padding: 0 24px 28px; }
pre { margin: 0; font: 13px/1.8 var(--font-code); white-space: pre-wrap; overflow-wrap: anywhere; }
pre code { font: inherit; }
pre a { color: #376f80; text-decoration: none; }
pre a:hover { text-decoration: underline; }
strong.self { color: #30383c; font-weight: 600; }
.cmt, .proof, .proof a, .trunc { color: var(--muted); }
.cmt, .trunc { font-style: italic; }
.usedby { font-size: 12px; color: var(--muted); margin-top: 16px; }
.usedby a { overflow-wrap: anywhere; }
.entry-pair:target { outline: 2px solid #aec2b4; outline-offset: 3px; scroll-margin-top: 18px; }
.badge, .pill { font: 600 12px/1.6 system-ui, sans-serif; padding: 2px 6px; border-radius: 4px; }
.badge { margin-left: 8px; }
.tainted { background: #f3e4bd; color: #7a5200; }
.sorry { background: #f6cccc; color: #8a1515; }
.verified { background: #e3f5e3; color: #145214; }
.axioms { font: 12px/1.6 var(--font-code); color: #7a5200; margin-left: 6px; }
.vpanel { display: flex; gap: 12px; padding: 16px; margin: 16px 0; border-radius: 6px; }
.vpanel.ok { background: #eef4ec; }
.vpanel.warn { background: #fdf6e3; }
.vpanel.sorry { background: #fdecec; }
.vpanel.info { background: #eef4f5; }
.vpanel-head { font-weight: 600; }
.vpanel-sub { font-size: 14px; margin-top: 6px; }
.vpanel-foot { font-size: 12px; color: var(--muted); margin-top: 10px; }
.vpanel-pills { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 6px; }
code.ax { margin-right: 8px; }
@media (max-width: 900px) { body { padding-left: 24px; padding-right: 24px; } }
@media (max-width: 700px) {
  body { padding-left: 18px; padding-right: 18px; }
  .review-section + .review-section { margin-top: 56px; }
  .section-heading { padding-left: 20px; padding-right: 20px; }
  .section-title { flex-wrap: wrap; gap: 3px 10px; }
  .section-title h2 { font-size: 23px; }
  .entry-pair { grid-template-columns: minmax(0,1fr); }
  .entry-heading { flex-wrap: wrap; padding-left: 20px; padding-right: 20px; }
  .entry-heading h3 { font-size: 18px; }
  .heading-source { margin-left: 0; max-width: 100%; text-align: left; }
  .annotation { padding: 0 20px 18px; }
  .lean { padding: 0 20px 24px; }
  pre { font-size: 12px; }
  .entry-pair + .entry-pair::before { left: 20px; right: 20px; }
}
@media print {
  body { padding: 0; max-width: none; }
  .contents, .about, .usedby { display: none; }
  .review-section { background: none; }
  .entry-heading { break-after: avoid; }
}
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
        d.snippet, d.truncated = read_snippet(lean_root, d, max_lines=sys.maxsize, cache=module_lines)

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
        return (
            f"<details class='usedby'><summary>Used by {len(users)} declarations</summary>"
            f"{items}</details>"
        )

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

    def _entry(d: ConeDecl) -> str:
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
        docstring, snippet = split_docstring(d.snippet)
        body = linkify(snippet, ctx) if snippet else "<span class='trunc'>(source not found)</span>"
        tag = " <span class='trunc'>… (truncated)</span>" if d.truncated else ""
        file_disp = module_path(d.module).as_posix()
        href = html.escape(f"{src_prefix}{urllib.parse.quote(file_disp)}#L{d.start_line}")
        source = (
            f"<span class='heading-source'><a class='src' href='{href}' "
            f"title='{html.escape(file_disp)} · lines {d.start_line}–{d.end_line}'>"
            f"{html.escape(file_disp)} ↗</a></span>"
        )
        body_html = (
            f"<pre tabindex='0'><code>{body}{tag}</code></pre>{used_by_html(d)}"
        )
        return render_decl(
            d, body_html, title_map.get(name, ""), label_map.get(name, ""),
            summary_map.get(name) or docstring, source,
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

    if all_verified:
        panel = (
            f"<details class='verification'><summary>✓ All {n_total} declarations kernel-checked"
            f" · Verification details</summary>{panel}</details>"
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
        f"<header class='page-heading'><h1>Lean 4 formalization of <em>{html.escape(ptitle)}</em></h1>",
        "<p class='intro'>Compare each mathematical statement with its Lean declaration. "
        "Follow linked terms to their definitions below.</p>",
        "<details class='about'><summary>About this review</summary>",
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
        + ". Links in Lean open declarations in this document or the mathlib documentation.</p>",
        "</details>",
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

    parts.append("</header>")

    # Compact top navigation: primary declarations plus a support-section link.
    nav: list[str] = []
    for _, in_toc, entries in section_entries:
        if in_toc:
            nav.extend(f"<a href='#{anchor_id(d.name)}'>{toc_label(d)}</a>" for d in entries)
    if support and show_support_toc:
        nav.append(f"<a href='#support'>{html.escape(support_title)} ({len(support)})</a>")
    if nav:
        parts.append("<nav class='contents' aria-label='Contents'>" + "".join(nav) + "</nav>")

    def section_html(section_id: str, heading: str, entries: list[ConeDecl], note: str) -> str:
        count = len(entries)
        noun = "theorem" if all(d.kind == "theorem" for d in entries) else "declaration"
        count_text = f"{count} {noun}{'' if count == 1 else 's'}"
        return (
            f"<section class='review-section' aria-labelledby='{section_id}-title'>"
            f"<header class='section-heading' id='{section_id}'>"
            f"<div class='section-title'><h2 id='{section_id}-title'>{html.escape(heading)}</h2>"
            f"<span class='section-count'>{count_text}</span></div>"
            f"<p class='section-description'>{html.escape(note)}</p></header>"
            "<div class='table-body'>" + "".join(_entry(d) for d in entries) + "</div></section>"
        )

    parts.append("<main>")
    for i, (sec_title, _, entries) in enumerate(section_entries):
        if entries:
            parts.append(section_html(f"section-{i}", sec_title, entries, "Statements and their Lean declarations."))
    if support:
        parts.append(section_html(
            "support", support_title, support,
            "Definitions and supporting statements in dependency order. Descriptions default to source comments.",
        ))
    parts.append("</main></body></html>")
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
        run_review_cone(
            project_root, libs, config["roots"], json_path, build=not args.no_build, imports=config["imports"]
        )

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
