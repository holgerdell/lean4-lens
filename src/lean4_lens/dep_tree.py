"""Proof references between Lean declarations.

Scans the project's .lean files (see `lean4-lens.toml`), extracts theorem/lemma/def
decls, and builds a forward dep DAG. A declaration is "sorry-tainted" iff it
transitively depends on a direct `sorry` (comments and strings stripped first).

References come from exactly one source: the **elaborator**, via the `refs`
field of `dep-graph.json` (written by `lean4-lens emit-refs`). There is no
text-matching fallback — a decl absent from the data gets no edges and is
reported by `check data-complete`, never guessed at.

Chain: first `lake build`, then `lean4-lens emit-refs`, then
`lean4-lens refs ...`. Missing data yields zero edges and is reported, never
guessed. Old names (`dep-tree` for the command, flat subcommands such as
`summary`/`coverage`/`from`) stay as aliases for one release.

Status glyphs in listings:
  ✓ clean (sorry-free, no tainted deps)
  ⊥ direct `sorry` in body
  ? sorry-tainted via deps
  A stated `axiom` — an unproven assumption

Groups:
  check                 Data and health gates.
    data-complete [--list]  Check `dep-graph.json` describes every declaration
                            in the source — total coverage is what the other
                            commands assume. Counts the stragglers per file, or
                            names them with --list. Exits 1 on stale data (cure:
                            `lean4-lens emit-refs`), 0 on files no library
                            imports (cure: import the file, or delete it).
    taint-status            Counts + listings. --fail-on-sorry / --fail-on-axioms
                            exit 1 on findings, so the report can gate CI.
  show                  Human questions over the graph.
    direct-deps NAME    Immediate refs of NAME.
    deps NAME           Transitive deps of NAME as lean names.
    used-by NAME        Transitive reverse-deps.
    reach [NAME...]     Split every decl into "used" (transitively feeds
                        into a root) vs "unused". Roots = NAME args and/or
                        every decl in a --root-file; with neither, default to
                        the roots listed in every `review-cone*.toml`. Uses a
                        dot-notation-aware resolver that over-approximates on
                        ambiguous names, so a decl reported unused genuinely
                        never feeds a root. --out-used / --out-unused write
                        JSONL; else a summary.
    dead [NAME...]      Dead-code candidates = unreachable from roots (as in
                        `reach`) AND referenced by zero *live* decls. Default:
                        globally orphaned (conservative — a dead helper still
                        called from another dead decl is withheld until its
                        caller goes). --closure reports the full removable set
                        in one pass (dead if every referrer is dead). --global
                        ignores roots and lists globally unreferenced decls
                        (the old `orphans` question). Rows are split into
                        confirmed (plain theorem/def — safe) vs suspects
                        (@[simp]/instance/… reachable via elaboration —
                        verify first), grouped by file, annotated with LOC span
                        and reachability flags. Same root args as `reach`
                        (default: roots from every `review-cone*.toml`). --out
                        (default dead_candidates.jsonl; --no-out to skip) writes
                        JSONL for both buckets (filter on `implicit_reach`);
                        --out-used / --out-unused also available as in `reach`.
    sorry-impact        Direct-sorry decls ranked by # downstream blocked.
  export --format json|dot|text [--from NAME]
                        The whole graph for other tools: json (machines), dot
                        (GraphViz), text (`Name: dep1 dep2 ...` lines). --from
                        limits the output to one decl's cone.

Common options (all subcommands):
  --project=DIR         Lean project root (default: nearest lakefile from the CWD).

Every subcommand exits 2 when the scan finds no project .lean files at all —
a gate that scanned nothing must not pass as clean.

Name resolution for direct-deps/deps/used-by:
exact uid or full_name, then suffix match on '.NAME', then case-insensitive
substring. A name declared in several modules (e.g. `private` copies) has one
uid per copy (`name@module`); querying the bare name lists the copies.
"""

import argparse
import json
import re
import sys
from collections import Counter, defaultdict, deque
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from . import symbols

# Shared terminal palette. The `fmt_*` helpers return strings (printed by the
# `_cmd_*` handlers), so this module uses the colour functions and the
# string-returning `kv_s` rather than cli's print-side helpers.
from .cli import (
    bold,
    cyan,
    dim,
    green,
    kv_s,
    red,
    write_jsonl,
    yellow,
)
from .cone_config import CONE_CONFIG_GLOB, roots_from_configs
from .project import DEP_GRAPH_NAME, exit_no_lean_files, iter_lean_files, module_of, resolve_root_or_exit
from .source import blank_comments_and_strings

# ---------------------------------------------------------------------------
# Patterns and constants
# ---------------------------------------------------------------------------


def _kw(keyword: str) -> str:
    """Regex for one decl keyword; a two-word keyword (`class abbrev`) allows
    any whitespace between its words."""
    return r"\s+".join(re.escape(w) for w in keyword.split())


# `?` and `!` are legal in a Lean identifier and are *common*
# (`Foo.getLast?_bar`, `Foo.find!`). Omitting them does not skip such a
# decl — it silently truncates its name at the `?`, inventing `Foo.getLast`
# and losing the real one. They can only appear inside a segment, never as its
# first character. A segment may also be guillemet-quoted (`«foo bar»`), and
# the name is dot-joined segments — segment-wise so a universe binder
# (`theorem foo.{u}`) ends the name instead of donating a trailing dot.
_NAME_SEG = r"(?:[\w'][\w'?!]*|«[^»]*»)"
DECL_RE = re.compile(
    r"^[ \t]*"
    + symbols.ATTR_PREFIX
    + symbols.MODIFIERS
    + r"(?:"
    + r"|".join(_kw(k) for k in sorted(symbols.DECL_KEYWORDS, key=len, reverse=True))
    + rf")\s+(?:\(\s*priority\s*:=[^)]*\)\s+)?({_NAME_SEG}(?:\.{_NAME_SEG})*)",
    re.MULTILINE,
)

# Status prefix on every decl a listing prints.
GLYPH_SORRY = "⊥"
GLYPH_AXIOM = "A"
GLYPH_TAINTED = "?"
GLYPH_CLEAN = "✓"

# Scope names share the decl segment grammar — `namespace «Prop»` exists in
# mathlib, and an `end «Prop»` whose name fails to parse reads as a *bare*
# `end`, silently closing the wrong scope.
_SCOPE_NAME = rf"{_NAME_SEG}(?:\.{_NAME_SEG})*"
NS_RE = re.compile(rf"^namespace\s+({_SCOPE_NAME})")
NS_END_RE = re.compile(rf"^end\b\s*({_SCOPE_NAME})?")
SECTION_RE = re.compile(r"^" + symbols.MODIFIERS + rf"section\b\s*({_SCOPE_NAME})?")

# Structural keywords that terminate a body but declare nothing dep_tree tracks.
_BODY_BREAKERS = [
    "example", "mutual", "open", "end", "namespace", "section", "variable",
    "#check", "#print", "#eval", "#decide",
]  # fmt: skip

TOP_LEVEL_RE = re.compile(
    r"^"
    + symbols.ATTR_PREFIX
    + symbols.MODIFIERS
    + r"(?:"
    + r"|".join(_kw(k) for k in sorted(symbols.DECL_KEYWORDS + _BODY_BREAKERS, key=len, reverse=True))
    + r")\b"
)

# Detects whether a matched decl is an `axiom` (an unproven assumption with no
# proof body). Matched against `DECL_RE`'s full match text (`^` + attrs +
# modifiers + keyword + name).
AXIOM_DECL_RE = re.compile(r"^" + symbols.ATTR_PREFIX + symbols.MODIFIERS + r"axiom\b")

# Classifies the *kind* of a decl reached without a text-level name reference
# (typeclass synthesis, constructor/projection elaboration).
INSTANCE_RE = re.compile(r"^" + symbols.ATTR_PREFIX + symbols.MODIFIERS + r"(?:instance|class|structure|inductive)\b")

# Attributes that make a decl reachable through elaboration machinery the text
# resolver cannot see: simp-set rewriting, the `ext`/`refl`/`aesop`/`grind`
# lemma pools, `match_pattern` unfolding, and `default_target` (a lake build
# entry point). A decl carrying one of these can be "used" with no name
# reference, so `dead` must treat it as a *suspect*, not a confirmed corpse.
# `expose` is excluded — it does not affect reachability. Matched
# against `DECL_RE`'s header, so tokens come only from the leading attribute
# block, never a proof body.
IMPLICIT_ATTR_RE = re.compile(r"@\[[^\]]*\b(simp|ext|refl|grind|aesop|match_pattern|default_target)\b")

# A `private` modifier on the decl header. Matched against `DECL_RE`'s full
# match text (attrs + modifiers + keyword + name), so a `private` inside a
# proof body never counts. Decides graph identity: see `Decl.uid`.
PRIVATE_RE = re.compile(r"(?<![\w])private\b")

# No dot before: `Proof.sorry` / `.sorry` reference an identifier that merely
# shares the name — the sorry term is always bare.
SORRY_RE = re.compile(r"(?<![\w.])sorry\b")

# An attribute line (`@[simp]`, `@[ext]`, ...) at the declaration's indentation
# or less terminates the prior
# decl's body even though the actual keyword (`theorem`/`def`/...) lives on
# the next line. Without this, `extract_decl_body` absorbs the attribute
# block into the previous decl and leaks attribute-arg identifiers into its
# ref set.
ATTR_LINE_RE = re.compile(r"^@\[")

# Anonymous instances (e.g. `instance (inst : T) : ...`) are NOT captured
# by DECL_RE — the regex expects a name token after `instance\s+` and an
# anonymous instance has `(` next. Only named decls are tracked; anonymous
# instances are reached via typeclass synthesis, so they're invisible to
# dep_tree by design.

# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------


@dataclass
class Decl:
    """One tracked declaration: the parse-time facts, plus the refs and
    analysis flags `build_graph` fills in."""

    name: str
    full_name: str
    file: str
    line: int
    has_sorry: bool
    refs: list[str] = field(default_factory=list)  # graph uids (`Decl.uid`)
    tainted: bool = False
    is_axiom: bool = False  # stated `axiom` — an unproven assumption
    implicit_attr: str = ""  # matched @[simp]/@[ext]/… token; '' if none
    implicit_kind: bool = False  # instance/class/structure/inductive
    loc: int = 1  # source lines spanned (trailing blanks trimmed)
    # True iff `dep-graph.json` vouched for this decl. False means `refs` is
    # empty for want of data, never that it is a guess — see `coverage`.
    refs_covered: bool = False
    is_private: bool = False  # `private` decl — Lean mangles its stored name,
    # so the same user-facing name can exist in many modules at once
    module: str = ""  # Lean module parsed from (`module_of` on the file)
    uid: str = ""  # graph identity: `full_name`, or `full_name@module`
    # when several decls share one user-facing name

    @property
    def implicit_reach(self) -> bool:
        """True when this decl can be used without any text-level name
        reference (simp-set/typeclass/elaboration), so `dead` cannot confirm
        it. Such rows are reported as *suspects*, not confirmed dead."""
        return bool(self.implicit_attr) or self.implicit_kind


@dataclass
class Graph:
    decls: list[Decl]
    # Keyed by `Decl.uid` (the user-facing name when it is unique,
    # `name@module` for a name several modules declare, e.g. `private`
    # copies). Every `Decl.refs` entry and `rev` key is such a uid.
    by_full: dict[str, Decl]
    rev: dict[str, list[str]] = field(default_factory=dict)
    # The elaborator-derived cone map this graph's refs were built against,
    # or None when no review-cone JSON was available. `None` (unknown) vs
    # `{}` (present but empty) lets callers word their degradation notes
    # correctly.
    cone: "dict[tuple[str, str], ConeEntry] | None" = None


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------


# One open `namespace` component or `section`; name is None for an anonymous
# section. A bare `end` may close only the latter — a namespace needs its name.
Scope = tuple[str, str | None]


def _scope_update(scopes: list[Scope], line: str) -> None:
    """Fold one source line into the active scope stack."""
    s = line.strip()
    if m := NS_RE.match(s):
        scopes.extend(("ns", part) for part in m.group(1).split("."))
    elif m := SECTION_RE.match(s):
        scopes.append(("sec", m.group(1)))
    elif m := NS_END_RE.match(s):
        ended = m.group(1)
        if not ended:
            if scopes and scopes[-1] == ("sec", None):
                scopes.pop()
        elif scopes and scopes[-1] == ("sec", ended):
            scopes.pop()
        else:
            # `end A.B` closes namespace components B, then A.
            for part in reversed(ended.split(".")):
                if scopes and scopes[-1] == ("ns", part):
                    scopes.pop()
                else:
                    break


def _ns_names(scopes: list[Scope]) -> list[str]:
    return [name for kind, name in scopes if kind == "ns" and name]


def namespace_stack_at(lines: list[str], decl_line: int) -> list[str]:
    """Active namespace stack just before `decl_line` (0-indexed)."""
    scopes: list[Scope] = []
    blank_lines = blank_comments_and_strings("".join(lines)).splitlines(keepends=True)
    for line in blank_lines[:decl_line]:
        _scope_update(scopes, line)
    return _ns_names(scopes)


def _decl_body_end(lines: Sequence[str], start: int, header_end: int | None = None) -> int:
    """Find the next command at this declaration's indentation or less.

    `lines` must already have comments and literals blanked.
    """
    if header_end is None:
        header_end = start
    indent = len(lines[start]) - len(lines[start].lstrip(" \t"))
    for i in range(header_end + 1, len(lines)):
        line = lines[i]
        stripped = line.lstrip(" \t")
        if len(line) - len(stripped) <= indent and (TOP_LEVEL_RE.match(stripped) or ATTR_LINE_RE.match(stripped)):
            return i
    return len(lines)


def extract_decl_body(lines: Sequence[str], start: int, header_end: int | None = None) -> str:
    """Body = `start` through the next command at the same or lesser indentation.

    An attribute line (``@[...]``) at that indentation also ends the body — it
    belongs to the *next* decl even though the keyword is on a later line.

    `header_end` (0-indexed) is the last line of *this* decl's own header —
    when the decl carries a leading attribute (e.g. ``@[simp]``
    on the line above ``theorem``), `DECL_RE` anchors `start` at the attribute,
    so the keyword line would otherwise be mistaken for the *next* decl and the
    body collapse to just the attribute. Lines ``start..header_end`` are always
    kept and the next-decl break-scan begins after them. Defaults to `start`
    (single-line header) for backward compatibility.
    """
    blank_lines = blank_comments_and_strings("".join(lines)).splitlines(keepends=True)
    return "".join(lines[start : _decl_body_end(blank_lines, start, header_end)])


def scan_file(path: Path, root: Path) -> list[Decl]:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return []

    lines = text.splitlines(keepends=True)
    rel = str(path.relative_to(root))
    out: list[Decl] = []

    # wrapped prose in a doc comment reads like a decl at column 0; blank it
    scan_text = blank_comments_and_strings(text)
    # Blanking preserves offsets, so these lines align with `lines` and give a
    # comment/string-free view of any body slice.
    blank_lines = scan_text.splitlines(keepends=True)
    # `DECL_RE` matches arrive in source order, so one forward walk over the
    # file maintains the namespace stack for all of them.
    scopes: list[Scope] = []
    ns_cursor = 0  # next line index to fold into `scopes`
    for m in DECL_RE.finditer(scan_text):
        name = m.group(1)
        line_no = scan_text[: m.start()].count("\n") + 1
        line_idx = line_no - 1
        # Last line of this decl's own header (attrs + modifiers + keyword +
        # name). When a leading `@[…]` attribute sits above the keyword, this
        # is below `line_idx`, so `extract_decl_body` keeps the keyword line
        # instead of mistaking it for the next decl.
        header_end_idx = scan_text[: m.end()].count("\n")
        while ns_cursor < line_idx:
            _scope_update(scopes, blank_lines[ns_cursor])
            ns_cursor += 1
        if name.startswith("_root_."):
            # `def _root_.Foo.bar` inside `namespace My.Module` declares
            # `Foo.bar`, not `My.Module._root_.Foo.bar`:
            # `_root_` escapes the namespace stack rather than joining it.
            name = name[len("_root_.") :]
            full_name = name
        else:
            full_name = ".".join([*_ns_names(scopes), name])
        end_idx = _decl_body_end(blank_lines, line_idx, header_end_idx)
        body_span = lines[line_idx:end_idx]
        while body_span and not body_span[-1].strip():
            body_span.pop()
        header = m.group(0).lstrip(" \t")
        out.append(
            Decl(
                name=name,
                full_name=full_name,
                file=rel,
                line=line_no,
                # An axiom has no proof body, so `sorry` can never appear in it;
                # it taints dependents via `is_axiom`, not `has_sorry`.
                has_sorry=bool(SORRY_RE.search("".join(blank_lines[line_idx:end_idx]))),
                is_axiom=bool(AXIOM_DECL_RE.match(header)),
                implicit_attr=(m2.group(1) if (m2 := IMPLICIT_ATTR_RE.search(header)) else ""),
                implicit_kind=bool(INSTANCE_RE.match(header)),
                loc=max(1, len(body_span)),
                is_private=bool(PRIVATE_RE.search(header)),
                module=module_of(rel),
            )
        )
    return out


def collect_decls(root: Path) -> list[Decl]:
    out: list[Decl] = []
    for lean_file in iter_lean_files(root):
        out.extend(scan_file(lean_file, root))
    return out


# ---------------------------------------------------------------------------
# Reference resolution — elaborator (preferred)
# ---------------------------------------------------------------------------


@dataclass
class ConeEntry:
    """One `project` entry of the dependency graph: where the elaborator found a
    decl, and everything it referenced (statement *and* proof)."""

    module: str  # Lean module name, e.g. "My.Module.Name"
    refs: list[str]  # fully-elaborated names, incl. Mathlib/core/instances


def load_cone(root: Path, path: Path | None = None) -> dict[tuple[str, str], ConeEntry] | None:
    """Read the elaborator's refs out of ``dep-graph.json`` in `root`, or from
    `path` to read data generated elsewhere, keyed by ``(name, module)`` — a
    `private` decl is reported under its user-facing name, so the same name can
    describe a different decl in another module. A missing or malformed file
    yields ``None`` (*no data*, never "these decls have no refs"), which
    `build_graph` reports rather than passing off as "no dependencies"."""
    path = path or root / DEP_GRAPH_NAME
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None

    refs: dict[tuple[str, str], ConeEntry] | None = None
    project = data.get("project")
    if isinstance(project, list):
        refs = {}
        for entry in project:
            if not isinstance(entry, dict):
                continue
            name, module, entry_refs = entry.get("name"), entry.get("module"), entry.get("refs")
            if not (isinstance(name, str) and isinstance(module, str) and isinstance(entry_refs, list)):
                continue
            refs.setdefault(
                (name, module),
                ConeEntry(module=module, refs=[r for r in entry_refs if isinstance(r, str)]),
            )

    return refs


def _cone_refs_for(
    decl: Decl,
    cone: dict[tuple[str, str], ConeEntry] | None,
    known: set[str],
) -> list[str] | None:
    """Elaborator-derived refs for `decl`, restricted to `known` (elaborated names
    also carry Mathlib and auto-generated instances, which are no decl here), or
    ``None`` when the data cannot vouch for `decl`: no map, or no entry under this
    name *in the module `decl` was parsed from*. An in-place body edit since
    generation is undetectable short of re-elaborating."""
    if cone is None:
        return None
    entry = cone.get((decl.full_name, module_of(decl.file)))
    if entry is None:
        return None
    out: list[str] = []
    seen: set[str] = set()
    for ref in entry.refs:
        if ref == decl.full_name or ref in seen or ref not in known:
            continue
        seen.add(ref)
        out.append(ref)
    return out


# ---------------------------------------------------------------------------
# Graph construction
# ---------------------------------------------------------------------------


def _inject_sorry_virtual(by_full: dict[str, Decl], decls: list[Decl]) -> None:
    """Virtual 'sorry' node so `direct`/`from` surface 'sorry' as an explicit
    dependency. Invisible to summary/orphan/dot/json (not added to `decls`)."""
    sorry_decl = Decl(
        name="sorry",
        full_name="sorry",
        file="<builtin>",
        line=0,
        has_sorry=True,
        uid="sorry",
    )
    by_full["sorry"] = sorry_decl
    for d in decls:
        if d.has_sorry and "sorry" not in d.refs:
            d.refs.append("sorry")


def _bfs(starts: Iterable[str], neighbors: Callable[[str], Iterable[str]]) -> set[str]:
    """Everything reachable from `starts` (inclusive) over `neighbors`."""
    visited: set[str] = set()
    q: deque[str] = deque(starts)
    while q:
        name = q.popleft()
        if name in visited:
            continue
        visited.add(name)
        q.extend(n for n in neighbors(name) if n not in visited)
    return visited


def _sorry_reachable(by_full: dict[str, Decl], rev: dict[str, list[str]]) -> set[str]:
    """Tainted = directly unproven (has `sorry` or is an `axiom`), or
    transitively depends on such a decl — i.e. reverse-reachable from the
    unproven seeds. Axioms are unproven assumptions, so they seed taint
    exactly like `sorry`."""
    seeds = [d.uid for d in by_full.values() if d.has_sorry or d.is_axiom]
    return _bfs(seeds, lambda n: rev.get(n, ()))


def _build_rev(by_full: dict[str, Decl]) -> dict[str, list[str]]:
    rev: dict[str, list[str]] = defaultdict(list)
    for d in by_full.values():
        for ref in d.refs:
            rev[ref].append(d.uid)
    return rev


def by_file_line(d: Decl) -> tuple[str, int]:
    """Source order: the sort key every listing of decls uses."""
    return (d.file, d.line)


def uncovered(g: Graph) -> tuple[list[Decl], list[Decl]]:
    """Decls the data does not vouch for, as ``(stale, uncompiled)`` sorted by
    file then line. *stale* — the module is described but the decl is not, so
    regenerate; *uncompiled* — the whole module is absent, because no library
    root imports it, so there is nothing to regenerate. Only `stale` is a
    defect."""
    if g.cone is None:
        return sorted(g.decls, key=by_file_line), []
    known_modules = {module for _, module in g.cone}
    stale: list[Decl] = []
    uncompiled: list[Decl] = []
    for d in g.decls:
        if d.refs_covered:
            continue
        (stale if module_of(d.file) in known_modules else uncompiled).append(d)
    return sorted(stale, key=by_file_line), sorted(uncompiled, key=by_file_line)


def _resolve_ref_uids(ref: str, referrer: Decl, by_name: dict[str, list[Decl]]) -> list[str]:
    """The graph node(s) a user-facing ref `ref` names, seen from `referrer`.

    The elaborator reports user-facing names, so a name declared in several
    modules (e.g. `private` copies) is ambiguous. A `private` decl is visible
    only inside its own module, hence: a same-module copy wins; otherwise only
    the public copies are reachable. The all-private-elsewhere fallback keeps
    the edge (conservative) rather than dropping a dependency."""
    candidates = by_name.get(ref, [])
    if len(candidates) <= 1:
        return [c.uid for c in candidates]
    same = [c.uid for c in candidates if c.module == referrer.module]
    if same:
        return same
    public = [c.uid for c in candidates if not c.is_private]
    return public or [c.uid for c in candidates]


def build_graph(root: Path, graph_path: Path | None = None) -> Graph:
    """Parse `root`'s .lean tree into a dep DAG: the tree supplies the nodes,
    `dep-graph.json` supplies every edge (or `graph_path`, to check `root`
    against data generated elsewhere). A decl the data misses gets no refs rather
    than guessed ones — `coverage` names it and `summary` warns."""
    decls = collect_decls(root)
    cone = load_cone(root, graph_path)
    known: set[str] = {d.full_name for d in decls}

    # Graph identity: the user-facing name while it is unique, `name@module`
    # once several modules declare it (`private` copies). No node is ever
    # evicted by a same-named one.
    counts = Counter(d.full_name for d in decls)
    for d in decls:
        d.uid = d.full_name if counts[d.full_name] == 1 else f"{d.full_name}@{d.module}"
    by_name: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        by_name[d.full_name].append(d)

    for d in decls:
        cone_refs = _cone_refs_for(d, cone, known)
        if cone_refs is not None:
            seen: set[str] = set()
            uids: list[str] = []
            for ref in cone_refs:
                for uid in _resolve_ref_uids(ref, d, by_name):
                    if uid == d.uid or uid in seen:
                        continue
                    seen.add(uid)
                    uids.append(uid)
            d.refs = uids
            d.refs_covered = True

    by_full: dict[str, Decl] = {d.uid: d for d in decls}
    _inject_sorry_virtual(by_full, decls)
    rev = _build_rev(by_full)
    for name in _sorry_reachable(by_full, rev):
        by_full[name].tainted = True
    return Graph(decls=decls, by_full=by_full, rev=rev, cone=cone)


# ---------------------------------------------------------------------------
# Graph queries
# ---------------------------------------------------------------------------


def transitive_deps(start: str, by_full: dict[str, Decl]) -> set[str]:
    return _bfs([start], lambda n: d.refs if (d := by_full.get(n)) else ())


def reverse_deps(start: str, rev: dict[str, list[str]]) -> set[str]:
    return _bfs([start], lambda n: rev.get(n, ()))


def used_split(g: Graph, roots: set[str]) -> tuple[list[Decl], list[Decl]]:
    """Forward-closure over `roots` = the used decls; the complement = unused.
    The virtual `sorry` node is excluded; both halves sorted by (file, line)."""
    used = _bfs(roots, lambda n: d.refs if (d := g.by_full.get(n)) else ())
    used.discard("sorry")  # virtual node, never a real decl
    real = [d for d in g.decls if d.uid != "sorry"]
    return (
        sorted((d for d in real if d.uid in used), key=by_file_line),
        sorted((d for d in real if d.uid not in used), key=by_file_line),
    )


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------


def fmt_decl_line(d: Decl, include_location: bool = True) -> str:
    if d.has_sorry:
        prefix = GLYPH_SORRY
        color_fn = red
    elif d.is_axiom:
        prefix = GLYPH_AXIOM
        color_fn = yellow
    elif d.tainted:
        prefix = GLYPH_TAINTED
        color_fn = yellow
    else:
        prefix = GLYPH_CLEAN
        color_fn = green

    shown = d.full_name
    if d.is_axiom:
        shown = f"{shown} (axiom)"
    line = f"  {color_fn(prefix)} {color_fn(shown)}"
    if include_location:
        line += f"  {dim(f'({d.file}:{d.line})')}"
    return line


# ---------------------------------------------------------------------------
# Subcommand output formatters
# ---------------------------------------------------------------------------


def _by_file(decls: list[Decl]) -> dict[str, list[Decl]]:
    out: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        out[d.file].append(d)
    return out


def _group_by_file(decls: list[Decl]) -> list[str]:
    by_file = _by_file(decls)
    lines: list[str] = []
    for f in sorted(by_file):
        lines.append(bold(f))
        for d in by_file[f]:
            lines.append(f"  {dim(str(d.line).rjust(5))}  {d.full_name}")
    return lines


def _count_by_file(decls: list[Decl]) -> list[str]:
    """One line per file, `<n>  <path>` — the unit the reader acts on, since
    both causes are cured a whole file at a time."""
    counts = Counter(d.file for d in decls)
    return [f"  {dim(str(counts[f]).rjust(4))}  {bold(f)}" for f in sorted(counts)]


def fmt_coverage(g: Graph, show_names: bool = False) -> str:
    """Whether `dep-graph.json` still describes the code, decl by decl. This is
    the staleness check — total coverage is what lets every other command drop
    its guesswork, so partial coverage must not pass unnoticed. Stale data is a
    defect, and rare, so it always names its decls; files no library imports are
    a standing condition this prints on every graph rebuild, so they are
    counted per file unless `show_names` — a wall of names buries the ask."""
    if g.cone is None:
        return red(f"✗ no {DEP_GRAPH_NAME}") + dim("  — every decl reports zero deps. Run: lean4-lens emit-refs")

    stale, uncompiled = uncovered(g)
    total = len(g.decls)
    lines: list[str] = []

    covered = total - len(stale) - len(uncompiled)
    if not stale and not uncompiled:
        return green(f"✓ all {total} declarations covered")
    head = red if stale else yellow
    lines.append(head(f"{'✗' if stale else '⚠'} {covered} of {total} declarations have dependency data"))

    if stale:
        lines += [
            "",
            red(f"{len(stale)} declarations are missing from {DEP_GRAPH_NAME} although their file"),
            red("is in it, so they look dependency-free and sorry-taint cannot reach"),
            red("them."),
            "",
            *_group_by_file(stale),
            "",
            dim("  Fix: if the source changed since the data was written, re-run"),
            dim("  `lean4-lens emit-refs`. If a re-run leaves the same names here, the data"),
            dim("  is current and the mismatch is in the name: Lean registered this decl"),
            dim("  under a name this parser did not derive from the source. Then read the"),
            dim("  entries this file lists for that module and correct whichever side is"),
            dim("  wrong — regenerating will not help."),
        ]
    if uncompiled:
        lines += [
            "",
            yellow(
                f"{len(uncompiled)} declarations sit in {len({d.file for d in uncompiled})} files "
                "that no library imports. Lean compiles"
            ),
            yellow("only the libraries, so it never reads these files and reports nothing"),
            yellow("about them: sorry-taint, reverse-deps and dead-code checks all skip"),
            yellow("them silently."),
            "",
            *(_group_by_file if show_names else _count_by_file)(uncompiled),
            "",
            dim("  Fix each file — either import it from a module a library already"),
            dim("  reaches, or delete it. Regenerating the data will not change this."),
        ]
        if not show_names:
            lines.append(dim("  Declaration names: dep_tree.py coverage --list"))
    return "\n".join(lines)


def _staleness_banner(g: Graph) -> list[str]:
    """A warning for every decl the data does not describe, so no count below it
    is read as complete. `coverage` prints the details."""
    if g.cone is None:
        return [red(f"⚠ no {DEP_GRAPH_NAME} — every decl below reports zero deps; taint is meaningless."), ""]
    stale, uncompiled = uncovered(g)
    out: list[str] = []
    if stale:
        out += [
            red(f"⚠ {len(stale)} declaration(s) are missing from {DEP_GRAPH_NAME} — it is stale."),
            red("  Counts below understate deps and taint. Run: lean4-lens emit-refs"),
        ]
    if uncompiled:
        out.append(
            yellow(f"⚠ {len(uncompiled)} declaration(s) sit in files no library imports — no deps. See: coverage")
        )
    return [*out, ""] if out else []


def fmt_summary(g: Graph) -> str:
    lines: list[str] = _staleness_banner(g)

    direct_sorry = [d for d in g.decls if d.has_sorry]
    axioms = [d for d in g.decls if d.is_axiom]
    indirect_sorry = [d for d in g.decls if d.tainted and not d.has_sorry and not d.is_axiom]
    clean = len(g.decls) - len(direct_sorry) - len(axioms) - len(indirect_sorry)

    lines.append(bold(f"Total declarations: {len(g.decls)}"))
    lines.append(green(f"  Clean:          {clean}"))
    lines.append(red(f"  Direct sorry:   {len(direct_sorry)}"))
    lines.append(yellow(f"  Axioms:         {len(axioms)}"))
    lines.append(yellow(f"  Sorry-tainted:  {len(indirect_sorry)}"))
    lines.append("")
    lines.append(bold(red("=== Declarations with direct sorry ===")))
    for d in sorted(direct_sorry, key=lambda x: x.full_name):
        lines.append(fmt_decl_line(d))
    lines.append("")
    lines.append(bold(yellow("=== Declarations stated as axioms ===")))
    for d in sorted(axioms, key=lambda x: x.full_name):
        lines.append(fmt_decl_line(d))
    lines.append("")
    lines.append(bold(yellow("=== Sorry-tainted declarations (indirect) ===")))
    for d in sorted(indirect_sorry, key=lambda x: x.full_name):
        lines.append(fmt_decl_line(d))
    return "\n".join(lines)


def fmt_from(start: str, g: Graph) -> str:
    deps = transitive_deps(start, g.by_full)
    return "\n".join(sorted(n for n in deps if n != start))


def fmt_direct(start: str, g: Graph) -> str:
    d = g.by_full[start]
    return "\n".join(sorted(set(d.refs)))


def fmt_rdeps(start: str, g: Graph) -> str:
    deps = reverse_deps(start, g.rev)
    names = sorted(n for n in deps if n != start)
    lines = [
        bold(f"What depends (transitively) on: {start}  ({len(names)} total)"),
        "",
    ]
    for name in names:
        d = g.by_full.get(name)
        loc = dim(f"({d.file}:{d.line})") if d else ""
        lines.append(f"  {cyan(name)}  {loc}")
    return "\n".join(lines)


def fmt_dag(g: Graph, included: set[str] | None = None) -> str:
    lines: list[str] = []
    for d in sorted(g.decls, key=lambda x: x.full_name):
        if included is not None and d.uid not in included:
            continue
        refs = sorted(set(d.refs) if included is None else (set(d.refs) & included))
        if refs:
            shown = f"{d.full_name} (axiom)" if d.is_axiom else d.full_name
            lines.append(f"{shown}: {' '.join(refs)}")
        else:
            lines.append(fmt_decl_line(d, include_location=False))
    return "\n".join(lines)


def fmt_sorry_paths(g: Graph) -> str:
    direct_sorry = [d for d in g.by_full.values() if d.has_sorry and d.uid != "sorry"]

    lines = [bold("=== Sorry-blocked dependency paths ==="), ""]
    entries: list[tuple[int, str]] = []
    for sd in sorted(direct_sorry, key=lambda x: (x.file, x.line)):
        rdeps = reverse_deps(sd.uid, g.rev)
        entries.append((len(rdeps) - 1, sd.full_name + f"  ({sd.file}:{sd.line})"))

    for count, desc in sorted(entries, key=lambda x: -x[0]):
        bar = "█" * min(count, 40)
        count_str = f"[{count:3d} blocked]"
        if count >= 20:
            lines.append(f"{red(count_str)} {red(desc)}")
        elif count >= 5:
            lines.append(f"{yellow(count_str)} {yellow(desc)}")
        else:
            lines.append(f"{dim(count_str)} {desc}")
        if bar:
            lines.append(f"              {dim(bar)}")
    return "\n".join(lines)


def fmt_orphans(g: Graph) -> str:
    referenced: set[str] = set()
    for d in g.decls:
        referenced.update(d.refs)
    orphans = [d for d in g.decls if d.uid not in referenced]

    main_theorems: list[Decl] = []
    sorry_orphans: list[Decl] = []
    instance_orphans: list[Decl] = []
    for d in orphans:
        if d.implicit_kind:
            instance_orphans.append(d)
        elif d.has_sorry or d.tainted:
            sorry_orphans.append(d)
        else:
            main_theorems.append(d)

    lines = [
        bold(f"=== Orphan analysis ({len(orphans)} unreferenced declarations) ==="),
        "",
    ]
    lines.append(bold(green(f"--- Main entry points / proved orphans ({len(main_theorems)}) ---")))
    for d in sorted(main_theorems, key=lambda x: x.full_name):
        lines.append(fmt_decl_line(d))
    lines.append("")
    lines.append(bold(yellow(f"--- Sorry-tainted orphans ({len(sorry_orphans)}) ---")))
    for d in sorted(sorry_orphans, key=lambda x: (not x.has_sorry, x.full_name)):
        lines.append(fmt_decl_line(d))
    lines.append("")
    lines.append(dim(f"--- Instances/structures ({len(instance_orphans)}) ---"))
    lines.append(dim(f"  ({len(instance_orphans)} entries, omitted — expected for typeclass resolution)"))
    return "\n".join(lines)


def fmt_dot(g: Graph, subgraph: str | None) -> str:
    if subgraph:
        included = transitive_deps(subgraph, g.by_full)
    else:
        included = {d.uid for d in g.decls}

    def node_id(name: str) -> str:
        return json.dumps(name, ensure_ascii=False)

    def short(d: Decl) -> str:
        return d.full_name.split(".")[-1]

    dot = ["digraph deps {", "  rankdir=LR;", "  node [shape=box fontsize=9];", ""]
    for d in g.decls:
        if d.uid not in included:
            continue
        color = "red" if d.has_sorry else "orange" if d.tainted else "lightblue"
        label = node_id(f"{short(d)}\n{d.file}:{d.line}")
        dot.append(f"  {node_id(d.uid)} [label={label} style=filled fillcolor={color}];")
    dot.append("")
    for d in g.decls:
        if d.uid not in included:
            continue
        for ref in d.refs:
            if ref in included and ref in g.by_full:
                dot.append(f"  {node_id(d.uid)} -> {node_id(ref)};")
    dot.append("}")
    return "\n".join(dot)


def fmt_json(g: Graph, included: set[str] | None = None) -> str:
    data = []
    for d in g.decls:
        if included is not None and d.uid not in included:
            continue
        refs = d.refs if included is None else sorted(set(d.refs) & included)
        data.append(
            {
                "name": d.full_name,
                "uid": d.uid,
                "module": d.module,
                "short_name": d.name,
                "file": d.file,
                "line": d.line,
                "has_sorry": d.has_sorry,
                "sorry_tainted": d.tainted,
                "refs": refs,
            }
        )
    return json.dumps(data, indent=2)


# ---------------------------------------------------------------------------
# reach: used/unused split from a set of root declarations
# ---------------------------------------------------------------------------


def match_uids(query: str, decls: Iterable[Decl]) -> list[str]:
    """Graph uids whose user-facing name matches `query`: exact uid, exact
    full name, or `.query` suffix on the full name. A name declared in several
    modules yields every copy's uid — the caller reports the ambiguity rather
    than picking one."""
    return [
        d.uid
        for d in decls
        if query == d.uid or query == d.full_name or d.full_name.endswith("." + query)
    ]


def reach_roots(g: Graph, names: list[str], root_files: list[str], root: Path) -> set[str]:
    """Resolve `reach`/`dead` roots: every decl in a `--root-file`, plus each
    NAME (exact full name or `.NAME` suffix — all matches).

    With no NAME and no `--root-file`, default to the roots listed in every
    `review-cone*.toml` (the review-cone generators). This is the natural
    keep-set for dead-code analysis: anything those roots don't transitively
    reach is a candidate."""
    roots: set[str] = set()
    norm = {rf.replace("\\", "/").lstrip("./") for rf in root_files}
    if norm:
        for d in g.decls:
            f = d.file
            if f in norm or any(f == rf or f.endswith("/" + rf) for rf in norm):
                roots.add(d.uid)
    if not names and not root_files:
        names = sorted(roots_from_configs(root))
        if names:
            print(
                f"note: no roots given — defaulting to {len(names)} root(s) from {CONE_CONFIG_GLOB}",
                file=sys.stderr,
            )
    for nm in names:
        matched = match_uids(nm, g.decls)
        if not matched:
            print(f"note: reach root '{nm}' matched no declaration", file=sys.stderr)
        roots.update(matched)
    return roots


def _row(d: Decl) -> dict[str, Any]:
    """The fields every JSONL row a command writes starts from."""
    return {
        "name": d.full_name,
        "short_name": d.name,
        "file": d.file,
        "line": d.line,
        "has_sorry": d.has_sorry,
    }


def fmt_reach(
    g: Graph,
    roots: set[str],
    out_used: Path | None,
    out_unused: Path | None,
) -> str:
    """Forward-closure over `roots` = the used set; its complement = unused.
    Writes JSONL to out_used / out_unused when given; always returns a summary."""
    used_decls, unused_decls = used_split(g, roots)

    def rec(d: Decl) -> dict[str, Any]:
        return {
            **_row(d),
            "sorry_tainted": d.tainted,
            "is_root": d.uid in roots,
            "n_refs": len(d.refs),
        }

    if out_used is not None:
        write_jsonl(out_used, (rec(d) for d in used_decls))
    if out_unused is not None:
        write_jsonl(out_unused, (rec(d) for d in unused_decls))

    byfile = Counter(d.file for d in unused_decls)
    lines = [
        bold(f"Reachability from {len(roots)} root(s)"),
        f"  total decls: {len(used_decls) + len(unused_decls)}",
        green(f"  used:        {len(used_decls)}"),
        yellow(f"  unused:      {len(unused_decls)}"),
    ]
    if out_used:
        lines.append(dim(f"  wrote {out_used} ({len(used_decls)} rows)"))
    if out_unused:
        lines.append(dim(f"  wrote {out_unused} ({len(unused_decls)} rows)"))
    lines.append("")
    lines.append(bold("Unused decls by file (top 25):"))
    for fn, c in byfile.most_common(25):
        lines.append(f"  {c:4d}  {fn}")
    return "\n".join(lines)


def _dead_closure(unused_names: set[str], rev: dict[str, list[str]]) -> set[str]:
    """Fixpoint dead set: an unused decl is dead iff every decl that references
    it is itself dead. Orphans (no referrers) seed the set; the closure then
    grows down referrer chains, so a helper used only by other dead decls is
    reported in the *same* pass (no manual delete-rebuild-rerun round-trip).

    A referrer of an unused decl is always itself unused (if a used decl called
    it, it would feed a root and be used), so the closure stays within
    `unused_names`. Unused cycles — each decl referenced only from within the
    cycle — are conservatively excluded: they cannot be proven dead."""
    dead = {n for n in unused_names if not rev.get(n)}
    changed = True
    while changed:
        changed = False
        for n in unused_names - dead:
            referrers = rev.get(n, [])
            if referrers and all(r in dead for r in referrers):
                dead.add(n)
                changed = True
    return dead


def _dead_flags(d: Decl) -> list[str]:
    """Short annotations for a dead row: what might make it non-dead, plus size."""
    flags: list[str] = []
    if d.has_sorry:
        flags.append("sorry")
    if d.implicit_attr:
        flags.append(f"@[{d.implicit_attr}]")
    if d.implicit_kind:
        flags.append("kind")
    return flags


def fmt_dead(
    g: Graph,
    roots: set[str],
    out: Path | None,
    out_used: Path | None,
    out_unused: Path | None,
    closure: bool = False,
) -> str:
    """Dead-code candidates: decls unreachable from `roots` that are also not
    referenced by any *live* decl.

    Default mode = unused ∩ globally-orphaned (conservative: a dead helper still
    called from another dead decl is withheld until its caller is removed).
    `closure=True` = the full removable set in one pass (`_dead_closure`).

    Rows are split into **confirmed** (plain theorem/def/lemma — safe to attic)
    and **suspects** (`@[simp]`/instance/… reachable via elaboration the text
    resolver can't see — verify before deleting), grouped by file, annotated
    with LOC span and reachability flags. Writes JSONL to `out` when given;
    always returns a summary."""
    used_decls, unused_decls = used_split(g, roots)
    unused_names = {d.uid for d in unused_decls}

    if closure:
        dead_names = _dead_closure(unused_names, g.rev)
    else:
        referenced: set[str] = set()
        for d in g.decls:
            referenced.update(d.refs)
        dead_names = {n for n in unused_names if n not in referenced}

    dead_decls = [d for d in unused_decls if d.uid in dead_names]
    confirmed = [d for d in dead_decls if not d.implicit_reach]
    suspects = [d for d in dead_decls if d.implicit_reach]

    def rec(d: Decl) -> dict[str, Any]:
        return {
            **_row(d),
            "loc": d.loc,
            "implicit_reach": d.implicit_reach,
            "implicit_attr": d.implicit_attr,
            "implicit_kind": d.implicit_kind,
        }

    if out is not None:
        write_jsonl(out, (rec(d) for d in dead_decls))  # confirmed + suspects; filter via implicit_reach
    if out_used is not None:
        write_jsonl(out_used, (rec(d) for d in used_decls))
    if out_unused is not None:
        write_jsonl(out_unused, (rec(d) for d in unused_decls))

    # ---- summary (cli-style: dim labels, coloured values) ----
    mode = "closure" if closure else "orphan"
    lines = ["", "  " + bold(cyan("DEAD CODE")), dim(f"  {mode} mode · {len(roots)} root(s)"), ""]
    lines.append(kv_s("total decls", str(len(used_decls) + len(unused_decls)), 16))
    lines.append(kv_s("unused", yellow(str(len(unused_decls))), 16))
    lines.append(kv_s("confirmed dead", red(str(len(confirmed))), 16))
    lines.append(kv_s("suspects", yellow(str(len(suspects))) + dim("  (elaboration-reachable — verify)"), 16))
    if out is not None:
        lines.append(kv_s("wrote", dim(f"{out} ({len(dead_decls)} rows)"), 16))

    def _emit(title: str, decls: list[Decl], name_color: Callable[[str], str]) -> None:
        if not decls:
            return
        lines.append("")
        lines.append("  " + bold(cyan(title)) + dim(f"  ({len(decls)})"))
        byfile = _by_file(decls)
        # Files with the most dead rows first — biggest cleanup wins on top.
        for fn in sorted(byfile, key=lambda f: (-len(byfile[f]), f)):
            group = byfile[fn]
            lines.append(f"  {dim(fn)} {dim(f'({len(group)})')}")
            for d in sorted(group, key=lambda d: d.line):
                loc = dim(f"{d.loc:>4}L")
                flags = _dead_flags(d)
                ftxt = dim("  " + " ".join(flags)) if flags else ""
                lines.append(f"    {dim(f'{d.line:>5}')}  {name_color(d.name)}  {loc}{ftxt}")

    _emit("Confirmed dead", confirmed, red)
    _emit("Suspects (elaboration-reachable)", suspects, yellow)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Query resolution
# ---------------------------------------------------------------------------


def resolve_or_die(query: str, g: Graph) -> str:
    """Return resolved uid, or print candidates / not-found and exit."""
    candidates = match_uids(query, g.decls)
    if not candidates:
        candidates = [uid for uid in g.by_full if query.lower() in uid.lower()]
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        print(f"Ambiguous name '{query}'. Candidates:")
        for c in sorted(candidates):
            print(f"  {c}")
        sys.exit(0)
    print(f"Declaration '{query}' not found.", file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _make_parser() -> argparse.ArgumentParser:
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument(
        "--project", type=Path, default=None, help="Lean project root (default: nearest lakefile from the CWD)."
    )

    # The root/output arguments `reach` and `dead` share.
    roots_common = argparse.ArgumentParser(add_help=False)
    roots_common.add_argument("name", nargs="*", help="Root declaration names.")
    roots_common.add_argument(
        "--root-file",
        action="append",
        default=[],
        metavar="PATH",
        help="Project-relative file whose decls are all roots (repeatable).",
    )
    roots_common.add_argument("--out-used", type=Path, default=None, help="Write used decls as JSONL here.")
    roots_common.add_argument("--out-unused", type=Path, default=None, help="Write unused decls as JSONL here.")

    p = argparse.ArgumentParser(
        prog="lean4-lens refs",
        description="Proof references between Lean declarations: gates, shows, exports.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )
    sub = p.add_subparsers(dest="cmd", required=True, metavar="check|show|export")

    # ---- check: data and health gates ----
    p_check = sub.add_parser("check", help="Data and health gates.")
    check_sub = p_check.add_subparsers(dest="check_cmd", required=True)
    p_dc = check_sub.add_parser(
        "data-complete", parents=[common], help=f"Check {DEP_GRAPH_NAME} covers every decl. Exits 1 if not."
    )
    p_dc.set_defaults(handler=_cmd_coverage)
    p_dc.add_argument(
        "--list", action="store_true", help="Name the decls in never-imported files (default: count per file)."
    )
    p_ts = check_sub.add_parser("taint-status", parents=[common], help="Counts + listings.")
    p_ts.set_defaults(handler=_cmd_summary)
    p_ts.add_argument("--fail-on-sorry", action="store_true", help="Exit 1 if any decl has a direct sorry.")
    p_ts.add_argument("--fail-on-axioms", action="store_true", help="Exit 1 if any decl is a stated axiom.")

    # ---- show: human questions ----
    p_show = sub.add_parser("show", help="Human questions over the graph.")
    show_sub = p_show.add_subparsers(dest="show_cmd", required=True)
    p_dd = show_sub.add_parser("direct-deps", parents=[common], help="Immediate refs of one declaration.")
    p_dd.set_defaults(handler=_cmd_direct)
    p_dd.add_argument("name")
    p_deps = show_sub.add_parser("deps", parents=[common], help="Transitive deps of one declaration as lean names.")
    p_deps.set_defaults(handler=_cmd_from)
    p_deps.add_argument("name")
    p_ub = show_sub.add_parser("used-by", parents=[common], help="Transitive reverse-deps of one declaration.")
    p_ub.set_defaults(handler=_cmd_rdeps)
    p_ub.add_argument("name")
    show_sub.add_parser(
        "reach", parents=[common, roots_common], help="Used/unused split from root decls/files."
    ).set_defaults(handler=_cmd_reach)
    p_sdead = show_sub.add_parser(
        "dead", parents=[common, roots_common], help="unused ∩ orphans — dead-code candidates."
    )
    p_sdead.set_defaults(handler=_cmd_dead)
    _add_dead_options(p_sdead)
    show_sub.add_parser(
        "sorry-impact", parents=[common], help="Direct-sorry decls ranked by blast radius."
    ).set_defaults(handler=_cmd_sorry_paths)

    # ---- export: machine output ----
    p_export = sub.add_parser("export", parents=[common], help="The whole graph for other tools.")
    p_export.set_defaults(handler=_cmd_export)
    p_export.add_argument(
        "--format",
        required=True,
        choices=("json", "dot", "text"),
        help="json (machines), dot (GraphViz), text (`Name: dep1 dep2 ...` lines).",
    )
    p_export.add_argument(
        "--from",
        dest="from_name",
        default=None,
        metavar="NAME",
        help="Limit the output to one declaration's cone (default: the full graph).",
    )

    # ---- hidden flat aliases (one release): every old name still resolves ----
    a_sum = sub.add_parser("summary", parents=[common], help=argparse.SUPPRESS)
    a_sum.set_defaults(handler=_cmd_summary)
    a_sum.add_argument("--fail-on-sorry", action="store_true", help=argparse.SUPPRESS)
    a_sum.add_argument("--fail-on-axioms", action="store_true", help=argparse.SUPPRESS)
    a_cov = sub.add_parser("coverage", parents=[common], help=argparse.SUPPRESS)
    a_cov.set_defaults(handler=_cmd_coverage)
    a_cov.add_argument("--list", action="store_true", help=argparse.SUPPRESS)
    a_from = sub.add_parser("from", parents=[common], help=argparse.SUPPRESS)
    a_from.set_defaults(handler=_cmd_from)
    a_from.add_argument("name")
    a_direct = sub.add_parser("direct", parents=[common], help=argparse.SUPPRESS)
    a_direct.set_defaults(handler=_cmd_direct)
    a_direct.add_argument("name")
    a_rdeps = sub.add_parser("rdeps", parents=[common], help=argparse.SUPPRESS)
    a_rdeps.set_defaults(handler=_cmd_rdeps)
    a_rdeps.add_argument("name")
    sub.add_parser("dag", parents=[common], help=argparse.SUPPRESS).set_defaults(handler=_cmd_dag)
    a_dot = sub.add_parser("dot", parents=[common], help=argparse.SUPPRESS)
    a_dot.set_defaults(handler=_cmd_dot)
    a_dot.add_argument("name", nargs="?", default=None)
    sub.add_parser("json", parents=[common], help=argparse.SUPPRESS).set_defaults(handler=_cmd_json)
    sub.add_parser("reach", parents=[common, roots_common], help=argparse.SUPPRESS).set_defaults(
        handler=_cmd_reach
    )
    sub.add_parser("sorry-paths", parents=[common], help=argparse.SUPPRESS).set_defaults(
        handler=_cmd_sorry_paths
    )
    sub.add_parser("orphans", parents=[common], help=argparse.SUPPRESS).set_defaults(handler=_cmd_orphans)
    a_dead = sub.add_parser("dead", parents=[common, roots_common], help=argparse.SUPPRESS)
    a_dead.set_defaults(handler=_cmd_dead)
    _add_dead_options(a_dead)

    # Hidden aliases stay resolvable but out of the help listing, so `--help`
    # shows the new surface only.
    sub._choices_actions = [a for a in sub._choices_actions if a.help != argparse.SUPPRESS]

    return p


def _add_dead_options(p_dead: argparse.ArgumentParser) -> None:
    """The options `show dead` and its flat `dead` alias share."""
    p_dead.add_argument(
        "--out",
        type=Path,
        default=Path("dead_candidates.jsonl"),
        help="Write dead-candidate decls as JSONL here (default: dead_candidates.jsonl).",
    )
    p_dead.add_argument("--no-out", action="store_true", help="Skip the dead-candidate JSONL file.")
    p_dead.add_argument(
        "--closure",
        action="store_true",
        help="Report the full dead closure (a decl is dead if every referrer is dead), "
        "not just globally-orphaned decls — the whole removable set in one pass.",
    )
    p_dead.add_argument(
        "--global",
        dest="global_",
        action="store_true",
        help="Ignore roots and list globally unreferenced decls (the old `orphans` question).",
    )


# Each subcommand is one handler returning its exit code; `_make_parser`
# attaches the right one to its subparser, so the command names are enumerated
# once rather than again in a dispatch cascade.
Handler = Callable[[argparse.Namespace, Graph, Path], int]


def _resolve_roots(args: argparse.Namespace, g: Graph, root: Path, cmd: str) -> set[str] | None:
    """The root set `reach` and `dead` share, or None when none resolved —
    an error, since reporting everything as unreachable would read as a clean
    sweep."""
    roots = reach_roots(g, args.name, args.root_file, root)
    if not roots:
        print(f"{cmd}: no roots resolved (pass NAME args and/or --root-file)", file=sys.stderr)
        return None
    return roots


def _cmd_summary(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_summary(g))
    # CI gates. Both facts are parse-time exact, so they hold even when
    # the dependency data is missing or stale.
    if args.fail_on_sorry and any(d.has_sorry for d in g.decls):
        return 1
    if args.fail_on_axioms and any(d.is_axiom for d in g.decls):
        return 1
    return 0


def _cmd_coverage(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_coverage(g, show_names=args.list))
    # Non-zero on stale data so a pipeline can gate on it. Uncompiled
    # modules are reported but do not fail: regenerating cannot fix them.
    return 1 if (g.cone is None or uncovered(g)[0]) else 0


def _cmd_json(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_json(g))
    return 0


def _cmd_export(args: argparse.Namespace, g: Graph, root: Path) -> int:
    """One export command for machines, GraphViz, and humans — the old `json`,
    `dot`, and `dag` outputs, optionally limited to one decl's cone."""
    if args.from_name is not None:
        start = resolve_or_die(args.from_name, g)
        included = transitive_deps(start, g.by_full)
    else:
        start = None
        included = None
    if args.format == "json":
        print(fmt_json(g, included))
    elif args.format == "dot":
        print(fmt_dot(g, subgraph=start))
    else:
        print(fmt_dag(g, included))
    return 0


def _cmd_reach(args: argparse.Namespace, g: Graph, root: Path) -> int:
    roots = _resolve_roots(args, g, root, "reach")
    if roots is None:
        return 1
    print(fmt_reach(g, roots, args.out_used, args.out_unused))
    return 0


def _cmd_dag(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_dag(g))
    return 0


def _cmd_orphans(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_orphans(g))
    return 0


def _cmd_dead(args: argparse.Namespace, g: Graph, root: Path) -> int:
    if args.global_:
        # The old `orphans` question: globally unreferenced decls, roots ignored.
        if args.name or args.root_file or args.closure:
            print("note: --global ignores roots and --closure", file=sys.stderr)
        print(fmt_orphans(g))
        return 0
    roots = _resolve_roots(args, g, root, "dead")
    if roots is None:
        return 1
    out = None if args.no_out else args.out
    print(fmt_dead(g, roots, out, args.out_used, args.out_unused, closure=args.closure))
    return 0


def _cmd_sorry_paths(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_sorry_paths(g))
    return 0


def _cmd_dot(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_dot(g, subgraph=resolve_or_die(args.name, g) if args.name else None))
    return 0


def _cmd_from(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_from(resolve_or_die(args.name, g), g))
    return 0


def _cmd_direct(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_direct(resolve_or_die(args.name, g), g))
    return 0


def _cmd_rdeps(args: argparse.Namespace, g: Graph, root: Path) -> int:
    print(fmt_rdeps(resolve_or_die(args.name, g), g))
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = _make_parser()
    args = parser.parse_args(argv)

    root = resolve_root_or_exit(args.project)
    g = build_graph(root)
    if not g.decls and next(iter_lean_files(root), None) is None:
        exit_no_lean_files(root)

    handler: Handler = args.handler
    return handler(args, g, root)
