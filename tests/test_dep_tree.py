"""Smoke tests for dep_tree (run via `uv run pytest`).

Two feeds into one seam — the emitted `dep-graph.json`:

* **Fast** (default, no Lean build): fixture data written into a temp dir →
  the tool → assert what it reports. Plain pytest functions, grouped by topic
  (blanking/sorry, namespace stack, decl parsing, build_graph end-to-end,
  parser edge cases, load_cone contract, scratch-dir skipping).
* **Slow** (a *built* Lean project): the real emitter runs against it and
  asserts what fixtures cannot — that coverage is total, and that a theorem's
  refs include a dep only its proof uses. One test class per project: the
  `tests/lean-v*` fixtures, one per pinned Lean toolchain, or whatever
  `LEANLENS_TEST_PROJECT` names instead. Unbuilt projects skip.

Coverage focus (load-bearing functions whose bugs corrupt every report):
    - blank_comments_and_strings + sorry detection (status accuracy)
    - namespace_stack_at (full_name resolution)
    - scan_file (decl names the elaborator would recognise)
    - build_graph + taint propagation (against a temp .lean tree)
    - regex / parser edge cases
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import TYPE_CHECKING, Any, ClassVar

import pytest

from lean4_lens import build_times as B
from lean4_lens import cone_config as C
from lean4_lens import dep_tree as D
from lean4_lens import heavy_tactics as H
from lean4_lens import project as P
from lean4_lens import review_cone as R
from lean4_lens import source as S

# ---------------------------------------------------------------------------
# Fixture helpers
# ---------------------------------------------------------------------------


def _ns_at(text: str, line_1based: int) -> list[str]:
    return D.namespace_stack_at(text.splitlines(keepends=True), line_1based - 1)


def _has_sorry(body: str) -> bool:
    """The sorry check as `scan_file` performs it: blank, then word-match."""
    return bool(D.SORRY_RE.search(S.blank_comments_and_strings(body)))


def _names_in(source: str) -> set[str]:
    """full_names dep_tree parses out of one .lean source text."""
    with tempfile.TemporaryDirectory() as td:
        root = Path(td)
        (root / "A.lean").write_text(source, encoding="utf-8")
        return {d.full_name for d in D.scan_file(root / "A.lean", root)}


def _cone(entries: Sequence[Mapping[str, object]], **extra: object) -> str:
    return json.dumps({"projectRoot": ".", "project": entries, **extra})


def _write_lean_tree(
    tmp: Path,
    files: dict[str, str],
    deps: dict[str, tuple[str, list[str]]] | None = None,
) -> Path:
    """Build a fake project root: ``{relpath: contents}``. Adds a sentinel
    ``lakefile.lean`` so the directory is a valid 'root'.

    `deps` writes the `dep-graph.json` the emitter would produce, as
    ``{full_name: (source_file, refs)}`` — the module is derived from the
    file, exactly as the real emitter's `module` field tracks it. Every
    edge in this graph comes from that file, so a tree without `deps` is
    a project whose data is missing, not one with no dependencies.

    Entries are written with ``kind: "theorem"`` on purpose: a theorem's
    refs are proof refs now, and must be used rather than rejected.
    """
    root = tmp / "proj"
    root.mkdir()
    (root / "lakefile.lean").write_text("-- sentinel\n", encoding="utf-8")
    for rel, body in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(body, encoding="utf-8")
    if deps is not None:
        project = [
            {"name": n, "module": f.removesuffix(".lean").replace("/", "."), "kind": "theorem", "refs": refs}
            for n, (f, refs) in deps.items()
        ]
        (root / P.DEP_GRAPH_NAME).write_text(_cone(project), encoding="utf-8")
    return root


# ---------------------------------------------------------------------------
# Comment/string blanking & sorry detection
# ---------------------------------------------------------------------------

# 11–17. blank_comments_and_strings removes the right things; the sorry
# check only fires on a real `sorry` token outside comments/strings. We
# check the *semantic* invariant — `sorry` is absent — not the exact
# whitespace.


def test_blanks_line_comments() -> None:
    assert "sorry" not in S.blank_comments_and_strings("x-- sorry\n")


def test_blanks_block_comments() -> None:
    assert "sorry" not in S.blank_comments_and_strings("x /- sorry -/ y")


def test_blanks_nested_block_comments() -> None:
    assert "sorry" not in S.blank_comments_and_strings("x /- /- sorry -/ -/  y")


def test_blanks_string_literals() -> None:
    assert "sorry" not in S.blank_comments_and_strings('x = "sorry"')


def test_handles_escaped_quote_in_string() -> None:
    assert "sorry" not in S.blank_comments_and_strings('x = "a\\"sorry"')


def test_sorry_in_body_is_detected() -> None:
    assert _has_sorry("theorem t : True := by sorry")


def test_sorry_inside_comment_is_ignored() -> None:
    assert not _has_sorry("theorem t : True := by -- sorry\n  trivial")


def test_sorry_inside_string_is_ignored() -> None:
    assert not _has_sorry('def s : String := "sorry"')


def test_sorry_foo_is_not_sorry_word_boundary() -> None:
    assert not _has_sorry("def sorryFoo : Nat := 0")


def test_dotted_sorry_ref_is_not_a_sorry() -> None:
    # A dotted name (`Proof.sorry`, `.sorry`) references a constructor that
    # happens to be called sorry (mathlib ITauto.lean) — the sorry *term* is
    # always bare. Matching it flags sorry-free decls and fails the CI gate.
    assert not _has_sorry("def f : Proof := Proof.sorry")
    assert not _has_sorry("def g : Proof := .sorry")
    assert _has_sorry("theorem t : True := sorry")


# ---------------------------------------------------------------------------
# namespace_stack_at
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("literal", ['\'"\'', r"'\"'", r"'\''", r"'\\'", r"'\n'", "'λ'"])
def test_character_literal_keeps_following_sorry_visible(tmp_path: Path, literal: str) -> None:
    root = _write_lean_tree(
        tmp_path,
        {"A.lean": f"def quote' : Char := {literal}\ntheorem unfinished : True := by sorry\n"},
        deps={"quote'": ("A.lean", []), "unfinished": ("A.lean", [])},
    )
    g = D.build_graph(root)
    assert [(d.full_name, d.line, d.has_sorry) for d in g.decls] == [
        ("quote'", 1, False), ("unfinished", 2, True),
    ]
    assert D.main(["check", "taint-status", "--project", str(root), "--fail-on-sorry"]) == 1


def test_apostrophes_in_identifiers_are_not_character_literals() -> None:
    source = "def f' (x' : Nat) := x'\ntheorem t' : f' 0 = 0 := rfl\n"
    assert S.blank_comments_and_strings(source) == source


@pytest.mark.parametrize("name", ["«'a'»", "«'\"'»", "«--»", "«/-»"])
def test_quoted_identifiers_preserve_literal_and_comment_delimiters(name: str) -> None:
    source = f"def {name} : Nat := 0\ntheorem good : {name} = 0 := rfl\n"
    assert S.blank_comments_and_strings(source) == source
    assert _names_in(source) == {name, "good"}


@pytest.mark.parametrize("indent", ["  ", "\t"])
def test_indented_declarations_keep_separate_bodies_and_refs(tmp_path: Path, indent: str) -> None:
    root = _write_lean_tree(
        tmp_path,
        {"A.lean": (
            "namespace P\n"
            f"{indent}theorem clean : True := by trivial\n"
            f"{indent}@[simp]\n"
            f"{indent}theorem unfinished : True := by\n"
            f"{indent}  sorry\n"
            f"{indent}theorem dependent : True := unfinished\n"
            "end P\n"
            "theorem outside : True := by trivial\n"
        )},
        deps={
            "P.clean": ("A.lean", []), "P.unfinished": ("A.lean", []),
            "P.dependent": ("A.lean", ["P.unfinished"]), "outside": ("A.lean", []),
        },
    )
    g = D.build_graph(root)
    assert [(d.full_name, d.line, d.has_sorry) for d in g.decls] == [
        ("P.clean", 2, False), ("P.unfinished", 3, True),
        ("P.dependent", 6, False), ("outside", 8, False),
    ]
    assert g.by_full["P.dependent"].refs == ["P.unfinished"]
    assert g.by_full["P.dependent"].tainted
    assert D.main(["check", "data-complete", "--project", str(root)]) == 0
    assert D.main(["check", "taint-status", "--project", str(root), "--fail-on-sorry"]) == 1
    # A present module with an omitted indented declaration must fail coverage.
    data_path = root / P.DEP_GRAPH_NAME
    data = json.loads(data_path.read_text())
    data["project"] = [d for d in data["project"] if d["name"] != "P.unfinished"]
    data_path.write_text(json.dumps(data))
    assert D.main(["check", "data-complete", "--project", str(root)]) == 1


@pytest.mark.parametrize("comment_line", ["example prose", "theorem fake : True := sorry", "@[simp]", "end P"])
def test_comment_keywords_do_not_truncate_sorry_proofs(tmp_path: Path, comment_line: str) -> None:
    root = _write_lean_tree(
        tmp_path,
        {"A.lean": (
            "namespace P\ntheorem unfinished : True := by\n"
            f"  /-\n{comment_line}\n/- nested comment -/\n  -/\n  sorry\n"
            "theorem clean : True := by trivial\nend P\n"
        )},
        deps={"P.unfinished": ("A.lean", []), "P.clean": ("A.lean", [])},
    )
    assert [(d.full_name, d.has_sorry) for d in D.build_graph(root).decls] == [
        ("P.unfinished", True), ("P.clean", False),
    ]
    assert D.main(["check", "taint-status", "--project", str(root), "--fail-on-sorry"]) == 1


def test_comment_namespaces_do_not_change_declaration_names(tmp_path: Path) -> None:
    source = (
        "/-\nnamespace Fake\n-/\nnamespace Real\n"
        "/-\nend Real\n/-\nnamespace NestedFake\n-/\n-/\n"
        "theorem clean : True := by\n  /- sorry -/\n  trivial\nend Real\n"
    )
    root = _write_lean_tree(tmp_path, {"A.lean": source}, deps={"Real.clean": ("A.lean", [])})
    assert [(d.full_name, d.has_sorry) for d in D.build_graph(root).decls] == [("Real.clean", False)]
    assert D.namespace_stack_at(source.splitlines(keepends=True), 10) == ["Real"]
    assert D.main(["check", "data-complete", "--project", str(root)]) == 0


def test_nested_namespace_stack() -> None:
    # 18. Stack tracks nested namespaces and respects `end <name>` / bare `end`.
    src = "namespace A\nnamespace B\ntheorem t := sorry\nend B\ntheorem u := sorry\nend A\n"
    assert _ns_at(src, 3) == ["A", "B"]
    assert _ns_at(src, 5) == ["A"]  # popped after end B
    assert _ns_at(src, 7) == []  # empty after end A


def test_bare_end_closes_section_not_namespace() -> None:
    # 19. A bare `end` can only close an anonymous `section` — a namespace
    # needs `end <name>`. Popping the namespace instead unqualifies every
    # decl below the section (verbatim mathlib NonUnitalSubalgebra.lean).
    src = "namespace S\nsection\ndef a : Nat := 0\nend\ndef b : Nat := 0\nend S\n"
    assert _names_in(src) == {"S.a", "S.b"}


def test_named_section_end_cannot_pop_namespace() -> None:
    # 19b. A `section` may share the enclosing namespace's name; its
    # `end <name>` closes the section, and only the next one the namespace.
    src = "namespace S\nsection S\ndef a : Nat := 0\nend S\ndef b : Nat := 0\nend S\ndef c : Nat := 0\n"
    assert _names_in(src) == {"S.a", "S.b", "c"}


def test_mutual_end_does_not_pop_namespace() -> None:
    # 19c. `mutual … end` closes with a bare `end` too; decls after the block
    # must stay inside the namespace.
    src = "namespace S\nmutual\ndef a : Nat := 0\ndef b : Nat := a\nend\ndef c : Nat := 0\nend S\n"
    assert "S.c" in _names_in(src)


# ---------------------------------------------------------------------------
# Decl parsing: names the elaborator would recognise
# ---------------------------------------------------------------------------


def test_root_escapes_the_namespace_stack() -> None:
    # 20. `_root_.X.y` inside `namespace N` declares `X.y`, NOT `N._root_.X.y`.
    # A wrong full_name is unmatchable against the elaborator's data, so the
    # decl silently loses every dep.
    assert _names_in("namespace CC\n\ndef _root_.BranchConfig.hubNbr : Nat :=\n  0\n\nend CC\n") == {
        "BranchConfig.hubNbr"
    }


def test_question_mark_is_part_of_identifier() -> None:
    # 21. `?`/`!` are legal *inside* a Lean identifier. Dropping them from the
    # name pattern does not skip the decl — it truncates its name, inventing
    # `G.getLast` and losing `G.getLast?_toPath`.
    assert _names_in("namespace G\n\ntheorem getLast?_toPath : True :=\n  trivial\n\nend G\n") == {"G.getLast?_toPath"}


def test_universe_binder_is_not_part_of_the_name() -> None:
    # 21b. `theorem foo.{u} : …` binds universe `u`; capturing `foo.` invents
    # a name with a trailing dot that no elaborator data can ever match.
    assert _names_in("theorem foo.{u} : True :=\n  trivial\n") == {"foo"}


def test_guillemet_name_is_captured() -> None:
    # 21c. `def «foo bar»` is a legal (French-quoted) identifier; the decl
    # must not be dropped.
    assert _names_in("namespace G\ndef «foo bar» : Nat :=\n  0\nend G\n") == {"G.«foo bar»"}


def test_guillemet_namespace_is_tracked() -> None:
    # 21d. `namespace «Prop» … end «Prop»` (mathlib Order/Atoms.lean): the
    # name must qualify decls, and its `end` must not read as a *bare* end —
    # that would silently close the enclosing anonymous section instead.
    src = "section\nnamespace «Prop»\ndef isAtom_iff : Nat := 0\nend «Prop»\nend\ndef tail : Nat := 0\n"
    assert _names_in(src) == {"«Prop».isAtom_iff", "tail"}


def test_wrapped_prose_in_doc_comment_is_not_a_decl() -> None:
    # 22. Prose in a doc comment reads like a decl once it wraps: `DECL_RE`
    # anchors at column 0, and wrapped prose puts a keyword there — verbatim
    # from Coloring/K3/DecisionTree.lean and FinGraph/Basic.lean. Parsing it
    # invents declarations (`reductions`, `keeps`) no data can ever cover.
    assert _names_in(
        "/-!\n# Doc\n\nClosure vocabulary (cells, constraint generators, vertex certificates,\n"
        "structure reductions): see `docs/proof-framework.md`.\n\nThe carrier gives `DecidableEq`, and the\n"
        "instance keeps the data computable.\n-/\n\n"
        "/-- A real one. -/\ndef real : Nat :=\n  0\n"
    ) == {"real"}


def test_line_numbers_survive_comment_blanking(tmp_path: Path) -> None:
    # 23. Blanking comments must preserve offsets, or every line number after
    # a doc comment is wrong.
    (tmp_path / "A.lean").write_text("/- a\nmulti\nline -/\ndef d : Nat :=\n  0\n", encoding="utf-8")
    scanned = D.scan_file(tmp_path / "A.lean", tmp_path)
    assert len(scanned) == 1
    assert scanned[0].line == 4


# ---------------------------------------------------------------------------
# build_graph end-to-end against a temp .lean tree
# ---------------------------------------------------------------------------


def test_build_graph_links_refs_and_propagates_taint(tmp_path: Path) -> None:
    # 24. build_graph parses across files, links refs from the emitted data,
    #     and propagates taint transitively. `mid`/`top` are theorems whose
    #     refs are *proof* refs — the dep the taint travels along appears
    #     nowhere in their statements, which is the whole point.
    root = _write_lean_tree(
        tmp_path,
        {
            "Base.lean": "namespace Base\ntheorem leaf : True :=\n  sorry\nend Base\n",
            "Mid.lean": "namespace Base\ntheorem mid : True :=\n  leaf\nend Base\n",
            "Top.lean": "namespace Base\ntheorem top : True :=\n  mid\nend Base\n",
        },
        deps={
            "Base.leaf": ("Base.lean", []),
            "Base.mid": ("Mid.lean", ["Base.leaf"]),
            "Base.top": ("Top.lean", ["Base.mid"]),
        },
    )
    g = D.build_graph(root)
    leaf = g.by_full.get("Base.leaf")
    mid = g.by_full.get("Base.mid")
    top = g.by_full.get("Base.top")
    # build_graph parses all files
    assert leaf is not None
    assert mid is not None
    assert top is not None
    # ref from mid → leaf resolved
    assert "Base.leaf" in mid.refs
    # taint propagates leaf → mid → top
    assert leaf.tainted
    assert mid.tainted
    assert top.tainted
    # theorem entries are covered, not rejected
    assert all(d.refs_covered for d in g.decls)


def test_no_dep_graph_means_no_guesses(tmp_path: Path) -> None:
    # 24a. No data ⇒ no edges, and *no guesses*. `top` textually names `mid`,
    #      which the deleted scanner would have matched; the graph must report
    #      nothing rather than invent an edge.
    root = _write_lean_tree(
        tmp_path,
        {
            "Top.lean": "namespace Base\ntheorem top : True :=\n  mid\nend Base\n"
            "namespace Base\ntheorem mid : True :=\n  trivial\nend Base\n"
        },
    )
    g = D.build_graph(root)
    assert g.by_full["Base.top"].refs == []  # no refs invented
    assert g.cone is None  # cone is None (unknown)


def test_configured_skip_dirs_are_honoured(tmp_path: Path) -> None:
    # 24b. build_graph honours `lean4-lens.toml` — a directory named there is
    #      not parsed.
    root = _write_lean_tree(
        tmp_path,
        {
            "Live.lean": "namespace P\ntheorem alive : True := sorry\nend P\n",
            "Old/Dead.lean": "namespace P\ntheorem dead : True := sorry\nend P\n",
        },
    )
    (root / "lean4-lens.toml").write_text('[scan]\nskip_dirs = ["Old"]\n', encoding="utf-8")
    g = D.build_graph(root)
    assert "P.alive" in g.by_full
    assert "P.dead" not in g.by_full
    # Without the config the same tree is fully scanned — the skip is the
    # project's choice, not this tool's.
    (root / "lean4-lens.toml").unlink()
    assert "P.dead" in D.build_graph(root).by_full


def test_lakefile_is_not_scanned(tmp_path: Path) -> None:
    # 24b2. `lakefile.lean` declares the build; its decls are not project code
    #       and no elaborator data can ever cover them.
    root = _write_lean_tree(tmp_path, {"Live.lean": "namespace P\ntheorem alive : True := trivial\nend P\n"})
    (root / "lakefile.lean").write_text('def osTag : String :=\n  "linux"\n', encoding="utf-8")
    g = D.build_graph(root)
    assert "osTag" not in g.by_full
    assert "P.alive" in g.by_full


def test_axiom_decls_seed_taint(tmp_path: Path) -> None:
    # 24b. build_graph detects `axiom` decls, marks them is_axiom, and
    #      treats them as taint sources: a sorry-free consumer of an axiom
    #      is tainted exactly as if it depended on a `sorry`.
    root = _write_lean_tree(
        tmp_path,
        {
            "Ax.lean": "namespace P\naxiom assumed : True\ntheorem uses : True :=\n  assumed\nend P\n",
        },
        deps={"P.assumed": ("Ax.lean", []), "P.uses": ("Ax.lean", ["P.assumed"])},
    )
    g = D.build_graph(root)
    ax = g.by_full.get("P.assumed")
    uses = g.by_full.get("P.uses")
    assert ax is not None  # axiom decl is scanned
    assert ax.is_axiom  # flagged is_axiom
    assert not ax.has_sorry  # axiom has no sorry
    assert uses is not None
    assert not uses.is_axiom  # consumer of axiom is non-axiom
    # axiom seeds taint (self + consumer)
    assert ax.tainted
    assert uses.tainted


def test_reachability_attributes_captured_at_parse_time(tmp_path: Path) -> None:
    # 24c. Reachability attributes / kinds / LOC span are captured at parse
    #      time so `dead` can flag elaboration-reachable decls as suspects.
    root = _write_lean_tree(
        tmp_path,
        {
            "Attr.lean": (
                "namespace P\n"
                "@[simp] theorem simped : True :=\n  trivial\n"
                "instance myInst : Inhabited Nat :=\n  ⟨0⟩\n"
                "theorem plain : True :=\n  trivial\nend P\n"
            ),
        },
    )
    g = D.build_graph(root)
    simped = g.by_full.get("P.simped")
    inst = g.by_full.get("P.myInst")
    plain = g.by_full.get("P.plain")
    assert simped is not None
    assert simped.implicit_attr == "simp"  # @[simp] captured as implicit_attr
    assert simped.implicit_reach  # @[simp] decl is implicit_reach
    assert inst is not None
    assert inst.implicit_kind  # instance flagged implicit_kind
    assert plain is not None
    assert not plain.implicit_reach  # plain theorem is not implicit_reach
    assert plain.implicit_attr == ""  # plain theorem has no attr tag
    assert plain.loc >= 1  # loc span is at least 1


def test_dead_closure_sweep_and_cycle() -> None:
    # 24d. `_dead_closure`: a helper used only by other dead decls is in the
    #      closure (A orphan → B → C all dead); an unused cycle is excluded.
    chain_rev = {"B": ["A"], "C": ["B"]}  # A orphan, B←A, C←B
    assert D._dead_closure({"A", "B", "C"}, chain_rev) == {"A", "B", "C"}
    cycle_rev = {"D": ["E"], "E": ["D"]}  # D↔E, referenced only within
    assert D._dead_closure({"D", "E"}, cycle_rev) == set()


# ---------------------------------------------------------------------------
# Latent parser-bug hunt
# Each block asserts what the *intended* behavior should be. Failures expose
# bugs that mishandle real Lean source patterns.
# ---------------------------------------------------------------------------

# A. blank_comments_and_strings edge cases.


def test_a1_unterminated_string_at_eof() -> None:
    # A1. Unterminated string at EOF must not crash and must not leak `sorry`.
    assert "sorry" not in S.blank_comments_and_strings('x = "sorry without close')


def test_a2_unterminated_block_comment_at_eof() -> None:
    # A2. Unterminated block comment at EOF must not crash.
    assert "sorry" not in S.blank_comments_and_strings("x /- sorry never closed")


def test_a3_real_sorry_after_escaped_quote_string() -> None:
    # A3. String containing escaped quote followed by real `sorry` outside string.
    assert "sorry" in S.blank_comments_and_strings('s = "a\\"b" ; theorem t := sorry')


def test_a4_bare_identifier_sorry_is_preserved() -> None:
    # A4. Lean character literal `'\\n'` — character literals are written with
    # single quotes in Lean. Today the function only handles double quotes; this
    # test documents current behavior and flags if the user wants char-literal
    # stripping too.
    #
    # We assert what *should* happen: a char literal can't be `'sorry'` in Lean
    # (multi-char), but generally the function should leave plain identifiers
    # alone. `sorry` here is a bare identifier from the function's POV.
    assert "sorry" in S.blank_comments_and_strings("c = 'sorry'")


# B. extract_decl_body — body extends until next column-0 top-level decl.


def test_b1_multiline_signature_stays_inside_body() -> None:
    # B1. Body with multi-line indented signature followed by next theorem.
    src = "theorem foo\n    (h : True)\n    : True := by\n  trivial\ntheorem bar : True := by trivial\n"
    body = D.extract_decl_body(src.splitlines(keepends=True), 0)
    assert "(h : True)" in body
    assert "bar" not in body


def test_b2_body_terminates_at_column0_end() -> None:
    # B2. Body terminates at next column-0 `end` (treated as top-level).
    src = "theorem foo : True := by\n  trivial\nend MyNS\n"
    body = D.extract_decl_body(src.splitlines(keepends=True), 0)
    assert "trivial" in body
    assert "end MyNS" not in body


# C. NS_RE edge cases.


# C1. Dotted namespace.
def test_c1_dotted_namespace_name_captured() -> None:
    m = D.NS_RE.match("namespace Foo.Bar")
    assert m is not None
    assert m.group(1) == "Foo.Bar"


def test_c2_namespace_name_before_trailing_comment() -> None:
    # C2. Namespace with trailing comment (rare but valid).
    m = D.NS_RE.match("namespace Foo -- nested under bar")
    assert m is not None
    assert m.group(1) == "Foo"


# D. DECL_RE / TOP_LEVEL_RE coverage.


def test_d1_multiline_attr_then_theorem() -> None:
    # D1. Multi-line attribute then theorem: `@[simp]\ntheorem foo`.
    m = D.DECL_RE.search("@[simp]\ntheorem foo : True := trivial\n")
    assert m is not None
    assert m.group(1) == "foo"


def test_d2_comma_separated_attributes() -> None:
    # D2. Comma-separated attributes: `@[simp, ext]`.
    m = D.DECL_RE.search("@[simp, ext]\ntheorem foo : True := trivial\n")
    assert m is not None
    assert m.group(1) == "foo"


def test_d3_noncomputable_abbrev_captured() -> None:
    # D3. `noncomputable abbrev` (listed in DECL_KEYWORDS) is captured.
    m = D.DECL_RE.search("noncomputable abbrev myAbbrev : Nat := 0\n")
    assert m is not None
    assert m.group(1) == "myAbbrev"


def test_d4_stacked_modifiers_captured() -> None:
    # D4. `private noncomputable def` — stacked modifiers via MODIFIERS prefix.
    m = D.DECL_RE.search("private noncomputable def foo : Nat := 0\n")
    assert m is not None
    assert m.group(1) == "foo"


def test_d4d_instance_priority_keeps_the_name() -> None:
    # D4d. `instance (priority := 100) foo : …` — the priority group sits
    # between keyword and name; skipping it drops the named decl. An
    # anonymous `instance (priority := 100) : …` must stay uncaptured.
    m = D.DECL_RE.search("instance (priority := 100) foo : Nat := 0\n")
    assert m is not None
    assert m.group(1) == "foo"
    assert D.DECL_RE.search("instance (priority := 100) : Nat := 0\n") is None


def test_d4e_meta_modifier_and_meta_section() -> None:
    # D4e. `meta def` (module system) — mathlib has ~250 meta decls; and an
    # untracked `meta section` leaves a stray bare `end` that eats a scope.
    m = D.DECL_RE.search("meta def foo : Nat := 0\n")
    assert m is not None
    assert m.group(1) == "foo"
    src = "namespace S\nmeta section\ndef a : Nat := 0\nend\ndef b : Nat := 0\nend S\n"
    assert _names_in(src) == {"S.a", "S.b"}


def test_d4c_class_abbrev_name_captured() -> None:
    # D4c. `class abbrev X` (mathlib AffineMonoid/Basic.lean) — `class` alone
    # must not swallow the keyword pair and report a decl named `abbrev`.
    m = D.DECL_RE.search("class abbrev IsAffineAddMonoid (M : Type*) : Prop :=\n")
    assert m is not None
    assert m.group(1) == "IsAffineAddMonoid"
    # `class inductive X` (mathlib CharP/Defs.lean) has the same shape.
    m = D.DECL_RE.search("class inductive ExpChar : Nat → Prop\n")
    assert m is not None
    assert m.group(1) == "ExpChar"


def test_d4b_all_lean_modifiers_captured() -> None:
    # D4b. Every decl-modifier keyword mathlib uses at column 0 — a missing
    # one silently drops the decl (123 `scoped instance`, 566 `nonrec`, …).
    for header in (
        "scoped instance foo : Nat := 0\n",
        "local instance foo : Nat := 0\n",
        "partial def foo : Nat := 0\n",
        "unsafe def foo : Nat := 0\n",
        "public theorem foo : True := trivial\n",
        "protected nonrec def foo : Nat := 0\n",
    ):
        m = D.DECL_RE.search(header)
        assert m is not None, header
        assert m.group(1) == "foo", header


def test_d5_top_level_re_matches_noncomputable_abbrev() -> None:
    # D5. TOP_LEVEL_RE must stop body extraction at `noncomputable abbrev` too,
    # not just `noncomputable def`.
    assert D.TOP_LEVEL_RE.match("noncomputable abbrev foo := 0") is not None


def test_d6_top_level_re_matches_mutual() -> None:
    # D6. TOP_LEVEL_RE stops at `mutual`. (Lean has `mutual` blocks; if they
    # aren't recognized, the prior decl's body extends through them.)
    assert D.TOP_LEVEL_RE.match("mutual") is not None or D.TOP_LEVEL_RE.match("mutual\n") is not None


# D7. TOP_LEVEL_RE stops at `example`.
def test_d7_top_level_re_matches_example() -> None:
    assert D.TOP_LEVEL_RE.match("example : True := trivial") is not None


def test_d8_top_level_re_matches_open() -> None:
    # D8. TOP_LEVEL_RE stops at `open`. Otherwise a long `open Foo Bar` block
    # becomes part of the prior decl's body.
    assert D.TOP_LEVEL_RE.match("open Foo Bar") is not None


# E. (was: text-scanner walk-back over field projections — `Foo.bar.baz`
# → `Foo.bar`, longest-prefix, paren-broken runs.) That resolver is gone;
# the elaborator reports `Foo.bar` directly, with no dotted run to unpick.


# ---- parser-bug hunt, batch 2 ----

# F. blank_comments_and_strings — doc comments and complex escapes.


def test_f1_doc_comment_blanked() -> None:
    # F1. Doc-comment block `/-- ... -/` (Lean's docstring) — same as `/- ... -/`.
    assert "sorry" not in S.blank_comments_and_strings("/-- sorry -/")


def test_f2_module_docstring_blanked() -> None:
    # F2. Module docstring `/-! ... -/`.
    assert "sorry" not in S.blank_comments_and_strings("/-! sorry -/")


def test_f3_backslash_only_string_then_real_sorry() -> None:
    # F3. String containing only an escaped backslash followed by a quote that
    # ends the string: `"\\\\"` in source = the two-char Python string `"\\"`
    # = a Lean string containing a literal backslash.
    assert "sorry" in S.blank_comments_and_strings('x = "\\\\" ; sorry')


# G. extract_decl_body — indented `end` and trailing decls.


def test_g1_indented_end_does_not_terminate_body() -> None:
    # G1. Decl whose proof contains an indented `end` (e.g. inside a structure
    # literal or `match ... end`). MUST NOT terminate the body — only column-0
    # top-level keywords do.
    src = (
        "theorem foo : True := by\n"
        "  have x := 0\n"
        "  end  -- not actually Lean but indented, should not stop body\n"
        "  trivial\n"
        "theorem bar : True := trivial\n"
    )
    body = D.extract_decl_body(src.splitlines(keepends=True), 0)
    assert "trivial" in body
    assert "theorem bar" not in body


def test_g2_last_decl_body_runs_to_eof() -> None:
    # G2. Decl is the last thing in the file — body runs to EOF.
    src = "theorem foo : True := by\n  trivial\n"
    body = D.extract_decl_body(src.splitlines(keepends=True), 0)
    assert "trivial" in body


def test_g3_column0_attr_line_terminates_prior_body() -> None:
    # G3. Column-0 `@[...]` line terminates the prior body: the attribute block
    # belongs to the *next* decl. Without ATTR_LINE_RE handling, identifiers
    # inside attribute args (rare but real) would leak into the prior decl's
    # ref set.
    src = "theorem foo : True := trivial\n@[simp]\ntheorem bar : True := trivial\n"
    body = D.extract_decl_body(src.splitlines(keepends=True), 0)
    assert "@[simp]" not in body
    assert "theorem bar" not in body


# H. DECL_RE — attribute parsing.


def test_h1_attribute_with_parenthesized_args() -> None:
    # H1. Attribute with arguments containing brackets: `@[simp (config := { })]`.
    # ATTR_PREFIX is `@\[[^\]]*\]` — bracket-class disallows `]`, so any nested
    # `]` in the attr arg list breaks the match. Mathlib uses such attributes.
    # (Documents behavior.)
    m = D.DECL_RE.search("@[simp (config := { skip := true })]\ntheorem foo : True := trivial\n")
    assert m is not None
    assert m.group(1) == "foo"


def test_h2_stacked_attrs_on_separate_lines() -> None:
    # H2. Stacked attributes on separate lines: `@[simp]\n@[ext]\ntheorem foo`.
    # ATTR_PREFIX is `(?:@\[[^\]]*\]\s*)*` — `*` for the group, `\s` matches `\n`,
    # so this should chain.
    m = D.DECL_RE.search("@[simp]\n@[ext]\ntheorem foo : True := trivial\n")
    assert m is not None
    assert m.group(1) == "foo"


def test_h3_h4_nested_bracket_attributes(tmp_path: Path) -> None:
    # H3 / H4. Attribute with nested square brackets: `@[simp [other_lemma]]`.
    # ATTR_PREFIX's `[^\]]*` only consumes up to the *first* `]`, so the
    # malformed attribute prefix-match fails. But DECL_RE is anchored
    # with re.MULTILINE, so the next line (`theorem foo`) matches the
    # keyword arm independently. End result: the decl is captured.
    for src in (
        "@[simp [other_lemma]]\ntheorem foo : True := trivial\n",  # H3: nested [brackets]
        "@[simp [other_lemma], ext]\ntheorem foo : True := trivial\n",  # H4: multi-arg + nested
    ):
        m = D.DECL_RE.search(src)
        assert m is not None, src
        assert m.group(1) == "foo", src
    # Belt-and-braces end-to-end: build_graph against a temp tree
    # containing the same decl confirms it lands in the graph.
    r = tmp_path / "proj"
    r.mkdir()
    (r / "lakefile.lean").write_text("-- sentinel\n", encoding="utf-8")
    (r / "F.lean").write_text(
        "namespace M\n@[simp [other_lemma]]\ntheorem foo : True :=\n  trivial\nend M\n",
        encoding="utf-8",
    )
    g = D.build_graph(r)
    assert "M.foo" in g.by_full


# I. (was: a trailing doc-comment's identifiers must not leak into the
# text scanner's refs.) The scanner is gone, so nothing reads a body for
# refs. Doc comments are still blanked before *decl* matching — case 22.

# J. (was: IDENT_RE tokenization. The text-matching ref scanner is gone
# and its identifier regex with it.)


def test_k8b_review_cone_is_not_the_dep_graph(tmp_path: Path) -> None:
    # K8b. The review documents' data must NEVER be read as dep edges: a
    # theorem's refs there are statement-only, so taint would go quiet. The
    # separation is by filename, so pin it.
    (tmp_path / "review-cone.json").write_text(
        json.dumps({"project": [{"name": "A.t", "module": "A", "kind": "theorem", "refs": ["A.stmt"]}]}),
        encoding="utf-8",
    )
    assert D.load_cone(tmp_path) is None


# ---------------------------------------------------------------------------
# N. every ref comes from the elaborator, and only from it
# ---------------------------------------------------------------------------
# Every call in the sample code is dot-notation on a LOCAL BINDER
# (`S.removeDead` where `S : Spin`). No regex can map that to
# `Pkg.removeDead` — `S` is a local, not a namespace — and the deleted
# scanner, walking the dotted prefix down to the bare binder `S`, found an
# unrelated global `Other.S` and linked to it. A fabricated dep is worse
# than a missing one: it corrupts the DAG, taint, and build order.

# A local binder `S`, an unrelated global `Other.S` the buggy prefix walk
# used to capture, and two real rules reached only via dot-notation.
_BINDER_TREE: dict[str, str] = {
    "Core.lean": "namespace Pkg\nstructure Spin where\n  q : Nat\nend Pkg\n",
    "Rules.lean": (
        "namespace Pkg\ndef removeDead (s : Spin) : Spin :=\n  s\ndef foldBare (s : Spin) : Spin :=\n  s\nend Pkg\n"
    ),
    "Step.lean": "namespace Pkg\ndef reduceStep (S : Spin) : Spin :=\n  S.removeDead.foldBare\nend Pkg\n",
    "Other.lean": "namespace Other\ndef S : Nat :=\n  0\nend Other\n",
}
_STEP_ENTRY: dict[str, object] = {
    "name": "Pkg.reduceStep",
    "module": "Step",
    "kind": "def",
    # As the elaborator writes it: fully qualified, and carrying core
    # names (`Nat`, `ite`) that have no source-level declaration here.
    "refs": ["Pkg.Spin", "Pkg.removeDead", "Pkg.foldBare", "Nat", "ite"],
}


def test_n0_local_binder_dot_notation_resolves(tmp_path: Path) -> None:
    # N0. The calibration case. Dot-notation on a local binder resolves, the
    # fabricated `Other.S` never appears, and core/Mathlib names are filtered
    # out (they have no decl here, so they must not become dep edges).
    root = _write_lean_tree(tmp_path, _BINDER_TREE)
    (root / P.DEP_GRAPH_NAME).write_text(_cone([_STEP_ENTRY]), encoding="utf-8")
    g = D.build_graph(root)
    step = g.by_full["Pkg.reduceStep"]
    # dot-notation on a local binder resolves
    assert "Pkg.removeDead" in step.refs
    assert "Pkg.foldBare" in step.refs
    # local binder does NOT resolve to a global decl
    assert "Other.S" not in step.refs
    # non-project names filtered out
    assert "Nat" not in step.refs
    assert "ite" not in step.refs
    # covered decls are flagged
    assert step.refs_covered


def test_n1_uncovered_decl_gets_no_refs(tmp_path: Path) -> None:
    # N1. No text fallback exists. `Pkg.removeDead` has no entry, so it gets
    # NO refs — the scanner would have guessed some. Reporting nothing is the
    # point: `coverage` names it, where a guess was silent.
    root = _write_lean_tree(tmp_path, _BINDER_TREE)
    (root / P.DEP_GRAPH_NAME).write_text(_cone([_STEP_ENTRY]), encoding="utf-8")
    g = D.build_graph(root)
    assert g.by_full["Pkg.removeDead"].refs == []  # no guesses
    assert not g.by_full["Pkg.removeDead"].refs_covered  # reported as uncovered


def test_n1b_coverage_splits_stale_from_uncompiled(tmp_path: Path) -> None:
    # N1b. `coverage` splits by cause, because the cures differ. A decl absent
    # from a module the data *does* describe is STALE — regenerate. A decl
    # whose whole module is absent was never compiled (no lean_lib root
    # imports it) — regenerating changes nothing, so it must not fail the gate
    # or every run cries wolf over an orphaned file.
    root = _write_lean_tree(
        tmp_path,
        {
            "Step.lean": "namespace Pkg\ndef covered : Nat :=\n  0\ndef vanished : Nat :=\n  0\nend Pkg\n",
            "Orphan.lean": "namespace Pkg\ndef never_built : Nat :=\n  0\nend Pkg\n",
        },
        # `Pkg.vanished` is missing though its module `Step` is described;
        # module `Orphan` is described nowhere.
        deps={"Pkg.covered": ("Step.lean", [])},
    )
    g = D.build_graph(root)
    stale, uncompiled = D.uncovered(g)
    assert [d.full_name for d in stale] == ["Pkg.vanished"]  # covered module ⇒ STALE
    assert [d.full_name for d in uncompiled] == ["Pkg.never_built"]  # absent module ⇒ UNCOMPILED
    assert "vanished" in D.fmt_coverage(g)  # coverage reports the stale one
    assert "stale" in D.fmt_summary(g)  # summary warns when stale


def test_n2_theorem_refs_are_proof_refs(tmp_path: Path) -> None:
    # N2. THE central claim. A theorem's refs are its PROOF's refs. `Pkg.bad`
    # appears nowhere in `uses_bad`'s statement; the old code rejected theorem
    # entries outright for that reason, which is exactly how sorry-taint went
    # quiet. Now the entry is used, and taint travels along a proof-only edge.
    root = _write_lean_tree(
        tmp_path,
        {"Thm.lean": ("namespace Pkg\ntheorem bad : True :=\n  sorry\ntheorem uses_bad : True :=\n  bad\nend Pkg\n")},
    )
    (root / P.DEP_GRAPH_NAME).write_text(
        _cone(
            [
                {"name": "Pkg.bad", "module": "Thm", "kind": "theorem", "refs": ["True"]},
                # A proof dep: `True` is the statement, `Pkg.bad` the proof.
                {"name": "Pkg.uses_bad", "module": "Thm", "kind": "theorem", "refs": ["True", "Pkg.bad"]},
            ]
        ),
        encoding="utf-8",
    )
    g = D.build_graph(root)
    assert g.by_full["Pkg.uses_bad"].refs_covered  # a theorem entry is USED, not rejected
    assert "Pkg.bad" in g.by_full["Pkg.uses_bad"].refs  # a proof-only dep is an edge
    assert g.by_full["Pkg.uses_bad"].tainted  # sorry-taint propagates through the proof


def test_n3_stale_module_entry_is_not_used(tmp_path: Path) -> None:
    # N3. Staleness/identity: an entry whose `module` no longer names the file
    # the decl was parsed from describes a *different* declaration (moved or
    # renamed), so it is not used. No refs, and reported — never a crash.
    root = _write_lean_tree(tmp_path, _BINDER_TREE)
    moved = dict(_STEP_ENTRY, module="SomeOther.Place")
    (root / P.DEP_GRAPH_NAME).write_text(_cone([moved]), encoding="utf-8")
    g = D.build_graph(root)
    step = g.by_full["Pkg.reduceStep"]
    assert not step.refs_covered  # module/file mismatch ⇒ not covered
    assert step.refs == []  # a stale entry contributes no refs


def test_n4_load_cone_none_vs_empty_contract(tmp_path: Path) -> None:
    # N4. load_cone's contract — None (unknown) vs {} (empty), so "no data"
    # is distinguishable from "no refs".
    assert D.load_cone(tmp_path) is None  # no dep graph ⇒ None (unknown, not empty)
    (tmp_path / P.DEP_GRAPH_NAME).write_text(
        _cone([{"name": "A.x", "module": "A", "kind": "def", "refs": ["A.y"]}]), encoding="utf-8"
    )
    cone_map = D.load_cone(tmp_path)
    assert cone_map is not None
    assert cone_map[("A.x", "A")].refs == ["A.y"]  # refs captured
    assert cone_map[("A.x", "A")].module == "A"  # module captured
    (tmp_path / P.DEP_GRAPH_NAME).write_text(json.dumps({"project": []}), encoding="utf-8")
    assert D.load_cone(tmp_path) == {}  # present-but-empty ⇒ {} (empty), not None
    (tmp_path / P.DEP_GRAPH_NAME).write_text(json.dumps({"other": {"A.x": "A"}}), encoding="utf-8")
    assert D.load_cone(tmp_path) is None  # data without a `project` array ⇒ None
    (tmp_path / P.DEP_GRAPH_NAME).write_text("{not json", encoding="utf-8")
    assert D.load_cone(tmp_path) is None  # malformed ⇒ None, not a crash


def test_n5_one_name_two_modules(tmp_path: Path) -> None:
    # N5. One name, two modules. A `private` theorem is reported under its
    # user-facing name, so a public decl elsewhere can carry the same name and
    # the graph then holds two entries for it. Keying the entries by name alone
    # kept whichever came first and left the other decl looking uncovered — a
    # "stale data" report that no regeneration could ever clear.
    root = _write_lean_tree(
        tmp_path,
        {
            "Pub.lean": "namespace Pkg\ntheorem twin : True :=\n  trivial\nend Pkg\n",
            "Priv.lean": (
                "namespace Pkg\ntheorem other : True :=\n  trivial\n"
                "private theorem twin : True :=\n  trivial\nend Pkg\n"
            ),
        },
    )
    (root / P.DEP_GRAPH_NAME).write_text(
        _cone(
            [
                {"name": "Pkg.twin", "module": "Pub", "kind": "theorem", "refs": ["True"]},
                # `Pkg.other` puts module `Priv` in the graph, so a missed
                # `Pkg.twin` there counts as stale data, not an unbuilt file.
                {"name": "Pkg.other", "module": "Priv", "kind": "theorem", "refs": ["True"]},
                {"name": "Pkg.twin", "module": "Priv", "kind": "theorem", "refs": ["True", "Pkg.other"]},
            ]
        ),
        encoding="utf-8",
    )
    g = D.build_graph(root)
    assert all(d.refs_covered for d in g.decls)  # both same-named decls are covered
    assert D.uncovered(g)[0] == []  # coverage reports no stale decls


def test_n6_duplicate_private_names_get_module_uids(tmp_path: Path) -> None:
    # N6. Two `private` copies of one name are two nodes, not a duplicate
    # warning: uids carry the module, each same-module user resolves to its
    # own copy (so sorry-taint stays inside the right copy), and a user
    # elsewhere resolves to the public copy only.
    root = _write_lean_tree(
        tmp_path,
        {
            "A.lean": (
                "namespace Pkg\nprivate theorem twin : True :=\n  trivial\n"
                "theorem usesA : True :=\n  twin\nend Pkg\n"
            ),
            "B.lean": (
                "namespace Pkg\nprivate theorem twin : True :=\n  sorry\n"
                "theorem usesB : True :=\n  twin\nend Pkg\n"
            ),
            "Pub.lean": "namespace Pkg\ntheorem twin : True :=\n  trivial\nend Pkg\n",
            "C.lean": "namespace Pkg\ntheorem usesC : True :=\n  twin\nend Pkg\n",
        },
    )
    (root / P.DEP_GRAPH_NAME).write_text(
        _cone(
            [
                {"name": "Pkg.twin", "module": "A", "kind": "theorem", "refs": ["True"]},
                {"name": "Pkg.usesA", "module": "A", "kind": "theorem", "refs": ["Pkg.twin"]},
                {"name": "Pkg.twin", "module": "B", "kind": "theorem", "refs": ["True"]},
                {"name": "Pkg.usesB", "module": "B", "kind": "theorem", "refs": ["Pkg.twin"]},
                {"name": "Pkg.twin", "module": "Pub", "kind": "theorem", "refs": ["True"]},
                {"name": "Pkg.usesC", "module": "C", "kind": "theorem", "refs": ["Pkg.twin"]},
            ]
        ),
        encoding="utf-8",
    )
    g = D.build_graph(root)
    assert {d.uid for d in g.decls if d.full_name == "Pkg.twin"} == {
        "Pkg.twin@A",
        "Pkg.twin@B",
        "Pkg.twin@Pub",
    }  # one node per copy — nothing evicted
    assert all(d.refs_covered for d in g.decls)
    assert D.uncovered(g)[0] == []
    assert g.by_full["Pkg.usesA"].refs == ["Pkg.twin@A"]  # same-module copy
    assert g.by_full["Pkg.usesB"].refs == ["Pkg.twin@B"]  # same-module copy
    assert g.by_full["Pkg.usesC"].refs == ["Pkg.twin@Pub"]  # private copies invisible elsewhere
    assert not g.by_full["Pkg.usesA"].tainted  # B's sorry stays in B's copy
    assert g.by_full["Pkg.usesB"].tainted


# ---------------------------------------------------------------------------
# O. `.scratch` is not part of the project
# ---------------------------------------------------------------------------
# `.scratch/<slug>/prototypes/` holds throwaway COPIES of live modules,
# re-declaring real names. Scanning them duplicated 19 real decls. The
# damage is now via identity: `by_full` is keyed by name, so a copy can
# evict the real decl, and the survivor's `file` then disagrees with the
# elaborator's `module` — costing the REAL decl every ref (see
# `_cone_refs_for`), and with them its taint.


def test_o1_scratch_prototypes_are_not_scanned(tmp_path: Path) -> None:
    root = _write_lean_tree(
        tmp_path,
        {
            "Live.lean": "namespace P\ndef allOnes : Nat :=\n  0\ndef user : Nat :=\n  allOnes\nend P\n",
            # A prototype copy: same decl re-declared, plus a BARE-namespace
            # `allOnes` whose leaf collides with the real `P.allOnes`.
            # `zz_` so it sorts AFTER Live.lean and would win the eviction.
            ".scratch/zz_topic/prototypes/Copy.lean": (
                "def allOnes : Nat :=\n  0\nnamespace P\ndef allOnes : Nat :=\n  sorry\nend P\n"
            ),
        },
        deps={"P.allOnes": ("Live.lean", []), "P.user": ("Live.lean", ["P.allOnes"])},
    )
    g = D.build_graph(root)
    assert all(not d.file.startswith(".scratch") for d in g.decls)  # .scratch decls not scanned
    # no duplicate node for a shadowed decl
    assert len([d for d in g.decls if d.full_name == "P.allOnes"]) == 1
    assert "allOnes" not in g.by_full  # the bare-namespace copy is gone
    # Teeth: were the copy scanned, `P.allOnes` would resolve to the
    # .scratch file, fail the module/file identity check, and lose its
    # data — silently, and with `P.user`'s edge to it still intact.
    assert g.by_full["P.allOnes"].refs_covered  # the real decl keeps its exact data
    assert "P.allOnes" in g.by_full["P.user"].refs  # shadowing does not delete a live ref
    # And the prototype's `sorry` must not taint the real decl.
    assert not g.by_full["P.allOnes"].tainted
    # legitimate decls are kept
    assert "P.user" in g.by_full
    assert "P.allOnes" in g.by_full


def test_o2_dot_dirs_skipped_without_configuration() -> None:
    # O2. Every dot-dir is skipped generically, so no project has to name
    #     `.scratch` (or `.lake`) in its config.
    assert P.ScanConfig().skips(Path(".scratch/A.lean"))
    assert not P.ScanConfig().skips(Path("Coloring/A.lean"))  # a plain dir is not skipped


def test_help_runs() -> None:
    """The usage docstring renders (catches a broken epilog/format)."""
    proc = subprocess.run(
        [sys.executable, "-m", "lean4_lens", "dep-tree", "dead", "--help"],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0
    assert "--closure" in proc.stdout


# ---------------------------------------------------------------------------
# CI gates: summary --fail-on-* and the empty-scan guard
# ---------------------------------------------------------------------------


def test_summary_fail_on_sorry_exits_1(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {"A.lean": "namespace P\ntheorem t : True :=\n  sorry\nend P\n"})
    assert D.main(["summary", "--project", str(root), "--fail-on-sorry"]) == 1


def test_summary_fail_on_axioms_exits_1(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {"A.lean": "namespace P\naxiom a : True\nend P\n"})
    assert D.main(["summary", "--project", str(root), "--fail-on-axioms"]) == 1


def test_summary_gates_pass_on_a_clean_tree(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {"A.lean": "namespace P\ntheorem t : True :=\n  trivial\nend P\n"})
    assert D.main(["summary", "--project", str(root), "--fail-on-sorry", "--fail-on-axioms"]) == 0


def test_summary_without_gates_only_reports(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {"A.lean": "namespace P\ntheorem t : True :=\n  sorry\nend P\n"})
    assert D.main(["summary", "--project", str(root)]) == 0


# A gate that scanned nothing must not pass as clean (the sentinel
# lakefile.lean is always skipped, so an empty tree scans zero files).
def test_dep_tree_exits_2_when_nothing_is_scanned(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {})
    with pytest.raises(SystemExit) as e:
        D.main(["summary", "--project", str(root)])
    assert e.value.code == 2


def test_heavy_tactics_exits_2_when_nothing_is_scanned(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {})
    with pytest.raises(SystemExit) as e:
        H.main(["--project", str(root)])
    assert e.value.code == 2


def test_files_without_decls_are_not_an_empty_scan(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {"A.lean": "import Foo\n"})
    assert D.main(["summary", "--project", str(root)]) == 0


# ---------------------------------------------------------------------------
# build-times: module discovery and the timing record
# ---------------------------------------------------------------------------

# `lake` is never invoked here: `discover_modules` is pure, and `time_one` is
# driven against a stub subprocess. What the real `lake` costs is the one thing
# these cannot assert; everything around it is testable without a toolchain.


def _lib_tree(tmp_path: Path, files: dict[str, str], lakefile: str = "") -> Path:
    root = _write_lean_tree(tmp_path, files)
    if lakefile:
        (root / P.CONFIG_NAME).write_text(lakefile, encoding="utf-8")
    return root


def test_discover_modules_takes_the_aggregator_and_its_directory(tmp_path: Path) -> None:
    root = _lib_tree(tmp_path, {"Lib.lean": "", "Lib/A.lean": "", "Lib/Sub/B.lean": "", "Other/C.lean": ""})
    assert [r.as_posix() for r in B.discover_modules(root, ["Lib"], [])] == [
        "Lib.lean",
        "Lib/A.lean",
        "Lib/Sub/B.lean",
    ]


def test_discover_modules_honours_the_scan_config(tmp_path: Path) -> None:
    """`lean4-lens.toml` decides what counts as project code here too, so a
    module the other tools ignore is not timed either."""
    root = _lib_tree(tmp_path, {"Lib/A.lean": "", "Lib/Old/B.lean": ""}, '[scan]\nskip_dirs = ["Old"]\n')
    assert [r.as_posix() for r in B.discover_modules(root, ["Lib"], [])] == ["Lib/A.lean"]


def test_discover_modules_excludes_named_directory_components(tmp_path: Path) -> None:
    root = _lib_tree(tmp_path, {"Lib/A.lean": "", "Lib/Draft/B.lean": ""})
    assert [r.as_posix() for r in B.discover_modules(root, ["Lib"], ["Draft"])] == ["Lib/A.lean"]


class _Proc:
    """Just the `subprocess.run` result fields `time_one` reads."""

    def __init__(self, returncode: int, stderr: str = "") -> None:
        self.returncode = returncode
        self.stdout = ""
        self.stderr = stderr


def test_time_one_reports_the_minimum_of_its_runs(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """The minimum, not the last or the mean: it is the least noisy estimate
    of what the module actually costs."""
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Proc(0))
    # start/end pairs, so the three runs measure 3.0s, 1.0s and 2.0s
    ticks = iter([0.0, 3.0, 10.0, 11.0, 20.0, 22.0])
    monkeypatch.setattr(time, "perf_counter", lambda: next(ticks))
    record = B.time_one(Path("Lib/A.lean"), tmp_path, runs=3)
    assert record["seconds"] == 1.0
    assert record["runs"] == 3
    assert record["module"] == "Lib.A"
    assert record["ok"] is True
    assert "error_tail" not in record


def test_time_one_stops_and_records_a_failing_module(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """A module that does not compile is recorded, not fatal — and is not
    retried, since it will not get faster."""
    calls = 0

    def fake_run(*_a: object, **_k: object) -> _Proc:
        nonlocal calls
        calls += 1
        return _Proc(1, stderr="error: unknown identifier 'foo'")

    monkeypatch.setattr(subprocess, "run", fake_run)
    record = B.time_one(Path("Lib/A.lean"), tmp_path, runs=3)
    assert calls == 1
    assert record["ok"] is False
    assert record["returncode"] == 1
    assert "unknown identifier" in record["error_tail"]


# ---------------------------------------------------------------------------
# Slow feed: the real emitter (opt-in)
# ---------------------------------------------------------------------------

# Which built Lean projects to run the emitter against. By default the fixture
# projects in this directory, one per pinned Lean toolchain (`tests/lean-v*`);
# LEANLENS_TEST_PROJECT points at a real project instead. Either way the project
# must already be built — `lake build` in it, which fetches its toolchain.
PROJECT_ENV = "LEANLENS_TEST_PROJECT"
FIXTURE_GLOB = "lean-v*"


def _projects() -> list[Path]:
    env = os.environ.get(PROJECT_ENV)
    if env:
        return [Path(env).resolve()]
    return sorted(d for d in Path(__file__).parent.glob(FIXTURE_GLOB) if P.has_lakefile(d))


def _is_built(project: Path) -> bool:
    """Whether the project has compiled modules. Older Lake versions put the
    `.olean` files straight into `.lake/build/lib`, newer ones into a `lean/`
    subdirectory of it, so look for the files rather than a fixed path."""
    return any((project / ".lake" / "build" / "lib").glob("**/*.olean"))


if TYPE_CHECKING:
    # `self.assert*` and `skipTest` come from the TestCase each generated
    # subclass mixes in; the mixin must not be one itself, or pytest would
    # collect it with no project set.
    class _MixinBase(unittest.TestCase): ...

else:

    class _MixinBase: ...


class _EmitterTests(_MixinBase):
    """The real emitter's output, asserted against one built Lean project —
    what fixture JSON cannot supply. Not a TestCase itself: one subclass per
    project is generated below.

    Each run costs a Lean import of the whole project, so it skips rather than
    fails when that project is not built.
    """

    project: ClassVar[Path]
    emitted: ClassVar[Path]
    tmp: ClassVar[tempfile.TemporaryDirectory[str]]

    @classmethod
    def _run_emitter(cls, out: Path, *, deps: bool, roots: Sequence[str] = ()) -> None:
        """Run the Lean emitter, writing JSON to `out`. Goes through the
        command's own code path, so a broken invocation fails here too."""
        libs = P.read_lib_names(cls.project)
        R.run_review_cone(cls.project, libs, list(roots), out, deps=deps)

    @classmethod
    def setUpClass(cls) -> None:
        if shutil.which("lake") is None:
            raise unittest.SkipTest("no `lake` on PATH")
        if not _is_built(cls.project):
            raise unittest.SkipTest(f"not built — run `lake build` in {cls.project}")
        cls.tmp = tempfile.TemporaryDirectory()
        cls.emitted = Path(cls.tmp.name) / "dep-graph.json"
        # No `except SystemExit: skip` here. The project is built (checked
        # above), so an emitter that will not run is this tool failing against
        # that Lean version — exactly what these tests exist to catch.
        cls._run_emitter(cls.emitted, deps=True)

    @classmethod
    def tearDownClass(cls) -> None:
        cls.tmp.cleanup()

    # Emitter runs and graph builds are expensive (a whole-project Lean import
    # / parse), so tests share one result per class run.
    _graph_cache: ClassVar[D.Graph | None] = None
    _cone_cache: ClassVar[dict[str, Any] | None] = None

    def _graph(self) -> D.Graph:
        """The project graph, built against freshly emitted data. Reads it in
        place: a test must never write over the project's own artifact."""
        cls = type(self)
        if cls._graph_cache is None:
            cls._graph_cache = D.build_graph(cls.project, self.emitted)
        return cls._graph_cache

    def _cone_data(self) -> dict[str, Any]:
        """The document's JSON for the project's own roots, or a skip when the
        project has no review-cone config to name them."""
        cls = type(self)
        if cls._cone_cache is None:
            configs = sorted(cls.project.glob(C.CONE_CONFIG_GLOB))
            if not configs:
                self.skipTest("the test project has no review-cone config to take roots from")
            cone = Path(self.tmp.name) / "cone.json"
            cls._run_emitter(cone, deps=False, roots=C.load_config(configs[0])["roots"])
            cls._cone_cache = json.loads(cone.read_text())
        return cls._cone_cache

    def _cone(self) -> list[dict[str, Any]]:
        project: list[dict[str, Any]] = self._cone_data()["project"]
        return project

    def test_coverage_is_total(self) -> None:
        """Every compiled project decl has data — the claim that let the text
        scanner be deleted, so it is enforced rather than assumed."""
        stale, _ = D.uncovered(self._graph())
        self.assertEqual([d.full_name for d in stale], [], "declarations missing from freshly emitted data")

    def test_theorem_refs_include_a_proof_only_dep(self) -> None:
        """A theorem's refs cover its proof, not just its statement — verified
        against the document's refs for the same theorem, which must lack it."""
        stmt = {e["name"]: set(e["refs"]) for e in self._cone() if e["kind"] == "theorem"}
        proof = {e["name"]: set(e["refs"]) for e in json.loads(self.emitted.read_text())["project"]}
        extra = {n: proof[n] - stmt[n] for n in stmt if n in proof}
        self.assertTrue(any(extra.values()), "no theorem gained a ref from its proof — is depMode wired up?")

    def test_cone_mode_stays_statement_only(self) -> None:
        """A theorem's document refs are what a reader must trust, so they must
        never exceed the refs its proof reports."""
        stmt = {e["name"]: set(e["refs"]) for e in self._cone() if e["kind"] == "theorem"}
        proof = {e["name"]: set(e["refs"]) for e in json.loads(self.emitted.read_text())["project"]}
        self.assertTrue(
            all(stmt[n] <= proof[n] for n in stmt if n in proof),
            "a theorem's document refs are not a subset of its dependency refs",
        )

    def test_review_cone_includes_private_dependencies(self) -> None:
        if not (self.project / "Fixture" / "Basic.lean").is_file():
            self.skipTest("requires the repository's Fixture declarations")
        out = Path(self.tmp.name) / "private-cone.json"
        self._run_emitter(out, deps=False, roots=["Fixture.double_x"])
        data = json.loads(out.read_text())
        decls = {d["name"]: d for d in data["project"]}
        self.assertIn("Fixture.scale", decls)
        self.assertIn("Fixture.scale", decls["Fixture.double"]["refs"])
        self.assertIn("Fixture.Point", decls["Fixture.scale"]["refs"])
        self.assertIn("Fixture.Point", decls)
        self.assertFalse(any("_private." in ref for d in decls.values() for ref in d["refs"]))

    def test_module_cone_preserves_locations_and_axioms(self) -> None:
        if not (self.project / "Fixture" / "Module.lean").is_file():
            self.skipTest("requires the module-system fixture")
        out = Path(self.tmp.name) / "module-cone.json"
        R.run_review_cone(self.project, P.read_lib_names(self.project),
                          ["Fixture.Module.clean", "Fixture.Module.usesExtra", "Fixture.Module.unfinished"],
                          out, imports=["Fixture.Module"])
        decls = {d["name"]: d for d in json.loads(out.read_text())["project"]}
        self.assertIn("Fixture.Module.offset", decls)
        self.assertEqual(decls["Fixture.Module.clean"]["status"], "verified")
        self.assertEqual(decls["Fixture.Module.usesExtra"]["status"], "tainted")
        self.assertIn("Fixture.Module.extra", decls["Fixture.Module.usesExtra"]["axioms"])
        self.assertEqual(decls["Fixture.Module.unfinished"]["status"], "sorry")
        for decl in decls.values():
            self.assertGreater(decl["startLine"], 0, decl["name"])
            self.assertGreaterEqual(decl["endLine"], decl["startLine"], decl["name"])

    def test_inductive_kinds_match_their_source_keyword(self) -> None:
        """A structure/class/inductive is labeled by its own keyword — the
        review document prints the label, so an `inductive` must not say
        "structure"."""
        sources: dict[str, list[str]] = {}
        bad: list[str] = []
        for e in json.loads(self.emitted.read_text())["project"]:
            kind = e["kind"]
            if kind not in ("structure", "class", "inductive") or e["startLine"] <= 0:
                continue
            if e["module"] not in sources:
                path = self.project / P.module_path(e["module"])
                sources[e["module"]] = path.read_text(encoding="utf-8").splitlines()
            block = "\n".join(sources[e["module"]][e["startLine"] - 1 : e["endLine"]])
            if not re.search(rf"\b{kind}\b", block):
                bad.append(f"{e['name']} ({kind})")
        self.assertEqual(bad, [], "kind label absent from the decl's own source lines")

    # Synthesized companions doc-gen4 has no page for: primitive/auxiliary
    # recursors, noConfusion, equation-compiler matchers, sizeOf_spec lemmas.
    _SYNTH_RE = re.compile(
        r"\.(rec|recOn|casesOn|brecOn|binductionOn|below|ibelow|ndrec"
        r"|noConfusion|noConfusionType|match_\d+|sizeOf_spec)$"
    )

    def test_mathlib_list_has_no_synthesized_companions(self) -> None:
        """Every mathlib entry is a doc-linkable declaration: a synthesized
        companion (e.g. `Eq.ndrec`, `And.casesOn`, `List.foo.match_1`) has no
        mathlib4_docs entry, so the emitter must report its parent instead."""
        bad = [d["name"] for d in self._cone_data()["mathlib"] if self._SYNTH_RE.search(d["name"])]
        self.assertEqual(bad, [], "synthesized companions leaked into the mathlib list")

    def test_taint_does_not_shrink(self) -> None:
        """Every decl tainted under the project's committed data stays tainted
        under fresh data. A shrinking taint set reports proofs clean that are not."""
        if not (self.project / P.DEP_GRAPH_NAME).is_file():
            self.skipTest("no committed dep-graph.json to compare against")
        before = {d.full_name for d in D.build_graph(self.project).decls if d.tainted}
        after = {d.full_name for d in self._graph().decls if d.tainted}
        self.assertEqual(before - after, set(), "declarations lost their taint")


# ---------------------------------------------------------------------------
# P. Self-explanatory dep surface: emit-refs/refs with check/show/export
# ---------------------------------------------------------------------------
# New names resolve, old flat names stay as aliases, export formats equal the
# old outputs, `show dead --global` equals `orphans`, and the exit codes hold:
# stale/missing data fail with 1, an empty scan exits 2. One seam only: the
# reader main with a fake project root fed by fixture JSON data.


def _small_tree(tmp_path: Path) -> Path:
    return _write_lean_tree(
        tmp_path,
        {
            "A.lean": (
                "namespace P\ntheorem leaf : True :=\n  sorry\n"
                "theorem mid : True :=\n  leaf\ntheorem top : True :=\n  mid\n"
                "theorem lone : True :=\n  trivial\nend P\n"
            ),
        },
        deps={
            "P.leaf": ("A.lean", []),
            "P.mid": ("A.lean", ["P.leaf"]),
            "P.top": ("A.lean", ["P.mid"]),
            "P.lone": ("A.lean", []),
        },
    )


def _run(argv: list[str], capsys: pytest.CaptureFixture[str]) -> tuple[int, str]:
    capsys.readouterr()
    code = D.main(argv)
    return code, capsys.readouterr().out


def test_p1_check_data_complete_passes_on_full_cover(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    code, out = _run(["check", "data-complete", "--project", str(root)], capsys)
    assert code == 0
    assert "4 declarations covered" in out


def test_p2_check_taint_status_reports_counts(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    code, out = _run(["check", "taint-status", "--project", str(root)], capsys)
    assert code == 0
    assert "Direct sorry:   1" in out
    assert "Sorry-tainted:  2" in out
    code, _ = _run(["check", "taint-status", "--project", str(root), "--fail-on-sorry"], capsys)
    assert code == 1


def test_p3_show_single_decl_queries(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    code, out = _run(["show", "direct-deps", "P.mid", "--project", str(root)], capsys)
    assert code == 0
    assert "P.leaf" in out
    code, out = _run(["show", "deps", "P.top", "--project", str(root)], capsys)
    assert code == 0
    assert "P.leaf" in out and "P.mid" in out
    code, out = _run(["show", "used-by", "P.leaf", "--project", str(root)], capsys)
    assert code == 0
    assert "P.top" in out


def test_p4_show_whole_graph_queries(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    assert _run(["show", "reach", "P.top", "--project", str(root)], capsys)[0] == 0
    assert _run(["show", "dead", "P.top", "--project", str(root), "--no-out"], capsys)[0] == 0
    code, out = _run(["show", "sorry-impact", "--project", str(root)], capsys)
    assert code == 0
    assert "P.leaf" in out


def test_p5_export_formats_resolve(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    for fmt in ("json", "dot", "text"):
        assert _run(["export", "--format", fmt, "--project", str(root)], capsys)[0] == 0


def test_p6_old_flat_aliases_still_resolve(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    assert _run(["summary", "--project", str(root)], capsys)[0] == 0
    assert _run(["coverage", "--project", str(root)], capsys)[0] == 0
    assert _run(["from", "P.top", "--project", str(root)], capsys)[0] == 0
    assert _run(["direct", "P.mid", "--project", str(root)], capsys)[0] == 0
    assert _run(["rdeps", "P.leaf", "--project", str(root)], capsys)[0] == 0
    assert _run(["dag", "--project", str(root)], capsys)[0] == 0
    assert _run(["dot", "--project", str(root)], capsys)[0] == 0
    assert _run(["json", "--project", str(root)], capsys)[0] == 0
    assert _run(["reach", "P.top", "--project", str(root)], capsys)[0] == 0
    assert _run(["dead", "P.top", "--project", str(root), "--no-out"], capsys)[0] == 0
    assert _run(["sorry-paths", "--project", str(root)], capsys)[0] == 0
    assert _run(["orphans", "--project", str(root)], capsys)[0] == 0


def test_p7_export_equals_old_outputs(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    _, old_dag = _run(["dag", "--project", str(root)], capsys)
    _, new_text = _run(["export", "--format", "text", "--project", str(root)], capsys)
    assert new_text == old_dag
    _, old_dot = _run(["dot", "--project", str(root)], capsys)
    _, new_dot = _run(["export", "--format", "dot", "--project", str(root)], capsys)
    assert new_dot == old_dot
    _, old_json = _run(["json", "--project", str(root)], capsys)
    _, new_json = _run(["export", "--format", "json", "--project", str(root)], capsys)
    assert json.loads(new_json) == json.loads(old_json)


def test_p8_dead_global_equals_orphans(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    _, old = _run(["orphans", "--project", str(root)], capsys)
    _, new = _run(["show", "dead", "--global", "--project", str(root), "--no-out"], capsys)
    assert new == old


def test_p9_stale_data_fails_data_complete(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _write_lean_tree(
        tmp_path,
        {"A.lean": "namespace P\ntheorem a : True :=\n  trivial\ntheorem b : True :=\n  trivial\nend P\n"},
        deps={"P.a": ("A.lean", [])},
    )
    assert _run(["check", "data-complete", "--project", str(root)], capsys)[0] == 1


def test_p10_missing_data_file_fails_data_complete(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _write_lean_tree(
        tmp_path, {"A.lean": "namespace P\ntheorem a : True :=\n  trivial\nend P\n"}
    )
    assert _run(["check", "data-complete", "--project", str(root)], capsys)[0] == 1


def test_p11_zero_files_exits_2_on_new_names(tmp_path: Path) -> None:
    root = _write_lean_tree(tmp_path, {})
    with pytest.raises(SystemExit) as e:
        D.main(["check", "data-complete", "--project", str(root)])
    assert e.value.code == 2
    with pytest.raises(SystemExit) as e2:
        D.main(["export", "--format", "json", "--project", str(root)])
    assert e2.value.code == 2


def test_p12_top_level_aliases_share_code_paths(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    from lean4_lens.main import COMMANDS
    from lean4_lens.main import main as top_main

    assert set(("emit-refs", "refs", "dep-graph", "dep-tree")) <= set(COMMANDS)
    # Writer contract: one code path, so the JSON shape cannot drift by name.
    assert COMMANDS["emit-refs"][0] is COMMANDS["dep-graph"][0]
    assert COMMANDS["refs"][0] is COMMANDS["dep-tree"][0]
    root = _small_tree(tmp_path)
    capsys.readouterr()
    assert top_main(["refs", "check", "data-complete", "--project", str(root)]) == 0
    capsys.readouterr()
    assert top_main(["dep-tree", "coverage", "--project", str(root)]) == 0


def test_p13_export_from_limits_to_cone(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _small_tree(tmp_path)
    _, out = _run(["export", "--format", "text", "--from", "P.top", "--project", str(root)], capsys)
    assert "P.top" in out
    assert "P.lone" not in out
    _, old_dot = _run(["dot", "P.top", "--project", str(root)], capsys)
    _, new_dot = _run(["export", "--format", "dot", "--from", "P.top", "--project", str(root)], capsys)
    assert new_dot == old_dot


def test_dot_export_preserves_distinct_names(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _write_lean_tree(
        tmp_path,
        {"A.lean": "def A.b : Nat := 0\ndef A_b : Nat := A.b\n"},
        deps={"A.b": ("A.lean", []), "A_b": ("A.lean", ["A.b"])},
    )
    code, out = _run(["export", "--format", "dot", "--project", str(root)], capsys)
    assert code == 0
    assert '"A.b" [label=' in out
    assert '"A_b" [label=' in out
    assert '"A_b" -> "A.b";' in out
    assert '"A_b" -> "A_b";' not in out


def test_dot_export_escapes_quoted_identifiers(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    root = _write_lean_tree(
        tmp_path,
        {"A.lean": 'def «a\\b» : Nat := 0\n'},
        deps={"«a\\b»": ("A.lean", [])},
    )
    code, out = _run(["export", "--format", "dot", "--project", str(root)], capsys)
    assert code == 0
    assert '"«a\\\\b»" [label="«a\\\\b»\\nA.lean:1"' in out


# One TestCase per project, so a failure names the Lean version it came from.
for _project in _projects():
    _name = "TestEmitter_" + re.sub(r"\W", "_", _project.name)
    globals()[_name] = type(_name, (_EmitterTests, unittest.TestCase), {"project": _project})


if __name__ == "__main__":
    unittest.main()
