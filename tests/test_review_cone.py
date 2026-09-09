import json
import re
from html import unescape
from pathlib import Path

import pytest

from lean4_lens import cone_config as C
from lean4_lens import review_cone as R
from lean4_lens.review_cone import ConeDecl, LinkCtx, build_indexes, linkify


@pytest.mark.parametrize("left,right", [("⌊", "⌋₊"), ("⌈", "⌉₊"), ("⌊", "⌋"), ("⌈", "⌉")])
@pytest.mark.parametrize("term", ["lowerTimeScale", "lowerTimeScale Δ φ"])
def test_rounding_notation_links(left: str, right: str, term: str) -> None:
    name = "FiniteTemporalGraph.lowerTimeScale"
    idx = build_indexes([ConeDecl.from_json({"name": name})], [], {})
    ctx = LinkCtx(idx, "FiniteTemporalGraph.lowerSteps", "lowerSteps", {"lowerTimeScale": name}, {})
    source = f"def lowerSteps (Δ : ℕ) (φ : ℝ) : ℕ∞ := {left}{term}{right}"
    result = linkify(source, ctx)
    link = '<a class="proj" href="#d-FiniteTemporalGraph_46lowerTimeScale">lowerTimeScale</a>'
    expected = source.replace("lowerSteps", '<strong class="self">lowerSteps</strong>').replace("lowerTimeScale", link)
    assert result == expected


@pytest.mark.parametrize(
    "config_out,cli_out",
    [(None, None), ("docs/config.html", None), ("docs/config.html", "cli.html")],
)
def test_review_documents_use_config_names_and_output_overrides(
    tmp_path: Path,
    config_out: str | None,
    cli_out: str | None,
) -> None:
    (tmp_path / "lakefile.toml").write_text('name = "fixture"\n')
    data_path = tmp_path / "input.json"
    data_path.write_text(json.dumps({"project": [], "mathlib": [], "fieldOf": {}}))
    outputs: list[Path] = []
    for stem in ["review-cone", "review-cone-other"]:
        config = tmp_path / f"{stem}.toml"
        config.write_text(
            f'title = "{stem}"\n'
            + (f'out = "{config_out}"\n' if config_out else "")
            + '[[section]]\ntitle = "Results"\ndecls = []\n'
        )
        args = ["--project", str(tmp_path), "--json", str(data_path), "--config", str(config)]
        if cli_out:
            args.extend(["--out", str(tmp_path / cli_out)])
        assert R.main(args) == 0
        output = tmp_path / (cli_out or config_out or f"{stem}.html")
        assert output.is_file()
        assert f"<title>Lean 4 formalization of {stem}</title>" in output.read_text()
        outputs.append(output)
    if config_out is None and cli_out is None:
        assert outputs[0] != outputs[1]
        assert "<title>Lean 4 formalization of review-cone</title>" in outputs[0].read_text()


def _render_fixture(tmp_path: Path, config_body: str, n_decls: int = 0) -> str:
    """Render a minimal document from `config_body` and return its HTML."""
    (tmp_path / "lakefile.toml").write_text('name = "fixture"\n')
    names = [f"Fixture.thm{i}" for i in range(n_decls)]
    data_path = tmp_path / "input.json"
    data_path.write_text(
        json.dumps(
            {
                "project": [{"name": n, "kind": "theorem", "status": "verified"} for n in names],
                "mathlib": [],
                "fieldOf": {},
            }
        )
    )
    decls = ", ".join(f'"{n}"' for n in names)
    config = tmp_path / "review-cone.toml"
    config.write_text(config_body + f'\n[[section]]\ntitle = "Results"\ndecls = [{decls}]\n')
    out = tmp_path / "out.html"
    args = ["--project", str(tmp_path), "--json", str(data_path), "--config", str(config), "--out", str(out)]
    assert R.main(args) == 0
    return out.read_text()


def test_info_panel_renders_only_when_configured(tmp_path: Path) -> None:
    url = "https://anonymous.4open.science/r/temporal-conductance/"
    html = _render_fixture(
        tmp_path,
        f'title = "Fixture"\n[info]\nheading = "Full source code"\ntext = "Sources live at"\nurl = "{url}"\n',
    )
    assert html.count("vpanel info") == 1
    assert "Full source code" in html
    assert f"<a class='proj' href='{url}' target='_blank' rel='noopener'>{url}</a>" in html


def test_document_without_info_table_has_no_info_panel(tmp_path: Path) -> None:
    assert "vpanel info" not in _render_fixture(tmp_path, 'title = "Fixture"\n')


def test_heading_names_the_document_a_formalization(tmp_path: Path) -> None:
    html = _render_fixture(tmp_path, 'title = "Fixture"\n')
    assert "<title>Lean 4 formalization of Fixture</title>" in html
    assert "<h1>Lean 4 formalization of <em>Fixture</em></h1>" in html


def test_intro_spells_out_how_much_the_document_covers(tmp_path: Path) -> None:
    html = _render_fixture(tmp_path, 'title = "Fixture"\n', n_decls=3)
    assert "The three results are grouped into sections" in html
    assert "remaining <em>supporting declarations</em>" not in html


@pytest.mark.parametrize(
    "info,message",
    [
        ('info = "https://example.com"', "`[info]` must be a table"),
        ('[info]\nheading = "Sources"', "`info.url` is required"),
        ("[info]\nurl = 3", "`info.url` is required"),
        ('[info]\nurl = "https://example.com"\nheading = ""', "`info.heading` must be a non-empty string"),
    ],
)
def test_malformed_info_table_is_rejected(tmp_path: Path, info: str, message: str) -> None:
    config = tmp_path / "review-cone.toml"
    config.write_text(f'{info}\n[[section]]\ntitle = "Results"\ndecls = []\n')
    with pytest.raises(C.ConfigError) as excinfo:
        C.load_config(config)
    assert message in str(excinfo.value.code)


def _ctx(defined: str, project: list[str], field_of: dict[str, str] | None = None, src: str = "") -> LinkCtx:
    idx = build_indexes([ConeDecl.from_json({"name": n}) for n in project], [], field_of or {})
    return LinkCtx(idx, defined, defined.split(".")[-1], {}, {}, R.local_binders(src))


def test_local_binder_is_not_linked_to_a_decl_sharing_its_name() -> None:
    src = "structure FiniteSimpleGraph (Vertex : Type*) where\n  fintypeVertex : Fintype Vertex"
    field_of = {"TemporalGraph.Vertex": "TemporalGraph"}
    ctx = _ctx("FiniteSimpleGraph", ["FiniteSimpleGraph", "TemporalGraph"], field_of, src)
    assert "href" not in linkify(src, ctx).replace('<strong class="self">FiniteSimpleGraph</strong>', "")


def test_field_projection_links_to_its_structure_and_says_so() -> None:
    src = "def vertexCount (G : TemporalGraph) : ℕ := Fintype.card G.Vertex"
    ctx = _ctx("TemporalGraph.vertexCount", ["TemporalGraph"], {"TemporalGraph.Vertex": "TemporalGraph"}, src)
    link = '<a class="proj field" href="#d-TemporalGraph" title="field of TemporalGraph">Vertex</a>'
    assert link in linkify(src, ctx)


def test_head_of_dotted_chain_links_when_it_is_a_project_decl() -> None:
    src = "theorem t (S : Sys) : (independentSetAlgorithm.tree S).numLeaves ≤ S.graph.card"
    ctx = _ctx("Ns.t", ["Ns.independentSetAlgorithm", "Ns.Sys", "Ns.Sys.graph"], src=src)
    out = linkify(src, ctx)
    assert '<a class="proj" href="#d-Ns_46independentSetAlgorithm">independentSetAlgorithm</a>.tree' in out
    assert "S.<a" in out and ">S</a>" not in out


def test_universe_annotated_name_is_linked() -> None:
    src = "theorem t : ∃ G : TemporalGraph.{0}, True"
    ctx = _ctx("TemporalGraph.t", ["TemporalGraph"], src=src)
    assert '<a class="proj" href="#d-TemporalGraph">TemporalGraph</a>.{0}' in linkify(src, ctx)


def test_document_has_top_navigation(tmp_path: Path) -> None:
    html = _render_fixture(tmp_path, 'title = "Fixture"\n', n_decls=2)
    assert "<nav class='contents' aria-label='Contents'>" in html
    assert "<meta name='viewport'" in html and "<html lang='en'>" in html
    assert "kernel-checked" in html and "requires human review" in html
    assert "href='#'" not in html


def test_title_and_summary_lead_the_entry(tmp_path: Path) -> None:
    (tmp_path / "lakefile.toml").write_text('name = "fixture"\n')
    data_path = tmp_path / "input.json"
    decl = {"name": "Fixture.main", "kind": "theorem", "status": "verified"}
    data_path.write_text(json.dumps({"project": [decl], "mathlib": [], "fieldOf": {}}))
    config = tmp_path / "review-cone.toml"
    config.write_text(
        '[[section]]\ntitle = "Main"\ndecls = ["Fixture.main"]\n'
        '[section.titles]\n"Fixture.main" = "The main bound"\n'
        '[section.summaries]\n"Fixture.main" = "Every graph mixes fast."\n'
    )
    out = tmp_path / "out.html"
    args = ["--project", str(tmp_path), "--json", str(data_path), "--config", str(config), "--out", str(out)]
    assert R.main(args) == 0
    html = out.read_text()
    assert "<article class='entry entry-pair' id='d-Fixture_46main'>" in html
    assert "<h3>The main bound</h3>" in html
    assert "class='subhead'" not in html
    assert "class='badge verified'" not in html
    assert "<p class='summary'>Every graph mixes fast.</p>" in html


def test_type_ascription_is_not_mistaken_for_a_binder() -> None:
    src = "def t (G : TemporalGraph) : ℕ := (vertexCount G : ℕ) + (Δ : ℝ)^2"
    ctx = _ctx("Fixture.t", ["TemporalGraph", "TemporalGraph.vertexCount"], src=src)
    assert '<a class="proj" href="#d-TemporalGraph_46vertexCount">vertexCount</a>' in linkify(src, ctx)
    assert R.local_binders(src) == {"G"}


def test_document_without_contents_has_no_sidebar_grid(tmp_path: Path) -> None:
    html = _render_fixture(tmp_path, 'title = "Fixture"\n[support]\ntoc = false\n')
    assert "class='layout'" not in html and "<nav" not in html and "<main>" in html


@pytest.mark.parametrize("version,modern", [("4.19.0", False), ("4.30.0", False),
                                           ("4.32.2", True), ("4.33.1", True), ("4.34.0-rc1", True)])
def test_emitter_keeps_legacy_support_and_private_dependency_mode(tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
                                                                    version: str, modern: bool) -> None:
    monkeypatch.delenv("ELAN_TOOLCHAIN", raising=False)
    (tmp_path / "lean-toolchain").write_text(f"leanprover/lean4:v{version}\n")
    cone = R.emitter_source(tmp_path, deps=False)
    deps = R.emitter_source(tmp_path, deps=True)
    assert cone.startswith("module\n") == modern
    assert ("else .server)" in cone) == modern
    assert "else .server)" not in deps
    assert deps.startswith("module\n") == modern


def test_custom_or_overridden_toolchain_is_conservative(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.33.1")
    monkeypatch.setenv("ELAN_TOOLCHAIN", "custom-toolchain")
    assert not R.module_emitter_supported(tmp_path)
    monkeypatch.setenv("ELAN_TOOLCHAIN", "leanprover/lean4:v4.19.0")
    assert not R.module_emitter_supported(tmp_path)


@pytest.mark.parametrize("imports", ['[]', '"Fixture"', '[1]', '[""]', '["A,B"]'])
def test_config_rejects_invalid_imports(tmp_path: Path, imports: str) -> None:
    cfg = tmp_path / "review-cone.toml"
    cfg.write_text(f'imports = {imports}\n[[section]]\ntitle="Results"\ndecls=[]\n')
    with pytest.raises(C.ConfigError, match="imports"):
        C.load_config(cfg)


def test_narrow_imports_preserve_project_classification(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    import subprocess

    cfg = tmp_path / "review-cone.toml"
    cfg.write_text('imports=["Entry"]\n[[section]]\ntitle="Results"\ndecls=["result"]\n')
    config = C.load_config(cfg)
    monkeypatch.setenv("REVIEW_CONE_DEPS", "1")
    monkeypatch.setenv("REVIEW_CONE_IMPORTS", "Stale")
    captured: dict[str, str] = {}

    def run(command: list[str], root: Path, env: dict[str, str]) -> subprocess.CompletedProcess[str]:
        captured.update(env)
        assert Path(command[-1]).is_file()
        return subprocess.CompletedProcess(command, 0, "", "")

    monkeypatch.setattr(R, "run_emitter_process", run)
    R.run_review_cone(tmp_path, ["Entry", "Support"], ["result"], tmp_path / "out.json",
                      imports=config["imports"])
    assert captured["REVIEW_CONE_LIBS"] == "Entry,Support"
    assert captured["REVIEW_CONE_IMPORTS"] == "Entry"
    assert "REVIEW_CONE_DEPS" not in captured
    with pytest.raises(ValueError, match="all project modules"):
        R.run_review_cone(tmp_path, ["Entry"], [], tmp_path / "deps.json", deps=True, imports=["Entry"])


def test_progress_and_large_stdout_are_both_preserved(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    import sys

    proc = R.run_emitter_process(
        [sys.executable, "-c", "import sys; print('x'*100000); print('import complete', file=sys.stderr)"],
        tmp_path, {},
    )
    assert proc.returncode == 0
    assert len(proc.stdout) == 100001
    assert proc.stderr == "import complete\n"
    assert "import complete" in capsys.readouterr().err


def test_docstring_moves_to_prose_without_touching_field_comments() -> None:
    body = 'structure Sample where\n  /-- A /- nested -/ field comment. -/\n  value : Nat'
    doc, source = R.split_docstring('/-- A /- nested -/ description. -/\n' + body)
    assert doc == 'A /- nested -/ description.'
    assert source == body
    assert R.split_docstring(body) == ('', body)


def test_prose_renders_fenced_code_block_verbatim() -> None:
    doc = "Apply the first rule.\n\n```\nif a < b then x\nelse   y\n```\n"
    out = R.prose_html(doc)
    assert "<p class='summary'>Apply the first rule.</p>" in out
    assert "<pre class='summary'><code>if a &lt; b then x\nelse   y</code></pre>" in out
    assert "``" not in out


def test_prose_escapes_html_and_preserves_inline_code() -> None:
    prose = R.prose_html('For `<x>` & y.\n\n<script>alert(1)</script>')
    assert '<code>&lt;x&gt;</code> &amp; y.' in prose
    assert '<script>' not in prose
    assert prose.count("<p class='summary'>") == 2
    assert R.prose_html("`unclosed") == "<p class='summary'>`unclosed</p>"


def test_prose_renders_math_lists_and_emphasis() -> None:
    doc = (
        "Let $\\pi(S) = \\sum_{v \\in S} \\pi(v)$ be the mass, *not* `S`.\n\n$$ a < b $$\n\n"
        "- first\n  continued\n- **second**\n\n1. one\n2) two"
    )
    out = R.prose_html(doc)
    assert "<span class='math'>\\pi(S) = \\sum_{v \\in S} \\pi(v)</span>" in out
    assert "<span class='math display'>a &lt; b</span>" in out
    assert "<em>not</em> <code>S</code>" in out
    assert "<ul class='summary'><li>first\ncontinued</li><li><strong>second</strong></li></ul>" in out
    assert "<ol class='summary'><li>one</li><li>two</li></ol>" in out
    # A lone or unclosed delimiter stays literal, as does markup inside code and math.
    assert R.prose_html("costs $5 and `$x$` and $a*b*c$") == (
        "<p class='summary'>costs $5 and <code>$x$</code> and <span class='math'>a*b*c</span></p>"
    )
    assert R.prose_html("2 * 3 * 4") == "<p class='summary'>2 * 3 * 4</p>"
    assert R.prose_html("from $0 < x$ to $1/2$, $5 and $6") == (
        "<p class='summary'>from <span class='math'>0 &lt; x</span> to <span class='math'>1/2</span>, $5 and $6</p>"
    )


def test_katex_included_only_when_prose_has_math(tmp_path: Path) -> None:
    (tmp_path / 'Fixture.lean').write_text('/-- Plain. -/\ndef a : Nat := 1\n/-- Math $x$. -/\ndef b : Nat := 2\n')
    config_path = tmp_path / 'review-cone.toml'
    config_path.write_text('[[section]]\ntitle="Results"\ndecls=["Fixture.a", "Fixture.b"]\n')
    config = C.load_config(config_path)

    def render(name: str, line: int) -> str:
        decl = {'name': f'Fixture.{name}', 'module': 'Fixture', 'kind': 'def',
                'startLine': line, 'endLine': line + 1, 'status': 'verified', 'axioms': []}
        return R.render({'project': [decl], 'mathlib': []}, tmp_path, None, None, config, True, '../')

    assert R.KATEX_HEAD not in render('a', 1)
    math = render('b', 3)
    assert R.KATEX_HEAD in math and R.KATEX_SCRIPT in math
    assert "<span class='math'>x</span>" in math


def test_comparison_keeps_long_definitions_and_warnings_visible(tmp_path: Path) -> None:
    source = '/-- Source description. -/\ndef longValue : Nat :=\n' + '  1 +\n' * 65 + '  0\n'
    (tmp_path / 'Fixture.lean').write_text(source)
    config_path = tmp_path / 'review-cone.toml'
    config_path.write_text('[[section]]\ntitle="Results"\ndecls=["Fixture.longValue"]\n')
    decl = {
        'name': 'Fixture.longValue', 'module': 'Fixture', 'kind': 'def',
        'startLine': 1, 'endLine': len(source.splitlines()), 'status': 'tainted', 'axioms': ['extra'],
    }
    result = R.render(
        {'project': [decl], 'mathlib': []}, tmp_path, None, None,
        C.load_config(config_path), True, '../',
    )
    code = re.search(r'<pre[^>]*><code>(.*?)</code></pre>', result, re.S)
    assert code is not None
    plain_code = unescape(re.sub(r'<[^>]*>', '', code.group(1)))
    assert plain_code == source.split('-/\n', 1)[1].rstrip('\n')
    assert result.count('Source description.') == 1
    assert "class='annotation'><p class='summary'>Source description." in result
    assert "class='badge tainted'" in result and 'extra' in result
    assert "href='../Fixture.lean#L1'" in result and 'Fixture.lean ↗' in result
    assert '<details' not in result[result.index("class='lean'"):result.index('</article>')]



def test_interface_axiom_metadata_does_not_expose_theorem_proof(tmp_path: Path) -> None:
    (tmp_path / "Fixture.lean").write_text(
        "/-- A theorem, despite the interface metadata. -/\n"
        "theorem result (h : True := by trivial) : True := by\n  exact h\n"
    )
    decl = ConeDecl.from_json({
        "name": "Fixture.result", "module": "Fixture", "kind": "axiom", "startLine": 1, "endLine": 3,
    })
    snippet, truncated = R.read_snippet(tmp_path, decl)
    assert snippet.endswith("theorem result (h : True := by trivial) : True")
    assert "exact h" not in snippet and not truncated


def test_let_bound_statement_survives_the_proof_cut(tmp_path: Path) -> None:
    (tmp_path / "Fixture.lean").write_text(
        "/-- A statement that names its tree. -/\n"
        "theorem result (n : Nat) : True := by\n"
        "  trivial\n"
    )
    source = (
        "/-- A statement that names its tree. -/\n"
        "theorem result (n : Nat) :\n"
        "    let t := tree n\n"
        "    have h : Nat := n\n"
        "    t.size = h :=\n"
        "  proof n\n"
    )
    (tmp_path / "Fixture.lean").write_text(source)
    decl = ConeDecl.from_json({
        "name": "Fixture.result", "module": "Fixture", "kind": "theorem", "startLine": 1, "endLine": 6,
    })
    snippet, truncated = R.read_snippet(tmp_path, decl)
    assert snippet.endswith("t.size = h")
    assert "let t := tree n" in snippet and "have h : Nat := n" in snippet
    assert "proof n" not in snippet and not truncated
