import json
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
    tmp_path: Path, config_out: str | None, cli_out: str | None,
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
    assert f"<a class='proj' href='{url}' target='_blank'>{url}</a>" in html


def test_document_without_info_table_has_no_info_panel(tmp_path: Path) -> None:
    assert "vpanel info" not in _render_fixture(tmp_path, 'title = "Fixture"\n')


def test_heading_names_the_document_a_formalization(tmp_path: Path) -> None:
    html = _render_fixture(tmp_path, 'title = "Fixture"\n')
    assert "<title>Lean 4 formalization of Fixture</title>" in html
    assert "<h1>Lean 4 formalization of <em>Fixture</em></h1>" in html


def test_intro_spells_out_how_much_the_document_covers(tmp_path: Path) -> None:
    html = _render_fixture(tmp_path, 'title = "Fixture"\n', n_decls=3)
    assert "The three results are grouped into sections" in html
    assert "the zero remaining <em>supporting declarations</em>" in html


@pytest.mark.parametrize(
    "info,message",
    [
        ('info = "https://example.com"', "`[info]` must be a table"),
        ("[info]\nheading = \"Sources\"", "`info.url` is required"),
        ('[info]\nurl = 3', "`info.url` is required"),
        ('[info]\nurl = "https://example.com"\nheading = ""', "`info.heading` must be a non-empty string"),
    ],
)
def test_malformed_info_table_is_rejected(tmp_path: Path, info: str, message: str) -> None:
    config = tmp_path / "review-cone.toml"
    config.write_text(f'{info}\n[[section]]\ntitle = "Results"\ndecls = []\n')
    with pytest.raises(C.ConfigError) as excinfo:
        C.load_config(config)
    assert message in str(excinfo.value.code)
