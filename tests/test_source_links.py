import json
import os
from pathlib import Path

import pytest

from lean4_lens.review_cone import ConeDecl, LinkCtx, build_indexes, linkify
from lean4_lens.source_links import SourceRef, read_source_refs


def _write_ilean(root: Path, source: str, references: dict[str, object]) -> Path:
    (root / "Fixture.lean").write_text(source)
    path = root / ".lake/build/lib/lean/Fixture.ilean"
    path.parent.mkdir(parents=True)
    path.write_text(json.dumps({"version": 5, "module": "Fixture", "references": references}))
    return path


def _ident(name: str) -> str:
    return json.dumps({"c": {"m": "Fixture", "n": name}})


def _ctx(*names: str, fields: dict[str, str] | None = None) -> LinkCtx:
    return LinkCtx(build_indexes([ConeDecl.from_json({"name": n}) for n in names], [], fields or {}),
                   "Fixture.branch")


def test_compiler_ranges_distinguish_local_and_field_names(tmp_path: Path) -> None:
    source = "def branch := fun z => z + t.z + Other.z"
    field_start = source.index("t.z") + 2
    other_start = source.index("Other.z")
    _write_ilean(tmp_path, source, {
        _ident("Fixture.branch"): {"definition": [0, 4, 0, 10], "usages": []},
        _ident("TwinSite.z"): {"definition": None, "usages": [[0, field_start, 0, field_start + 1]]},
        _ident("Other.z"): {"definition": None, "usages": [[0, other_start, 0, other_start + 7]]},
        json.dumps({"f": {"m": "Fixture", "i": "local"}}): {
            "definition": [0, 18, 0, 19], "usages": [[0, 23, 0, 24]]},
    })
    refs = read_source_refs(tmp_path, "Fixture", source)
    out = linkify(source, _ctx("TwinSite", "Other.z", fields={"TwinSite.z": "TwinSite"}), refs)
    assert 'fun z =&gt; z + t.<a' in out
    assert out.count('>z</a>') == 1
    assert 'href="#d-Other_46z">Other.z</a>' in out
    assert '<strong class="self">branch</strong>' in out


def test_utf16_columns_and_private_names(tmp_path: Path) -> None:
    source = '/-- 😀 --/\ndef branch := "😀" ++ privateValue'
    start = source.index("privateValue")
    column = len(source.splitlines()[1].split("privateValue")[0].encode("utf-16-le")) // 2
    _write_ilean(tmp_path, source, {
        _ident("_private.Fixture.0.Fixture.privateValue"): {
            "definition": None, "usages": [[1, column, 1, column + len("privateValue")]]},
    })
    refs = read_source_refs(tmp_path, "Fixture", source)
    assert refs == (SourceRef(start, len(source), "Fixture.privateValue"),)
    out = linkify(source, _ctx("Fixture.privateValue"), refs)
    assert 'href="#d-Fixture_46privateValue">privateValue</a>' in out
    assert '😀' in out


@pytest.mark.parametrize("mode", ["missing", "stale", "invalid", "wrong-module", "invalid-range"])
def test_unusable_compiler_data_never_falls_back_to_name_guessing(
    tmp_path: Path, capsys: pytest.CaptureFixture[str], mode: str,
) -> None:
    source = "def branch := fun z => z"
    path = _write_ilean(tmp_path, source, {})
    if mode == "missing":
        path.unlink()
    elif mode == "stale":
        stamp = path.stat().st_mtime_ns + 1_000_000
        os.utime(tmp_path / "Fixture.lean", ns=(stamp, stamp))
    elif mode == "invalid":
        path.write_text("{")
    elif mode == "wrong-module":
        path.write_text(json.dumps({"module": "Other", "references": {}}))
    else:
        path.write_text(json.dumps({"module": "Fixture", "references": {
            _ident("TwinSite.z"): {"definition": None, "usages": [[0, -1, 0, 2]]},
        }}))
    refs = read_source_refs(tmp_path, "Fixture", source)
    assert refs == ()
    out = linkify(source, _ctx("TwinSite", fields={"TwinSite.z": "TwinSite"}), refs)
    assert 'href' not in out
    assert 'source links omitted for Fixture' in capsys.readouterr().err


def test_comments_strings_and_ambiguous_ranges_are_not_linked() -> None:
    source = 'z "z" /- z -/ z'
    refs = [SourceRef(0, 1, "A.z"), SourceRef(0, 1, "B.z"), SourceRef(3, 4, "A.z"),
            SourceRef(9, 10, "A.z"), SourceRef(14, 15, "B.z")]
    out = linkify(source, _ctx("A.z", "B.z"), refs)
    assert out.startswith('z &quot;z&quot; <span class="cmt">/- z -/</span> ')
    assert out.count('href') == 1
    assert 'href="#d-B_46z">z</a>' in out


def test_two_fields_with_the_same_short_name_use_their_resolved_targets() -> None:
    source = "def branch := fun z => (z, a.z, b.z)"
    left = source.index("a.z") + 2
    right = source.index("b.z") + 2
    ctx = _ctx("Left", "Right", fields={"Left.z": "Left", "Right.z": "Right"})
    out = linkify(source, ctx, [SourceRef(left, left + 1, "Left.z"), SourceRef(right, right + 1, "Right.z")])
    assert 'fun z =&gt; (z, a.<a' in out
    assert 'href="#d-Left" title="field of Left">z</a>' in out
    assert 'href="#d-Right" title="field of Right">z</a>' in out


def test_resolved_proof_fields_keep_their_muted_bodies() -> None:
    source = "def branch := {\n  sound := by\n    trivial\n  value := 1 }"
    start = source.index("sound")
    idx = build_indexes([ConeDecl.from_json({"name": "Rule"})], [], {"Rule.sound": "Rule"}, {"Rule.sound"})
    out = linkify(source, LinkCtx(idx, "Fixture.branch"), [SourceRef(start, start + 5, "Rule.sound")])
    assert '<span class="proof">  <a' in out
    assert '<span class="proof">    trivial\n</span>' in out
    assert '<span class="proof">  value' not in out
