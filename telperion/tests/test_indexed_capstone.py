"""The A2 indexed capstone emitter (campaign.py `emit-indexed`), node AND_ladder_h280000.

Pure-text tests against the REAL emitted segment files of the zeta_zero_localization
island (no lake, no Lean): the literal box tables are read from the segment files and
cross-checked against the band-module names; the registry span is contained in the emitted
module followed by `:=` under the hardened gate (`missions/verify.statement_matches`); the
proposed statement text carries no proof body; the checked-in module and guard are exactly
what the emitter produces.  Kernel evidence (elaboration, axiom battery) is recorded in
LANE_NOTES_h280k.md, not here.

Finite verification to a finite height, conditional on Arb-class box hypotheses; NOT a
proof of RH.  conjecture1_proved = False.
"""
from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

import pytest

_TELPERION = Path(__file__).resolve().parents[1]
_CAMPAIGN = _TELPERION / "examples" / "zeta_zero_localization" / "campaign.py"
sys.path.insert(0, str(_TELPERION / "src"))

from telperion.missions import verify as V  # noqa: E402
from telperion.missions.statements import _build_body, _last_declaration_has_proof  # noqa: E402

TOP = 280000


@pytest.fixture(scope="module")
def C():
    spec = importlib.util.spec_from_file_location("zzl_campaign_indexed", _CAMPAIGN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def emitted(C):
    return {
        "recs": C._indexed_tables(TOP),
        "span": C.emit_indexed_span(TOP),
        "module": C.emit_indexed_capstone(TOP),
        "statement": C.emit_indexed_statement(TOP),
        "guard": C.emit_indexed_guard_module(TOP),
    }


def test_tables_follow_the_segment_files_and_vary(emitted):
    recs = emitted["recs"]
    assert [r["top"] for r in recs] == [1000 * (k + 1) for k in range(280)]
    counts = [r["K"] for r in recs]
    # the band count is NOT constant: 25 per segment at the bottom, 40 at the top
    assert counts[0] == 25 and counts[-1] == 40 and min(counts) == 25 and max(counts) == 40
    assert sum(counts) == 10379
    assert {r["den"] for r in recs} == {4000000}
    # one band module per box, no box reused across segments
    bands = [b for r in recs for b in r["bands"]]
    assert len(bands) == len(set(bands)) == 10379


def test_span_is_contained_in_the_module_and_followed_by_the_proof(emitted):
    needle = V.normalize_lean(emitted["span"])
    assert V.statement_matches(emitted["module"], needle)
    hay = V.normalize_lean(V._strip_string_literals(emitted["module"]))
    assert hay.count(needle) == 1
    assert V.artifact_incompleteness_markers(emitted["module"]) == []
    assert V.artifact_incompleteness_markers(emitted["guard"]) == []
    # the theorem-only tail also matches (if the lead keeps the tables elsewhere)
    thm = needle[needle.index(f"theorem all_nontrivial_zeros_up_to_height_{TOP}"):]
    assert V.statement_matches(emitted["module"], thm)


@pytest.mark.parametrize("old,new", [
    ("∀ k, k < 280 → SegBandHyp k", "∀ k, k < 279 → SegBandHyp k"),
    ("ρ.im ≤ 280000 → ρ.re = 1 / 2", "ρ.im ≤ 280001 → ρ.re = 1 / 2"),
    ("| 0 => 25 | 1 => 25", "| 0 => 26 | 1 => 25"),
])
def test_perturbed_statements_do_not_match(emitted, old, new):
    needle = V.normalize_lean(emitted["span"])
    bad = needle.replace(old, new, 1)
    assert bad != needle
    assert not V.statement_matches(emitted["module"], bad)
    assert not V.statement_matches(emitted["module"], needle + " ∨ True")


def test_span_names_no_island_module(emitted):
    code = V.normalize_lean(emitted["span"])
    assert not re.search(r"AllZeros_h\d+\.", code)
    assert "RHInBox" not in code
    for ln in emitted["span"].split("\n"):
        assert not ln.strip().startswith(("import ", "open "))


def test_statement_text_has_no_proof_body(emitted):
    st = emitted["statement"]
    assert "sorry" not in st
    assert not _last_declaration_has_proof(st)
    assert emitted["span"] in st
    assert _build_body(st).rstrip().endswith(":= by " + "sorry")   # the tool's placeholder
    assert [ln for ln in st.split("\n") if ln.startswith("import ")] == ["import Mathlib"]


def test_guard_covers_capstone_and_wrapper(emitted):
    g = emitted["guard"]
    assert f"import AllZeros_h{TOP}_Indexed\n" in g
    for name in (f"AllZeros_h{TOP}.all_nontrivial_zeros_up_to_height_{TOP}_of_bands",
                 f"AllZeros_h{TOP}_Indexed.all_nontrivial_zeros_up_to_height_{TOP}"):
        assert (f"/-- info: '{name}' depends on axioms: "
                f"[propext, Classical.choice, Quot.sound] -/\n"
                f"#guard_msgs (whitespace := lax) in #print axioms {name}\n") in g


def test_checked_in_files_are_what_the_emitter_produces(C, emitted):
    lean = _CAMPAIGN.parent / "lean"
    assert (lean / f"AllZeros_h{TOP}_Indexed.lean").read_text() == emitted["module"]
    assert (lean / f"Guard_h{TOP}.lean").read_text() == emitted["guard"]


def test_segment_record_refuses_a_box_that_does_not_match_its_band(C, tmp_path):
    src = (_CAMPAIGN.parent / "lean" / "AllZeros_h1000.lean").read_text()
    at = src.index("noncomputable def bLo")      # tamper box 0's lower edge (1 -> 2)
    assert src[at:].index("  | 0 => 1\n") < src[at:].index("\n\n")
    bad = src[:at] + src[at:].replace("  | 0 => 1\n", "  | 0 => 2\n", 1)
    (tmp_path / "AllZeros_h1000.lean").write_text(bad)
    with pytest.raises(ValueError, match="does not match its band module"):
        C._segment_record(1000, tmp_path)


def test_register_libs_is_idempotent(C, tmp_path):
    lf = tmp_path / "lakefile.toml"
    lf.write_text('name = "X"\ndefaultTargets = ["A"]\nsrcDir = ".."\n\n[[lean_lib]]\nname = "A"\n')
    assert C._register_libs(lf, ["B", "Guard_B"]) == ["B", "Guard_B"]
    text = lf.read_text()
    assert 'defaultTargets = ["A", "B", "Guard_B"]\n' in text
    assert text.endswith('[[lean_lib]]\nname = "B"\n[[lean_lib]]\nname = "Guard_B"\n')
    assert C._register_libs(lf, ["B", "Guard_B"]) == []
    assert lf.read_text() == text


def test_block_top_register_keeps_the_combined_guard(C, tmp_path, monkeypatch):
    """At a block top with an indexed wrapper, `register-lakefile --sharded` must write the
    COMBINED guard (capstone + wrapper), never the capstone-only one."""
    # hermetic, as in test_runner_shard: never touch the live stretch cache / state
    monkeypatch.setattr(C, "_STRETCH_CACHE_FILE", tmp_path / "edge_stretch.json")
    monkeypatch.setattr(C, "_stretch_cache", None)
    monkeypatch.setattr(C, "STATE", tmp_path / "campaign_state.json")
    top = 25000
    lean = tmp_path / "lean"
    lean.mkdir()
    (lean / "lean-toolchain").write_text("leanprover/lean4:v4.32.0\n")
    (lean / "lake-manifest.json").write_text('{"version": "1.1.0", "packages": []}\n')
    (lean / f"{C.indexed_module_name(top)}.lean").write_text("-- stub\n")
    C.register_lakefile_sharded(24960, top, True, lean)
    guard = (lean / f"{C.guard_module_name(top)}.lean").read_text()
    assert guard == C.emit_indexed_guard_module(top)
    block = (lean / C.block_pkg_name(top) / "lakefile.toml").read_text()
    assert f'name = "{C.indexed_module_name(top)}"' in block
    assert f'name = "{C.guard_module_name(top)}"' in block


def test_indexed_wrapper_and_guards_never_leak_into_zzl_aux(C, tmp_path):
    """Registered in the monolith, the wrapper and its guard must NOT become zzl_aux
    candidates: they import the ladder, so zzl_aux (built on every CI run) could not
    build them."""
    lean = tmp_path / "lean"
    lean.mkdir()
    libs = ["AllZeros_h100", "BraggDefect", "AllZeros_h280000", "AllZeros_h280000_Indexed",
            "Guard_h280000", "Guard_h300000"]
    (lean / "lakefile.toml").write_text(
        'name = "mono"\n' + "".join(f'[[lean_lib]]\nname = "{n}"\n' for n in libs))
    for n in libs:
        (lean / f"{n}.lean").write_text("import Mathlib\n")
    assert C.aux_modules(lean) == ["AllZeros_h100", "BraggDefect"]


def test_real_monolith_registration_does_not_reach_zzl_aux(C):
    """With the wrapper + guard registered in the real monolith, the derived zzl_aux set
    still excludes them and stays within the checked-in zzl_aux lakefile.  (Equality does
    not hold, independently of this change: the checked-in zzl_aux also lists three
    modules the monolith lacks -- ExpEnclosureInstances, ExpLaurentDeficit,
    RecurrenceDeficit -- which a `register-lakefile --sharded` rerun would drop.)"""
    lean = _CAMPAIGN.parent / "lean"
    aux_txt = (lean / "zzl_aux" / "lakefile.toml").read_text()
    listed = set(re.findall(r'^\[\[lean_lib\]\]\s*\nname = "([^"]+)"', aux_txt, re.M))
    derived = set(C.aux_modules(lean))
    assert f"AllZeros_h{TOP}_Indexed" not in derived and f"Guard_h{TOP}" not in derived
    assert derived <= listed
