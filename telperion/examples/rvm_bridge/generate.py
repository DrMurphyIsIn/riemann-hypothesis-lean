"""E6 RvM bridge island -- drift check (no generation; the Lean is hand-written).

    python examples/rvm_bridge/generate.py --check    # drift check (the only mode)
    python examples/rvm_bridge/generate.py            # same as --check

The island `examples/rvm_bridge/lean/` discharges the MIRRORMERE residual
`MM_rvm_unbounded_mean_density` from Anthropic's zeta-23-lean (Alpoege--Furman
Theorem A + the unconditional Riemann--von Mangoldt main clause), on its own
toolchain island (Lean v4.33.0-rc2 / Mathlib 51e6992e, the zeta-23-lean pin).

Nothing is emitted, so "regeneration" is the containment invariant the registry's
grant gate relies on:

  1. `lean/E6Bridge.lean` contains, verbatim modulo whitespace/comments and the
     trailing `:= by sorry`, the node statement line of
     `missions/mirrormere/lean/Statements/MM_rvm_unbounded_mean_density.lean`
     (theorem NAME and binder-free form must match exactly);
  2. the two mirrored definitions (`RvMUnboundedMeanDensity`, `zetaOrdinates`)
     match `missions/mirrormere/lean/Statements/MMDefs.lean` verbatim modulo
     whitespace/comments;
  3. the island's toolchain pin is the zeta-23-lean pin recorded in
     `lean/lakefile.toml` (Lean v4.33.0-rc2);
  4. (second bridge, 2026-09-17) `lean/E6Bridge2.lean` contains the node statement
     of `missions/rh/lean/Statements/RH_rvm_unconditional.lean` verbatim, and its
     mirrored `RvMCount.zetaZeroCount` matches `missions/rh/lean/Statements/RHDefs.lean`;
  5. (third bridge, 2026-09-17) `lean/E6Bridge3.lean` contains the node statement of
     `missions/rh/lean/Statements/RH_corridor_bound.lean` verbatim (no mirrored
     definitions: the statement is in Mathlib vocabulary only).
  6. (fourth bridge, 2026-09-18) `lean/E6Bridge4.lean` contains the node statement of
     `missions/rh/lean/Statements/RH_limit_explicit_formula.lean` verbatim, and its six
     mirrored `WeilExplicit.*` definitions match the AUTHORED block of
     `missions/rh/lean/Statements/RHDefs.lean`.  The statement is ALSO checked against
     the copy embedded in the module's header comment between the lines
     `BEGIN REGISTRY STATEMENT` / `END REGISTRY STATEMENT` (always); the registry-file
     halves are skipped with a printed notice when the registry file (or the
     `WeilExplicit` block) is absent from this checkout, since the E8 registry node lives
     on its own branch until merged.

  7. (W2c assembly, 2026-09-18) `lean/W2cAssembly.lean` contains the node statement of
     `missions/mirrormere/lean/Statements/MM_zeta_ordinates_not_uniformly_discrete.lean`
     verbatim, its mirrored `IsUniformlyDiscrete` matches `MMDefs.lean`, it has no `sorry`,
     AND every ported brick statement (the four theorems + `RvMWindowedDensity`, plus
     `RvMUnboundedMeanDensity` from E6Bridge) equals, normalized, the v4.32 quasicrystal
     island's text (BoundaryLemmas.lean on branch rh/million-turing, blob
     b019e8e9167d51504a8775e9006ec8fceb9255bd; the statement lines are PINNED below as
     `_BRICK_V432_TEXT` because that island is not part of this checkout).  The comparison
     runs through `telperion.port_match.port_match_pinned`, the cross-toolchain port-match
     gate: statements must match, proofs may differ, and when the v4.32 file IS present in
     the checkout the pin is additionally diffed against it so the pin cannot rot.
     This is the certificate that the cross-toolchain RE-PROOF of MM_nt_brick_conditional
     cannot drift from the artifact it re-proves.

Any drift in the registry statement or definitions fails this check, so the
island cannot silently stop matching the node it discharges.

HONEST SCOPE: the discharged statement is a classical (Selberg-type) consequence
of a positive proportion of zeros on the critical line; it is not RH and does
not approach it.  conjecture1_proved = False.
"""
import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion.port_match import port_match_pinned  # noqa: E402

_HERE = Path(__file__).resolve().parent
_TELPERION = _HERE.parents[1]
_ISLAND = _HERE / "lean"
_BRIDGE = _ISLAND / "E6Bridge.lean"
_TOOLCHAIN = _ISLAND / "lean-toolchain"
_NODE = _TELPERION / "missions" / "mirrormere" / "lean" / "Statements" / "MM_rvm_unbounded_mean_density.lean"
_MMDEFS = _TELPERION / "missions" / "mirrormere" / "lean" / "Statements" / "MMDefs.lean"
_BRIDGE2 = _ISLAND / "E6Bridge2.lean"
_NODE2 = _TELPERION / "missions" / "rh" / "lean" / "Statements" / "RH_rvm_unconditional.lean"
_RHDEFS = _TELPERION / "missions" / "rh" / "lean" / "Statements" / "RHDefs.lean"
_DEF_NAMES2 = ("zetaZeroCount",)
_BRIDGE3 = _ISLAND / "E6Bridge3.lean"
_NODE3 = _TELPERION / "missions" / "rh" / "lean" / "Statements" / "RH_corridor_bound.lean"
_BRIDGE4 = _ISLAND / "E6Bridge4.lean"
_NODE4 = _TELPERION / "missions" / "rh" / "lean" / "Statements" / "RH_limit_explicit_formula.lean"
_DEF_NAMES4 = ("IsWeilTest", "weilKernel", "zeroMult", "archIntegrand", "archSide", "primeSide")

_ASSEMBLY = _ISLAND / "W2cAssembly.lean"
_NODE_W2C = _TELPERION / "missions" / "mirrormere" / "lean" / "Statements" / "MM_zeta_ordinates_not_uniformly_discrete.lean"
_QC_BRICK = _TELPERION / "examples" / "quasicrystal" / "lean" / "BoundaryLemmas.lean"
_DEF_NAMES_W2C = ("IsUniformlyDiscrete",)
# The ported brick: statement text of telperion/examples/quasicrystal/lean/BoundaryLemmas.lean
# (branch rh/million-turing @ 0bac3e608, blob b019e8e9167d51504a8775e9006ec8fceb9255bd),
# lines 42-43, 170-172, 183-186, 321-323, 342-344, 350-351, 365-366, 378-380, verbatim.
_BRICK_V432_TEXT = """
def IsUniformlyDiscrete (S : Set ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → δ ≤ |x - y|

theorem not_uniformlyDiscrete_of_gaps_to_zero {S : Set ℝ}
    (hgap : ∀ δ : ℝ, 0 < δ → ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ |x - y| < δ) :
    ¬ IsUniformlyDiscrete S := by

theorem exists_close_of_card_gt {F : Finset ℝ} {a L δ : ℝ}
    (hδ : 0 < δ) (hmem : ∀ x ∈ F, x ∈ Set.Icc a (a + L))
    (hcard : ⌊L / δ⌋₊ + 1 < F.card) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x - y| < δ := by

def RvMWindowedDensity (S : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (F : Finset ℝ) (a L : ℝ),
    (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ ⌊L / δ⌋₊ + 1 < F.card

def RvMUnboundedMeanDensity (S : Set ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ (F : Finset ℝ) (a L : ℝ),
    0 ≤ L ∧ (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ r * L + 1 < F.card

theorem windowedDensity_of_unboundedMeanDensity {S : Set ℝ}
    (h : RvMUnboundedMeanDensity S) : RvMWindowedDensity S := by

theorem not_uniformlyDiscrete_of_windowedDensity {S : Set ℝ}
    (hRvM : RvMWindowedDensity S) : ¬ IsUniformlyDiscrete S := by

theorem zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density
    {Ordinates : Set ℝ} (hRvM : RvMUnboundedMeanDensity Ordinates) :
    ¬ IsUniformlyDiscrete Ordinates :=
"""
# every declaration the assembly re-proves, in source order (defs and theorems alike:
# the gate takes each one's kind from the pinned source side)
_PORTED_BRICK = ("IsUniformlyDiscrete", "not_uniformlyDiscrete_of_gaps_to_zero",
                 "exists_close_of_card_gt", "RvMWindowedDensity", "RvMUnboundedMeanDensity",
                 "windowedDensity_of_unboundedMeanDensity",
                 "not_uniformlyDiscrete_of_windowedDensity",
                 "zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density")

_EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.0-rc2"
_DEF_NAMES = ("RvMUnboundedMeanDensity", "zetaOrdinates")


def _strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def _normalize(text: str) -> str:
    return re.sub(r"\s+", " ", _strip_comments(text)).strip()


def _node_statement(node_text: str, node_path: Path = _NODE) -> str:
    """The `theorem NAME [binders] : BODY` of the node file, with the `:= by sorry` tail dropped.
    Binders are explicit `(x : T)` groups (the E8 node takes `(g : ℝ → ℂ) (hg : ...)`)."""
    body = _normalize(node_text)
    m = re.search(r"(theorem\s+\S+(?:\s*\([^()]*\))*\s*:.*?)\s*:=\s*by\s+sorry", body)
    if not m:
        raise SystemExit(f"cannot find the node theorem in {node_path}")
    return m.group(1)


def _def_block(text: str, name: str) -> str:
    """The normalized `def NAME ... :=` block up to the next top-level declaration."""
    body = _strip_comments(text)
    m = re.search(rf"\bdef\s+{re.escape(name)}\b.*?(?=\n(?:def|theorem|lemma|end|namespace|noncomputable|abbrev|structure|open|section)\b)",
                  body, flags=re.S)
    if not m:
        raise SystemExit(f"cannot find `def {name}` in the source")
    return re.sub(r"\s+", " ", m.group(0)).strip()


def _embedded_statement(bridge_text: str, bridge_path: Path) -> str:
    """The normalized theorem embedded in the module header between the two marker lines."""
    m = re.search(r"BEGIN REGISTRY STATEMENT\s*(.*?)\s*END REGISTRY STATEMENT", bridge_text, flags=re.S)
    if not m:
        raise SystemExit(f"cannot find the BEGIN/END REGISTRY STATEMENT markers in {bridge_path}")
    body = re.sub(r"\s+", " ", m.group(1)).strip()
    if not body.startswith("theorem "):
        raise SystemExit(f"embedded registry statement in {bridge_path} does not start with `theorem`")
    return body


def check() -> int:
    failures = []
    bridge = _BRIDGE.read_text(encoding="utf-8")
    bridge_norm = _normalize(bridge)

    # 1. the node statement line, verbatim (name + binder-free form)
    stmt = _node_statement(_NODE.read_text(encoding="utf-8"))
    if stmt not in bridge_norm:
        failures.append(f"node statement not contained verbatim in E6Bridge.lean: {stmt!r}")
    if re.search(r":=\s*by\s+sorry", bridge_norm) or "sorry" in bridge_norm.split():
        failures.append("E6Bridge.lean contains a `sorry`")

    # 2. the two mirrored definitions
    mmdefs = _MMDEFS.read_text(encoding="utf-8")
    for name in _DEF_NAMES:
        want = _def_block(mmdefs, name)
        have = _def_block(bridge, name)
        if want != have:
            failures.append(f"`def {name}` drifted from MMDefs.lean:\n  registry: {want}\n  island:   {have}")

    # 3. the toolchain pin
    tc = _TOOLCHAIN.read_text(encoding="utf-8").strip()
    if tc != _EXPECTED_TOOLCHAIN:
        failures.append(f"lean-toolchain is {tc!r}, expected {_EXPECTED_TOOLCHAIN!r}")

    # 4. the second bridge: the RH node RH_rvm_unconditional + its mirrored definition
    bridge2 = _BRIDGE2.read_text(encoding="utf-8")
    bridge2_norm = _normalize(bridge2)
    stmt2 = _node_statement(_NODE2.read_text(encoding="utf-8"), _NODE2)
    if stmt2 not in bridge2_norm:
        failures.append(f"node statement not contained verbatim in E6Bridge2.lean: {stmt2!r}")
    if re.search(r":=\s*by\s+sorry", bridge2_norm) or "sorry" in bridge2_norm.split():
        failures.append("E6Bridge2.lean contains a `sorry`")
    rhdefs = _RHDEFS.read_text(encoding="utf-8")
    for name in _DEF_NAMES2:
        want = _def_block(rhdefs, name)
        have = _def_block(bridge2, name)
        if want != have:
            failures.append(f"`def {name}` drifted from RHDefs.lean:\n  registry: {want}\n  island:   {have}")

    # 5. the third bridge: the RH node RH_corridor_bound (Mathlib vocabulary only, no mirrored defs)
    bridge3 = _BRIDGE3.read_text(encoding="utf-8")
    bridge3_norm = _normalize(bridge3)
    stmt3 = _node_statement(_NODE3.read_text(encoding="utf-8"), _NODE3)
    if stmt3 not in bridge3_norm:
        failures.append(f"node statement not contained verbatim in E6Bridge3.lean: {stmt3!r}")
    if re.search(r":=\s*by\s+sorry", bridge3_norm) or "sorry" in bridge3_norm.split():
        failures.append("E6Bridge3.lean contains a `sorry`")

    # 6. the fourth bridge: the RH node RH_limit_explicit_formula + its six mirrored definitions.
    #    The registry node lives on branch rh/e8-statement until merged, so each registry half is
    #    skipped with a notice when its file/block is absent; the embedded copy is always checked.
    bridge4 = _BRIDGE4.read_text(encoding="utf-8")
    bridge4_norm = _normalize(bridge4)
    stmt4_embedded = _embedded_statement(bridge4, _BRIDGE4)
    if stmt4_embedded not in bridge4_norm:
        failures.append("embedded registry statement not contained verbatim in E6Bridge4.lean: "
                        f"{stmt4_embedded!r}")
    if re.search(r":=\s*by\s+sorry", bridge4_norm) or "sorry" in bridge4_norm.split():
        failures.append("E6Bridge4.lean contains a `sorry`")
    notices = []
    if _NODE4.exists():
        stmt4 = _node_statement(_NODE4.read_text(encoding="utf-8"), _NODE4)
        if stmt4 not in bridge4_norm:
            failures.append(f"node statement not contained verbatim in E6Bridge4.lean: {stmt4!r}")
        if stmt4 != stmt4_embedded:
            failures.append("E6Bridge4.lean's embedded registry statement drifted from "
                            f"{_NODE4.relative_to(_TELPERION)}:\n  registry: {stmt4}\n  embedded: {stmt4_embedded}")
    else:
        notices.append(f"NOTICE: {_NODE4.relative_to(_TELPERION)} is absent from this checkout "
                       "(E8 registry node not merged here); the registry half of the E6Bridge4 "
                       "statement check is skipped, the embedded-copy half was checked")
    rhdefs4 = _RHDEFS.read_text(encoding="utf-8") if _RHDEFS.exists() else ""
    if "namespace WeilExplicit" in rhdefs4:
        for name in _DEF_NAMES4:
            want = _def_block(rhdefs4, name)
            have = _def_block(bridge4, name)
            if want != have:
                failures.append(f"`def {name}` drifted from RHDefs.lean (WeilExplicit):\n  registry: {want}\n  island:   {have}")
    else:
        notices.append(f"NOTICE: {_RHDEFS.relative_to(_TELPERION)} has no `WeilExplicit` block in this "
                       "checkout (E8 registry vocabulary not merged here); the six mirrored-def "
                       "checks for E6Bridge4 are skipped")
    # 7. the W2c assembly: MIRRORMERE node MM_zeta_ordinates_not_uniformly_discrete + the mirrored
    #    IsUniformlyDiscrete + the ported v4.32 brick (statements pinned in _BRICK_V432_TEXT).
    assembly = _ASSEMBLY.read_text(encoding="utf-8")
    assembly_norm = _normalize(assembly)
    stmt_w2c = _node_statement(_NODE_W2C.read_text(encoding="utf-8"), _NODE_W2C)
    if stmt_w2c not in assembly_norm:
        failures.append(f"node statement not contained verbatim in W2cAssembly.lean: {stmt_w2c!r}")
    if re.search(r":=\s*by\s+sorry", assembly_norm) or "sorry" in assembly_norm.split():
        failures.append("W2cAssembly.lean contains a `sorry`")
    for name in _DEF_NAMES_W2C:
        want = _def_block(mmdefs, name)
        have = _def_block(assembly, name)
        if want != have:
            failures.append(f"`def {name}` drifted from MMDefs.lean:\n  registry: {want}\n  island:   {have}")
    # The ported brick, through the cross-toolchain port-match gate `telperion.port_match`:
    # target = W2cAssembly.lean + E6Bridge.lean (RvMUnboundedMeanDensity was mirrored there
    # by the first bridge), source = the pinned v4.32 text, plus the live v4.32 file when the
    # quasicrystal island happens to be in this checkout (so the pin itself cannot rot).
    live = _QC_BRICK.read_text(encoding="utf-8") if _QC_BRICK.exists() else None
    port, pin_vs_live = port_match_pinned(
        _BRICK_V432_TEXT,
        [(assembly, "W2cAssembly.lean"), (bridge, "E6Bridge.lean")],
        _PORTED_BRICK,
        live=live,
        pin_label="v4.32 BoundaryLemmas pin",
        target_label="rvm_bridge island",
        live_label=str(_QC_BRICK.relative_to(_TELPERION)),
    )
    failures.extend(port.failure_lines())
    if pin_vs_live is None:
        notices.append(f"NOTICE: {_QC_BRICK.relative_to(_TELPERION)} is absent from this checkout "
                       "(v4.32 quasicrystal island lives on rh/million-turing); the ported brick was "
                       "checked against the pinned v4.32 text only")
    else:
        failures.extend(pin_vs_live.failure_lines())
    for n in notices:
        print(n)

    if failures:
        print("rvm_bridge drift check FAILED:")
        for f in failures:
            print("  - " + f)
        return 1
    print(f"rvm_bridge: node statement + {len(_DEF_NAMES)} mirrored defs + toolchain pin match "
          f"({_BRIDGE.relative_to(_TELPERION)}); "
          f"RH node statement + {len(_DEF_NAMES2)} mirrored def match "
          f"({_BRIDGE2.relative_to(_TELPERION)}); "
          f"RH corridor node statement matches ({_BRIDGE3.relative_to(_TELPERION)}); "
          f"RH explicit-formula node statement matches its embedded copy"
          f"{'' if notices else ' and the registry'} ({_BRIDGE4.relative_to(_TELPERION)}); "
          f"W2c node statement + {len(_DEF_NAMES_W2C)} mirrored def match, and the "
          f"{len(_PORTED_BRICK)} ported v4.32 brick declarations pass the port-match gate "
          f"({_ASSEMBLY.relative_to(_TELPERION)})")
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--check", action="store_true", help="drift check (the only mode; default)")
    p.parse_args(argv)
    return check()


if __name__ == "__main__":
    sys.exit(main())
