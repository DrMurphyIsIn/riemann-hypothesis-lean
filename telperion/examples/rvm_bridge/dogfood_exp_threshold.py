"""Dogfood: regenerate two hand-proof sites of the rvm_bridge island with the `exp_threshold` kind.

    python examples/rvm_bridge/dogfood_exp_threshold.py           # write lean/Probes/Dogfood_exp_threshold.lean
    python examples/rvm_bridge/dogfood_exp_threshold.py --check   # drift check (no write)

The sites (SHAPES_AUDIT_48H_2026-09-22.md section 7, sprint 1 item 3; B N2):

  * ``E6Bridge7.lean:554-590`` -- the threshold ``lam0 = max 1 (max (A/(2 eta K)) (B/(2 M K)))``
    and its two exponential consequences ``hexpeta`` / ``hexpM`` (one strict), emitted TOGETHER as
    one guarded linear bundle ``gaussian_dominance_thresholds`` (the ``eventual_threshold`` guard
    fold-in: the ``max 1`` conjunct rides along as ``1 <= lam``);
  * ``E6Bridge14.lean:66-86`` -- ``le_exp_of_log_le`` (the single log step, regenerated as
    ``le_exp_of_log_le_regen``) and the two log consequences of ``effectiveThreshold`` as a guarded
    log bundle ``effectiveThreshold_consequences``.

The written file is: a banner, the FROZEN emitter output (provenance header, imports, namespace),
then kernel cross-checks appended by this generator -- each regenerated theorem applied to prove the
ORIGINAL's statement (and the original applied to prove the regenerated one), plus the guarded log
bundle consuming ``RvMBridge14.effectiveThreshold`` by definitional unfolding.  It imports the modules
it regenerates from and touches neither; the lead compiles it on the island:

    cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_exp_threshold.lean

``tests/test_emit_exp_threshold.py`` regenerates the file through this module and asserts byte
equality, so the checked-in Lean can never drift from the emitter.

conjecture1_proved = False -- elementary real inequalities; nothing here bears on RH.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    ExpThresholdEmitter, ValidationReport, certify, emit, exp_threshold_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
OUT = _LEAN / "Probes" / "Dogfood_exp_threshold.lean"

# The three instances, exactly as the hand proofs shape them.
SPECS = {
    # E6Bridge7.lean:568-590: lam0 := max 1 (max (A / (2 * eta * K)) (B / (2 * M * K))), then
    # hexpeta : A <= K * exp (2 * lam * eta) and hexpM : B < K * exp (2 * lam * M).
    0: dict(mode="linear", guard=True, steps=[
        dict(Q="A", a="eta", K="K", scale=2),
        dict(Q="B", a="M", K="K", scale=2, strict=True),
    ]),
    # E6Bridge14.lean:78-86: log (max 1 Q) / (2 * a) <= lam -> Q <= exp (2 * lam * a).
    1: dict(mode="log", Q="Q", a="a", scale=2),
    # E6Bridge14.lean:66-75 + 281-291: effectiveThreshold = max 1 (max (log (max 1 Q1) / (2 a1))
    # (log (max 1 Q2) / (2 a2))) with Q1 = 4 N (D^2 + 1/4) / y0^2, a1 = xmin^2, Q2 = 4 B / y0^2,
    # a2 = y0^2; the consumer extracts hthr1 / hthr2 and applies le_exp_of_log_le to each.
    2: dict(mode="log", guard=True, steps=[
        dict(Q="Q1", a="a1", scale=2),
        dict(Q="Q2", a="a2", scale=2),
    ]),
}
NAMES = {
    0: "gaussian_dominance_thresholds",
    1: "le_exp_of_log_le_regen",
    2: "effectiveThreshold_consequences",
}

BANNER = """/-
  Dogfood_exp_threshold -- the Telperion `exp_threshold` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 5; B N2) regenerating two hand-proof sites of this island, 2026-09-22:

    E6Bridge7.lean:554-590   the threshold lam0 = max 1 (max (A/(2 eta K)) (B/(2 M K))) and its two
                             exponential consequences hexpeta / hexpM, as ONE guarded linear bundle
                             (`gaussian_dominance_thresholds`; the eventual_threshold guard fold-in);
    E6Bridge14.lean:66-86    `le_exp_of_log_le` (log mode, `le_exp_of_log_le_regen`) and the two log
                             consequences of `effectiveThreshold` (`effectiveThreshold_consequences`).

  The block between the telperion provenance header and `end DogfoodExpThreshold` is the FROZEN
  emitter output (examples/rvm_bridge/dogfood_exp_threshold.py regenerates it; a test pins the
  bytes).  The cross-checks after it apply each regenerated theorem to the ORIGINAL's statement, so
  the kernel confirms the regeneration is interchangeable with the hand proof.  Nothing in
  E6Bridge7 / E6Bridge14 is modified.

  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_exp_threshold.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is an elementary real
  inequality (a threshold hypothesis on a real parameter implies an exponential bound).
-/
"""

TRAILER = """
/-! ## Kernel cross-checks against the hand-written originals (generator-appended; the block above
    is the frozen emitter output).  Each `example` is closed by applying one side to the other's
    statement, so a drift in either statement fails to elaborate. -/

section CrossChecks
open DogfoodExpThreshold

/-- The regenerated log step proves the ORIGINAL `RvMBridge14.le_exp_of_log_le` statement. -/
example {Q a lam : ℝ} (ha : 0 < a) (h : Real.log (max 1 Q) / (2 * a) ≤ lam) :
    Q ≤ Real.exp (2 * lam * a) :=
  le_exp_of_log_le_regen Q a lam ha h

/-- ... and the original proves the regenerated statement: the two are interchangeable. -/
example (Q a lam : ℝ) (ha0 : 0 < a) (h : Real.log (max 1 Q) / (2 * a) ≤ lam) :
    Q ≤ Real.exp (2 * lam * a) :=
  RvMBridge14.le_exp_of_log_le ha0 h

/-- The guarded log bundle consumes `RvMBridge14.effectiveThreshold` by definitional unfolding and
    returns E6Bridge14's `hlam1`, `hQ1`, `hQ2` (E6Bridge14.lean:281-291) in one stroke. -/
example (y0 xmin : ℝ) (N : ℕ) (B D lam : ℝ) (hy0 : 0 < y0) (hx : 0 < xmin)
    (hlam : RvMBridge14.effectiveThreshold y0 xmin N B D ≤ lam) :
    1 ≤ lam ∧ 4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2 ≤ Real.exp (2 * lam * xmin ^ 2)
      ∧ 4 * B / y0 ^ 2 ≤ Real.exp (2 * lam * y0 ^ 2) :=
  effectiveThreshold_consequences (4 * N * (D ^ 2 + 1 / 4) / y0 ^ 2) (xmin ^ 2)
    (4 * B / y0 ^ 2) (y0 ^ 2) lam (by positivity) (by positivity) hlam

/-- The guarded linear bundle yields E6Bridge7's `hexpeta` and `hexpM` (E6Bridge7.lean:575-590)
    from the `lam0 <= lam` hypothesis its `exists_lam_re_gaussTest` phase choice provides. -/
example (A eta K B M lam : ℝ) (heta : 0 < eta) (hK : 0 < K) (hM : 0 < M)
    (hlam : max 1 (max (A / (2 * eta * K)) (B / (2 * M * K))) ≤ lam) :
    A ≤ K * Real.exp (2 * lam * eta) ∧ B < K * Real.exp (2 * lam * M) :=
  (gaussian_dominance_thresholds A eta K B M lam heta hK hM hlam).2

end CrossChecks

#print axioms DogfoodExpThreshold.gaussian_dominance_thresholds
#print axioms DogfoodExpThreshold.le_exp_of_log_le_regen
#print axioms DogfoodExpThreshold.effectiveThreshold_consequences
"""


def family():
    return exp_threshold_family(
        "DogfoodExpThreshold",
        GridSpec([("i", sorted(SPECS))]),
        lambda pt: NAMES[pt["i"]],
        spec=lambda pt: SPECS[pt["i"]],
    )


def emitted_text() -> str:
    """The frozen emitter output alone (header + imports + namespace + theorems)."""
    report = emit(
        certify(family()),
        LeanProfile(namespace=("DogfoodExpThreshold",), imports=("E6Bridge7", "E6Bridge14")),
        [ExpThresholdEmitter()],
        ValidationReport(checks=(("exp_threshold", True),)),
        file_name="Dogfood_exp_threshold.lean",
    )
    return report.files["Dogfood_exp_threshold.lean"]


def build_text() -> str:
    """The complete probe file: banner + frozen emitter output + kernel cross-checks."""
    return BANNER + emitted_text() + TRAILER


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true", help="drift check against the file on disk")
    args = ap.parse_args(argv)
    text = build_text()
    if args.check:
        if not OUT.is_file():
            print(f"MISSING {OUT}")
            return 1
        if OUT.read_text(encoding="utf-8") != text:
            print(f"DRIFT {OUT}: regenerate with {Path(__file__).name}")
            return 1
        print(f"OK {OUT} matches the emitter")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text, encoding="utf-8")
    print(f"wrote {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
