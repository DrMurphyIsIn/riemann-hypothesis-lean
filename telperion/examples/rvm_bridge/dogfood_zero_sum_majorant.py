"""Dogfood: regenerate three hand-proof sites of the rvm_bridge island with the `zero_sum_majorant` kind.

    python examples/rvm_bridge/dogfood_zero_sum_majorant.py           # write lean/Probes/Dogfood_zero_sum_majorant.lean
    python examples/rvm_bridge/dogfood_zero_sum_majorant.py --check   # drift check (no write)

The sites (SHAPES_AUDIT_48H_2026-09-22.md section 7, sprint 2 item 4; audit C 2.1):

  * ``E6Bridge19.lean`` ``zbound`` / ``norm_zterm_le_zbound`` (audit lines 324-355; 249-280 after the
    P1 prelude landed) -- the k-th Taylor term of the double-pole series on a ball, far constant
    ``(k+1)! 2^(k+2) (9/4)``: instance ``zbound_regen`` (centre 0, h = 1, ``1/normSq rho``, prefactor
    ``K = (k+1)! 2^(k+2)``);
  * ``E6Bridge18.lean`` ``polBound`` / ``norm_polTerm_le`` / ``summable_polTerm`` (audit lines 116-184)
    -- the double-pole term ``m/(s - rho)^2`` about the ordinate of ``s``, far constant
    ``13/4 + 2 (Im s)^2``: instance ``polBound_regen`` (centre ``Im s``, h = 1,
    ``1/(Im rho - Im s)^2``, the certificate's square ``(Im rho - 2 Im s)^2`` is the hand hint);
  * ``E6Bridge15.lean`` ``liBound`` / ``norm_liPaired_le`` / ``summable_liPaired`` (audit lines 349-410)
    -- the paired Li kernel, far constant ``(9/4) 2^n``: instance ``liBound_regen`` (the same 9/4
    certificate as ``zbound``, prefactor ``K = 2^n``);

plus the ``tail_envelope`` face (``tail_regen``, symbolic ``E``, rational ``P = -1/4``) re-deriving
E6Bridge12's ``tail_bound_window`` (audit B N5).

The written file is: a banner, the FROZEN emitter output (provenance header, imports, namespace),
then generator-appended Lean: the instance GLUE (each term family's own far-region norm shape,
copied from the hand proof -- the emitted ``hshape`` hypothesis, never emitted) and kernel
CROSS-CHECKS applying each regenerated theorem to the ORIGINAL's statement (and the original to the
regenerated one).  It imports the modules it regenerates from and modifies none; compile it with

    cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_zero_sum_majorant.lean

``tests/test_emit_zero_sum_majorant.py`` regenerates the file through this module and asserts byte
equality, so the checked-in Lean can never drift from the emitter.

conjecture1_proved = False -- summability of zero-indexed families and strip inequalities; nothing
here bears on RH.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    ValidationReport, ZeroSumMajorantEmitter, certify, emit, zero_sum_majorant_family,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_LEAN = Path(__file__).resolve().parent / "lean"
OUT = _LEAN / "Probes" / "Dogfood_zero_sum_majorant.lean"
IMPORTS = ("E6Bridge12", "E6Bridge15", "E6Bridge18", "E6Bridge19", "RvMBridgeXi")

# The four instances, exactly as the hand proofs shape them.
SPECS = {
    # E6Bridge19 zbound: zeroBound ((k+1)! 2^(k+2) (9/4)) b; far region via inv_normSq_le_majorant.
    0: dict(centre=0, h=1, c_far="9/4", num=1, den_kind="normSq", prefactor=True),
    # E6Bridge18 polBound: window |Im rho - Im s| < 1, far constant 13/4 + 2 (Im s)^2 over the
    # ordinate distance (the hand proof's hd : (Im rho - Im s)^2 <= |s - rho|^2 is the glue).
    1: dict(params=[("a", "s.im")], binders=[("s", "ℂ")], centre="a", h=1,
            c_far="13/4 + 2*a^2", num=1, den_kind="ordinate_sq"),
    # E6Bridge15 liBound: liC n = (9/4) 2^n; the same strip certificate as zbound.
    2: dict(centre=0, h=1, c_far="9/4", num=1, den_kind="normSq", prefactor=True),
    # B N5 tail face: E6Bridge12 tail_bound_window's envelope (symbolic E), and the rate
    # companion at the rational P = -1/4.
    3: dict(mode="tail_envelope", envelope_E="symbolic", rate_P="-1/4"),
}
NAMES = {
    0: "zbound_regen",
    1: "polBound_regen",
    2: "liBound_regen",
    3: "tail_regen",
}

BANNER = """/-
  Dogfood_zero_sum_majorant -- the Telperion `zero_sum_majorant` kind (SHAPES_AUDIT_48H_2026-09-22.md
  section 2 rank 2; audit C 3.1 + B N5) regenerating three hand-proof sites of this island and the
  tail-envelope consumer face, 2026-09-22:

    E6Bridge19  zbound / norm_zterm_le_zbound             -> zbound_regen_{strip,le,summable}
    E6Bridge18  polBound / norm_polTerm_le / summable_polTerm -> polBound_regen_{strip,le,summable}
    E6Bridge15  liBound / norm_liPaired_le / summable_liPaired -> liBound_regen_{strip,le,summable}
    E6Bridge12  tail_bound_window (the B N5 envelope)      -> tail_regen_{envelope,rate}

  Each zero_window instance's certificate is ONE strip inequality (1/|rho|^2 <= (9/4)/(1 + |gamma|^2)
  twice, 1/(Im rho - Im s)^2 <= (13/4 + 2 (Im s)^2)/(1 + |gamma|^2) once) certified as an exact
  nonnegative Bernstein / Polya combination checked by `ring`; the composition with the prelude atom
  RvMBridgeXi.zeroBoundAt is the frozen skeleton.

  The block between the telperion provenance header and `end DogfoodZeroSumMajorant` is the FROZEN
  emitter output (examples/rvm_bridge/dogfood_zero_sum_majorant.py regenerates it; a test pins the
  bytes).  After it, generator-appended and hand-written: the instance GLUE (each family's own
  far-region norm shape, copied from the hand proof; the emitted theorems take it as the named
  hypothesis `hshape`) and kernel CROSS-CHECKS that apply each regenerated theorem to the ORIGINAL's
  statement, so the kernel confirms the regeneration is interchangeable with the hand proof.  Nothing
  in E6Bridge12 / 15 / 18 / 19 is modified.

  Run: cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_zero_sum_majorant.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a summability or
  pointwise-majorant fact about a family indexed by the nontrivial zeros, or a rational inequality on
  the open strip, true whatever the real parts of the zeros are.
-/
"""

TRAILER = """
/-! ## Instance glue (generator-appended, hand-written; NOT emitted).  Each lemma is the term
    family's own analysis -- the far-region norm shape the emitted `hshape` hypothesis asks for, or
    the window bound `hwin` -- copied from the hand proof it replaces. -/

namespace DogfoodZeroSumMajorant.Glue
open Zeta23

/-- E6Bridge19: off the unit window the k-th Taylor term is at most
    `m(rho) ((k+1)! 2^(k+2)) (1 / normSq rho)` (norm_zterm_le and `|rho|^(k+2) >= |rho|^2`). -/
theorem zterm_shape (k : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2))
    {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((((k + 1).factorial : ℝ) * 2 ^ (k + 2)) * (1 / Complex.normSq ρ)) := by
  refine (RvMBridge19.norm_zterm_le hs h).trans ?_
  have hρ1 := RvMBridge19.one_le_norm_of_nontrivial him
  have hρ := RvMBridge19.norm_pos_of_nontrivial h
  have hpow : ‖ρ‖ ^ 2 ≤ ‖ρ‖ ^ (k + 2) := pow_le_pow_right₀ hρ1 (by omega)
  rw [Complex.normSq_eq_norm_sq]
  calc (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2) / ‖ρ‖ ^ (k + 2)
      ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ) * 2 ^ (k + 2) / ‖ρ‖ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by ring

/-- E6Bridge19: on the finitely many small zeros the k-th term is bounded by `zbound`'s window
    function `m(rho) (k+1)! 2^(k+2) / zeroRadius^(k+2)` (the radius is below every `|rho|`). -/
theorem zterm_window (k : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2))
    {ρ : ℂ} (h : IsNontrivialZero ρ) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * ((k + 1).factorial : ℝ)
      * 2 ^ (k + 2) / RvMBridge19.zeroRadius ^ (k + 2) := by
  refine (RvMBridge19.norm_zterm_le hs h).trans ?_
  have hr := RvMBridge19.zeroRadius_pos
  have hρ := RvMBridge19.norm_pos_of_nontrivial h
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact pow_le_pow_left₀ hr.le (RvMBridge19.zeroRadius_le h) _

/-- E6Bridge18: off the unit ordinate window about `Im s` the double-pole term is at most
    `m(rho) (1 / (Im rho - Im s)^2)` (the hand proof's `hd : (Im rho - Im s)^2 <= |s - rho|^2`). -/
theorem polTerm_shape {s ρ : ℂ} (hfar : (1 : ℝ) ≤ |ρ.im - s.im|) :
    ‖RvMBridge18.polTerm s ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (1 / (ρ.im - s.im) ^ 2) := by
  rw [RvMBridge18.norm_polTerm, ← mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hd1 : 1 ≤ (ρ.im - s.im) ^ 2 := by
    have := sq_abs (ρ.im - s.im)
    nlinarith [abs_nonneg (ρ.im - s.im)]
  have hd : (ρ.im - s.im) ^ 2 ≤ ‖s - ρ‖ ^ 2 := by
    have := Complex.abs_im_le_norm (s - ρ)
    rw [Complex.sub_im] at this
    have h2 : |s.im - ρ.im| ^ 2 = (s.im - ρ.im) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (s.im - ρ.im)]
  exact one_div_le_one_div_of_le (by linarith) hd

/-- E6Bridge15: off the unit window the paired Li term is at most `m(rho) (2^n (1 / normSq rho))`
    (abs_re_liKernel_le, the binomial expansion with the `j = 1` pairing). -/
theorem liPaired_shape (n : ℕ) {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    ‖RvMBridge15.liPaired n ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ) * (2 ^ n * (1 / Complex.normSq ρ)) := by
  rw [RvMBridge15.norm_liPaired]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hρ : 1 ≤ ‖ρ‖ := him.trans (Complex.abs_im_le_norm ρ)
  rw [mul_one_div]
  exact RvMBridge15.abs_re_liKernel_le h.2.1 h.2.2 hρ

end DogfoodZeroSumMajorant.Glue

/-! ## Kernel cross-checks against the hand-written originals (generator-appended).  Each
    `example` is closed by applying one side to the other's statement, so a drift in either
    statement fails to elaborate. -/

section CrossChecks
open Zeta23 DogfoodZeroSumMajorant

/-- The 9/4 strip certificate proves the prelude's hand-proved `RvMBridgeXi.inv_normSq_le_majorant`
    statement (the inequality E6Bridge19's `zbound` and E6Bridge15's `liBound` close with) ... -/
example {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (gammaOf ρ)) :=
  zbound_regen_strip h him

/-- ... and the hand-proved lemma proves the regenerated statement: the two are interchangeable. -/
example {ρ : ℂ} (h : IsNontrivialZero ρ) (him : (1 : ℝ) ≤ |ρ.im|) :
    1 / Complex.normSq ρ ≤ (9 / 4) / (1 + Complex.normSq (gammaOf ρ)) :=
  RvMBridgeXi.inv_normSq_le_majorant h him

/-- E6Bridge19 `norm_zterm_le_zbound`, VERBATIM: with `K := (k+1)! 2^(k+2)` the emitted constant
    `K * (9/4)` is `zbound`'s constant on the nose, and `zeroBoundAt 0 1` is `zeroBound`. -/
example (k : ℕ) (ρ : ℂ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2)) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ RvMBridge19.zbound k ρ := by
  unfold RvMBridge19.zbound
  rw [RvMBridgeXi.zeroBound_eq]
  exact zbound_regen_le (f := fun ρ => RvMBridge19.zterm k ρ s)
    (K := ((k + 1).factorial : ℝ) * 2 ^ (k + 2)) (by positivity)
    (fun _ h => RvMBridge19.zterm_eq_zero_of_not_nontrivial h s)
    (fun _ h _ => Glue.zterm_window k hs h)
    (fun _ h him => Glue.zterm_shape k hs h him) ρ

/-- The original proves the same statement. -/
example (k : ℕ) (ρ : ℂ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2)) :
    ‖RvMBridge19.zterm k ρ s‖ ≤ RvMBridge19.zbound k ρ :=
  RvMBridge19.norm_zterm_le_zbound k ρ hs

/-- The k-th Taylor terms are summable on the ball (the family `iteratedDeriv_tsum_ball` sums). -/
example (k : ℕ) {s : ℂ} (hs : s ∈ Metric.ball (0 : ℂ) (RvMBridge19.zeroRadius / 2)) :
    Summable (fun ρ => RvMBridge19.zterm k ρ s) :=
  zbound_regen_summable (K := ((k + 1).factorial : ℝ) * 2 ^ (k + 2)) (by positivity)
    (fun _ h => RvMBridge19.zterm_eq_zero_of_not_nontrivial h s)
    (fun _ h him => Glue.zterm_shape k hs h him)

/-- E6Bridge18 `norm_polTerm_le_majorant`: the regenerated ordinate strip plus the glue. -/
example {s ρ : ℂ} (h : IsNontrivialZero ρ) (hfar : 1 ≤ |ρ.im - s.im|) :
    ‖RvMBridge18.polTerm s ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((13 / 4 + 2 * s.im ^ 2) / (1 + Complex.normSq (gammaOf ρ))) :=
  (Glue.polTerm_shape hfar).trans
    (mul_le_mul_of_nonneg_left (polBound_regen_strip s h hfar) (Nat.cast_nonneg _))

/-- The original proves the same statement. -/
example {s ρ : ℂ} (h : IsNontrivialZero ρ) (hfar : 1 ≤ |ρ.im - s.im|) :
    ‖RvMBridge18.polTerm s ρ‖ ≤ (WeilExplicit.zeroMult ρ : ℝ)
      * ((13 / 4 + 2 * s.im ^ 2) / (1 + Complex.normSq (gammaOf ρ))) :=
  RvMBridge18.norm_polTerm_le_majorant h hfar

/-- E6Bridge18 `norm_polTerm_le`, VERBATIM: `polBound s` IS `zeroBoundAt (Im s) 1 (13/4 + 2 (Im s)^2)`
    with the window bound `norm (polTerm s)`, definitionally. -/
example (s ρ : ℂ) : ‖RvMBridge18.polTerm s ρ‖ ≤ RvMBridge18.polBound s ρ :=
  polBound_regen_le s (b := fun ρ => ‖RvMBridge18.polTerm s ρ‖)
    (fun _ h => RvMBridge18.polTerm_eq_zero_of_not_nontrivial h) (fun _ _ _ => le_rfl)
    (fun _ _ hfar => Glue.polTerm_shape hfar) ρ

/-- E6Bridge18 `summable_polTerm`, VERBATIM. -/
example (s : ℂ) : Summable (RvMBridge18.polTerm s) :=
  polBound_regen_summable s (fun _ h => RvMBridge18.polTerm_eq_zero_of_not_nontrivial h)
    (fun _ _ hfar => Glue.polTerm_shape hfar)

/-- E6Bridge15 `norm_liPaired_le`, VERBATIM: with `K := 2^n` the regenerated majorant equals
    `liBound n` (`liC n = (9/4) 2^n`; `zeroBoundAt 0 1` is the small-zero window). -/
example (n : ℕ) (ρ : ℂ) : ‖RvMBridge15.liPaired n ρ‖ ≤ RvMBridge15.liBound n ρ := by
  have hle := liBound_regen_le (f := RvMBridge15.liPaired n)
    (b := fun ρ => ‖RvMBridge15.liPaired n ρ‖) (K := 2 ^ n) (by positivity)
    (fun _ h => RvMBridge15.liPaired_eq_zero_of_not_nontrivial h) (fun _ _ _ => le_rfl)
    (fun _ h him => Glue.liPaired_shape n h him) ρ
  have heq : RvMBridgeXi.zeroBoundAt 0 1 (2 ^ n * (9 / 4)) (fun ρ => ‖RvMBridge15.liPaired n ρ‖) ρ
      = RvMBridge15.liBound n ρ := by
    simp only [RvMBridgeXi.zeroBoundAt, RvMBridge15.liBound, RvMBridge15.liC,
      RvMBridgeXi.windowZeros, sub_zero]
    ring
  exact hle.trans heq.le

/-- E6Bridge15 `summable_liPaired`, VERBATIM. -/
example (n : ℕ) : Summable (RvMBridge15.liPaired n) :=
  liBound_regen_summable (K := 2 ^ n) (by positivity)
    (fun _ h => RvMBridge15.liPaired_eq_zero_of_not_nontrivial h)
    (fun _ h him => Glue.liPaired_shape n h him)

/-- The regenerated envelope (symbolic `E`) and the prelude's `norm_tsum_subtype_le_mul_tsum` prove
    each other's statement ... -/
example {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) {E : ℝ} (hE : 0 ≤ E)
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ E * w x) :
    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x :=
  RvMBridgeGauss.norm_tsum_subtype_le_mul_tsum S hE hw hw0 hle

example {ι : Type*} {f : ι → ℂ} {w : ι → ℝ} (S : Set ι) {E : ℝ} (hE : 0 ≤ E)
    (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x) (hle : ∀ x : S, ‖f x‖ ≤ E * w x) :
    ‖∑' x : S, f x‖ ≤ E * ∑' x : ι, w x :=
  tail_regen_envelope S hE hw hw0 hle

/-- ... and the regenerated envelope re-derives E6Bridge12's `tail_bound_window` line for line
    (E6Bridge12.lean:271-281 with the envelope swapped in). -/
example {c D : ℝ} (hD : 0 ≤ D) {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : ↥(RvMBridgeGauss.winSet c D)ᶜ, RvMBridge7.term c lam ρ‖
      ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * RvMBridge7.constB c := by
  rw [← RvMBridge12.tsum_tailWeight c]
  refine tail_regen_envelope (RvMBridgeGauss.winSet c D)ᶜ (Real.exp_pos _).le
    (RvMBridge12.summable_tailWeight c) (RvMBridge12.tailWeight_nonneg c) fun ρ => ?_
  have hfar : D < |(ρ : ℂ).im - c| := by
    have h := ρ.2
    simp only [RvMBridgeGauss.winSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at h
    exact h
  exact RvMBridge12.norm_term_le_tail hD hlam hfar

/-- The original proves the same statement. -/
example {c D : ℝ} (hD : 0 ≤ D) {lam : ℝ} (hlam : 1 ≤ lam) :
    ‖∑' ρ : ↥(RvMBridgeGauss.winSet c D)ᶜ, RvMBridge7.term c lam ρ‖
      ≤ Real.exp (2 * (lam - 1) * (1 / 4 - D ^ 2)) * RvMBridge7.constB c :=
  RvMBridge12.tail_bound_window hD hlam

/-- The rate face's first conjunct is the prelude companion `exp_two_mul_le_of_le` at `P = -1/4`;
    the second is what `P < 0` buys (the envelope factor is at most 1). -/
example {lam φ : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ -(1 / 4)) :
    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * (-(1 / 4))) * Real.exp (2 * φ) :=
  (tail_regen_rate hlam hφ).1

example {lam φ : ℝ} (hlam : 1 ≤ lam) (hφ : φ ≤ -(1 / 4)) :
    Real.exp (2 * lam * φ) ≤ Real.exp (2 * (lam - 1) * (-(1 / 4))) * Real.exp (2 * φ) :=
  RvMBridgeGauss.exp_two_mul_le_of_le hlam hφ

end CrossChecks

#print axioms DogfoodZeroSumMajorant.zbound_regen_strip
#print axioms DogfoodZeroSumMajorant.zbound_regen_le
#print axioms DogfoodZeroSumMajorant.zbound_regen_summable
#print axioms DogfoodZeroSumMajorant.polBound_regen_strip
#print axioms DogfoodZeroSumMajorant.polBound_regen_le
#print axioms DogfoodZeroSumMajorant.polBound_regen_summable
#print axioms DogfoodZeroSumMajorant.liBound_regen_strip
#print axioms DogfoodZeroSumMajorant.liBound_regen_le
#print axioms DogfoodZeroSumMajorant.liBound_regen_summable
#print axioms DogfoodZeroSumMajorant.tail_regen_envelope
#print axioms DogfoodZeroSumMajorant.tail_regen_rate
#print axioms DogfoodZeroSumMajorant.Glue.zterm_shape
#print axioms DogfoodZeroSumMajorant.Glue.zterm_window
#print axioms DogfoodZeroSumMajorant.Glue.polTerm_shape
#print axioms DogfoodZeroSumMajorant.Glue.liPaired_shape
"""


def family():
    return zero_sum_majorant_family(
        "DogfoodZeroSumMajorant",
        GridSpec([("i", sorted(SPECS))]),
        lambda pt: NAMES[pt["i"]],
        spec=lambda pt: SPECS[pt["i"]],
    )


def emitted_text() -> str:
    """The frozen emitter output alone (header + imports + namespace + theorems)."""
    report = emit(
        certify(family()),
        LeanProfile(namespace=("DogfoodZeroSumMajorant",), imports=IMPORTS),
        [ZeroSumMajorantEmitter()],
        ValidationReport(checks=(("zero_sum_majorant", True),)),
        file_name="Dogfood_zero_sum_majorant.lean",
    )
    return report.files["Dogfood_zero_sum_majorant.lean"]


def build_text() -> str:
    """The complete probe file: banner + frozen emitter output + glue + kernel cross-checks."""
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
