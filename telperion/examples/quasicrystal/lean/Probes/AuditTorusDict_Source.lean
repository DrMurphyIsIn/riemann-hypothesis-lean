/-  AUDIT PROBE A2 (2026-09-22), node MM_torus_section_dictionary, auditor 2 of 2 (blind).
    NOT a lean_lib, NOT a default target, NOT covered by any axiom guard.  Run by hand with

        cd telperion/examples/quasicrystal/lean && lake env lean Probes/AuditTorusDict_Source.lean

    Between the two AUDIT PROBE markers this file is TorusSectionLadder.lean VERBATIM (the
    artifact of the node), re-elaborated from source so that no pre-built olean of the artifact
    is trusted (the only such olean found on this machine, in an old local checkout, is orphaned: its
    source no longer exists there).  The trailing block prints the axiom set of the node
    theorem, of the sibling rung, of the vocabulary anchor, of every definition they unfold,
    and of the Mathlib lemmas the simp proof reaches.  Expected on every line:
    [propext, Classical.choice, Quot.sound] or a subset; no sorryAx, no ofReduceBool.

    conjecture1_proved = False.  Nothing here proves, or approaches, RH.
    ===== BEGIN TorusSectionLadder.lean VERBATIM ===== -/
/-
  TorusSectionLadder.lean -- PROGRAM MIRRORMERE torus-section ladder, rung T1
  (QC_TORUS_SECTION_LADDER_MEMO_2026-09-14, sections 5-6).

  Discharges the two registry nodes of the ladder's T1 track, stated VERBATIM from
  telperion/missions/mirrormere/lean/Statements/:
    * MM_torus_section_dictionary  -- twoFreq (the island's verbatim two-frequency
      sum, TwoFreqRigidity.lean:40-42) IS the N = 2 instance of the ladder's section
      vocabulary: linearTorusForm 2 ![c₁, c₂] on torusOrbit 2 ![lam₁, lam₂].
    * MM_torus_section_n2_rigidity -- the R3(n=2) rigidity biconditional
      (twoFreq_realRooted_iff, TwoFreqRigidity.lean:92-94) restated in ladder
      vocabulary; the discharge is the dictionary rewrite followed by the island
      theorem.

  GRADE (recorded honestly, per the 2026-09-18 adversarial re-read): BOTH are
  vocabulary bridges, not mathematics.  The dictionary closes by `simp` (a Fin-2 sum
  unfolding: Fin.sum_univ_two + Matrix.cons_val_zero/one); the rigidity rung is a
  one-line rewrite into the already-proved island theorem.  They are what the
  ladder's vocabulary needs and what the registry consumes; they are NOT counted as
  wins.  The general-N identity expSum = linearTorusForm on torusOrbit is
  definitional (rfl) and is recorded below only so the vocabulary anchor is explicit.

  The three definitions MIRROR MMDefs.lean:69-76 verbatim (AUTHORED registry
  vocabulary, not island extracts), so the registry's normalized-containment grant
  gate matches the theorem lines.

  No RH progress is claimed.  conjecture1_proved = False.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import TwoFreqRigidity

open Complex

namespace Quasicrystal

noncomputable section

-- ===== MIRROR of MMDefs.lean:69-70 (AUTHORED for the torus-section ladder, T1) =====
noncomputable def torusOrbit (N : ℕ) (lam : Fin N → ℝ) (x : ℂ) : Fin N → ℂ :=
  fun j => Complex.exp ((lam j : ℂ) * x * Complex.I)

-- ===== MIRROR of MMDefs.lean:72-73 =====
def linearTorusForm (N : ℕ) (c : Fin N → ℂ) (z : Fin N → ℂ) : ℂ :=
  ∑ j, c j * z j

-- ===== MIRROR of MMDefs.lean:75-76 =====
noncomputable def expSum (N : ℕ) (c : Fin N → ℂ) (lam : Fin N → ℝ) (x : ℂ) : ℂ :=
  ∑ j, c j * Complex.exp ((lam j : ℂ) * x * Complex.I)

/-- The general-N section identity.  DEFINITIONAL (rfl): this is the statement the
2026-09-14 blind audit flagged as zero-content; kept only as the explicit vocabulary
anchor, never as a node. -/
theorem expSum_eq_linearTorusForm_torusOrbit (N : ℕ) (c : Fin N → ℂ) (lam : Fin N → ℝ)
    (x : ℂ) :
    expSum N c lam x = linearTorusForm N c (torusOrbit N lam x) := rfl

/-- **MM_torus_section_dictionary** (statement VERBATIM from the registry).  The
island's `twoFreq` is the N = 2 section: a Fin-2 sum unfolding across the two
vocabularies.  simp-grade. -/
theorem torus_section_dictionary (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ) (x : ℂ) :
    twoFreq c₁ c₂ lam₁ lam₂ x
      = linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) := by
  simp [twoFreq, linearTorusForm, torusOrbit, Fin.sum_univ_two]

/-- **MM_torus_section_n2_rigidity** (statement VERBATIM from the registry).  The
N = 2 rung in ladder vocabulary: rewrite through the dictionary and apply the island's
`twoFreq_realRooted_iff`.  Pure bridge; the mathematics lives in TwoFreqRigidity. -/
theorem torus_section_n2_rigidity (c₁ c₂ : ℂ) (lam₁ lam₂ : ℝ)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hlam : lam₁ ≠ lam₂) :
    (∀ x : ℂ, linearTorusForm 2 ![c₁, c₂] (torusOrbit 2 ![lam₁, lam₂] x) = 0 → x.im = 0)
      ↔ ‖c₁‖ = ‖c₂‖ := by
  simp only [← torus_section_dictionary]
  exact twoFreq_realRooted_iff c₁ c₂ lam₁ lam₂ hc₁ hc₂ hlam

end

end Quasicrystal

-- ===== END TorusSectionLadder.lean VERBATIM; AUDIT PROBE A2 prints follow =====
#print Quasicrystal.twoFreq
#print axioms Quasicrystal.twoFreq
#print axioms Quasicrystal.torusOrbit
#print axioms Quasicrystal.linearTorusForm
#print axioms Quasicrystal.expSum
#print axioms Quasicrystal.expSum_eq_linearTorusForm_torusOrbit
#print axioms Quasicrystal.torus_section_dictionary
#print axioms Quasicrystal.torus_section_n2_rigidity
#print axioms Quasicrystal.twoFreq_realRooted_iff
#print axioms Fin.sum_univ_two
#print axioms Matrix.cons_val_zero
#print axioms Matrix.cons_val_one
#print axioms Matrix.head_cons
