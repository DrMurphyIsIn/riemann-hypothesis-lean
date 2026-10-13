/-
  E6Bridge -- routes-roadmap E6 (2026-09-17): the MIRRORMERE residual
  MM_rvm_unbounded_mean_density discharged from Anthropic's zeta-23-lean
  (Alpoege--Furman, "More than two thirds of the zeta zeros are simple and on the critical
  line", arXiv:2608.13637; Apache-2.0; pinned in lakefile.toml).

  WHAT IS CONSUMED (all unconditional in the pinned Zeta23, #print axioms =
  [propext, Classical.choice, Quot.sound], see AxiomGuardRvMBridge.lean):
    * Zeta23.thmA₀ : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2/3 - ε) * Ncount T (2T) ≤ N0star T (2T)
      (Theorem A, dyadic form: N0star is the ncard of the DISTINCT critical-line zeros).
    * Zeta23.riemannVonMangoldt_zeta.main : ∃ C T₀, ∀ T ≥ T₀,
        |Ncount T (2T) - T/(2π) * ell1 T| ≤ C * log T   (the dyadic RvM main clause).
    * Zeta23.zetaSeam.finite_window (finitely many strip zeros in a window).

  WHY THEOREM A AND NOT THE RvM FORMULA ALONE (roadmap correction): the target needs
  DISTINCT ordinates; every multiplicity-weighted count, however sharp, only bounds the
  fibre of Complex.im by the local count O(log T), which kills the superlinear growth.
  Distinct points on Re = 1/2 have distinct ordinates, so a positive proportion of zeros on
  the critical line is exactly the missing input.

  The window is [T, 2T] itself (a := T, L := T); F is the image of Complex.im on the finite
  set of critical-line zeros with T < Im ≤ 2T; thmA₀ at ε = 1/3 and
  Ncount T (2T) ≥ (T/4π) log T give r*T + 1 < F.card for large T.

  The two definitions below MIRROR telperion/missions/mirrormere/lean/Statements/MMDefs.lean:48-53
  verbatim (RvMUnboundedMeanDensity is itself a verbatim extract of the v4.32 quasicrystal
  island's BoundaryLemmas.lean:342-344; zetaOrdinates is the registry's AUTHORED pin of the
  ordinate set). The theorem line is the node statement of
  telperion/missions/mirrormere/lean/Statements/MM_rvm_unbounded_mean_density.lean verbatim
  (name and binder-free form), so the registry's normalized-containment grant gate matches.

  No RH progress is claimed: this is a classical (Selberg-type) consequence, machine-checked.
  conjecture1_proved = False.
-/
import Zeta23.Unconditional

open Zeta23 Filter

namespace RvMBridge

-- ===== MIRROR of MMDefs.lean:48-50 (BoundaryLemmas.lean:342-344) =====
def RvMUnboundedMeanDensity (S : Set ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ (F : Finset ℝ) (a L : ℝ),
    0 ≤ L ∧ (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ r * L + 1 < F.card

-- ===== MIRROR of MMDefs.lean:52-53 (AUTHORED for the registry) =====
def zetaOrdinates : Set ℝ :=
  {t : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.im = t}

/-- `ell1 T = log T + c0` for `T > 0` (Zeta23's `ell1 T := log (T / 2π) + 2 log 2 - 1`). -/
lemma ell1_eq_log_add {T : ℝ} (hT : 0 < T) :
    ell1 T = Real.log T + (2 * Real.log 2 - 1 - Real.log (2 * Real.pi)) := by
  unfold ell1 l
  rw [Real.log_div hT.ne' (by positivity)]
  ring

/-- The dyadic multiplicity count grows like `T log T` (from the RvM main clause). -/
lemma eventually_Ncount_ge :
    ∀ᶠ T in atTop, T / (4 * Real.pi) * Real.log T ≤ (Ncount T (2 * T) : ℝ) := by
  obtain ⟨C, T₀, h⟩ := riemannVonMangoldt_zeta.main
  set c0 : ℝ := 2 * Real.log 2 - 1 - Real.log (2 * Real.pi) with hc0
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hev1 : ∀ᶠ T in atTop, 4 * |c0| ≤ Real.log T := hlog.eventually_ge_atTop _
  have hev2 : ∀ᶠ T in atTop, max 1 (8 * Real.pi * C) ≤ T := eventually_ge_atTop _
  have hev3 : ∀ᶠ T in atTop, T₀ ≤ T := eventually_ge_atTop _
  filter_upwards [hev1, hev2, hev3] with T h1 h2 h3
  have hT1 : 1 ≤ T := (le_max_left _ _).trans h2
  have hTC : 8 * Real.pi * C ≤ T := (le_max_right _ _).trans h2
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hπ : 0 < Real.pi := Real.pi_pos
  have hmain := h T h3
  rw [zetaZeroConfig_N] at hmain
  have hlow : T / (2 * Real.pi) * ell1 T - C * Real.log T ≤ (Ncount T (2 * T) : ℝ) := by
    have := (abs_le.mp hmain).1
    linarith
  rw [ell1_eq_log_add hTpos, ← hc0] at hlow
  -- T/(2π)(log T + c0) - C log T ≥ T/(4π) log T
  have hc0' : -|c0| ≤ c0 := neg_abs_le c0
  -- piece 1: T/(8π) log T ≥ T |c0| / (2π)  since log T ≥ 4|c0|
  have hp1 : T / (2 * Real.pi) * |c0| ≤ T / (8 * Real.pi) * Real.log T := by
    have : T / (2 * Real.pi) * |c0| = T / (8 * Real.pi) * (4 * |c0|) := by
      field_simp; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  -- piece 2: C log T ≤ T/(8π) log T since T ≥ 8πC
  have hp2 : C * Real.log T ≤ T / (8 * Real.pi) * Real.log T := by
    apply mul_le_mul_of_nonneg_right _ hlogT
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hsplit : T / (2 * Real.pi) * (Real.log T + c0) =
      T / (4 * Real.pi) * Real.log T + T / (8 * Real.pi) * Real.log T
        + T / (8 * Real.pi) * Real.log T + T / (2 * Real.pi) * c0 := by
    field_simp; ring
  have hc0T : - (T / (2 * Real.pi) * |c0|) ≤ T / (2 * Real.pi) * c0 := by
    have := mul_le_mul_of_nonneg_left hc0' (by positivity : (0:ℝ) ≤ T / (2 * Real.pi))
    linarith
  nlinarith [hlow, hsplit, hp1, hp2, hc0T]

/-- The MIRRORMERE node statement, verbatim: window `[T, 2T]`, ordinates of the distinct
critical-line zeros (Zeta23 Theorem A + the RvM main clause). -/
theorem rvm_unbounded_mean_density : RvMUnboundedMeanDensity zetaOrdinates := by
  intro r hr
  obtain ⟨T₂, hA⟩ := thmA₀ (1 / 3) (by norm_num)
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hev3 : ∀ᶠ T in atTop, 12 * Real.pi * (r + 2) ≤ Real.log T :=
    hlog.eventually_ge_atTop _
  obtain ⟨T, hT2, hT1, hT3, hTge1⟩ :=
    ((eventually_ge_atTop T₂).and (eventually_Ncount_ge.and
      (hev3.and (eventually_ge_atTop (1 : ℝ))))).exists
  have hTpos : 0 < T := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  -- the set of distinct critical-line zeros in the dyadic window
  set S : Set ℂ := zerosIn T (2 * T) ∩ {ρ | ρ.re = 1 / 2} with hS
  have hfin : S.Finite := by
    refine (zetaSeam.finite_window T (2 * T)).subset ?_
    intro ρ hρ
    exact ⟨hρ.1.1, hρ.1.2⟩
  have hinj : Set.InjOn Complex.im S := by
    intro ρ hρ ρ' hρ' h
    apply Complex.ext
    · have e1 : ρ.re = 1 / 2 := hρ.2
      have e2 : ρ'.re = 1 / 2 := hρ'.2
      rw [e1, e2]
    · exact h
  have hfinI : (Complex.im '' S).Finite := hfin.image _
  refine ⟨hfinI.toFinset, T, T, hTpos.le, ?_, ?_, ?_⟩
  · -- ordinates of zeta zeros
    intro x hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    obtain ⟨⟨hz, h0, h1⟩, _, _⟩ := hρ.1
    exact ⟨ρ, hz, h0, h1, rfl⟩
  · -- inside the window [T, T + T]
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    obtain ⟨_, hlt, hle⟩ := hρ.1
    constructor
    · exact hlt.le
    · linarith
  · -- the count
    have hcard : (hfinI.toFinset.card : ℝ) = (N0star T (2 * T) : ℝ) := by
      rw [← Set.ncard_eq_toFinset_card _ hfinI, hinj.ncard_image]
      rfl
    have hA' := hA T hT2
    have hcnt : T / (4 * Real.pi) * Real.log T ≤ (Ncount T (2 * T) : ℝ) := hT1
    rw [hcard]
    have h13 : (2 / 3 - 1 / 3 : ℝ) = 1 / 3 := by norm_num
    rw [h13] at hA'
    -- r*T + 1 < (1/3) * T/(4π) * log T  ≤ (1/3) Ncount ≤ N0star
    have hbig : r * T + 1 < 1 / 3 * (T / (4 * Real.pi) * Real.log T) := by
      have : 1 / 3 * (T / (4 * Real.pi) * Real.log T) = T / (12 * Real.pi) * Real.log T := by
        field_simp; ring
      rw [this]
      have hh : T / (12 * Real.pi) * (12 * Real.pi * (r + 2)) ≤
          T / (12 * Real.pi) * Real.log T :=
        mul_le_mul_of_nonneg_left hT3 (by positivity)
      have : T / (12 * Real.pi) * (12 * Real.pi * (r + 2)) = T * (r + 2) := by
        field_simp
      nlinarith
    have hNc : (0 : ℝ) ≤ Ncount T (2 * T) := Nat.cast_nonneg _
    calc r * T + 1 < 1 / 3 * (T / (4 * Real.pi) * Real.log T) := hbig
      _ ≤ 1 / 3 * (Ncount T (2 * T) : ℝ) := by nlinarith
      _ ≤ (N0star T (2 * T) : ℝ) := hA'

end RvMBridge
