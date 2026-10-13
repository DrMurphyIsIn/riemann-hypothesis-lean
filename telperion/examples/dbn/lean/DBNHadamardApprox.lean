/-
  DBNHadamardApprox -- obligation L3 for the de Bruijn approximants, and the assembly of
  de Bruijn's theorem (Route C / C3, registry node `RH_dbn_debruijn_real_zeros`, statement
  verbatim).

  * `norm_Gδ_le_growth`: the island's order bound `norm_Gδ_le_exp_rpow_norm` rewritten in the
    shape `‖Gδ δ N z‖ ≤ A exp(B ‖z‖^(3/2))` with `1 ≤ A`, `0 ≤ B` (order `3/2 < 2`);
  * `approxHadamard : ApproxHadamard` -- every approximant `Gδ δ k` carries even Hadamard data,
    by `DBNHadamard.evenHadamardData_of_order_lt_two` (entire: `differentiable_Gδ`; even:
    `Gδ_neg`; not identically zero: `Gδ_zero_re_pos`);
  * `H0ZeroFreeOffStrip_holds : H0ZeroFreeOffStrip` -- the contrapositive of the strip theorem
    `H0_zero_strip` (registry node `RH_dbn_H0_zero_strip`, `DBNStrip`);
  * `H_zero_im_sq_le` / `H_ne_zero_of_half_le` -- the conditional theorems of
    `DBNDeBruijnReduction` with both obligations discharged;
  * `dbn_debruijn_real_zeros` -- de Bruijn's theorem: for `t ≥ 1/2` every zero of `H_t` is real,
    i.e. the de Bruijn-Newman constant satisfies `Λ ≤ 1/2`.

  This is classical (de Bruijn 1950) and says nothing about the zeros of `H_0` inside the strip
  `|Im z| ≤ 1`, which is where RH lives.  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNHadamard
import DBNDeBruijnReduction
import DBNStrip

open Real

namespace DBN

/-- **Order `3/2` growth bound in the shape the factorisation theorem consumes.** -/
lemma norm_Gδ_le_growth (δ : ℝ) (N : ℕ) :
    ∃ A B : ℝ, 1 ≤ A ∧ 0 ≤ B ∧ ∀ z, ‖Gδ δ N z‖ ≤ A * Real.exp (B * ‖z‖ ^ (3 / 2 : ℝ)) := by
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = 9 + N * |δ| := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  have hC : 0 ≤ ΦBoundConst / π := div_nonneg ΦBoundConst_nonneg Real.pi_pos.le
  refine ⟨max 1 (ΦBoundConst / π * Real.exp (2 / 3 * c₀ ^ (3 / 2 : ℝ))), 2 / 3,
    le_max_left _ _, by norm_num, fun z ↦ ?_⟩
  have h := norm_Gδ_le_exp_rpow_norm δ N z
  rw [← hc₀] at h
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hmax : ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ) ≤ c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ) := by
    rcases le_total c₀ ‖z‖ with hle | hle
    · calc ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ) ≤ ‖z‖ ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ ≤ c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ) :=
            le_add_of_nonneg_left (Real.rpow_nonneg hc₀0 _)
    · calc ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ) ≤ c₀ ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ ≤ c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ) :=
            le_add_of_nonneg_right (Real.rpow_nonneg hz0 _)
  calc ‖Gδ δ N z‖
      ≤ ΦBoundConst / π * Real.exp (2 / 3 * ((c₀ + ‖z‖) / 2) ^ (3 / 2 : ℝ)) := h
    _ ≤ ΦBoundConst / π * Real.exp (2 / 3 * (c₀ ^ (3 / 2 : ℝ) + ‖z‖ ^ (3 / 2 : ℝ))) := by
        gcongr
    _ = (ΦBoundConst / π * Real.exp (2 / 3 * c₀ ^ (3 / 2 : ℝ)))
          * Real.exp (2 / 3 * ‖z‖ ^ (3 / 2 : ℝ)) := by
        rw [mul_add, Real.exp_add]; ring
    _ ≤ max 1 (ΦBoundConst / π * Real.exp (2 / 3 * c₀ ^ (3 / 2 : ℝ)))
          * Real.exp (2 / 3 * ‖z‖ ^ (3 / 2 : ℝ)) := by
        gcongr
        exact le_max_right _ _

/-- The approximants are not identically zero. -/
lemma Gδ_exists_ne_zero (δ : ℝ) (N : ℕ) : ∃ z, Gδ δ N z ≠ 0 :=
  ⟨0, fun h ↦ by
    have := Gδ_zero_re_pos δ N
    rw [h] at this
    simp at this⟩

/-- **Obligation L3 discharged**: every de Bruijn approximant carries even Hadamard data. -/
theorem approxHadamard : ApproxHadamard := by
  intro δ _ k
  obtain ⟨A, B, hA, hB, hgrowth⟩ := norm_Gδ_le_growth δ k
  exact evenHadamardData_of_order_lt_two (differentiable_Gδ δ k) (Gδ_neg δ k)
    (Gδ_exists_ne_zero δ k) hA hB (by norm_num) (by norm_num) hgrowth

/-- **Obligation L1 discharged**: the contrapositive of the strip theorem `H0_zero_strip`. -/
theorem H0ZeroFreeOffStrip_holds : H0ZeroFreeOffStrip := fun z hz h0 ↦ by
  have := H0_zero_strip z h0
  linarith

/-- Strip contraction for the heat flow, unconditional: for `t ≥ 0` every zero of `H t`
satisfies `(Im z)² ≤ max (1 − 2t) 0`. -/
theorem H_zero_im_sq_le {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : H t z = 0) :
    z.im ^ 2 ≤ max (1 - 2 * t) 0 :=
  H_zero_im_sq_le_of_obligations H0ZeroFreeOffStrip_holds approxHadamard ht hz

/-- De Bruijn's theorem, island form: for `t ≥ 1/2`, `H t` has no zero off the real axis. -/
theorem H_ne_zero_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) {z : ℂ} (hz : z.im ≠ 0) : H t z ≠ 0 :=
  H_ne_zero_of_obligations H0ZeroFreeOffStrip_holds approxHadamard ht hz

end DBN

/-- Registry node `RH_dbn_debruijn_real_zeros`, statement verbatim: de Bruijn's theorem, for
`t ≥ 1/2` every zero of `H_t` is real (`Λ ≤ 1/2`).  Classical (1950), unconditional on this
island; it says nothing about the zeros of `H_0` inside the strip, which is where RH lives.
Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_debruijn_real_zeros :
    ∀ t : ℝ, 1 / 2 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  fun _ ht _ hz ↦ by_contra fun him ↦ DBN.H_ne_zero_of_half_le ht him hz
