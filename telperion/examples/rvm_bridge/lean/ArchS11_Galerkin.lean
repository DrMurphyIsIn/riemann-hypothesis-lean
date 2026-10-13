/-
  ArchS11_Galerkin -- the Galerkin + Schur-complement quadratic-form bound (stage S11, rvm_bridge
  island, 2026-10-11).  Pure Hilbert-space algebra; the KWin_Tail pattern with a computed cross term.

  `galerkin_form`: let T be symmetric on an inner product space E over 𝕜 (ℝ or ℂ), φ_0..φ_{N-1}
  vectors spanning V, ρ_j vectors with T φ_j - ρ_j ∈ V, and real matrices G, C, R with
      ⟪φ_j, φ_l⟫ = G_jl,   ⟪T φ_j, φ_l⟫ = C_jl,   ‖Σ z_j ρ_j‖² ≤ qf R z  (e.g. R = Gram(ρ), or the
  diagonal weighted-Cauchy-Schwarz bound `norm_sum_sq_le_weighted`).
  If re ⟪T r, r⟫ ≤ q ‖r‖² on Vᗮ (the tail), t > 0, q + 1/t ≤ λ, and λG - C - tR is positive
  semidefinite (as a real quadratic form), then re ⟪T f, f⟫ ≤ λ ‖f‖² for EVERY f ∈ E.
  Proof: f = h + r with h the orthogonal projection on V; ⟪T h, r⟫ = ⟪Σ a_j ρ_j, r⟫ because
  T h - Σ a_j ρ_j ∈ V; then 2‖w‖‖r‖ ≤ t‖w‖² + ‖r‖²/t.  No `sorry`.  conjecture1_proved = False.
-/
import Mathlib

open Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS11

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The real quadratic form of a real matrix, evaluated at a 𝕜-vector. -/
def qf (N : ℕ) (M : ℕ → ℕ → ℝ) (z : ℕ → 𝕜) : ℝ :=
  ∑ j ∈ range N, ∑ l ∈ range N, M j l * RCLike.re (conj (z j) * z l)

theorem re_conj_mul (z w : 𝕜) :
    RCLike.re (conj z * w) = RCLike.re z * RCLike.re w + RCLike.im z * RCLike.im w := by
  rw [RCLike.mul_re, RCLike.conj_re, RCLike.conj_im]
  ring

theorem qf_eq (N : ℕ) (M : ℕ → ℕ → ℝ) (z : ℕ → 𝕜) :
    qf N M z = (∑ j ∈ range N, ∑ l ∈ range N, RCLike.re (z j) * RCLike.re (z l) * M j l)
      + ∑ j ∈ range N, ∑ l ∈ range N, RCLike.im (z j) * RCLike.im (z l) * M j l := by
  unfold qf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [re_conj_mul]
  ring

theorem inner_sum_smul (N : ℕ) (x y : ℕ → E) (z : ℕ → 𝕜) :
    ⟪∑ j ∈ range N, z j • x j, ∑ l ∈ range N, z l • y l⟫_𝕜
      = ∑ j ∈ range N, ∑ l ∈ range N, conj (z j) * z l * ⟪x j, y l⟫_𝕜 := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem re_inner_sum_smul (N : ℕ) (x y : ℕ → E) (z : ℕ → 𝕜) (M : ℕ → ℕ → ℝ)
    (hM : ∀ j < N, ∀ l < N, ⟪x j, y l⟫_𝕜 = (M j l : 𝕜)) :
    RCLike.re ⟪∑ j ∈ range N, z j • x j, ∑ l ∈ range N, z l • y l⟫_𝕜 = qf N M z := by
  rw [inner_sum_smul, map_sum]
  unfold qf
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [hM j (Finset.mem_range.1 hj) l (Finset.mem_range.1 hl), mul_comm, RCLike.re_ofReal_mul]

/-- A positive semidefinite real form, applied to the real and imaginary parts. -/
theorem qf_nonneg (N : ℕ) (M : ℕ → ℕ → ℝ)
    (hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ j ∈ range N, ∑ l ∈ range N, x j * x l * M j l) (z : ℕ → 𝕜) :
    0 ≤ qf N M z := by
  rw [qf_eq]
  exact add_nonneg (hpsd fun j => RCLike.re (z j)) (hpsd fun j => RCLike.im (z j))

theorem qf_sub_smul (N : ℕ) (lam t : ℝ) (G C R : ℕ → ℕ → ℝ) (z : ℕ → 𝕜) :
    qf N (fun j l => lam * G j l - C j l - t * R j l) z
      = lam * qf N G z - qf N C z - t * qf N R z := by
  unfold qf
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The Galerkin + Schur bound.**  See the module docstring. -/
theorem galerkin_form (T : E →L[𝕜] E) (hT : ∀ x y, ⟪T x, y⟫_𝕜 = ⟪x, T y⟫_𝕜)
    (N : ℕ) (φ ρ : ℕ → E) (G C R : ℕ → ℕ → ℝ)
    (hG : ∀ j < N, ∀ l < N, ⟪φ j, φ l⟫_𝕜 = (G j l : 𝕜))
    (hC : ∀ j < N, ∀ l < N, ⟪T (φ j), φ l⟫_𝕜 = (C j l : 𝕜))
    (hres : ∀ z : ℕ → 𝕜, ‖∑ j ∈ range N, z j • ρ j‖ ^ 2 ≤ qf N R z)
    (hρ : ∀ j < N, T (φ j) - ρ j ∈ Submodule.span 𝕜 (Set.range fun l : Fin N => φ l))
    {q lam t : ℝ}
    (hq : ∀ r ∈ (Submodule.span 𝕜 (Set.range fun l : Fin N => φ l))ᗮ,
      RCLike.re ⟪T r, r⟫_𝕜 ≤ q * ‖r‖ ^ 2)
    (ht : 0 < t) (hlt : q + 1 / t ≤ lam)
    (hpsd : ∀ x : ℕ → ℝ,
      0 ≤ ∑ j ∈ range N, ∑ l ∈ range N, x j * x l * (lam * G j l - C j l - t * R j l))
    (f : E) : RCLike.re ⟪T f, f⟫_𝕜 ≤ lam * ‖f‖ ^ 2 := by
  set V := Submodule.span 𝕜 (Set.range fun l : Fin N => φ l) with hV
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)
  set h := V.starProjection f with hhdef
  set r := f - h with hrdef
  have hr : r ∈ Vᗮ := V.sub_starProjection_mem_orthogonal f
  have hh : h ∈ V := by
    rw [hhdef, Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hh
  set z : ℕ → 𝕜 := fun j => if hj : j < N then c ⟨j, hj⟩ else 0 with hzdef
  have hsum : ∀ g : ℕ → E, ∑ i : Fin N, c i • g i = ∑ j ∈ range N, z j • g j := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun j => z j • g j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hzdef, i.2]
  have hhz : h = ∑ j ∈ range N, z j • φ j := by rw [← hc, hsum]
  have hf : f = h + r := by rw [hrdef]; abel
  -- the pieces
  set w := ∑ j ∈ range N, z j • ρ j with hwdef
  have hThw : T h - w ∈ V := by
    rw [hhz, map_sum, hwdef, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (hρ j (Finset.mem_range.1 hj))
  have hcross : ⟪T h, r⟫_𝕜 = ⟪w, r⟫_𝕜 := by
    have h0 : ⟪T h - w, r⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hThw hr
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have hTh : RCLike.re ⟪T h, h⟫_𝕜 = qf N C z := by
    rw [hhz, map_sum]
    simp_rw [map_smul]
    exact re_inner_sum_smul N (fun j => T (φ j)) φ z C hC
  have hhn : ‖h‖ ^ 2 = qf N G z := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), hhz]
    exact re_inner_sum_smul N φ φ z G hG
  have hwn : ‖w‖ ^ 2 ≤ qf N R z := hres z
  have hhr : ⟪h, r⟫_𝕜 = 0 := Submodule.inner_right_of_mem_orthogonal hh hr
  have hpy : ‖f‖ ^ 2 = ‖h‖ ^ 2 + ‖r‖ ^ 2 := by
    rw [hf, sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero h r hhr]
  -- expansion of the form
  have hexp : RCLike.re ⟪T f, f⟫_𝕜
      = RCLike.re ⟪T h, h⟫_𝕜 + 2 * RCLike.re ⟪w, r⟫_𝕜 + RCLike.re ⟪T r, r⟫_𝕜 := by
    have hsym : RCLike.re ⟪T r, h⟫_𝕜 = RCLike.re ⟪T h, r⟫_𝕜 := by
      rw [hT, ← inner_conj_symm, RCLike.conj_re]
    rw [hf, map_add, inner_add_left, inner_add_right, inner_add_right, map_add, map_add, map_add,
      hsym, hcross]
    ring
  have hcs : RCLike.re ⟪w, r⟫_𝕜 ≤ ‖w‖ * ‖r‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm w r)
  have hamgm : 2 * (‖w‖ * ‖r‖) ≤ t * ‖w‖ ^ 2 + ‖r‖ ^ 2 / t := by
    have h0 : 0 ≤ (t * ‖w‖ - ‖r‖) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have e : (t * ‖w‖ - ‖r‖) ^ 2 / t = t * ‖w‖ ^ 2 + ‖r‖ ^ 2 / t - 2 * (‖w‖ * ‖r‖) := by
      field_simp
      ring
    linarith
  have hpsd' := qf_nonneg N _ hpsd z
  rw [qf_sub_smul] at hpsd'
  have htail := hq r hr
  have hr2 : (q + 1 / t) * ‖r‖ ^ 2 ≤ lam * ‖r‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hlt (sq_nonneg _)
  have hdiv : ‖r‖ ^ 2 / t = 1 / t * ‖r‖ ^ 2 := by ring
  have htw : t * ‖w‖ ^ 2 ≤ t * qf N R z := mul_le_mul_of_nonneg_left hwn ht.le
  rw [hexp, hpy, hTh, hhn]
  nlinarith

/-! ## The diagonal residual bound. -/

/-- The diagonal matrix with entries `d`. -/
def dg (d : ℕ → ℝ) (j l : ℕ) : ℝ := if j = l then d j else 0

theorem qf_dg (N : ℕ) (d : ℕ → ℝ) (z : ℕ → 𝕜) : qf N (dg d) z = ∑ j ∈ range N, d j * ‖z j‖ ^ 2 := by
  unfold qf dg
  refine Finset.sum_congr rfl fun j hj => ?_
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq (range N) j, if_pos hj, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re]

/-- **Weighted Cauchy-Schwarz** (Sedrakyan): `‖Σ z_j v_j‖² ≤ Σ_j (n_j (Σ al)/al_j) |z_j|²`
whenever `‖v_j‖² ≤ n_j` and `al_j > 0`. -/
theorem norm_sum_sq_le_weighted (N : ℕ) (v : ℕ → E) (z : ℕ → 𝕜) (n al : ℕ → ℝ)
    (hal : ∀ j < N, 0 < al j) (hn : ∀ j < N, ‖v j‖ ^ 2 ≤ n j) :
    ‖∑ j ∈ range N, z j • v j‖ ^ 2 ≤ qf N (dg fun j => n j * (∑ k ∈ range N, al k) / al j) z := by
  rw [qf_dg]
  have hS : 0 < ∑ k ∈ range N, al k ∨ N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sum_pos (fun k hk => hal k (Finset.mem_range.1 hk)) ⟨0, by simpa using h⟩)
  rcases hS with hS | hN
  · have h1 : ‖∑ j ∈ range N, z j • v j‖ ≤ ∑ j ∈ range N, ‖z j‖ * ‖v j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_smul _ _))
    have h2 := Finset.sq_sum_div_le_sum_sq_div (range N) (fun j => ‖z j‖ * ‖v j‖)
      (g := al) fun j hj => hal j (Finset.mem_range.1 hj)
    have h0 : 0 ≤ ∑ j ∈ range N, ‖z j‖ * ‖v j‖ := Finset.sum_nonneg fun j _ => by positivity
    have h3 : ‖∑ j ∈ range N, z j • v j‖ ^ 2 ≤ (∑ j ∈ range N, ‖z j‖ * ‖v j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [div_le_iff₀ hS] at h2
    refine h3.trans (h2.trans ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have hal' := hal j hj'
    rw [mul_pow, div_mul_eq_mul_div, div_le_iff₀ hal']
    have : ‖v j‖ ^ 2 * (∑ k ∈ range N, al k) ≤ n j * (∑ k ∈ range N, al k) :=
      mul_le_mul_of_nonneg_right (hn j hj') hS.le
    have e : n j * (∑ k ∈ range N, al k) / al j * ‖z j‖ ^ 2 * al j
        = n j * (∑ k ∈ range N, al k) * ‖z j‖ ^ 2 := by field_simp
    rw [e]
    nlinarith [sq_nonneg ‖z j‖]
  · subst hN
    simp

end ArchS11
