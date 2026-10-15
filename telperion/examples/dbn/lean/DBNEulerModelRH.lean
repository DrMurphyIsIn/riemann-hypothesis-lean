/-
  DBNEulerModelRH -- "RH above an explicit height, near the line" for the finite Euler-product
  model Z_X(s) = E_X(s) + χ(s) E_X(1-s), E_X(s) = ∏_{p ≤ X} (1 - p^{-s})⁻¹,
  χ(s) = π^{s-1/2} Γ((1-s)/2) / Γ(s/2) (LY-1/E; design notes, unpublished).

  Statement.  For 0 < y < 1/2 and t with log(|t|/2π) - 1/|t| - 2/t² > Λ_X(y),
      Λ_X(y) = (1/y) Σ_{p ≤ X} log[(1 - p^{-1/2-y}) / (1 - p^{-1/2+y})],
  Z_X(σ + it) ≠ 0 whenever 0 < |σ - 1/2| ≤ y.

  Proof.  L1 (`norm_eulerX_one_sub_le`): the prime factor |E_X(1-s)|/|E_X(s)| ≤ e^{δ Λ_X(δ)} at
  s = 1/2 + δ + it, factor by factor (|1 - a w| / |1 - b w| is maximised at w = 1 for a < b < 1;
  sharp on the torus).  L2 (`norm_chiM_le`): |χ(1/2 + δ + it)| ≤ e^{-δ(log(|t|/2π) - 1/|t| - 2/t²)},
  by the mean value theorem on σ ↦ log|χ(σ + it)| = (σ - 1/2) log π + Re L((1-s)/2) - Re L(s/2)
  (DBNStirling's branch-free Γ = exp ∘ L), its derivative log π - ½ Re ψ((1-s)/2) - ½ Re ψ(s/2),
  DBNStirling.norm_digamma_sub_log_le, and |χ(1/2 + it)| = 1 from Γ(z̄) = conj Γ(z).
  L3 (`LamX_monotoneOn`): Λ_X is monotone on (0, 1/2), via the series
  log[(1 - p^{-1/2-y})/(1 - p^{-1/2+y})] = Σ_k (2 p^{-k/2}/k) sinh(k y log p) and convexity of sinh.
  σ < 1/2 by Z_X(1-s) = χ(1-s) Z_X(s) (χ(s) χ(1-s) = 1 is algebraic; no reflection formula).
  Concrete instance (`ZX_two_ne_zero`): X = 2, y = 2/5, t ≥ 1000.

  This is a statement about a MODEL (finite Euler product + χ), NOT about ζ.  Nothing here bears
  on RH.  conjecture1_proved = False.
-/
import DBNStirling

open Complex Filter Topology Set

namespace DBNEulerModel

/-- The primes `p ≤ X`. -/
def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

/-- The truncated Euler product `E_X(s) = ∏_{p ≤ X} (1 - p^{-s})⁻¹`. -/
noncomputable def eulerX (X : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ primesUpTo X, (1 - (p : ℂ) ^ (-s))⁻¹

/-- The functional-equation factor `χ(s) = π^{s-1/2} Γ((1-s)/2) / Γ(s/2)`. -/
noncomputable def chiM (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (s - 1 / 2) * Gamma ((1 - s) / 2) / Gamma (s / 2)

/-- The model `Z_X(s) = E_X(s) + χ(s) E_X(1-s)`. -/
noncomputable def ZX (X : ℕ) (s : ℂ) : ℂ := eulerX X s + chiM s * eulerX X (1 - s)

/-- `Λ_X(y) = (1/y) Σ_{p ≤ X} log [(1 - p^{-1/2-y}) / (1 - p^{-1/2+y})]`. -/
noncomputable def LamX (X : ℕ) (y : ℝ) : ℝ :=
  (1 / y) * ∑ p ∈ primesUpTo X,
    Real.log ((1 - (p : ℝ) ^ (-1 / 2 - y)) / (1 - (p : ℝ) ^ (-1 / 2 + y)))

lemma two_le_of_mem {X p : ℕ} (hp : p ∈ primesUpTo X) : (2 : ℝ) ≤ p := by
  have := (Finset.mem_filter.mp hp).2.two_le
  exact_mod_cast this

/-! ### L1: the prime factor -/

lemma cpow_re_of_pos {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℂ) ^ z).re = x ^ z.re * Real.cos (z.im * Real.log x) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), exp_re, ← ofReal_log hx.le]
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
  rw [Real.rpow_def_of_pos hx]
  ring_nf

lemma norm_one_sub_sq (u : ℂ) : ‖1 - u‖ ^ 2 = 1 - 2 * u.re + ‖u‖ ^ 2 := by
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im]
  ring

/-- One Euler factor: `(1 - b) ‖1 - u‖ ≤ (1 - a) ‖1 - v‖` when `u, v` have moduli `a < b < 1` and
the same phase cosine `c`. -/
lemma factor_bound {u v : ℂ} {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hu : ‖u‖ = a) (hv : ‖v‖ = b) (hc : c ≤ 1) (hur : u.re = a * c) (hvr : v.re = b * c) :
    ‖1 - u‖ * (1 - b) ≤ (1 - a) * ‖1 - v‖ := by
  rw [← pow_le_pow_iff_left₀ (by have := norm_nonneg (1 - u); nlinarith)
    (by have := norm_nonneg (1 - v); nlinarith) two_ne_zero, mul_pow, mul_pow,
    norm_one_sub_sq, norm_one_sub_sq, hu, hv, hur, hvr]
  have h1 : 0 ≤ (1 - c) := by linarith
  have h2 : 0 ≤ (b - a) * (1 - a * b) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith [mul_nonneg h1 h2]

lemma norm_eulerX (X : ℕ) (s : ℂ) :
    ‖eulerX X s‖ = ∏ p ∈ primesUpTo X, ‖1 - (p : ℂ) ^ (-s)‖⁻¹ := by
  rw [eulerX, norm_prod]
  simp only [norm_inv]

lemma exp_mul_LamX (X : ℕ) {y : ℝ} (hy : 0 < y) (hy' : y < 1 / 2) :
    Real.exp (y * LamX X y) = ∏ p ∈ primesUpTo X,
      (1 - (p : ℝ) ^ (-1 / 2 - y)) / (1 - (p : ℝ) ^ (-1 / 2 + y)) := by
  rw [LamX, ← mul_assoc, mul_one_div_cancel hy.ne', one_mul, Real.exp_sum]
  refine Finset.prod_congr rfl fun p hp => Real.exp_log ?_
  have h2 := two_le_of_mem hp
  have hb : (p : ℝ) ^ (-1 / 2 + y) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
    (by linarith)
  have hab : (p : ℝ) ^ (-1 / 2 - y) < (p : ℝ) ^ (-1 / 2 + y) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  exact div_pos (by linarith) (by linarith)

/-- **L1 (prime factor, torus-sharp).**  At `s = 1/2 + δ + it`, `0 < δ < 1/2`:
`‖E_X(1-s)‖ ≤ exp(δ Λ_X(δ)) ‖E_X(s)‖`. -/
theorem norm_eulerX_one_sub_le (X : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (t : ℝ) :
    ‖eulerX X (1 - (((1 / 2 + δ : ℝ) : ℂ) + t * I))‖ ≤
      Real.exp (δ * LamX X δ) * ‖eulerX X (((1 / 2 + δ : ℝ) : ℂ) + t * I)‖ := by
  set s : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + t * I with hs
  rw [exp_mul_LamX X hδ hδ', norm_eulerX, norm_eulerX, ← Finset.prod_mul_distrib]
  have hure : (-s).re = -1 / 2 - δ := by simp [hs]; ring
  have huim : (-s).im = -t := by simp [hs]
  have hvre : (-(1 - s)).re = -1 / 2 + δ := by simp [hs]; ring
  have hvim : (-(1 - s)).im = t := by simp [hs]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have h2 := two_le_of_mem hp
  have hp0 : (0 : ℝ) < p := by linarith
  set a : ℝ := (p : ℝ) ^ (-1 / 2 - δ) with ha
  set b : ℝ := (p : ℝ) ^ (-1 / 2 + δ) with hb
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hab : a < b := Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have ha0 : 0 ≤ a := Real.rpow_nonneg hp0.le _
  have hpc : (p : ℂ) = ((p : ℝ) : ℂ) := by simp
  set u : ℂ := (p : ℂ) ^ (-s) with hu
  set v : ℂ := (p : ℂ) ^ (-(1 - s)) with hv
  have hun : ‖u‖ = a := by rw [hu, hpc, norm_cpow_eq_rpow_re_of_pos hp0, hure]
  have hvn : ‖v‖ = b := by rw [hv, hpc, norm_cpow_eq_rpow_re_of_pos hp0, hvre]
  have hur : u.re = a * Real.cos (t * Real.log p) := by
    rw [hu, hpc, cpow_re_of_pos hp0, hure, huim, neg_mul, Real.cos_neg]
  have hvr : v.re = b * Real.cos (t * Real.log p) := by
    rw [hv, hpc, cpow_re_of_pos hp0, hvre, hvim]
  have key := factor_bound ha0 hab hb1 hun hvn (Real.cos_le_one _) hur hvr
  have hu0 : 0 < ‖1 - u‖ := by
    have := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one, hun] at this
    linarith
  have hv0 : 0 < ‖1 - v‖ := by
    have := norm_sub_norm_le (1 : ℂ) v
    rw [norm_one, hvn] at this
    linarith
  rw [mul_comm, inv_mul_eq_div, div_div, ← one_div,
    div_le_div_iff₀ hv0 (mul_pos (by linarith) hu0)]
  linarith

/-! ### L2: the archimedean factor -/

lemma hasDerivAt_re_ofReal {f : ℂ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' (x : ℂ)) :
    HasDerivAt (fun y : ℝ => (f y).re) f'.re x := by
  exact h.real_of_complex

/-- `log ‖χ(σ + it)‖` on `0 < σ < 1`, through the branch-free `Γ = exp ∘ L` of `DBNStirling`. -/
noncomputable def phiChi (t σ : ℝ) : ℝ :=
  (σ - 1 / 2) * Real.log Real.pi + (DBNStirling.L ((1 - ((σ : ℂ) + t * I)) / 2)).re -
    (DBNStirling.L (((σ : ℂ) + t * I) / 2)).re

lemma re_z1 (t σ : ℝ) : (((σ : ℂ) + t * I) / 2).re = σ / 2 := by simp

lemma re_z2 (t σ : ℝ) : ((1 - ((σ : ℂ) + t * I)) / 2).re = (1 - σ) / 2 := by simp

lemma im_z1 (t σ : ℝ) : (((σ : ℂ) + t * I) / 2).im = t / 2 := by simp

lemma im_z2 (t σ : ℝ) : ((1 - ((σ : ℂ) + t * I)) / 2).im = -t / 2 := by simp [neg_div]

lemma norm_chiM_eq (t : ℝ) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ‖chiM ((σ : ℂ) + t * I)‖ = Real.exp (phiChi t σ) := by
  have hz1 : 0 < (((σ : ℂ) + t * I) / 2).re := by rw [re_z1]; linarith
  have hz2 : 0 < ((1 - ((σ : ℂ) + t * I)) / 2).re := by rw [re_z2]; linarith
  rw [chiM, DBNStirling.Gamma_eq_exp_L hz1, DBNStirling.Gamma_eq_exp_L hz2, norm_div, norm_mul,
    norm_exp, norm_exp, norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Real.rpow_def_of_pos Real.pi_pos, phiChi, Real.exp_sub, Real.exp_add]
  congr 3
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  norm_num
  ring

lemma re_L_conj {z : ℂ} (hz : 0 < z.re) :
    (DBNStirling.L ((starRingEnd ℂ) z)).re = (DBNStirling.L z).re := by
  have hz' : 0 < ((starRingEnd ℂ) z).re := by simpa using hz
  apply Real.exp_injective
  rw [← norm_exp, ← norm_exp, ← DBNStirling.Gamma_eq_exp_L hz', ← DBNStirling.Gamma_eq_exp_L hz,
    Gamma_conj, Complex.norm_conj]

lemma phiChi_half (t : ℝ) : phiChi t (1 / 2) = 0 := by
  have hc : (1 - (((1 / 2 : ℝ) : ℂ) + t * I)) / 2 = (starRingEnd ℂ) ((((1 / 2 : ℝ) : ℂ) + t * I) / 2) := by
    rw [map_div₀, map_add, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]
    push_cast
    ring
  have hz : 0 < ((((1 / 2 : ℝ) : ℂ) + t * I) / 2).re := by rw [re_z1]; norm_num
  rw [phiChi, hc, re_L_conj hz]
  ring

lemma hasDerivAt_phiChi (t : ℝ) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    HasDerivAt (phiChi t)
      (Real.log Real.pi - (digamma ((1 - ((σ : ℂ) + t * I)) / 2)).re / 2 -
        (digamma (((σ : ℂ) + t * I) / 2)).re / 2) σ := by
  have hz1 : 0 < (((σ : ℂ) + t * I) / 2).re := by rw [re_z1]; linarith
  have hz2 : 0 < ((1 - ((σ : ℂ) + t * I)) / 2).re := by rw [re_z2]; linarith
  have hA : HasDerivAt (fun x : ℝ => (x - 1 / 2) * Real.log Real.pi) (1 * Real.log Real.pi) σ :=
    ((hasDerivAt_id σ).sub_const _).mul_const _
  have hw1 : HasDerivAt (fun w : ℂ => (w + t * I) / 2) (1 / 2) (σ : ℂ) :=
    ((hasDerivAt_id (σ : ℂ)).add_const _).div_const 2
  have hw2 : HasDerivAt (fun w : ℂ => (1 - (w + t * I)) / 2) (-1 / 2) (σ : ℂ) := by
    have := (((hasDerivAt_id (σ : ℂ)).add_const (t * I)).const_sub 1).div_const 2
    simpa [neg_div] using this
  have hB := hasDerivAt_re_ofReal ((DBNStirling.hasDerivAt_L hz2).comp (σ : ℂ) hw2)
  have hC := hasDerivAt_re_ofReal ((DBNStirling.hasDerivAt_L hz1).comp (σ : ℂ) hw1)
  have h := (hA.add hB).sub hC
  rw [← DBNStirling.digamma_eq hz2, ← DBNStirling.digamma_eq hz1] at h
  refine HasDerivAt.congr_deriv (f := phiChi t) h ?_
  simp only [mul_re, div_ofNat_re, div_ofNat_im, neg_re, neg_im, one_re, one_im]
  ring

/-- `Re ψ(z) ≥ log(|t|/2) - (1/|t| + 2/t²)` on the right half-plane when `|Im z| = |t|/2`. -/
lemma re_digamma_ge {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : t ≠ 0) (him : |z.im| = |t| / 2) :
    Real.log (|t| / 2) - (1 / |t| + 2 / t ^ 2) ≤ (digamma z).re := by
  have hta : 0 < |t| := abs_pos.mpr ht
  have hzn : |t| / 2 ≤ ‖z‖ := him ▸ Complex.abs_im_le_norm z
  have hzpos : 0 < ‖z‖ := by linarith
  have hE := DBNStirling.norm_digamma_sub_log_le hz
  have hE1 : 1 / (2 * ‖z‖) ≤ 1 / |t| := by
    rw [div_le_div_iff₀ (by positivity) hta]; linarith
  have hE2 : 1 / (2 * ‖z‖ ^ 2) ≤ 2 / t ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), ← sq_abs t]; nlinarith
  have hlog : Real.log (|t| / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by positivity) hzn
  have hre : -‖digamma z - log z‖ ≤ (digamma z - log z).re := by
    have := Complex.abs_re_le_norm (digamma z - log z)
    rw [abs_le] at this; exact this.1
  have hsplit : (digamma z).re = (log z).re + (digamma z - log z).re := by simp
  rw [hsplit, log_re]
  linarith

/-- **L2 (archimedean factor).**  For `t ≠ 0` and `0 < δ < 1/2`,
`‖χ(1/2 + δ + it)‖ ≤ exp(-δ (log(|t|/2π) - 1/|t| - 2/t²))`. -/
theorem norm_chiM_le (t : ℝ) (ht : t ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ‖chiM (((1 / 2 + δ : ℝ) : ℂ) + t * I)‖ ≤
      Real.exp (-δ * (Real.log (|t| / (2 * Real.pi)) - 1 / |t| - 2 / t ^ 2)) := by
  rw [norm_chiM_eq t (by linarith) (by linarith), Real.exp_le_exp]
  set K := Real.log (|t| / (2 * Real.pi)) - 1 / |t| - 2 / t ^ 2 with hK
  set f' : ℝ → ℝ := fun σ => Real.log Real.pi - (digamma ((1 - ((σ : ℂ) + t * I)) / 2)).re / 2 -
        (digamma (((σ : ℂ) + t * I) / 2)).re / 2 with hf'
  have hder : ∀ x ∈ Icc (1 / 2 : ℝ) (1 / 2 + δ), HasDerivAt (phiChi t) (f' x) x := fun x hx =>
    hasDerivAt_phiChi t (by linarith [hx.1]) (by linarith [hx.2])
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (phiChi t) f' (by linarith : (1 / 2 : ℝ) < 1 / 2 + δ)
    (fun x hx => (hder x hx).continuousAt.continuousWithinAt)
    (fun x hx => hder x (Ioo_subset_Icc_self hx))
  have hc0 : 0 < c := by linarith [hc.1]
  have hc1 : c < 1 := by linarith [hc.2]
  have hta : 0 < |t| := abs_pos.mpr ht
  have hb1 := re_digamma_ge (z := ((c : ℂ) + t * I) / 2) (by rw [re_z1]; linarith) ht
    (by rw [im_z1, abs_div]; norm_num)
  have hb2 := re_digamma_ge (z := (1 - ((c : ℂ) + t * I)) / 2) (by rw [re_z2]; linarith) ht
    (by rw [im_z2, abs_div, abs_neg]; norm_num)
  have hfc : f' c ≤ -K := by
    have hl : Real.log (|t| / (2 * Real.pi)) = Real.log (|t| / 2) - Real.log Real.pi := by
      rw [show |t| / (2 * Real.pi) = (|t| / 2) / Real.pi by ring,
        Real.log_div (by positivity) Real.pi_pos.ne']
    simp only [hf', hK, hl]
    linarith
  rw [phiChi_half, sub_zero, show 1 / 2 + δ - 1 / 2 = δ by ring] at hcd
  have : phiChi t (1 / 2 + δ) = δ * f' c := by rw [hcd]; field_simp
  rw [this, neg_mul, ← mul_neg]
  exact mul_le_mul_of_nonneg_left hfc hδ.le

/-! ### L3: monotonicity of `Λ_X` -/

lemma convexOn_sinh : ConvexOn ℝ (Ici 0) Real.sinh := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) Real.continuous_sinh.continuousOn
    Real.differentiable_sinh.differentiableOn ?_
  rw [Real.deriv_sinh, interior_Ici]
  intro x hx y hy hxy
  rw [Real.cosh_le_cosh, abs_of_pos hx, abs_of_pos hy]
  exact hxy

lemma sinh_mul_le {l x : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hx : 0 ≤ x) :
    Real.sinh (l * x) ≤ l * Real.sinh x := by
  have h := convexOn_sinh.2 (show x ∈ Ici (0 : ℝ) from hx) (Set.mem_Ici.mpr le_rfl)
    hl0 (by linarith : 0 ≤ 1 - l) (by ring)
  simpa [smul_eq_mul, Real.sinh_zero] using h

/-- `y ↦ sinh(k y)/y` is monotone on `y > 0` for `k ≥ 0`. -/
lemma sinh_div_mono {k y₁ y₂ : ℝ} (hk : 0 ≤ k) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂) :
    Real.sinh (k * y₁) / y₁ ≤ Real.sinh (k * y₂) / y₂ := by
  have h2 : 0 < y₂ := by linarith
  have h := sinh_mul_le (l := y₁ / y₂) (x := k * y₂) (by positivity)
    ((div_le_one h2).mpr h12) (by positivity)
  rw [show y₁ / y₂ * (k * y₂) = k * y₁ by field_simp] at h
  rw [div_le_div_iff₀ h1 h2]
  have := mul_le_mul_of_nonneg_right h h2.le
  rw [show y₁ / y₂ * Real.sinh (k * y₂) * y₂ = Real.sinh (k * y₂) * y₁ by field_simp] at this
  exact this

/-- The per-prime series: `log[(1 - p^{-1/2-y})/(1 - p^{-1/2+y})] = Σ_k (2 p^{-k/2}/k) sinh(k y log p)`. -/
lemma hasSum_log_ratio {p : ℝ} (hp : 2 ≤ p) {y : ℝ} (hy0 : 0 < y) (hy : y < 1 / 2) :
    HasSum (fun n : ℕ => 2 * Real.exp (-((n + 1) * Real.log p) / 2) / (n + 1) *
        Real.sinh ((n + 1) * Real.log p * y))
      (Real.log ((1 - p ^ (-1 / 2 - y)) / (1 - p ^ (-1 / 2 + y)))) := by
  have hp0 : 0 < p := by linarith
  have hb1 : p ^ (-1 / 2 + y) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hab : p ^ (-1 / 2 - y) < p ^ (-1 / 2 + y) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have ha0 : 0 ≤ p ^ (-1 / 2 - y) := Real.rpow_nonneg hp0.le _
  have hB := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |p ^ (-1 / 2 + y)| < 1 by rw [abs_of_nonneg (by linarith)]; exact hb1)
  have hA := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |p ^ (-1 / 2 - y)| < 1 by rw [abs_of_nonneg ha0]; linarith)
  have h := hB.sub hA
  rw [Real.log_div (by linarith) (by linarith), show Real.log (1 - p ^ (-1 / 2 - y)) -
    Real.log (1 - p ^ (-1 / 2 + y)) = -Real.log (1 - p ^ (-1 / 2 + y)) -
      -Real.log (1 - p ^ (-1 / 2 - y)) by ring]
  refine (congrArg (HasSum · _) ?_).mpr h
  · funext n
    rw [← sub_div, Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0, ← Real.exp_nat_mul,
      ← Real.exp_nat_mul, Real.sinh_eq]
    push_cast
    rw [show ((n : ℝ) + 1) * (Real.log p * (-1 / 2 + y)) =
        -((n + 1) * Real.log p) / 2 + (n + 1) * Real.log p * y by ring,
      show ((n : ℝ) + 1) * (Real.log p * (-1 / 2 - y)) =
        -((n + 1) * Real.log p) / 2 + -((n + 1) * Real.log p * y) by ring,
      Real.exp_add, Real.exp_add]
    field_simp

lemma log_ratio_div_mono {p : ℝ} (hp : 2 ≤ p) {y₁ y₂ : ℝ} (h1 : 0 < y₁) (h12 : y₁ ≤ y₂)
    (h2 : y₂ < 1 / 2) :
    Real.log ((1 - p ^ (-1 / 2 - y₁)) / (1 - p ^ (-1 / 2 + y₁))) / y₁ ≤
      Real.log ((1 - p ^ (-1 / 2 - y₂)) / (1 - p ^ (-1 / 2 + y₂))) / y₂ := by
  have hc : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  refine hasSum_le (fun n => ?_) ((hasSum_log_ratio hp h1 (by linarith)).div_const y₁)
    ((hasSum_log_ratio hp (by linarith) h2).div_const y₂)
  simp only [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (sinh_div_mono (by positivity) h1 h12) (by positivity)

lemma LamX_eq_sum (X : ℕ) (y : ℝ) :
    LamX X y = ∑ p ∈ primesUpTo X,
      Real.log ((1 - (p : ℝ) ^ (-1 / 2 - y)) / (1 - (p : ℝ) ^ (-1 / 2 + y))) / y := by
  rw [LamX, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => one_div_mul_eq_div _ _

/-- **L3 (monotonicity).**  `Λ_X` is monotone on `(0, 1/2)`. -/
theorem LamX_monotoneOn (X : ℕ) : MonotoneOn (LamX X) (Ioo 0 (1 / 2)) := by
  intro y₁ h1 y₂ h2 h12
  rw [LamX_eq_sum, LamX_eq_sum]
  exact Finset.sum_le_sum fun p hp => log_ratio_div_mono (two_le_of_mem hp) h1.1 h12 h2.2

/-! ### Main theorem -/

lemma eulerX_ne_zero (X : ℕ) {s : ℂ} (hs : 0 < s.re) : eulerX X s ≠ 0 := by
  rw [eulerX, Finset.prod_ne_zero_iff]
  intro p hp
  refine inv_ne_zero fun h => ?_
  have h2 := two_le_of_mem hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hp0, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hn
  exact lt_irrefl _ hn

/-- The right half of the main theorem, for any `t ≠ 0` (stated with `|t|`). -/
theorem ZX_ne_zero_right (X : ℕ) {t : ℝ} (ht : t ≠ 0) {y δ : ℝ} (hy : y < 1 / 2)
    (hδ : 0 < δ) (hδy : δ ≤ y)
    (hK : LamX X y < Real.log (|t| / (2 * Real.pi)) - 1 / |t| - 2 / t ^ 2) :
    ZX X (((1 / 2 + δ : ℝ) : ℂ) + t * I) ≠ 0 := by
  intro hZ
  set s : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + t * I with hs
  set K := Real.log (|t| / (2 * Real.pi)) - 1 / |t| - 2 / t ^ 2 with hKdef
  have hδ' : δ < 1 / 2 := by linarith
  have hmono : LamX X δ ≤ LamX X y :=
    LamX_monotoneOn X ⟨hδ, hδ'⟩ ⟨by linarith, hy⟩ hδy
  have hE : 0 < ‖eulerX X s‖ :=
    norm_pos_iff.mpr (eulerX_ne_zero X (by simp [hs]; linarith))
  have heq : eulerX X s = -(chiM s * eulerX X (1 - s)) := by
    rw [ZX] at hZ; linear_combination hZ
  have hn : ‖eulerX X s‖ = ‖chiM s‖ * ‖eulerX X (1 - s)‖ := by
    rw [heq, norm_neg, norm_mul]
  have h1 := norm_eulerX_one_sub_le X hδ hδ' t
  have h2 := norm_chiM_le t ht hδ hδ'
  have hlt : Real.exp (-δ * K) * Real.exp (δ * LamX X δ) < 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have : ‖eulerX X s‖ ≤ Real.exp (-δ * K) * Real.exp (δ * LamX X δ) * ‖eulerX X s‖ := by
    calc ‖eulerX X s‖ = ‖chiM s‖ * ‖eulerX X (1 - s)‖ := hn
      _ ≤ Real.exp (-δ * K) * (Real.exp (δ * LamX X δ) * ‖eulerX X s‖) :=
          mul_le_mul h2 h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  nlinarith

lemma chiM_mul_chiM_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    chiM s * chiM (1 - s) = 1 := by
  have hg1 : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hg2 : Gamma ((1 - s) / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc : (Real.pi : ℂ) ^ (s - 1 / 2) * (Real.pi : ℂ) ^ (1 - s - 1 / 2) = 1 := by
    rw [← cpow_add _ _ hpi, show s - 1 / 2 + (1 - s - 1 / 2) = 0 by ring, cpow_zero]
  rw [chiM, chiM, sub_sub_cancel]
  calc _ = ((Real.pi : ℂ) ^ (s - 1 / 2) * (Real.pi : ℂ) ^ (1 - s - 1 / 2)) *
        (Gamma ((1 - s) / 2) * Gamma (s / 2)) / (Gamma ((1 - s) / 2) * Gamma (s / 2)) := by ring
    _ = 1 := by rw [hc, one_mul, div_self (mul_ne_zero hg2 hg1)]

/-- Functional symmetry `Z_X(1-s) = χ(1-s) Z_X(s)` on `0 < Re s < 1`. -/
lemma ZX_one_sub {X : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ZX X (1 - s) = chiM (1 - s) * ZX X s := by
  have h := chiM_mul_chiM_one_sub h0 h1
  rw [ZX, ZX, sub_sub_cancel]
  linear_combination (-eulerX X (1 - s)) * h

/-- **Main theorem (model only).**  Let `0 < y < 1/2`, `t ≠ 0` with
`log(|t|/2π) - 1/|t| - 2/t² > Λ_X(y)`.  Then `Z_X(σ + it) ≠ 0` for `0 < |σ - 1/2| ≤ y`.
A statement about the finite Euler-product model `Z_X`, NOT about `ζ`; nothing here bears on RH.
conjecture1_proved = False. -/
theorem ZX_ne_zero_of_abs (X : ℕ) {y t : ℝ} (hy : y < 1 / 2) (ht : t ≠ 0)
    (hK : Real.log (|t| / (2 * Real.pi)) - 1 / |t| - 2 / t ^ 2 > LamX X y)
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσy : |σ - 1 / 2| ≤ y) :
    ZX X ((σ : ℂ) + t * I) ≠ 0 := by
  rcases lt_or_gt_of_ne (abs_pos.mp hσ) with hneg | hpos
  · -- σ < 1/2: mirror through the functional symmetry.
    set δ := 1 / 2 - σ with hδ
    have hδ0 : 0 < δ := by linarith
    have hδy : δ ≤ y := by rw [abs_of_neg hneg] at hσy; linarith
    have hK' : LamX X y < Real.log (|-t| / (2 * Real.pi)) - 1 / |-t| - 2 / (-t) ^ 2 := by
      rw [abs_neg, neg_sq]; exact hK
    have hR := ZX_ne_zero_right X (neg_ne_zero.mpr ht) hy hδ0 hδy hK'
    intro hZ
    apply hR
    have hre0 : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
    have hre1 : ((σ : ℂ) + t * I).re < 1 := by simp; linarith
    have hs : ((1 / 2 + δ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - ((σ : ℂ) + t * I) := by
      rw [hδ]; push_cast; ring
    rw [hs, ZX_one_sub hre0 hre1, hZ, mul_zero]
  · set δ := σ - 1 / 2 with hδ
    have hδy : δ ≤ y := by rw [abs_of_pos hpos] at hσy; linarith
    have hs : ((σ : ℂ) + t * I) = ((1 / 2 + δ : ℝ) : ℂ) + t * I := by
      rw [hδ]; push_cast; ring
    rw [hs]
    exact ZX_ne_zero_right X ht hy hpos hδy hK

/-- **Main theorem, as stated in LY-1/E** (`t > 0`). -/
theorem ZX_ne_zero (X : ℕ) {y t : ℝ} (hy : y < 1 / 2) (ht : 0 < t)
    (hK : Real.log (t / (2 * Real.pi)) - 1 / t - 2 / t ^ 2 > LamX X y)
    {σ : ℝ} (hσ : 0 < |σ - 1 / 2|) (hσy : |σ - 1 / 2| ≤ y) :
    ZX X ((σ : ℂ) + t * I) ≠ 0 :=
  ZX_ne_zero_of_abs X hy ht.ne' (by rwa [abs_of_pos ht]) hσ hσy

/-! ### Concrete instance: `X = 2`, `y = 2/5`, `t ≥ 1000` -/

lemma primesUpTo_two : primesUpTo 2 = {2} := by
  unfold primesUpTo; decide

lemma two_rpow_neg_nine_tenths_ge : (53 / 100 : ℝ) ≤ (2 : ℝ) ^ (-9 / 10 : ℝ) := by
  have hx : ((2 : ℝ) ^ (-9 / 10 : ℝ)) ^ (10 : ℕ) = (2 : ℝ) ^ ((-9 : ℤ) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [← pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num : (10 : ℕ) ≠ 0), hx,
    Real.rpow_intCast]
  norm_num

lemma two_rpow_neg_one_tenth_le : (2 : ℝ) ^ (-1 / 10 : ℝ) ≤ 9331 / 10000 := by
  have hx : ((2 : ℝ) ^ (-1 / 10 : ℝ)) ^ (10 : ℕ) = (2 : ℝ) ^ ((-1 : ℤ) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [← pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (10 : ℕ) ≠ 0), hx,
    Real.rpow_intCast]
  norm_num

/-- `Λ_2(2/5) < 5` (numerically `Λ_2(2/5) ≈ 4.840`). -/
lemma LamX_two_lt : LamX 2 (2 / 5) < 5 := by
  rw [LamX, primesUpTo_two, Finset.sum_singleton]
  push_cast
  rw [show (-1 / 2 - 2 / 5 : ℝ) = -9 / 10 by norm_num, show (-1 / 2 + 2 / 5 : ℝ) = -1 / 10 by norm_num]
  have ha := two_rpow_neg_nine_tenths_ge
  have hb := two_rpow_neg_one_tenth_le
  have hb1 : (2 : ℝ) ^ (-1 / 10 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hab : (2 : ℝ) ^ (-9 / 10 : ℝ) < (2 : ℝ) ^ (-1 / 10 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hr : (1 - (2 : ℝ) ^ (-9 / 10 : ℝ)) / (1 - (2 : ℝ) ^ (-1 / 10 : ℝ)) < Real.exp 2 := by
    have he : (73 / 10 : ℝ) < Real.exp 2 := by
      have := Real.exp_one_gt_d9
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hl : Real.log ((1 - (2 : ℝ) ^ (-9 / 10 : ℝ)) / (1 - (2 : ℝ) ^ (-1 / 10 : ℝ))) < 2 :=
    (Real.log_lt_iff_lt_exp (div_pos (by linarith) (by linarith))).mpr hr
  linarith

/-- `log(t/2π) - 1/t - 2/t² > 5` for `t ≥ 1000`. -/
lemma height_gt_five {t : ℝ} (ht : 1000 ≤ t) :
    5 < Real.log (t / (2 * Real.pi)) - 1 / t - 2 / t ^ 2 := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have h158 : (158 : ℝ) ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hexp : Real.exp (501 / 100) < 158 := by
    have h1 := Real.exp_one_lt_d9
    have h2 := Real.exp_bound_div_one_sub_of_interval' (x := 1 / 100) (by norm_num) (by norm_num)
    have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have he0 := Real.exp_pos 1
    have h15 : Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 := pow_lt_pow_left₀ h1 he0.le (by norm_num)
    rw [show (501 / 100 : ℝ) = 5 + 1 / 100 by norm_num, Real.exp_add, h5]
    have := Real.exp_pos (1 / 100)
    calc Real.exp 1 ^ 5 * Real.exp (1 / 100) < (2.7182818286 : ℝ) ^ 5 * (1 / (1 - 1 / 100)) :=
          mul_lt_mul'' h15 h2 (by positivity) this.le
      _ < 158 := by norm_num
  have hlog : 501 / 100 < Real.log (t / (2 * Real.pi)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]; linarith
  have h1t : 1 / t ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) ht
  have h2t : 2 / t ^ 2 ≤ 2 / 1000 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) ht 2)
  linarith

/-- **Concrete instance.**  Every zero of `Z_2` with `t ≥ 1000` and `|σ - 1/2| ≤ 2/5` lies on
`σ = 1/2`.  (The lead's proved height at `y = 2/5` is `≈ 794`; `1000` is a cheap certified bound.)
Model only, not `ζ`.  conjecture1_proved = False. -/
theorem ZX_two_ne_zero {t : ℝ} (ht : 1000 ≤ t) {σ : ℝ} (hσ : 0 < |σ - 1 / 2|)
    (hσy : |σ - 1 / 2| ≤ 2 / 5) : ZX 2 ((σ : ℂ) + t * I) ≠ 0 :=
  ZX_ne_zero 2 (by norm_num) (by linarith) (by linarith [LamX_two_lt, height_gt_five ht]) hσ hσy

end DBNEulerModel
