/-
  DBNM5Alpha -- Route C milestone M5 (effective approximation of H_t, Polymath15 Theorem 1.3),
  brick 1: the Stirling-phase vocabulary alpha, log M_0, log M_t of P15 (arXiv:1904.12438)
  equations (6)-(10), (16)-(18), and the explicit parameter bounds (20), (21), (22) of Theorem 1.3
  (= P15 Proposition 6.6 (i)-(iii)).  Design: telperion/docs/DESIGN_RH_dbn_effective_Ht_2026-09-23.md.

  Mathlib-only on purpose (no island import): these are elementary facts about explicit functions,
  so the module can be ported to the ANDURIL (zeta_reflection) pin as shared infrastructure.

  Objects (P15 numbering; Log = principal branch = `Complex.log`):

    (9)   alpha s    = 1/(2s) + 1/(s-1) + (1/2) Log(s/(2 pi))
    (42)  alpha' s   = -1/(2 s^2) - 1/(s-1)^2 + 1/(2s)
    (7)   log M_0 s  = Log s + Log(s-1) - (s/2) log pi + log(sqrt(2 pi)/16) + (s/2 - 1/2) Log(s/2) - s/2
    (6)   M_0 s      = exp(log M_0 s)
    (10)  log M_t s  = (t/4) alpha(s)^2 + log M_0 s,      M_t s = exp(log M_t s)
    (16)  gamma      = M_t((1-y+ix)/2) / M_t((1+y-ix)/2)
    (17)  s_*        = (1+y-ix)/2 + (t/2) alpha((1+y-ix)/2)
    (18)  kappa      = (t/2) (alpha((1-y+ix)/2) - alpha((1+y+ix)/2))

  What IS proved here (every theorem axiom-checked in AxiomGuardDBN.lean, closure within
  [propext, Classical.choice, Quot.sound]):

    * `M0_eq_p15_eq6`: `M0` is P15's display (6) verbatim (for s /= 0, 1).
    * `hasDerivAt_alpha`, `hasDerivAt_logM0`, `hasDerivAt_logMt`: (log M_0)' = alpha (P15 (8)), and the
      derivative formula (42), off the slit (-oo, 1].
    * `norm_alphaDeriv_le`   (P15 (43)): Im s > 3  ->  |alpha'(s)| <= 1/(2 Im s - 6).
    * `alpha_conj`, `logM0_conj`, `logMt_conj`: M_0 = M_0^*, M_t = M_t^*, alpha = alpha^* off the real axis.
    * `norm_kappa_le`        (P15 (22)): x > 6, t, y >= 0  ->  |kappa| <= t y / (2 (x - 6)).
    * `re_sStar_ge`          (P15 (21), the form printed in Theorem 1.3; needs only x > 0, y >= 0,
      t >= 0) and `re_sStar_ge_prop66` (P15 Proposition 6.6 (ii), the form printed there; x > 0,
      0 <= y <= 1, t >= 0).  Neither implies the other (they differ by 4y(1-3y)/x^2 inside the
      positive part).  Both come from the exact formula `re_alpha_sPlus` for Re alpha((1+y-ix)/2);
      (21) via the polynomial identity in `rat_part_ge_21` (P15's own proof of (ii) goes through the
      8y(1-y) form and does not reach (21) as printed).
    * `norm_gammaP_le`       (P15 (20)): region (5)  ->  |gamma| <= e^{0.02 y} (x/(4 pi))^{-y/2}.
      P15's own proof of Prop 6.6 (i) does not reach the constant 0.02: its display (76) claims
      alpha(ix/2) = (1/2) log(x/(4 pi)) + i pi/4 + O(2/x), but the remainder 1/(ix) + 1/(ix/2 - 1) has
      modulus about 3/x (`p15_eq76_fails_at_200` below is the kernel-checked negative control), and
      with 3 in place of 2 the paper's chain gives 0.0235, not 0.02.  The proof here uses a real-part
      argument instead (Re alpha is (1/2) log|s/(2 pi)| up to O(1/x^2)) and reaches 0.02 with room.
    * `norm_alpha_sub_main_le` (corrected P15 (76)): |alpha(sigma + ix/2) - (1/2) log(x/(4 pi)) - i pi/4|
      <= (3 + sigma)/(x - 6) for 0 <= sigma, x > 6.

  What is NOT here: the analytic content of Theorem 1.3 (the heat-kernel / Riemann-Siegel
  representation of H_t, the saddle-point estimates of Props 6.1 and 6.3, Arias de Reyna's bounds,
  effective complex Stirling).  This brick only bounds explicitly defined elementary quantities.
  Nothing here bears on the Riemann Hypothesis.  conjecture1_proved = False.
-/
import Mathlib

open Complex ComplexConjugate

namespace DBNM5

noncomputable section

/-! ### Vocabulary (P15 (6)-(10), (16)-(18)) -/

/-- P15 (9): `alpha s = 1/(2s) + 1/(s-1) + (1/2) Log(s/(2 pi))`, the logarithmic derivative of `M_0`. -/
def alpha (s : ℂ) : ℂ := 1 / (2 * s) + 1 / (s - 1) + Complex.log (s / (2 * Real.pi)) / 2

/-- P15 (42): the derivative of `alpha`. -/
def alphaDeriv (s : ℂ) : ℂ := -(1 / (2 * s ^ 2)) - 1 / (s - 1) ^ 2 + 1 / (2 * s)

/-- P15 (7): the holomorphic branch of `log M_0` on `ℂ \ (-∞, 1]`. -/
def logM0 (s : ℂ) : ℂ :=
  Complex.log s + Complex.log (s - 1) - s / 2 * (Real.log Real.pi : ℂ)
    + (Real.log (Real.sqrt (2 * Real.pi) / 16) : ℂ) + (s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2

/-- P15 (6): `M_0 = exp (log M_0)`, the Stirling approximation to `(1/8) (s(s-1)/2) π^{-s/2} Γ(s/2)`. -/
def M0 (s : ℂ) : ℂ := Complex.exp (logM0 s)

/-- P15 (10): the branch `log M_t = (t/4) alpha^2 + log M_0`. -/
def logMt (t : ℝ) (s : ℂ) : ℂ := (t : ℂ) / 4 * alpha s ^ 2 + logM0 s

/-- P15 (10): `M_t s = exp((t/4) alpha(s)^2) M_0(s)`. -/
def Mt (t : ℝ) (s : ℂ) : ℂ := Complex.exp (logMt t s)

/-- P15 (17): `s_* = (1+y-ix)/2 + (t/2) alpha((1+y-ix)/2)`. -/
def sStar (t x y : ℝ) : ℂ :=
  (1 + (y : ℂ) - (x : ℂ) * I) / 2 + (t : ℂ) / 2 * alpha ((1 + (y : ℂ) - (x : ℂ) * I) / 2)

/-- P15 (18): `kappa = (t/2) (alpha((1-y+ix)/2) - alpha((1+y+ix)/2))`. -/
def kappa (t x y : ℝ) : ℂ :=
  (t : ℂ) / 2 * (alpha ((1 - (y : ℂ) + (x : ℂ) * I) / 2) - alpha ((1 + (y : ℂ) + (x : ℂ) * I) / 2))

/-- P15 (16): `gamma = M_t((1-y+ix)/2) / M_t((1+y-ix)/2)`. -/
def gammaP (t x y : ℝ) : ℂ :=
  Mt t ((1 - (y : ℂ) + (x : ℂ) * I) / 2) / Mt t ((1 + (y : ℂ) - (x : ℂ) * I) / 2)

/-! ### Derivatives: `(log M_0)' = alpha` (P15 (8)) and `alpha' = alphaDeriv` (P15 (42)) -/

lemma mem_slitPlane_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : s ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr h)

lemma ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : s ≠ 0 := by
  intro h0; apply h; simp [h0]

lemma sub_one_ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : s - 1 ≠ 0 :=
  ne_zero_of_im_ne_zero (by simpa using h)

lemma two_pi_ne_zero : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)

/-- `Log(s/(2π)) = Log(s/2) - log π` for `s ≠ 0`. -/
lemma log_div_two_pi (s : ℂ) (hs : s ≠ 0) :
    Complex.log (s / (2 * Real.pi)) = Complex.log (s / 2) - (Real.log Real.pi : ℂ) := by
  have h2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  have e : s / (2 * Real.pi) = s / 2 * ((Real.pi⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [e, log_mul_ofReal _ (inv_pos.mpr Real.pi_pos) _ h2, Real.log_inv]
  push_cast
  ring

/-- **P15 (42)**: `alpha' = alphaDeriv` on the slit plane minus `1`. -/
theorem hasDerivAt_alpha {s : ℂ} (hs : s ∈ slitPlane) (hs1 : s ≠ 1) :
    HasDerivAt alpha (alphaDeriv s) s := by
  have h0 : s ≠ 0 := slitPlane_ne_zero hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi0
  have h2 : HasDerivAt (fun w : ℂ ↦ 2 * w) (2 * 1) s := (hasDerivAt_id' s).const_mul (2 : ℂ)
  have hA : HasDerivAt (fun w : ℂ ↦ 1 / (2 * w)) ((0 * (2 * s) - 1 * (2 * 1)) / (2 * s) ^ 2) s :=
    (hasDerivAt_const s (1 : ℂ)).fun_div h2 (mul_ne_zero two_ne_zero h0)
  have hB : HasDerivAt (fun w : ℂ ↦ 1 / (w - 1)) ((0 * (s - 1) - 1 * 1) / (s - 1) ^ 2) s :=
    (hasDerivAt_const s (1 : ℂ)).fun_div ((hasDerivAt_id' s).sub_const (1 : ℂ)) hs1'
  have hmem : s / (2 * (Real.pi : ℂ)) ∈ slitPlane := by
    have e : s / (2 * (Real.pi : ℂ)) = s / (((2 * Real.pi : ℝ)) : ℂ) := by push_cast; ring
    rw [e]
    rcases mem_slitPlane_iff.mp hs with h | h
    · refine mem_slitPlane_iff.mpr (Or.inl ?_)
      rw [div_ofReal_re]; exact div_pos h (by positivity)
    · refine mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [div_ofReal_im]; exact div_ne_zero h (by positivity)
  have hC : HasDerivAt (fun w : ℂ ↦ Complex.log (w / (2 * (Real.pi : ℂ))) / 2)
      (1 / (2 * (Real.pi : ℂ)) / (s / (2 * (Real.pi : ℂ))) / 2) s :=
    (((hasDerivAt_id' s).div_const (2 * (Real.pi : ℂ))).clog hmem).div_const (2 : ℂ)
  have hsum := (hA.add hB).add hC
  refine hsum.congr_deriv ?_
  unfold alphaDeriv
  field_simp
  ring

/-- **P15 (8)**: `(log M_0)' = alpha` off the slit `(-∞, 1]`. -/
theorem hasDerivAt_logM0 {s : ℂ} (hs : s ∈ slitPlane) (hs1 : s - 1 ∈ slitPlane) :
    HasDerivAt logM0 (alpha s) s := by
  have h0 : s ≠ 0 := slitPlane_ne_zero hs
  have h10 : s - 1 ≠ 0 := slitPlane_ne_zero hs1
  have hs2 : s / 2 ∈ slitPlane := by
    rcases mem_slitPlane_iff.mp hs with h | h
    · exact mem_slitPlane_iff.mpr (Or.inl (by simpa using h))
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h))
  have h1 : HasDerivAt (fun w : ℂ ↦ Complex.log w) s⁻¹ s := hasDerivAt_log hs
  have h2 : HasDerivAt (fun w : ℂ ↦ Complex.log (w - 1)) (1 / (s - 1)) s :=
    ((hasDerivAt_id' s).sub_const (1 : ℂ)).clog hs1
  have h3 : HasDerivAt (fun w : ℂ ↦ w / 2 * (Real.log Real.pi : ℂ))
      (1 / 2 * (Real.log Real.pi : ℂ)) s :=
    ((hasDerivAt_id' s).div_const (2 : ℂ)).mul_const (Real.log Real.pi : ℂ)
  have h4 : HasDerivAt (fun w : ℂ ↦ Complex.log (w / 2)) (1 / 2 / (s / 2)) s :=
    ((hasDerivAt_id' s).div_const (2 : ℂ)).clog hs2
  have h5 : HasDerivAt (fun w : ℂ ↦ (w / 2 - 1 / 2) * Complex.log (w / 2))
      (1 / 2 * Complex.log (s / 2) + (s / 2 - 1 / 2) * (1 / 2 / (s / 2))) s :=
    (((hasDerivAt_id' s).div_const (2 : ℂ)).sub_const (1 / 2 : ℂ)).mul h4
  have h6 : HasDerivAt (fun w : ℂ ↦ w / 2) (1 / 2) s := (hasDerivAt_id' s).div_const (2 : ℂ)
  have hsum := ((((h1.add h2).sub h3).add_const
    ((Real.log (Real.sqrt (2 * Real.pi) / 16) : ℝ) : ℂ)).add h5).sub h6
  refine hsum.congr_deriv ?_
  unfold alpha
  have e := log_div_two_pi s h0
  rw [e]
  field_simp
  ring

/-- `(log M_t)' = alpha + (t/2) alpha alpha'` off the slit `(-∞, 1]`. -/
theorem hasDerivAt_logMt (t : ℝ) {s : ℂ} (hs : s ∈ slitPlane) (hs1 : s - 1 ∈ slitPlane) :
    HasDerivAt (logMt t) (alpha s + (t : ℂ) / 2 * alpha s * alphaDeriv s) s := by
  have hs1' : s ≠ 1 := fun h ↦ slitPlane_ne_zero hs1 (by rw [h, sub_self])
  have hA := hasDerivAt_alpha hs hs1'
  have h := ((hA.pow 2).const_mul ((t : ℂ) / 4)).add (hasDerivAt_logM0 hs hs1)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- `M0` is P15's display (6) verbatim, for `s ≠ 0, 1`:
`M_0(s) = (1/8) (s(s−1)/2) π^{−s/2} √(2π) exp((s/2 − 1/2) Log(s/2) − s/2)`.  (The branch choice in (7)
matters only for holomorphy of `log M_0`, not for this identity.) -/
theorem M0_eq_p15_eq6 {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    M0 s = 1 / 8 * (s * (s - 1) / 2) * (Real.pi : ℂ) ^ (-s / 2) * (Real.sqrt (2 * Real.pi) : ℂ)
      * Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2) := by
  have h10 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsq : 0 < Real.sqrt (2 * Real.pi) / 16 := by positivity
  have e : logM0 s = Complex.log s + Complex.log (s - 1) + Complex.log (Real.pi : ℂ) * (-s / 2)
      + ((Real.log (Real.sqrt (2 * Real.pi) / 16) : ℝ) : ℂ)
      + ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2) := by
    unfold logM0
    rw [← Complex.ofReal_log Real.pi_pos.le]
    ring
  rw [M0, e, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add,
    Complex.exp_log h0, Complex.exp_log h10, ← Complex.ofReal_exp, Real.exp_log hsq,
    Complex.cpow_def_of_ne_zero hpi]
  push_cast
  ring

/-! ### P15 (43): `Im s > 3 → |alpha'(s)| ≤ 1/(2 Im s − 6)` -/

/-- **P15 (43).** -/
theorem norm_alphaDeriv_le {s : ℂ} (hs : 3 < s.im) :
    ‖alphaDeriv s‖ ≤ 1 / (2 * s.im - 6) := by
  set T := s.im with hT
  have hT0 : 0 < T := by linarith
  have hs0 : T ≤ ‖s‖ := le_trans (le_abs_self _) (abs_im_le_norm s)
  have hs1 : T ≤ ‖s - 1‖ := by
    have := abs_im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero] at this
    exact le_trans (le_abs_self _) this
  have hn0 : 0 < ‖s‖ := lt_of_lt_of_le hT0 hs0
  have hn1 : 0 < ‖s - 1‖ := lt_of_lt_of_le hT0 hs1
  have e1 : ‖1 / (2 * s ^ 2)‖ = 1 / (2 * ‖s‖ ^ 2) := by
    rw [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_two]
  have e2 : ‖1 / (s - 1) ^ 2‖ = 1 / ‖s - 1‖ ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
  have e3 : ‖1 / (2 * s)‖ = 1 / (2 * ‖s‖) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two]
  have htri : ‖alphaDeriv s‖ ≤ 1 / (2 * ‖s‖ ^ 2) + 1 / ‖s - 1‖ ^ 2 + 1 / (2 * ‖s‖) := by
    unfold alphaDeriv
    calc ‖-(1 / (2 * s ^ 2)) - 1 / (s - 1) ^ 2 + 1 / (2 * s)‖
        ≤ ‖-(1 / (2 * s ^ 2)) - 1 / (s - 1) ^ 2‖ + ‖1 / (2 * s)‖ := norm_add_le _ _
      _ ≤ ‖-(1 / (2 * s ^ 2))‖ + ‖1 / (s - 1) ^ 2‖ + ‖1 / (2 * s)‖ := by
          gcongr; exact norm_sub_le _ _
      _ = 1 / (2 * ‖s‖ ^ 2) + 1 / ‖s - 1‖ ^ 2 + 1 / (2 * ‖s‖) := by rw [norm_neg, e1, e2, e3]
  have b1 : 1 / (2 * ‖s‖ ^ 2) ≤ 1 / (2 * T ^ 2) := by gcongr
  have b2 : 1 / ‖s - 1‖ ^ 2 ≤ 1 / T ^ 2 := by gcongr
  have b3 : 1 / (2 * ‖s‖) ≤ 1 / (2 * T) := by gcongr
  have key : 1 / (2 * T ^ 2) + 1 / T ^ 2 + 1 / (2 * T) ≤ 1 / (2 * T - 6) := by
    have h6 : 0 < 2 * T - 6 := by linarith
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) h6]
    nlinarith [sq_nonneg T, pow_pos hT0 3, pow_pos hT0 4, pow_pos hT0 5]
  linarith

/-! ### Reflection symmetry: `alpha = alpha^*`, `M_0 = M_0^*`, `M_t = M_t^*` off the real axis -/

lemma arg_ne_pi_of_im_ne_zero {z : ℂ} (h : z.im ≠ 0) : z.arg ≠ Real.pi :=
  fun h' ↦ h (arg_eq_pi_iff.mp h').2

theorem alpha_conj {s : ℂ} (hs : s.im ≠ 0) : alpha (conj s) = conj (alpha s) := by
  have h1 : (s / (2 * (Real.pi : ℂ))).im ≠ 0 := by
    rw [show s / (2 * (Real.pi : ℂ)) = s / ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      div_ofReal_im]
    exact div_ne_zero hs (by positivity)
  have hl : Complex.log (conj s / (2 * (Real.pi : ℂ)))
      = conj (Complex.log (s / (2 * (Real.pi : ℂ)))) := by
    rw [← log_conj _ (arg_ne_pi_of_im_ne_zero h1)]
    congr 1
    simp [map_div₀, map_ofNat]
  unfold alpha
  rw [hl]
  simp [map_div₀, map_ofNat]

theorem logM0_conj {s : ℂ} (hs : s.im ≠ 0) : logM0 (conj s) = conj (logM0 s) := by
  have hs1 : (s - 1).im ≠ 0 := by simpa using hs
  have hs2 : (s / 2).im ≠ 0 := by simpa using hs
  have ha : Complex.log (conj s) = conj (Complex.log s) := log_conj _ (arg_ne_pi_of_im_ne_zero hs)
  have hb : Complex.log (conj s - 1) = conj (Complex.log (s - 1)) := by
    rw [← log_conj _ (arg_ne_pi_of_im_ne_zero hs1)]; simp
  have hc : Complex.log (conj s / 2) = conj (Complex.log (s / 2)) := by
    rw [← log_conj _ (arg_ne_pi_of_im_ne_zero hs2)]; simp [map_div₀, map_ofNat]
  unfold logM0
  rw [ha, hb, hc]
  simp [map_div₀, map_ofNat]

theorem logMt_conj (t : ℝ) {s : ℂ} (hs : s.im ≠ 0) : logMt t (conj s) = conj (logMt t s) := by
  unfold logMt
  rw [alpha_conj hs, logM0_conj hs]
  simp [map_div₀, map_ofNat]

/-- `|M_t s| = exp (Re log M_t s)`. -/
lemma norm_Mt (t : ℝ) (s : ℂ) : ‖Mt t s‖ = Real.exp (logMt t s).re := Complex.norm_exp _

/-! ### P15 (22) = Proposition 6.6 (iii): `|kappa| ≤ t y / (2 (x − 6))` -/

/-- The horizontal line `Im w = c` is convex. -/
lemma convex_im_eq (c : ℝ) : Convex ℝ {w : ℂ | w.im = c} :=
  convex_hyperplane (f := fun w : ℂ ↦ w.im) ⟨fun a b ↦ by simp, fun r a ↦ by simp⟩ c

/-- On the horizontal line `Im w = x/2` (`x > 6`), `alpha` is `1/(x − 6)`-Lipschitz. -/
theorem norm_alpha_sub_le_of_im_eq {x : ℝ} (hx : 6 < x) {a b : ℂ} (ha : a.im = x / 2)
    (hb : b.im = x / 2) : ‖alpha b - alpha a‖ ≤ 1 / (x - 6) * ‖b - a‖ := by
  have hne : ∀ w : ℂ, w.im = x / 2 → w.im ≠ 0 := fun w hw ↦ by rw [hw]; positivity
  have hder : ∀ w : ℂ, w.im = x / 2 → HasDerivAt alpha (alphaDeriv w) w := fun w hw ↦
    hasDerivAt_alpha (mem_slitPlane_of_im_ne_zero (hne w hw))
      (fun h1 ↦ hne w hw (by rw [h1]; simp))
  refine (convex_im_eq (x / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun w hw ↦ (hder w hw).differentiableAt) (fun w hw ↦ ?_) ha hb
  rw [(hder w hw).deriv]
  have h3 : 3 < w.im := by rw [show w.im = x / 2 from hw]; linarith
  have := norm_alphaDeriv_le h3
  rwa [show 2 * w.im - 6 = x - 6 by rw [show w.im = x / 2 from hw]; ring] at this

/-- **P15 (22)** (= Proposition 6.6 (iii)): for `x > 6` and `t, y ≥ 0`,
`|kappa| ≤ t y / (2 (x − 6))`. -/
theorem norm_kappa_le {t x y : ℝ} (ht : 0 ≤ t) (hx : 6 < x) (hy : 0 ≤ y) :
    ‖kappa t x y‖ ≤ t * y / (2 * (x - 6)) := by
  set a : ℂ := (1 - (y : ℂ) + (x : ℂ) * I) / 2 with ha_def
  set b : ℂ := (1 + (y : ℂ) + (x : ℂ) * I) / 2 with hb_def
  have ha : a.im = x / 2 := by simp [ha_def]
  have hb : b.im = x / 2 := by simp [hb_def]
  have hba : b - a = (y : ℂ) := by rw [ha_def, hb_def]; ring
  have hmv := norm_alpha_sub_le_of_im_eq hx ha hb
  rw [hba, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy] at hmv
  have hk : kappa t x y = (t : ℂ) / 2 * (alpha a - alpha b) := rfl
  have hx6 : 0 < x - 6 := by linarith
  rw [hk, norm_mul, norm_sub_rev, show ‖(t : ℂ) / 2‖ = t / 2 by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_two]]
  calc t / 2 * ‖alpha b - alpha a‖ ≤ t / 2 * (1 / (x - 6) * y) := by gcongr
    _ = t * y / (2 * (x - 6)) := by field_simp

/-! ### Corrected P15 (76), and a kernel-checked negative control for (76) as printed -/

/-- The remainder of `alpha` on the imaginary axis: `alpha(ix/2) − (1/2) log(x/(4π)) − iπ/4
= 1/(ix) + 1/(ix/2 − 1)` for `x > 0`. -/
theorem alpha_I_sub_main {x : ℝ} (hx : 0 < x) :
    alpha ((x / 2 : ℝ) * I) - (((Real.log (x / (4 * Real.pi)) / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * I)
      = 1 / (2 * ((x / 2 : ℝ) * I)) + 1 / ((x / 2 : ℝ) * I - 1) := by
  have hpos : 0 < x / (4 * Real.pi) := by positivity
  have hlog : Complex.log (((x / 2 : ℝ) : ℂ) * I / (2 * (Real.pi : ℂ)))
      = ((Real.log (x / (4 * Real.pi)) : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I := by
    have e : ((x / 2 : ℝ) : ℂ) * I / (2 * (Real.pi : ℂ)) = ((x / (4 * Real.pi) : ℝ) : ℂ) * I := by
      push_cast; field_simp; ring
    rw [e]
    apply Complex.ext
    · rw [Complex.log_re]
      simp [Complex.norm_real, abs_of_pos hx, abs_of_pos Real.pi_pos]
    · rw [Complex.log_im, arg_real_mul _ hpos, arg_I]; simp
  unfold alpha
  rw [hlog]
  push_cast
  ring

/-- **Negative control: P15 (76) as printed is false.**  At `x = 200`, `sigma = 0` (a point of the
region where P15 applies (76), e.g. `y = 1`), the claimed remainder bound `(2 + sigma)/(x − 6)`
fails: the true remainder `1/(ix) + 1/(ix/2 − 1)` has imaginary part of modulus about `3/x`. -/
theorem p15_eq76_fails_at_200 :
    ¬ ‖alpha ((200 / 2 : ℝ) * I)
        - (((Real.log (200 / (4 * Real.pi)) / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * I)‖
      ≤ (2 + 0) / (200 - 6) := by
  rw [alpha_I_sub_main (by norm_num : (0 : ℝ) < 200)]
  intro h
  set z : ℂ := 1 / (2 * ((((200 : ℝ) / 2 : ℝ) : ℂ) * I)) + 1 / ((((200 : ℝ) / 2 : ℝ) : ℂ) * I - 1)
    with hz
  have him := abs_im_le_norm z
  have hv : z.im = -(30001 / 2000200) := by
    rw [hz]
    simp [Complex.normSq_apply]
    norm_num
  rw [hv] at him
  norm_num at him h
  linarith

/-- **Corrected P15 (76)**: for `x > 6` and `0 ≤ sigma`,
`|alpha(sigma + ix/2) − (1/2) log(x/(4π)) − iπ/4| ≤ (3 + sigma)/(x − 6)`. -/
theorem norm_alpha_sub_main_le {x σ : ℝ} (hx : 6 < x) (hσ : 0 ≤ σ) :
    ‖alpha ((σ : ℂ) + (x / 2 : ℝ) * I)
        - (((Real.log (x / (4 * Real.pi)) / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * I)‖
      ≤ (3 + σ) / (x - 6) := by
  have hx0 : 0 < x := by linarith
  have hx6 : 0 < x - 6 := by linarith
  have hmv := norm_alpha_sub_le_of_im_eq hx (a := ((x / 2 : ℝ) : ℂ) * I)
    (b := (σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I) (by simp) (by simp)
  rw [show (σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I - ((x / 2 : ℝ) : ℂ) * I = (σ : ℂ) by ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ] at hmv
  have hrem : ‖1 / (2 * (((x / 2 : ℝ) : ℂ) * I)) + 1 / (((x / 2 : ℝ) : ℂ) * I - 1)‖ ≤ 3 / x := by
    have n1 : ‖1 / (2 * (((x / 2 : ℝ) : ℂ) * I))‖ = 1 / x := by
      rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
        Complex.norm_two, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < x / 2)]
      field_simp
    have n2 : ‖1 / (((x / 2 : ℝ) : ℂ) * I - 1)‖ ≤ 2 / x := by
      rw [norm_div, norm_one]
      have hlow : x / 2 ≤ ‖((x / 2 : ℝ) : ℂ) * I - 1‖ := by
        have := abs_im_le_norm (((x / 2 : ℝ) : ℂ) * I - 1)
        simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
          one_im, sub_zero] at this
        rwa [abs_of_pos (by positivity : (0 : ℝ) < x / 2)] at this
      calc 1 / ‖((x / 2 : ℝ) : ℂ) * I - 1‖ ≤ 1 / (x / 2) := by gcongr
        _ = 2 / x := by field_simp
    calc _ ≤ ‖1 / (2 * (((x / 2 : ℝ) : ℂ) * I))‖ + ‖1 / (((x / 2 : ℝ) : ℂ) * I - 1)‖ :=
          norm_add_le _ _
      _ ≤ 1 / x + 2 / x := by rw [n1]; gcongr
      _ = 3 / x := by ring
  have h3 : 3 / x ≤ 3 / (x - 6) := by gcongr; linarith
  have hsplit : alpha ((σ : ℂ) + (x / 2 : ℝ) * I)
        - (((Real.log (x / (4 * Real.pi)) / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * I)
      = (alpha ((σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I) - alpha (((x / 2 : ℝ) : ℂ) * I))
        + (alpha (((x / 2 : ℝ) : ℂ) * I)
          - (((Real.log (x / (4 * Real.pi)) / 2 : ℝ) : ℂ) + ((Real.pi / 4 : ℝ) : ℂ) * I)) := by
    ring
  rw [hsplit, alpha_I_sub_main hx0]
  calc _ ≤ ‖alpha ((σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I) - alpha (((x / 2 : ℝ) : ℂ) * I)‖
        + ‖1 / (2 * (((x / 2 : ℝ) : ℂ) * I)) + 1 / (((x / 2 : ℝ) : ℂ) * I - 1)‖ := norm_add_le _ _
    _ ≤ 1 / (x - 6) * σ + 3 / (x - 6) := add_le_add hmv (hrem.trans h3)
    _ = (3 + σ) / (x - 6) := by field_simp; ring

/-! ### P15 (21) and Proposition 6.6 (ii): lower bounds for `Re s_*` -/

/-- Exact real part of `alpha` at `s₊ = (1+y−ix)/2`:
`Re alpha(s₊) = (1+y)/((1+y)²+x²) − 2(1−y)/((1−y)²+x²) + (1/2) log(|s₊|/(2π))`. -/
theorem re_alpha_sPlus {x : ℝ} (hx : 0 < x) (y : ℝ) :
    (alpha ((1 + (y : ℂ) - (x : ℂ) * I) / 2)).re
      = (1 + y) / ((1 + y) ^ 2 + x ^ 2) - 2 * (1 - y) / ((1 - y) ^ 2 + x ^ 2)
        + Real.log (‖(1 + (y : ℂ) - (x : ℂ) * I) / 2‖ / (2 * Real.pi)) / 2 := by
  have hA : 0 < (1 + y) ^ 2 + x ^ 2 := by positivity
  have hB : 0 < (1 - y) ^ 2 + x ^ 2 := by positivity
  set w : ℂ := (1 + (y : ℂ) - (x : ℂ) * I) / 2 with hw
  have t1 : (1 / (2 * w)).re = (1 + y) / ((1 + y) ^ 2 + x ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have e1 : (2 * w).re = 1 + y := by simp [hw]; ring
    have e2 : (2 * w).im = -x := by simp [hw]; ring
    rw [e1, e2]
    congr 1
    ring
  have t2 : (1 / (w - 1)).re = -(2 * (1 - y)) / ((1 - y) ^ 2 + x ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have e1 : (w - 1).re = -(1 - y) / 2 := by simp [hw]; ring
    have e2 : (w - 1).im = -x / 2 := by simp [hw]
    rw [e1, e2]
    field_simp
  have t3 : (Complex.log (w / (2 * (Real.pi : ℂ))) / 2).re
      = Real.log (‖w‖ / (2 * Real.pi)) / 2 := by
    rw [Complex.div_ofNat_re, Complex.log_re, norm_div, norm_mul, Complex.norm_two,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  unfold alpha
  rw [Complex.add_re, Complex.add_re, t1, t2, t3]
  ring

/-- The rational part of `Re alpha(s₊)` obeys the P15 (21) bound. -/
lemma rat_part_ge_21 {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) :
    -(1 / x ^ 2) * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0
      ≤ (1 + y) / ((1 + y) ^ 2 + x ^ 2) - 2 * (1 - y) / ((1 - y) ^ 2 + x ^ 2) := by
  set A := (1 + y) ^ 2 + x ^ 2 with hA_def
  set B := (1 - y) ^ 2 + x ^ 2 with hB_def
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hx2 : 0 < x ^ 2 := by positivity
  set N1 := x ^ 2 * (1 - 3 * y) + (1 - y ^ 2) * (1 + 3 * y) with hN1
  have hR : (1 + y) / A - 2 * (1 - y) / B = -N1 / (A * B) := by
    rw [div_sub_div _ _ hA.ne' hB.ne', hN1, hA_def, hB_def]
    congr 1
    ring
  rw [hR]
  have hmax : 0 ≤ max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0 := le_max_right _ _
  rcases le_or_gt N1 0 with hN | hN
  · have h1 : 0 ≤ -N1 / (A * B) := div_nonneg (by linarith) (by positivity)
    have h2 : -(1 / x ^ 2) * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0 ≤ 0 := by
      have : 0 ≤ 1 / x ^ 2 * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0 := by positivity
      linarith
    linarith
  · -- N1 > 0 forces P > 0, and then N1 x⁴ ≤ (x²(1−3y) + 4y(1+y)) A B by an explicit identity.
    have hP : 0 < 1 - 3 * y + 4 * y * (1 + y) / x ^ 2 := by
      have e : 1 - 3 * y + 4 * y * (1 + y) / x ^ 2 = (N1 + (1 + y) ^ 2 * (3 * y - 1)) / x ^ 2 := by
        rw [hN1]; field_simp; ring
      rcases lt_or_ge (3 * y - 1) 0 with h3 | h3
      · have : 0 ≤ 4 * y * (1 + y) / x ^ 2 := by positivity
        linarith
      · rw [e]; apply div_pos _ hx2; nlinarith [sq_nonneg (1 + y)]
    rw [max_eq_left hP.le]
    have hid : (x ^ 2 * (1 - 3 * y) + 4 * y * (1 + y)) * (A * B) - N1 * (x ^ 2) ^ 2
        = x ^ 2 * (1 - y) ^ 2 * N1 + 4 * y * (1 + y) ^ 3 * x ^ 2
          + 4 * y * (1 + y) * (1 - y ^ 2) ^ 2 := by
      rw [hA_def, hB_def, hN1]; ring
    have hnn : 0 ≤ x ^ 2 * (1 - y) ^ 2 * N1 + 4 * y * (1 + y) ^ 3 * x ^ 2
        + 4 * y * (1 + y) * (1 - y ^ 2) ^ 2 := by positivity
    have hlhs : -(1 / x ^ 2) * (1 - 3 * y + 4 * y * (1 + y) / x ^ 2)
        = -(x ^ 2 * (1 - 3 * y) + 4 * y * (1 + y)) / (x ^ 2) ^ 2 := by
      field_simp
    rw [hlhs, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The rational part of `Re alpha(s₊)` obeys the P15 Proposition 6.6 (ii) bound. -/
lemma rat_part_ge_66 {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    -(max (1 - 3 * y + 8 * y * (1 - y) / x ^ 2) 0) / x ^ 2
      ≤ (1 + y) / ((1 + y) ^ 2 + x ^ 2) - 2 * (1 - y) / ((1 - y) ^ 2 + x ^ 2) := by
  set A := (1 + y) ^ 2 + x ^ 2 with hA_def
  set B := (1 - y) ^ 2 + x ^ 2 with hB_def
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hx2 : 0 < x ^ 2 := by positivity
  have hAx : x ^ 2 ≤ A := by rw [hA_def]; nlinarith [sq_nonneg (1 + y)]
  have hBx : x ^ 2 ≤ B := by rw [hB_def]; nlinarith [sq_nonneg (1 - y)]
  have hyy : 0 ≤ 8 * y * (1 - y) := by nlinarith
  have hR : (1 + y) / A - 2 * (1 - y) / B = -(1 - 3 * y) / A - 8 * y * (1 - y) / (A * B) := by
    rw [hA_def, hB_def]; field_simp; ring
  rw [hR]
  set Q := 1 - 3 * y + 8 * y * (1 - y) / x ^ 2 with hQ
  have step1 : 8 * y * (1 - y) / (A * B) ≤ 8 * y * (1 - y) / (A * x ^ 2) := by
    apply div_le_div_of_nonneg_left hyy (by positivity)
    exact mul_le_mul_of_nonneg_left hBx hA.le
  have step2 : -(1 - 3 * y) / A - 8 * y * (1 - y) / (A * x ^ 2) = -Q / A := by
    rw [hQ]; field_simp; ring
  have step3 : -(max Q 0) / A ≤ -Q / A := by
    apply div_le_div_of_nonneg_right _ hA.le; linarith [le_max_left Q 0]
  have step4 : -(max Q 0) / x ^ 2 ≤ -(max Q 0) / A := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (le_max_right _ _) hx2 hAx
  linarith

/-- `Re s_* = (1+y)/2 + (t/2) Re alpha(s₊)`. -/
lemma re_sStar (t x y : ℝ) :
    (sStar t x y).re = (1 + y) / 2 + t / 2 * (alpha ((1 + (y : ℂ) - (x : ℂ) * I) / 2)).re := by
  unfold sStar
  simp only [add_re, div_ofNat_re, sub_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_zero, div_ofNat_im, zero_div, zero_mul]

/-- `(1/2) log(|s₊|/(2π)) ≥ (1/2) log(x/(4π))`. -/
lemma log_norm_sPlus_ge {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.log (x / (4 * Real.pi)) ≤ Real.log (‖(1 + (y : ℂ) - (x : ℂ) * I) / 2‖ / (2 * Real.pi)) := by
  have hn : x / 2 ≤ ‖(1 + (y : ℂ) - (x : ℂ) * I) / 2‖ := by
    have := abs_im_le_norm ((1 + (y : ℂ) - (x : ℂ) * I) / 2)
    have e : ((1 + (y : ℂ) - (x : ℂ) * I) / 2).im = -x / 2 := by simp
    rw [e, abs_div, abs_neg, abs_of_pos hx, abs_two] at this
    exact this
  apply Real.log_le_log (by positivity)
  rw [show x / (4 * Real.pi) = x / 2 / (2 * Real.pi) by field_simp; ring]
  gcongr

/-- **P15 (21)**, the form printed in Theorem 1.3: for `x > 0`, `0 ≤ y ≤ 1`, `t ≥ 0`,
`Re s_* ≥ (1+y)/2 + (t/4) log(x/(4π)) − (t/(2x²)) (1 − 3y + 4y(1+y)/x²)₊`. -/
theorem re_sStar_ge {t x y : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hy0 : 0 ≤ y) :
    (1 + y) / 2 + t / 4 * Real.log (x / (4 * Real.pi))
        - t / (2 * x ^ 2) * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0
      ≤ (sStar t x y).re := by
  rw [re_sStar, re_alpha_sPlus hx]
  have h1 := rat_part_ge_21 hx hy0 (y := y)
  have h2 := log_norm_sPlus_ge hx y
  have e : t / (2 * x ^ 2) * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0
      = t / 2 * (1 / x ^ 2 * max (1 - 3 * y + 4 * y * (1 + y) / x ^ 2) 0) := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ t / 2),
    mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ t / 4)]

/-- **P15 Proposition 6.6 (ii)**, the form printed there: for `x > 0`, `0 ≤ y ≤ 1`, `t ≥ 0`,
`Re s_* ≥ (1+y)/2 + (t/4) log(x/(4π)) − (1 − 3y + 8y(1−y)/x²)₊ t/(2x²)`. -/
theorem re_sStar_ge_prop66 {t x y : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 + y) / 2 + t / 4 * Real.log (x / (4 * Real.pi))
        - max (1 - 3 * y + 8 * y * (1 - y) / x ^ 2) 0 * t / (2 * x ^ 2)
      ≤ (sStar t x y).re := by
  rw [re_sStar, re_alpha_sPlus hx]
  have h1 := rat_part_ge_66 hx hy0 hy1
  have h2 := log_norm_sPlus_ge hx y
  have e : max (1 - 3 * y + 8 * y * (1 - y) / x ^ 2) 0 * t / (2 * x ^ 2)
      = t / 2 * (max (1 - 3 * y + 8 * y * (1 - y) / x ^ 2) 0 / x ^ 2) := by
    field_simp
  rw [e]
  have h1' : -(t / 2 * (max (1 - 3 * y + 8 * y * (1 - y) / x ^ 2) 0 / x ^ 2))
      ≤ t / 2 * ((1 + y) / ((1 + y) ^ 2 + x ^ 2) - 2 * (1 - y) / ((1 - y) ^ 2 + x ^ 2)) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ t / 2)
    rw [neg_div] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ t / 4)]

/-! ### P15 (20) = Proposition 6.6 (i): `|gamma| ≤ e^{0.02 y} (x/(4π))^{−y/2}`

P15's proof bounds the full complex error of its display (76) and so needs the (false) constant `2`;
the proof below only needs the REAL part of `(log M_t)'` on the segment, where the `1/(ix)` and
`1/(ix/2 − 1)` terms contribute `O(1/x²)`. -/

/-- Lower bound for `Re alpha` on the line `Im w = x/2`, `0 ≤ Re w`. -/
lemma re_alpha_ge_of_im {x : ℝ} (hx : 0 < x) {w : ℂ} (hw : w.im = x / 2) (h0 : 0 ≤ w.re) :
    Real.log (x / (4 * Real.pi)) / 2 - 4 / x ^ 2 ≤ (alpha w).re := by
  have hwn : x / 2 ≤ ‖w‖ := by
    have := abs_im_le_norm w; rwa [hw, abs_of_pos (by positivity)] at this
  have t1 : 0 ≤ (1 / (2 * w)).re := by
    rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp; linarith
  have t2 : -(4 / x ^ 2) ≤ (1 / (w - 1)).re := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have e1 : (w - 1).re = w.re - 1 := by simp
    have e2 : (w - 1).im = x / 2 := by simp [hw]
    rw [e1, e2]
    have hD : x ^ 2 / 4 ≤ (w.re - 1) * (w.re - 1) + x / 2 * (x / 2) := by nlinarith [sq_nonneg (w.re - 1)]
    have hDpos : 0 < (w.re - 1) * (w.re - 1) + x / 2 * (x / 2) := by
      nlinarith [mul_self_nonneg (w.re - 1)]
    rw [le_div_iff₀ hDpos]
    have : 4 / x ^ 2 * ((w.re - 1) * (w.re - 1) + x / 2 * (x / 2)) ≥ 1 := by
      rw [ge_iff_le, ← sub_nonneg]
      have : 4 / x ^ 2 * ((w.re - 1) * (w.re - 1) + x / 2 * (x / 2)) - 1
          = 4 * (w.re - 1) ^ 2 / x ^ 2 := by field_simp; ring
      rw [this]; positivity
    nlinarith
  have t3 : Real.log (x / (4 * Real.pi)) / 2 ≤ (Complex.log (w / (2 * (Real.pi : ℂ))) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.log_re, norm_div, norm_mul, Complex.norm_two,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hlog : Real.log (x / (4 * Real.pi)) ≤ Real.log (‖w‖ / (2 * Real.pi)) := by
      apply Real.log_le_log (by positivity)
      rw [show x / (4 * Real.pi) = x / 2 / (2 * Real.pi) by field_simp; ring]
      exact div_le_div_of_nonneg_right hwn (by positivity)
    linarith
  unfold alpha
  rw [Complex.add_re, Complex.add_re]
  linarith

/-- Upper bound for `|alpha|` on the line `Im w = x/2`, `0 ≤ Re w ≤ 1`, `x ≥ 4π`. -/
lemma norm_alpha_le_of_im {x : ℝ} (hx : 4 * Real.pi ≤ x) {w : ℂ} (hw : w.im = x / 2)
    (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) :
    ‖alpha w‖ ≤ 3 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hwn : x / 2 ≤ ‖w‖ := by
    have := abs_im_le_norm w; rwa [hw, abs_of_pos (by positivity)] at this
  have hwn' : ‖w‖ ≤ 1 + x / 2 := by
    have := norm_le_abs_re_add_abs_im w
    rw [hw, abs_of_nonneg h0, abs_of_pos (by positivity)] at this
    linarith
  have hw1 : x / 2 ≤ ‖w - 1‖ := by
    have := abs_im_le_norm (w - 1)
    rwa [show (w - 1).im = x / 2 by simp [hw], abs_of_pos (by positivity)] at this
  have n1 : ‖1 / (2 * w)‖ ≤ 1 / x := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two]
    rw [div_le_div_iff₀ (by nlinarith) hx0]; linarith
  have n2 : ‖1 / (w - 1)‖ ≤ 2 / x := by
    rw [norm_div, norm_one, div_le_div_iff₀ (by linarith) hx0]; linarith
  set z : ℂ := w / (2 * (Real.pi : ℂ)) with hz
  have hzn : ‖z‖ = ‖w‖ / (2 * Real.pi) := by
    rw [hz, norm_div, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hz1 : 1 ≤ ‖z‖ := by
    rw [hzn, le_div_iff₀ (by positivity)]; linarith
  have n3 : ‖Complex.log z‖ ≤ (1 + x / 2) / (2 * Real.pi) + Real.pi := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    have hl0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz1
    have hl1 : Real.log ‖z‖ ≤ ‖z‖ := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖z‖); linarith
    have hl2 : ‖z‖ ≤ (1 + x / 2) / (2 * Real.pi) := by
      rw [hzn]; gcongr
    rw [abs_of_nonneg hl0]
    linarith [abs_arg_le_pi z]
  unfold alpha
  calc ‖1 / (2 * w) + 1 / (w - 1) + Complex.log (w / (2 * (Real.pi : ℂ))) / 2‖
      ≤ ‖1 / (2 * w)‖ + ‖1 / (w - 1)‖ + ‖Complex.log z / 2‖ := by
        rw [← hz]; exact norm_add₃_le
    _ ≤ 1 / x + 2 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2 := by
        have n4 : ‖Complex.log z / 2‖ = ‖Complex.log z‖ / 2 := by
          rw [norm_div, Complex.norm_two]
        rw [n4]; linarith [n1, n2, n3]
    _ = 3 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2 := by ring

/-- The numeric step of (20): `4/x² + (1/4)(3/x + ((1+x/2)/(2π) + π)/2)/(x − 6) ≤ 0.02` for `x ≥ 200`. -/
lemma gamma_numeric {x : ℝ} (hx : 200 ≤ x) :
    4 / x ^ 2 + 1 / 4 * (3 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2) * (1 / (x - 6))
      ≤ 0.02 := by
  have hx0 : 0 < x := by linarith
  have hx6 : 0 < x - 6 := by linarith
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have a1 : 4 / x ^ 2 ≤ 1 / 10000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have a2 : 3 / x ≤ 3 / 200 := by gcongr
  have a3 : (1 + x / 2) / (2 * Real.pi) ≤ (1 + x / 2) / 6 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num); linarith
  have hB : 3 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2 ≤ x / 24 + 1.674 := by
    have : ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2 ≤ ((1 + x / 2) / 6 + 3.15) / 2 := by
      gcongr
    have e : ((1 + x / 2) / 6 + 3.15) / 2 = x / 24 + 1 / 12 + 1.575 := by ring
    norm_num at this e ⊢
    linarith
  have hB0 : 0 ≤ 3 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2 := by positivity
  have a4 : 1 / 4 * (3 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2) * (1 / (x - 6))
      ≤ (x / 24 + 1.674) / (4 * (x - 6)) := by
    rw [show (x / 24 + 1.674) / (4 * (x - 6)) = 1 / 4 * (x / 24 + 1.674) * (1 / (x - 6)) by
      field_simp]
    gcongr
  have a5 : (x / 24 + 1.674) / (4 * (x - 6)) ≤ 0.0199 := by
    rw [div_le_iff₀ (by positivity)]; norm_num; nlinarith
  norm_num at a1 a4 a5 ⊢
  linarith

/-- `Re (log M_t)' ≥ (1/2) log(x/(4π)) − 0.02` on the segment `Im w = x/2`, `0 ≤ Re w ≤ 1`, in the
region (5). -/
lemma re_logMtDeriv_ge {t x : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hx : 200 ≤ x) {w : ℂ}
    (hw : w.im = x / 2) (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) :
    Real.log (x / (4 * Real.pi)) / 2 - 0.02
      ≤ (alpha w + (t : ℂ) / 2 * alpha w * alphaDeriv w).re := by
  have hx0 : 0 < x := by linarith
  have hx6 : 0 < x - 6 := by linarith
  have hre := re_alpha_ge_of_im hx0 hw h0
  have hna := norm_alpha_le_of_im (by nlinarith [Real.pi_lt_d2]) hw h0 h1
  have hnd : ‖alphaDeriv w‖ ≤ 1 / (x - 6) := by
    have := norm_alphaDeriv_le (s := w) (by rw [hw]; linarith)
    rwa [show 2 * w.im - 6 = x - 6 by rw [hw]; ring] at this
  have hnum := gamma_numeric hx
  have hprod : ‖(t : ℂ) / 2 * alpha w * alphaDeriv w‖
      ≤ 1 / 4 * (3 / x + ((1 + x / 2) / (2 * Real.pi) + Real.pi) / 2) * (1 / (x - 6)) := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0,
      Complex.norm_two]
    have : t / 2 ≤ 1 / 4 := by linarith
    gcongr
  have hre2 : -‖(t : ℂ) / 2 * alpha w * alphaDeriv w‖
      ≤ ((t : ℂ) / 2 * alpha w * alphaDeriv w).re := by
    have h1 := abs_re_le_norm ((t : ℂ) / 2 * alpha w * alphaDeriv w)
    have h2 := neg_abs_le ((t : ℂ) / 2 * alpha w * alphaDeriv w).re
    linarith
  rw [Complex.add_re]
  linarith

/-- The real-part function `g(σ) = Re log M_t(σ + ix/2)` along the horizontal line. -/
def gLine (t x σ : ℝ) : ℝ := (logMt t ((σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I)).re

lemma hasDerivAt_gLine (t : ℝ) {x : ℝ} (hx : 0 < x) (σ : ℝ) :
    HasDerivAt (gLine t x)
      (alpha ((σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I)
        + (t : ℂ) / 2 * alpha ((σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I)
          * alphaDeriv ((σ : ℂ) + ((x / 2 : ℝ) : ℂ) * I)).re σ := by
  set c : ℂ := ((x / 2 : ℝ) : ℂ) * I with hc
  have him : ((σ : ℂ) + c).im ≠ 0 := by simp [hc]; exact hx.ne'
  have hs : (σ : ℂ) + c ∈ slitPlane := mem_slitPlane_of_im_ne_zero him
  have hs1 : (σ : ℂ) + c - 1 ∈ slitPlane := mem_slitPlane_of_im_ne_zero (by simpa using him)
  have hL := hasDerivAt_logMt t hs hs1
  have hshift : HasDerivAt (fun z : ℂ ↦ z + c) 1 (σ : ℂ) := (hasDerivAt_id' _).add_const c
  have hcomp := (hL.comp (σ : ℂ) hshift).real_of_complex
  refine hcomp.congr_deriv ?_
  rw [mul_one]

/-- `|gamma| = exp(g((1−y)/2) − g((1+y)/2))`, via `M_t = M_t^*`. -/
lemma norm_gammaP_eq (t : ℝ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖gammaP t x y‖ = Real.exp (gLine t x ((1 - y) / 2) - gLine t x ((1 + y) / 2)) := by
  have hm : (1 - (y : ℂ) + (x : ℂ) * I) / 2 = (((1 - y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have hp : (1 + (y : ℂ) - (x : ℂ) * I) / 2 = conj ((((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I) := by
    simp only [map_add, map_mul, conj_ofReal, conj_I]; push_cast; ring
  have him : ((((1 + y) / 2 : ℝ) : ℂ) + ((x / 2 : ℝ) : ℂ) * I).im ≠ 0 := by simp; exact hx.ne'
  unfold gammaP
  rw [norm_div, norm_Mt, norm_Mt, hm, hp, logMt_conj t him, Complex.conj_re, ← Real.exp_sub]
  rfl

/-- **P15 (20)** (= Proposition 6.6 (i)): in the region (5),
`|gamma| ≤ e^{0.02 y} (x/(4π))^{−y/2}`. -/
theorem norm_gammaP_le {t x y : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hx : 200 ≤ x)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖gammaP t x y‖ ≤ Real.exp (0.02 * y) * (x / (4 * Real.pi)) ^ (-y / 2) := by
  have hx0 : 0 < x := by linarith
  set L : ℝ := Real.log (x / (4 * Real.pi)) / 2 - 0.02 with hL
  -- the slope bound along the segment [(1-y)/2, (1+y)/2]
  have hslope : L * y ≤ gLine t x ((1 + y) / 2) - gLine t x ((1 - y) / 2) := by
    rcases hy0.lt_or_eq with hy | hy
    · have hab : (1 - y) / 2 < (1 + y) / 2 := by linarith
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (gLine t x) _ hab
        (fun σ _ ↦ (hasDerivAt_gLine t hx0 σ).continuousAt.continuousWithinAt)
        (fun σ _ ↦ hasDerivAt_gLine t hx0 σ)
      have hcw : ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * I).im = x / 2 := by simp
      have hc0 : 0 ≤ ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * I).re := by simp; linarith [hc.1]
      have hc1 : ((c : ℂ) + ((x / 2 : ℝ) : ℂ) * I).re ≤ 1 := by simp; linarith [hc.2]
      have hder := re_logMtDeriv_ge ht0 ht hx hcw hc0 hc1
      rw [hceq, show (1 + y) / 2 - (1 - y) / 2 = y by ring] at hder
      rw [← hL] at hder
      have := mul_le_mul_of_nonneg_right hder hy.le
      rwa [div_mul_cancel₀ _ hy.ne'] at this
    · subst hy; simp
  rw [norm_gammaP_eq t hx0 y, Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hL] at hslope
  nlinarith

end

end DBNM5
