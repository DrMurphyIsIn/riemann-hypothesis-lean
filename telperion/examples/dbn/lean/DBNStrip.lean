/-
  DBNStrip -- Route C / C3 input on the de Bruijn-Newman island: the zero strip of H_0,
  registry node RH.dbn_H0_zero_strip, proved C2-FREE
  (telperion/docs/DESIGN_RH_dbn_debruijn_real_zeros_2026-09-22.md, section 2.1 and the lemma
  table rows L1a-L1d).

  Registry statement (stated verbatim at the end of this file as `dbn_H0_zero_strip`):

    ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1.

  Route, with `s := 1/2 + i z/2` (so `Re s = 1/2 − Im z / 2`, and `Im z < −1 ↔ Re s > 1`):

    L1a  two-sided fold: `H_0(z) = (1/2) ∫_ℝ Φ(u) e^{izu} du` for every complex `z`
         (`H_zero_eq_half_integral`), from the evenness of `Φ` and `cos w = (e^{iw} + e^{−iw})/2`;
         plus Schwarz reflection `conj (H_t z) = H_t (conj z)` (`H_conj`).
    L1b  the Gamma integral on the whole line,
         `∫_ℝ e^{wu} exp(−c e^{4u}) du = (1/4) (1/c)^{w/4} Γ(w/4)` for `Re w > 0`, `c > 0`
         (substitution `x = e^{4u}` over all of ℝ onto `Ioi 0`, then Mathlib's
         `Complex.integral_cpow_mul_exp_neg_mul_Ioi`); termwise, with `Γ(σ+1) = σ Γ(σ)` twice,
         `∫_ℝ a_n(u) e^{izu} du = (1/8) s (s−1) π^{−s/2} Γ(s/2) n^{−s}` for `Im z < −1`
         (`integral_expTerm`), where `a_n` is the `n`-th term of the `Φ` series.
    L1c  Tonelli: `∫_ℝ ‖a_n(u) e^{izu}‖ du = O(n^{(Im z − 1)/2})` by the real Gamma integral,
         summable exactly when `Im z < −1`; Fubini (`hasSum_integral_of_summable_integral_norm`)
         and `ζ(s) = ∑ n^{−s}` give the half-plane identity (`H_zero_eq_of_im_lt`)
         `H_0(z) = (1/16) s (s−1) π^{−s/2} Γ(s/2) ζ(s)`  for `Im z < −1`.
    L1d  on `Re s > 1` every factor is nonzero: `s ≠ 0, 1`, `π^{−s/2} ≠ 0`,
         `Complex.Gamma_ne_zero_of_re_pos`, and `riemannZeta_ne_zero_of_one_lt_re` (the Euler
         product).  So `H_0 ≠ 0` on `Im z < −1`, and by `H_neg` on `Im z > 1`: every zero of `H_0`
         has `|Im z| ≤ 1` (`H0_zero_strip`), and `H_0 ≢ 0` (`H0_ne_zero`).

  What this module does NOT use: the representation theorem `H_0 = xi/8` (C2, registry node
  RH.dbn_H0_eq_xi, not proved on this island), analytic continuation of zeta, any Hadamard or
  Weierstrass product, or Riemann's theta-integral route to xi.  One transitive input, stated
  plainly: the evenness `Φ_neg` consumed by the L1a fold is the existing `DBNDefs` theorem, which
  `DBNDefs` derives from Mathlib's `jacobiTheta₂_functional_equation` (via `thetaMoment_zero_fe`);
  the design memo's L1a is exactly this use of evenness.  This module invokes no functional
  equation directly, and the identity above is claimed ONLY on the absolutely convergent
  half-plane `Re s > 1`.

  SCOPE.  The theorem confines the zeros of `H_0` to the closed horizontal strip `|Im z| ≤ 1`
  (classically: the zeros of xi lie in the closed critical strip) and says NOTHING about the
  zeros inside the strip, which is where RH lives.  It is the clean seam between the zeta side and
  the heat-flow side of de Bruijn's `t ≥ 1/2` theorem (C3), which it does not prove.  It proves
  neither C2 nor C4.  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNDefs

open Real MeasureTheory Set Filter Topology

namespace DBN

/-! ### L1b: the Gamma integral on the whole line -/

/-- Change of variables `x = e^u` over the whole real line. -/
lemma integral_exp_smul_comp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) : ∫ u : ℝ, Real.exp u • g (Real.exp u) = ∫ x in Ioi (0 : ℝ), g x := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  simp only [Real.abs_exp]

/-- `(e^v)^a = e^{a v}` for the complex power of a positive real. -/
lemma ofReal_exp_cpow_comm (v : ℝ) (a : ℂ) :
    ((Real.exp v : ℝ) : ℂ) ^ a = Complex.exp (a * v) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'),
    ← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp, mul_comm]

/-- **Gamma integral on the line** (complex exponent):
`∫_ℝ e^{wu} exp(−c e^{4u}) du = (1/4) (1/c)^{w/4} Γ(w/4)` for `Re w > 0`, `c > 0`. -/
theorem integral_cexp_mul_exp_neg_exp {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, Complex.exp (w * u) * ((Real.exp (-c * Real.exp (4 * u)) : ℝ) : ℂ)
      = (1 / 4 : ℂ) * ((1 / (c : ℂ)) ^ (w / 4) * Complex.Gamma (w / 4)) := by
  have hw4 : 0 < (w / 4).re := by
    rw [Complex.div_ofNat_re]; positivity
  have h1 : ∫ u : ℝ, Complex.exp (w * u) * ((Real.exp (-c * Real.exp (4 * u)) : ℝ) : ℂ)
      = |(4 : ℝ)⁻¹| • ∫ v : ℝ, Complex.exp (w / 4 * v) * ((Real.exp (-c * Real.exp v) : ℝ) : ℂ) := by
    rw [← Measure.integral_comp_mul_left]
    congr 1
    funext u
    congr 2
    push_cast
    ring
  have h2 : ∫ v : ℝ, Complex.exp (w / 4 * v) * ((Real.exp (-c * Real.exp v) : ℝ) : ℂ)
      = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (w / 4 - 1) * Complex.exp (-(c * x)) := by
    rw [← integral_exp_smul_comp_exp]
    congr 1
    funext v
    rw [ofReal_exp_cpow_comm, Complex.real_smul]
    push_cast
    simp only [← Complex.exp_add]
    congr 1
    ring
  rw [h1, h2, Complex.integral_cpow_mul_exp_neg_mul_Ioi hw4 hc]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4⁻¹), Complex.real_smul]
  push_cast
  ring

/-- **Gamma integral on the line** (real exponent):
`∫_ℝ e^{ku} exp(−c e^{4u}) du = (1/4) (1/c)^{k/4} Γ(k/4)` for `k > 0`, `c > 0`. -/
theorem integral_exp_mul_exp_neg_exp {k : ℝ} (hk : 0 < k) {c : ℝ} (hc : 0 < c) :
    ∫ u : ℝ, Real.exp (k * u) * Real.exp (-c * Real.exp (4 * u))
      = 1 / 4 * ((1 / c) ^ (k / 4) * Real.Gamma (k / 4)) := by
  have hk4 : 0 < k / 4 := by positivity
  have h1 : ∫ u : ℝ, Real.exp (k * u) * Real.exp (-c * Real.exp (4 * u))
      = |(4 : ℝ)⁻¹| • ∫ v : ℝ, Real.exp (k / 4 * v) * Real.exp (-c * Real.exp v) := by
    rw [← Measure.integral_comp_mul_left]
    congr 1
    funext u
    congr 2
    ring
  have h2 : ∫ v : ℝ, Real.exp (k / 4 * v) * Real.exp (-c * Real.exp v)
      = ∫ x in Ioi (0 : ℝ), x ^ (k / 4 - 1) * Real.exp (-(c * x)) := by
    rw [← integral_exp_smul_comp_exp]
    congr 1
    funext v
    rw [smul_eq_mul, ← Real.exp_mul]
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [h1, h2, Real.integral_rpow_mul_exp_neg_mul_Ioi hk4 hc]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4⁻¹), smul_eq_mul]
  ring

/-- Integrability of the complex Gamma-line integrand (its integral is a nonzero Gamma value). -/
theorem integrable_cexp_mul_exp_neg_exp {w : ℂ} (hw : 0 < w.re) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ ↦ Complex.exp (w * u) * ((Real.exp (-c * Real.exp (4 * u)) : ℝ) : ℂ)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_cexp_mul_exp_neg_exp hw hc]
  have hw4 : 0 < (w / 4).re := by
    rw [Complex.div_ofNat_re]; positivity
  refine mul_ne_zero (by norm_num) (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hw4))
  intro h
  have := ((Complex.cpow_eq_zero_iff _ _).mp h).1
  exact one_div_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') this

/-- Integrability of the real Gamma-line integrand (its integral is a positive Gamma value). -/
theorem integrable_exp_mul_exp_neg_exp {k : ℝ} (hk : 0 < k) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ ↦ Real.exp (k * u) * Real.exp (-c * Real.exp (4 * u))) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_mul_exp_neg_exp hk hc]
  have hG := Real.Gamma_pos_of_pos (by positivity : 0 < k / 4)
  have : 0 < 1 / 4 * ((1 / c) ^ (k / 4) * Real.Gamma (k / 4)) := by positivity
  exact this.ne'

/-! ### L1a: the two-sided fold and Schwarz reflection -/

/-- The two-sided integrand `Φ(u) e^{izu}` on the whole real line. -/
noncomputable def expIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  ((Φ u : ℝ) : ℂ) * Complex.exp (z * u * Complex.I)

@[fun_prop]
lemma continuous_expIntegrand (z : ℂ) : Continuous (expIntegrand z) := by
  unfold expIntegrand
  fun_prop

/-- `‖e^{izu}‖ ≤ e^{‖z‖ u}` for `u ≥ 0`. -/
lemma norm_cexp_mul_I_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.exp (z * u * Complex.I)‖ ≤ Real.exp (‖z‖ * u) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (z * u * Complex.I).re = -(z.im * u) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have h : -z.im ≤ ‖z‖ := by linarith [neg_abs_le z.im, Complex.abs_im_le_norm z]
  nlinarith [mul_le_mul_of_nonneg_right h hu]

/-- Reflection: `Φ(−u) e^{iz(−u)} = Φ(u) e^{i(−z)u}` (evenness of `Φ`). -/
lemma expIntegrand_neg (z : ℂ) (u : ℝ) : expIntegrand z (-u) = expIntegrand (-z) u := by
  unfold expIntegrand
  rw [Φ_neg]
  congr 2
  push_cast
  ring

/-- `Φ(u) e^{izu}` is integrable on `(0, ∞)` for every complex `z`. -/
theorem integrableOn_expIntegrand_Ioi (z : ℂ) : IntegrableOn (expIntegrand z) (Ioi 0) := by
  have hg := (integrableOn_exp_quad_mul_exp_neg_exp 0 (9 + ‖z‖)).const_mul ΦBoundConst
  refine hg.mono' (continuous_expIntegrand z).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  have hΦ := abs_Φ_le hu0
  have hC := ΦBoundConst_nonneg
  have he := norm_cexp_mul_I_le z hu0
  unfold expIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |Φ u| * ‖Complex.exp (z * u * Complex.I)‖
      ≤ (ΦBoundConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * Real.exp (‖z‖ * u) := by gcongr
    _ = ΦBoundConst * (Real.exp (0 * u ^ 2 + (9 + ‖z‖) * u)
          * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
        rw [show 0 * u ^ 2 + (9 + ‖z‖) * u = 9 * u + ‖z‖ * u by ring, Real.exp_add]; ring

/-- `Φ(u) e^{izu}` is integrable on `(−∞, 0]` (reflect to `(0, ∞)` with `−z`). -/
theorem integrableOn_expIntegrand_Iic (z : ℂ) : IntegrableOn (expIntegrand z) (Iic 0) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simp_rw [Function.comp_def, neg_preimage, neg_Iic, neg_zero, expIntegrand_neg]
  exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_expIntegrand_Ioi (-z))

/-- `Φ(u) e^{izu}` is integrable on the whole real line for every complex `z`. -/
theorem integrable_expIntegrand (z : ℂ) : Integrable (expIntegrand z) := by
  have := (integrableOn_expIntegrand_Iic z).union (integrableOn_expIntegrand_Ioi z)
  rwa [Iic_union_Ioi, integrableOn_univ] at this

/-- **L1a, the two-sided fold**: `H_0(z) = (1/2) ∫_ℝ Φ(u) e^{izu} du` for every complex `z`
(evenness of `Φ` and `cos w = (e^{iw} + e^{−iw})/2`). -/
theorem H_zero_eq_half_integral (z : ℂ) :
    H 0 z = (1 / 2 : ℂ) * ∫ u : ℝ, expIntegrand z u := by
  have hpt : ∀ u : ℝ, HIntegrand 0 z u = (expIntegrand z u + expIntegrand z (-u)) / 2 := by
    intro u
    have hcos : Complex.cos (z * u)
        = (Complex.exp (z * u * Complex.I) + Complex.exp (-(z * u) * Complex.I)) / 2 := rfl
    have harg : z * ((-u : ℝ) : ℂ) * Complex.I = -(z * u) * Complex.I := by push_cast; ring
    unfold HIntegrand expIntegrand
    rw [hcos, Φ_neg, harg]
    simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
    ring
  have hInt1 := integrableOn_expIntegrand_Ioi z
  have hInt2 : IntegrableOn (fun u ↦ expIntegrand z (-u)) (Ioi 0) := by
    simp_rw [expIntegrand_neg]
    exact integrableOn_expIntegrand_Ioi (-z)
  unfold H
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ ↦ hpt u), integral_div,
    integral_add hInt1 hInt2, integral_comp_neg_Ioi (f := expIntegrand z), neg_zero,
    ← intervalIntegral.integral_Iic_add_Ioi (integrableOn_expIntegrand_Iic z) hInt1]
  ring

/-- **Schwarz reflection**: `conj (H_t z) = H_t (conj z)` for every real `t`. -/
theorem H_conj (t : ℝ) (z : ℂ) : (starRingEnd ℂ) (H t z) = H t ((starRingEnd ℂ) z) := by
  unfold H
  rw [← integral_conj]
  congr 1
  funext u
  unfold HIntegrand
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.cos_conj, map_mul,
    Complex.conj_ofReal]

/-! ### L1b (termwise): the Gamma value of each term of the `Φ` series -/

/-- The `n`-th term `a_n(u) = (2π²n⁴e^{9u} − 3πn²e^{5u}) exp(−πn²e^{4u})` of the `Φ` series. -/
noncomputable def ΦTerm (n : ℕ+) (u : ℝ) : ℝ :=
  (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u))
    * Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (4 * u))

lemma Φ_eq_tsum_ΦTerm (u : ℝ) : Φ u = ∑' n : ℕ+, ΦTerm n u := rfl

/-- The complex `n`-th term `a_n(u) e^{izu}`. -/
noncomputable def expTerm (z : ℂ) (n : ℕ+) (u : ℝ) : ℂ :=
  ((ΦTerm n u : ℝ) : ℂ) * Complex.exp (z * u * Complex.I)

/-- `a_n(u) e^{izu}` as a combination of two Gamma-line integrands with `c = π n²`. -/
lemma expTerm_eq (z : ℂ) (n : ℕ+) (u : ℝ) :
    expTerm z n u
      = 2 * (π : ℂ) ^ 2 * (n : ℂ) ^ 4 * (Complex.exp ((9 + z * Complex.I) * u)
          * ((Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u)) : ℝ) : ℂ))
        - 3 * (π : ℂ) * (n : ℂ) ^ 2 * (Complex.exp ((5 + z * Complex.I) * u)
          * ((Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u)) : ℝ) : ℂ)) := by
  unfold expTerm ΦTerm
  rw [show -π * (n : ℝ) ^ 2 * Real.exp (4 * u) = -(π * (n : ℝ) ^ 2) * Real.exp (4 * u) by ring,
    show (9 + z * Complex.I) * (u : ℂ) = ((9 * u : ℝ) : ℂ) + z * u * Complex.I by push_cast; ring,
    show (5 + z * Complex.I) * (u : ℂ) = ((5 * u : ℝ) : ℂ) + z * u * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_add]
  push_cast
  ring

/-- Real part of `s = 1/2 + iz/2`. -/
lemma stripArg_re (z : ℂ) : (1 / 2 + Complex.I * z / 2).re = 1 / 2 - z.im / 2 := by
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.I_mul_re, Complex.one_re]
  ring

/-- `(1/(πn²))^{s/2} = π^{−s/2} · n^{−s}` (complex powers of positive reals). -/
lemma one_div_pi_mul_sq_cpow (n : ℕ+) (s : ℂ) :
    (1 / ((π * (n : ℝ) ^ 2 : ℝ) : ℂ)) ^ (s / 2) = (π : ℂ) ^ (-s / 2) * (1 / (n : ℂ) ^ s) := by
  have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have harg : ((π * (n : ℝ) ^ 2 : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_pos.ne
  have hsq : ((n : ℝ) ^ 2 : ℝ) = (n : ℝ) * (n : ℝ) := sq _
  have h1 : (((π * (n : ℝ) ^ 2 : ℝ)) : ℂ) ^ (s / 2) = (π : ℂ) ^ (s / 2) * ((n : ℝ) : ℂ) ^ s := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hπ (by positivity), hsq,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hn hn, ← Complex.cpow_add _ _ hn0,
      add_halves]
  rw [one_div, Complex.inv_cpow _ _ harg, h1, neg_div, Complex.cpow_neg, Complex.ofReal_natCast]
  ring

/-- **L1b termwise**: for `Im z < −1`, with `s = 1/2 + iz/2`,
`∫_ℝ a_n(u) e^{izu} du = (1/8) s (s−1) π^{−s/2} Γ(s/2) n^{−s}`. -/
theorem integral_expTerm {z : ℂ} (hz : z.im < -1) (n : ℕ+) :
    ∫ u : ℝ, expTerm z n u
      = (1 / 8 : ℂ) * (1 / 2 + Complex.I * z / 2) * (1 / 2 + Complex.I * z / 2 - 1)
        * (π : ℂ) ^ (-(1 / 2 + Complex.I * z / 2) / 2)
        * Complex.Gamma ((1 / 2 + Complex.I * z / 2) / 2)
        * (1 / (n : ℂ) ^ (1 / 2 + Complex.I * z / 2)) := by
  have hsre : ((1 / 2 + Complex.I * z / 2) / 2).re = 1 / 4 - z.im / 4 := by
    rw [Complex.div_ofNat_re, stripArg_re]; ring
  set s : ℂ := 1 / 2 + Complex.I * z / 2 with hs
  have hc : 0 < π * (n : ℝ) ^ 2 := by positivity
  have hw1 : 0 < (9 + z * Complex.I).re := by simp; linarith
  have hw2 : 0 < (5 + z * Complex.I).re := by simp; linarith
  have hs0 : s / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre, Complex.zero_re] at this; linarith
  have hs1 : s / 2 + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h
    rw [Complex.add_re, hsre, Complex.one_re, Complex.zero_re] at this; linarith
  have hI1 := (integrable_cexp_mul_exp_neg_exp hw1 hc).const_mul (2 * (π : ℂ) ^ 2 * (n : ℂ) ^ 4)
  have hI2 := (integrable_cexp_mul_exp_neg_exp hw2 hc).const_mul (3 * (π : ℂ) * (n : ℂ) ^ 2)
  simp_rw [expTerm_eq]
  rw [integral_sub hI1 hI2, integral_const_mul, integral_const_mul,
    integral_cexp_mul_exp_neg_exp hw1 hc, integral_cexp_mul_exp_neg_exp hw2 hc]
  have e1 : (9 + z * Complex.I) / 4 = s / 2 + 1 + 1 := by rw [hs]; ring
  have e2 : (5 + z * Complex.I) / 4 = s / 2 + 1 := by rw [hs]; ring
  have hb : (1 / ((π * (n : ℝ) ^ 2 : ℝ) : ℂ)) ≠ 0 :=
    one_div_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
  rw [e1, e2, Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs0,
    Complex.cpow_add _ _ hb, Complex.cpow_add _ _ hb, Complex.cpow_one, one_div_pi_mul_sq_cpow]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hns : (n : ℂ) ^ s ≠ 0 := fun h ↦ hn ((Complex.cpow_eq_zero_iff _ _).mp h).1
  push_cast
  field_simp
  ring

/-- Each `a_n(u) e^{izu}` is integrable on the line (for `Im z < −1`). -/
theorem integrable_expTerm {z : ℂ} (hz : z.im < -1) (n : ℕ+) : Integrable (expTerm z n) := by
  have hc : 0 < π * (n : ℝ) ^ 2 := by positivity
  have hw1 : 0 < (9 + z * Complex.I).re := by simp; linarith
  have hw2 : 0 < (5 + z * Complex.I).re := by simp; linarith
  have h := ((integrable_cexp_mul_exp_neg_exp hw1 hc).const_mul (2 * (π : ℂ) ^ 2 * (n : ℂ) ^ 4)).sub
    ((integrable_cexp_mul_exp_neg_exp hw2 hc).const_mul (3 * (π : ℂ) * (n : ℂ) ^ 2))
  refine h.congr (Eventually.of_forall fun u ↦ ?_)
  simp only [Pi.sub_apply]
  exact (expTerm_eq z n u).symm

/-- Pointwise majorant of `‖a_n(u) e^{izu}‖` by two real Gamma-line integrands. -/
lemma norm_expTerm_le (z : ℂ) (n : ℕ+) (u : ℝ) :
    ‖expTerm z n u‖ ≤ 2 * π ^ 2 * (n : ℝ) ^ 4 * (Real.exp ((9 - z.im) * u)
          * Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u)))
      + 3 * π * (n : ℝ) ^ 2 * (Real.exp ((5 - z.im) * u)
          * Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u))) := by
  have hn1 : ‖2 * (π : ℂ) ^ 2 * (n : ℂ) ^ 4‖ = 2 * π ^ 2 * (n : ℝ) ^ 4 := by
    rw [show (2 * (π : ℂ) ^ 2 * (n : ℂ) ^ 4) = ((2 * π ^ 2 * (n : ℝ) ^ 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hn2 : ‖3 * (π : ℂ) * (n : ℂ) ^ 2‖ = 3 * π * (n : ℝ) ^ 2 := by
    rw [show (3 * (π : ℂ) * (n : ℂ) ^ 2) = ((3 * π * (n : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have he1 : ‖Complex.exp ((9 + z * Complex.I) * u)‖ = Real.exp ((9 - z.im) * u) := by
    rw [Complex.norm_exp]; congr 1; simp [sub_eq_add_neg]
  have he2 : ‖Complex.exp ((5 + z * Complex.I) * u)‖ = Real.exp ((5 - z.im) * u) := by
    rw [Complex.norm_exp]; congr 1; simp [sub_eq_add_neg]
  have hr : ‖((Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u)) : ℝ) : ℂ)‖
      = Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [expTerm_eq]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul (2 * (π : ℂ) ^ 2 * (n : ℂ) ^ 4), norm_mul (3 * (π : ℂ) * (n : ℂ) ^ 2),
    norm_mul (Complex.exp ((9 + z * Complex.I) * u)),
    norm_mul (Complex.exp ((5 + z * Complex.I) * u)), hn1, hn2, he1, he2, hr]

/-- `n^m (1/(πn²))^{k/4} = π^{−k/4} n^q` whenever `m − k/2 = q` (real powers). -/
lemma pnat_pow_mul_one_div_rpow (n : ℕ+) (m : ℕ) (k q : ℝ) (hq : (m : ℝ) - k / 2 = q) :
    (n : ℝ) ^ m * (1 / (π * (n : ℝ) ^ 2)) ^ (k / 4) = π ^ (-(k / 4)) * (n : ℝ) ^ q := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have h2 : ((n : ℝ) ^ 2) ^ (k / 4) = (n : ℝ) ^ (k / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    push_cast
    ring
  have hπk : π ^ (k / 4) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hnk : (n : ℝ) ^ (k / 2) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  rw [one_div, Real.inv_rpow (by positivity), Real.mul_rpow Real.pi_pos.le (by positivity), h2,
    Real.rpow_neg Real.pi_pos.le, ← hq, Real.rpow_sub hn, Real.rpow_natCast]
  field_simp

/-- **L1c, Tonelli**: for `Im z < −1`, `∑_n ∫ ‖a_n(u) e^{izu}‖ du < ∞`; the `n`-th integral is
`O(n^{(Im z − 1)/2})` by the real Gamma-line integral. -/
theorem summable_integral_norm_expTerm {z : ℂ} (hz : z.im < -1) :
    Summable (fun n : ℕ+ ↦ ∫ u : ℝ, ‖expTerm z n u‖) := by
  have hk1 : 0 < 9 - z.im := by linarith
  have hk2 : 0 < 5 - z.im := by linarith
  have hp1 : (z.im - 1) / 2 < -1 := by linarith
  have hsum : Summable (fun n : ℕ+ ↦ (n : ℝ) ^ ((z.im - 1) / 2)) :=
    (summable_pnat_iff_summable_nat (f := fun n : ℕ ↦ (n : ℝ) ^ ((z.im - 1) / 2))).mpr
      (Real.summable_nat_rpow.mpr hp1)
  refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun u ↦ norm_nonneg _) (fun n ↦ ?_)
    ((hsum.mul_left (2 * π ^ 2 * (1 / 4 * (π ^ (-((9 - z.im) / 4)) * Real.Gamma ((9 - z.im) / 4))))).add
      (hsum.mul_left (3 * π * (1 / 4 * (π ^ (-((5 - z.im) / 4)) * Real.Gamma ((5 - z.im) / 4))))))
  have hc : 0 < π * (n : ℝ) ^ 2 := by positivity
  have hI1 := (integrable_exp_mul_exp_neg_exp hk1 hc).const_mul (2 * π ^ 2 * (n : ℝ) ^ 4)
  have hI2 := (integrable_exp_mul_exp_neg_exp hk2 hc).const_mul (3 * π * (n : ℝ) ^ 2)
  have e1 := pnat_pow_mul_one_div_rpow n 4 (9 - z.im) ((z.im - 1) / 2) (by push_cast; ring)
  have e2 := pnat_pow_mul_one_div_rpow n 2 (5 - z.im) ((z.im - 1) / 2) (by push_cast; ring)
  calc ∫ u : ℝ, ‖expTerm z n u‖
      ≤ ∫ u : ℝ, (2 * π ^ 2 * (n : ℝ) ^ 4 * (Real.exp ((9 - z.im) * u)
            * Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u)))
          + 3 * π * (n : ℝ) ^ 2 * (Real.exp ((5 - z.im) * u)
            * Real.exp (-(π * (n : ℝ) ^ 2) * Real.exp (4 * u)))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun u ↦ norm_nonneg (expTerm z n u))
          (hI1.add hI2) (Eventually.of_forall fun u ↦ norm_expTerm_le z n u)
    _ = 2 * π ^ 2 * (n : ℝ) ^ 4 * (1 / 4 * ((1 / (π * (n : ℝ) ^ 2)) ^ ((9 - z.im) / 4)
            * Real.Gamma ((9 - z.im) / 4)))
        + 3 * π * (n : ℝ) ^ 2 * (1 / 4 * ((1 / (π * (n : ℝ) ^ 2)) ^ ((5 - z.im) / 4)
            * Real.Gamma ((5 - z.im) / 4))) := by
        rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul,
          integral_exp_mul_exp_neg_exp hk1 hc, integral_exp_mul_exp_neg_exp hk2 hc]
    _ = _ := by
        linear_combination (2 * π ^ 2 * (1 / 4) * Real.Gamma ((9 - z.im) / 4)) * e1
          + (3 * π * (1 / 4) * Real.Gamma ((5 - z.im) / 4)) * e2

/-! ### L1c: Fubini and the half-plane identity -/

/-- **L1c, Fubini**: for `Im z < −1`, `∑_n ∫_ℝ a_n e^{iz·} = ∫_ℝ Φ e^{iz·}`. -/
theorem hasSum_integral_expTerm {z : ℂ} (hz : z.im < -1) :
    HasSum (fun n : ℕ+ ↦ ∫ u : ℝ, expTerm z n u) (∫ u : ℝ, expIntegrand z u) := by
  have h := hasSum_integral_of_summable_integral_norm (μ := volume) (integrable_expTerm hz)
    (summable_integral_norm_expTerm hz)
  have hfun : (fun u : ℝ ↦ ∑' n : ℕ+, expTerm z n u) = expIntegrand z := by
    funext u
    unfold expIntegrand expTerm
    rw [Φ_eq_tsum_ΦTerm, Complex.ofReal_tsum, tsum_mul_right]
  rw [hfun] at h
  exact h

/-- **L1c, the half-plane identity** (two-sided form): for `Im z < −1`, with `s = 1/2 + iz/2`
(so `Re s > 1`), `∫_ℝ Φ(u) e^{izu} du = (1/8) s (s−1) π^{−s/2} Γ(s/2) ζ(s)`. -/
theorem integral_expIntegrand_eq {z : ℂ} (hz : z.im < -1) :
    ∫ u : ℝ, expIntegrand z u
      = (1 / 8 : ℂ) * (1 / 2 + Complex.I * z / 2) * (1 / 2 + Complex.I * z / 2 - 1)
        * (π : ℂ) ^ (-(1 / 2 + Complex.I * z / 2) / 2)
        * Complex.Gamma ((1 / 2 + Complex.I * z / 2) / 2)
        * riemannZeta (1 / 2 + Complex.I * z / 2) := by
  have hre : 1 < (1 / 2 + Complex.I * z / 2).re := by rw [stripArg_re]; linarith
  have h := hasSum_integral_expTerm hz
  simp_rw [integral_expTerm hz] at h
  rw [← h.tsum_eq, tsum_mul_left, zeta_eq_tsum_one_div_nat_add_one_cpow hre,
    tsum_pnat_eq_tsum_succ (f := fun m : ℕ ↦ 1 / (m : ℂ) ^ (1 / 2 + Complex.I * z / 2))]
  push_cast
  rfl

/-- **The half-plane identity for `H_0`** (C2-free): for `Im z < −1`, with `s = 1/2 + iz/2`,
`H_0(z) = (1/16) s (s−1) π^{−s/2} Γ(s/2) ζ(s)`.  No analytic continuation of zeta and no
representation theorem: this is the absolutely convergent Dirichlet-series half-plane `Re s > 1`
only (the fold uses the island's evenness `Φ_neg`). -/
theorem H_zero_eq_of_im_lt {z : ℂ} (hz : z.im < -1) :
    H 0 z = (1 / 16 : ℂ) * (1 / 2 + Complex.I * z / 2) * (1 / 2 + Complex.I * z / 2 - 1)
        * (π : ℂ) ^ (-(1 / 2 + Complex.I * z / 2) / 2)
        * Complex.Gamma ((1 / 2 + Complex.I * z / 2) / 2)
        * riemannZeta (1 / 2 + Complex.I * z / 2) := by
  rw [H_zero_eq_half_integral, integral_expIntegrand_eq hz]
  ring

/-! ### L1d: nonvanishing off the strip, and the zero strip -/

/-- `H_0(z) ≠ 0` for `Im z < −1` (Euler product: `ζ(s) ≠ 0` for `Re s > 1`; `Γ(s/2) ≠ 0`). -/
theorem H_zero_ne_zero_of_im_lt {z : ℂ} (hz : z.im < -1) : H 0 z ≠ 0 := by
  rw [H_zero_eq_of_im_lt hz]
  have hre : 1 < (1 / 2 + Complex.I * z / 2).re := by rw [stripArg_re]; linarith
  set s : ℂ := 1 / 2 + Complex.I * z / 2 with hs
  have hs0 : s ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hre; linarith
  have hs1 : s - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this; linarith
  have hπ : (π : ℂ) ^ (-s / 2) ≠ 0 := fun h ↦
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have hΓ : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.div_ofNat_re]; linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hs1)
    hπ) hΓ) hζ

/-- `H_0(z) ≠ 0` for `Im z > 1` (reflection `H_neg`). -/
theorem H_zero_ne_zero_of_one_lt_im {z : ℂ} (hz : 1 < z.im) : H 0 z ≠ 0 := by
  rw [← H_neg]
  exact H_zero_ne_zero_of_im_lt (by rw [Complex.neg_im]; linarith)

/-- **L1d, the zero strip of `H_0`** (C2-free): every zero of `H_0` lies in the closed strip
`|Im z| ≤ 1`.  Says nothing about zeros inside the strip. -/
theorem H0_zero_strip : ∀ z : ℂ, H 0 z = 0 → z.im ^ 2 ≤ 1 := by
  intro z hz
  have h1 : -1 ≤ z.im := not_lt.mp fun h ↦ H_zero_ne_zero_of_im_lt h hz
  have h2 : z.im ≤ 1 := not_lt.mp fun h ↦ H_zero_ne_zero_of_one_lt_im h hz
  nlinarith

/-- `H_0` is not identically zero (by-product of the half-plane identity at `z = −2i`). -/
theorem H0_ne_zero : ∃ z : ℂ, H 0 z ≠ 0 :=
  ⟨-2 * Complex.I, H_zero_ne_zero_of_im_lt (by simp)⟩

end DBN

/-- Registry node `RH_dbn_H0_zero_strip`, statement verbatim.  C2-free: no `H_0 = xi/8`, no
analytic continuation of zeta, no Hadamard product; the only functional-equation input is the
island's existing evenness `Φ_neg` (DBNDefs), consumed by the two-sided fold.  It confines the
zeros of `H_0` to the closed strip `|Im z| ≤ 1` and says nothing about zeros inside the strip,
which is where RH lives.  Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_H0_zero_strip :
    ∀ z : ℂ, DBN.H 0 z = 0 → z.im ^ 2 ≤ 1 :=
  DBN.H0_zero_strip
