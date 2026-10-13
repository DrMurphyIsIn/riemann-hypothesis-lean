/-
  E6Bridge6 -- the converse half of Weil's criterion on this island's vocabulary (2026-09-20):
  Weil positivity of the explicit-formula functional on Hermitian autocorrelations

      0 <= Re [ archSide (g * g~) - primeSide (g * g~) ]   for every smooth compactly
                                                            supported g : R -> C

  implies Mathlib's `RiemannHypothesis`, PROVED MODULO TWO NAMED ANALYTIC OBLIGATIONS
  (GaussianTransfer, GaussianDominance; both `def ... : Prop`, both stated in words in their
  docstrings, both consumed only as hypotheses of the delivered theorem).  Section H further
  reduces GaussianTransfer to GaussianApprox, a statement about test functions alone (no zeros),
  via Tannery's theorem; weil_positivity_implies_rh_of' consumes that form.  Classical
  mathematics (Weil 1952; Bombieri, Rend. Mat. Acc. Lincei 2000, on exactly C_c^infinity); the
  analytic argument is not formalized anywhere in this repository; this file is the honest
  skeleton and the design memo is telperion/docs/WEIL_CONVERSE_ATTACK_2026-09-20.md.

  WHAT IS CONSUMED (all unconditional, #print axioms = [propext, Classical.choice, Quot.sound]):
    RvMBridge4.limit_explicit_formula        (the E8 node: explicit formula as a HasSum over
                                              ALL rho : C with the divisor weight)
    RvMBridge4.weilKernel_eq_paperFT_gammaOf (H_g(s) = h_g(gammaOf s), gammaOf s = (s-1/2)/i)
    RvMBridge4.zeroMult_eq_mult, RvMBridge4.zeroMult_eq_zero_of_not_nontrivial
    RvMBridge5.autocorr_eq_weilTest, RvMBridge5.isWeilTest_autocorr   (forward-half file)
    RvMBridge5.rh_implies_weil_positivity   (only for the two-sided corollary at the end)
    RvMBridgeGauss.summable_mult_div_one_add_normSq, tendsto_tsum_zeroMult_of_strip_bound
                                            (the Gaussian prelude: local-count majorant, Tannery)
    Zeta23.EF.paperFT_weilTest              (h_{f * g~}(z) = h_f(z) conj (h_g (conj z)))
    Zeta23.zeta_reflect_zero, Zeta23.zeta_mult_reflect   (rho -> 1 - conj rho preserves the
                                              nontrivial zeros and their multiplicities)
    Mathlib: riemannZeta_one_sub, riemannZeta_ne_zero_of_one_le_re, riemannZeta_zero,
             Complex.Gamma_ne_zero, Complex.cos_eq_zero_iff   (the strip lemma).

  THE ARGUMENT (Weil / Bombieri, rearranged for this island).  Write h := paperFT g and
  gamma_rho := gammaOf rho = (rho - 1/2)/i, so gamma_rho is real iff rho is on the line and
  gamma_{1 - conj rho} = conj gamma_rho.  For the autocorrelation f = g * g~ the explicit
  formula reads
      weilForm f = Sum_rho m(rho) h(gamma_rho) conj (h (conj gamma_rho))
                 =: zeroSide (hermitianTransform g),                               (B)
  a REAL number (the summand at 1 - conj rho is the conjugate of the summand at rho, section C).
  On-line zeros contribute m |h(gamma)|^2 >= 0; an off-line pair {rho, 1 - conj rho} contributes
  2 m Re [h(gamma + i delta) conj (h (gamma - i delta))], delta = 1/2 - Re rho, whose sign is
  free.  The contradiction with positivity comes from the Gaussian-derivative family
      G_{c,lam}(z) := (z - c)^2 exp (-2 lam (z - c)^2)        (= h h* for h(z) = (z-c) e^{-lam (z-c)^2})
  whose zero side  S(c, lam) := Sum_rho m(rho) G_{c,lam}(gamma_rho)  satisfies, for every zero
  rho' = beta' + i gamma' with w = gamma_rho' - c = x + i y (x = gamma' - c, y = 1/2 - beta'):
      |m G(w)| = m |w|^2 exp (2 lam (y^2 - x^2)),   arg G(w) = 2 arg w - 4 lam x y.
  Given an off-line zero rho_0, choose c within |delta_0| of gamma_0 (so the exponent
  y^2 - x^2 is > 0 at rho_0) and generic (finitely many bad c: only zeros within ordinate
  distance 1 of gamma_0 can tie).  The maximiser of y^2 - x^2 over all zeros is attained (only
  finitely many zeros have y^2 - x^2 >= 0), is off the line, and is unique up to the pair
  rho <-> 1 - conj rho.  Its pair term is  -2 m y^2 e^{2 lam M}  when x = 0 and
  2 m |w|^2 e^{2 lam M} cos (2 arg w - 4 lam x y)  when x != 0 (choose lam_k -> infinity with the
  cosine equal to -1); every other zero contributes at most e^{2 lam (M - eta)} (finitely many
  with nonnegative exponent) or a lam-uniform constant (the rest, summable by the local zero
  count Sum m/(1+|gamma|^2) < infinity, Zeta23.WeilEF.zero_sum_inv_sq).  So Re S(c, lam) < 0
  for some lam: that is GaussianDominance (O2).  Positivity, however, is assumed only on
  C_c^infinity tests; the Gaussian-derivative transform is the limit of transforms of truncated
  tests, and the zero side passes to the limit by dominated convergence (C/(1+x^2)^2 decay of the
  transform on the strip |Im z| <= 1/2, uniform in the truncation, against the same summable
  local count): that is GaussianTransfer (O1).  With (B), positivity gives
  Re zeroSide (hermitianTransform g_n) >= 0 for the approximants, hence Re S(c, lam) >= 0 in the
  limit, contradicting O2.  Finally Mathlib's RiemannHypothesis quantifies over zeros that are
  not trivial and not the pole; the strip lemma (section D) puts such a zero in 0 < Re < 1 by the
  functional equation and nonvanishing on Re >= 1.

  HONESTY: nothing about the zeros of zeta is proved here beyond the algebraic rearrangement of
  the E8 node.  O2 is the analytic heart (it is implied by RH, vacuously, and is far weaker than
  RH: it is an unconditional statement about a concrete Gaussian-weighted sum over the zeros,
  whose intended proof is the dominance analysis above and never mentions RH).  O1 is a
  dominated-convergence statement independent of RH.  conjecture1_proved = False.
-/
import E6Bridge5
import RvMBridgeGauss
import Zeta23.Statement.SeamClosed
import Mathlib.Analysis.Normed.Group.Tannery

open Zeta23 Complex MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RvMBridge6
open WeilExplicit

/-! ## A. Vocabulary: the zero-side functional on entire transforms. -/

/-- The Hermitian transform of a test g: H(z) = h_g(z) conj (h_g (conj z)), h_g = paperFT g.
This is paperFT (g * g~) (Zeta23.EF.paperFT_weilTest); on the real axis it is |h_g|^2. -/
def hermitianTransform (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  paperFT g z * conj (paperFT g (conj z))

/-- The zero side of the explicit formula for an arbitrary transform H: Sum_rho m(rho) H(gamma_rho)
over ALL rho : C, with the registry multiplicity (zero off the nontrivial zeros), gammaOf rho =
(rho - 1/2)/i. -/
def zeroSide (H : ℂ → ℂ) : ℂ :=
  ∑' ρ : ℂ, (WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ)

/-- The Gaussian-derivative Hermitian transform G_{c,lam}(z) = (z - c)^2 exp (-2 lam (z - c)^2)
(= h h* for h(z) = (z - c) exp (-lam (z - c)^2), the transform of a frequency-shifted derivative
of a Gaussian).  Real and nonnegative on the real axis; at gamma = c + i y it equals
-y^2 exp (2 lam y^2) < 0. -/
def gaussTest (c lam : ℝ) (z : ℂ) : ℂ :=
  (z - c) ^ 2 * Complex.exp (-(2 * lam) * (z - c) ^ 2)

/-! ## B. The explicit formula for autocorrelations with the zero side isolated. -/

/-- H_{g * g~}(rho) = h_g(gamma_rho) conj (h_g (conj gamma_rho)). -/
lemma weilKernel_autocorr {g : ℝ → ℂ} (hg : IsWeilTest g) (ρ : ℂ) :
    weilKernel (autocorr g) ρ = hermitianTransform g (gammaOf ρ) := by
  rw [RvMBridge4.weilKernel_eq_paperFT_gammaOf, RvMBridge5.autocorr_eq_weilTest,
    Zeta23.EF.paperFT_weilTest hg.1.continuous hg.1.continuous hg.2 hg.2]
  rfl

/-- The explicit formula for f = g * g~ as a HasSum with the Hermitian summand. -/
theorem hasSum_weilForm_autocorr {g : ℝ → ℂ} (hg : IsWeilTest g) :
    HasSum (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * hermitianTransform g (gammaOf ρ))
      (weilForm (autocorr g)) := by
  have h := (RvMBridge4.limit_explicit_formula _ (RvMBridge5.isWeilTest_autocorr hg)).2
  have hfun : (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * weilKernel (autocorr g) ρ)
      = fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * hermitianTransform g (gammaOf ρ) :=
    funext fun ρ => by rw [weilKernel_autocorr hg]
  unfold weilForm
  rw [← hfun]
  exact h

/-- (B): the Weil functional of an autocorrelation IS the zero side of its Hermitian transform. -/
theorem weilForm_autocorr_eq_zeroSide {g : ℝ → ℂ} (hg : IsWeilTest g) :
    weilForm (autocorr g) = zeroSide (hermitianTransform g) :=
  (hasSum_weilForm_autocorr hg).tsum_eq.symm

theorem summable_hermitian_zeroSide {g : ℝ → ℂ} (hg : IsWeilTest g) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * hermitianTransform g (gammaOf ρ)) :=
  (hasSum_weilForm_autocorr hg).summable

/-! ## C. Reflection symmetry rho -> 1 - conj rho on the whole plane, and realness. -/

lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  unfold reflect
  simp

/-- gamma_{1 - conj rho} = conj gamma_rho. -/
lemma gammaOf_reflect (ρ : ℂ) : gammaOf (reflect ρ) = conj (gammaOf ρ) := by
  unfold gammaOf reflect
  rw [Complex.div_I, Complex.div_I, map_neg, map_mul, map_sub, map_div₀, map_one, map_ofNat,
    Complex.conj_I]
  ring

/-- The registry multiplicity is reflection-invariant on ALL of C (both sides vanish off the
nontrivial zeros, which the reflection preserves). -/
lemma zeroMult_reflect (ρ : ℂ) :
    WeilExplicit.zeroMult (reflect ρ) = WeilExplicit.zeroMult ρ := by
  by_cases h : IsNontrivialZero ρ
  · rw [RvMBridge4.zeroMult_eq_mult (zeta_reflect_zero ρ h), RvMBridge4.zeroMult_eq_mult h]
    exact zeta_mult_reflect ρ h
  · have h' : ¬ IsNontrivialZero (reflect ρ) := fun h' =>
      h (reflect_reflect ρ ▸ zeta_reflect_zero _ h')
    rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h,
      RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h']

/-- The reflection as an involutive equivalence of C. -/
def reflectEquiv : ℂ ≃ ℂ where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect

/-- A transform with H (conj z) = conj (H z) has a REAL zero side: pair each rho with
1 - conj rho. -/
theorem zeroSide_conj {H : ℂ → ℂ} (hH : ∀ z, H (conj z) = conj (H z)) :
    conj (zeroSide H) = zeroSide H := by
  unfold zeroSide
  rw [← RCLike.star_def, tsum_star]
  have hterm : ∀ ρ : ℂ, star ((WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ))
      = (WeilExplicit.zeroMult (reflectEquiv ρ) : ℂ) * H (gammaOf (reflectEquiv ρ)) := by
    intro ρ
    show conj ((WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ))
      = (WeilExplicit.zeroMult (reflect ρ) : ℂ) * H (gammaOf (reflect ρ))
    rw [map_mul, Complex.conj_natCast, zeroMult_reflect, gammaOf_reflect, hH]
  simp_rw [hterm]
  exact reflectEquiv.tsum_eq (fun ρ => (WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ))

lemma hermitianTransform_conj (g : ℝ → ℂ) (z : ℂ) :
    hermitianTransform g (conj z) = conj (hermitianTransform g z) := by
  unfold hermitianTransform
  rw [map_mul, Complex.conj_conj, Complex.conj_conj, mul_comm]

lemma gaussTest_conj (c lam : ℝ) (z : ℂ) : gaussTest c lam (conj z) = conj (gaussTest c lam z) := by
  unfold gaussTest
  rw [map_mul, map_pow, map_sub, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, map_pow,
    map_sub, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_ofReal, map_ofNat]

/-- The Weil functional of an autocorrelation is real. -/
theorem weilForm_autocorr_real {g : ℝ → ℂ} (hg : IsWeilTest g) :
    (weilForm (autocorr g)).im = 0 := by
  rw [weilForm_autocorr_eq_zeroSide hg]
  have h := zeroSide_conj (hermitianTransform_conj g)
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-! ## D. The strip lemma: a zero in Mathlib's RH sense is a nontrivial zero of the strip. -/

/-- If zeta s = 0, s is not a trivial zero -2(n+1), and s != 1, then 0 < Re s < 1: Re s < 1 by
nonvanishing on Re >= 1; Re s > 0 by the functional equation zeta(1 - t) = 2 (2pi)^{-t} Gamma t
cos(pi t/2) zeta t with t = 1 - s (Re t >= 1), whose only vanishing factor cos(pi t/2) = 0 forces
t odd, i.e. s = -2k, excluded (k = 0 by zeta 0 = -1/2, k >= 1 as a trivial zero). -/
theorem strip_of_zero {s : ℂ} (hz : riemannZeta s = 0) (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1))
    (h1 : s ≠ 1) : 0 < s.re ∧ s.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hle : s.re ≤ 0 := not_lt.mp hlt
    have hne0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hz
      norm_num at hz
    set t : ℂ := 1 - s with ht_def
    have htre : 1 ≤ t.re := by
      simp only [ht_def, Complex.sub_re, Complex.one_re]
      linarith
    have htn : ∀ n : ℕ, t ≠ -n := by
      intro n h
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have ht1 : t ≠ 1 := by
      intro h
      apply hne0
      have := congrArg (fun z : ℂ => 1 - z) h
      simpa [ht_def] using this
    have hfe := riemannZeta_one_sub htn ht1
    have hst : 1 - t = s := by simp [ht_def]
    rw [hst, hz] at hfe
    have hζ : riemannZeta t ≠ 0 := riemannZeta_ne_zero_of_one_le_re htre
    have hΓ : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero htn
    have h2π : (2 * (Real.pi : ℂ)) ^ (-t) ≠ 0 := by
      intro h
      rw [Complex.cpow_eq_zero_iff] at h
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this h.1
    have hcos : Complex.cos (Real.pi * t / 2) ≠ 0 := by
      intro hc
      rw [Complex.cos_eq_zero_iff] at hc
      obtain ⟨k, hk⟩ := hc
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hkt : t = 2 * k + 1 := by
        have h' := hk
        field_simp at h'
        linear_combination h'
      have hsk : s = -2 * k := by
        rw [← hst, hkt]
        ring
      have hkre : (0 : ℝ) ≤ k := by
        have := congrArg Complex.re hsk
        simp only [Complex.mul_re, Complex.neg_re, Complex.re_ofNat,
          Complex.intCast_re, Complex.intCast_im] at this
        linarith
      rcases lt_or_eq_of_le hkre with hkpos | hk0
      · have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hkpos
        apply htriv
        refine ⟨(k - 1).toNat, ?_⟩
        have hcast : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
          have h' : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
          have h'' : (((k - 1).toNat : ℕ) : ℂ) = (((k - 1).toNat : ℤ) : ℂ) := by norm_cast
          rw [h'', h']
          push_cast
          ring
        rw [hcast, hsk]
        ring
      · apply hne0
        rw [hsk]
        have : (k : ℂ) = 0 := by exact_mod_cast hk0.symm
        rw [this]
        ring
    have hprod : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-t) * Complex.Gamma t
        * Complex.cos (Real.pi * t / 2) * riemannZeta t ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h2π) hΓ) hcos) hζ
    exact hprod hfe.symm
  · by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz

/-- Every nontrivial zero on the line gives Mathlib's RiemannHypothesis. -/
theorem rh_of_all_on_line (h : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re = 1 / 2) :
    RiemannHypothesis := by
  intro s hz htriv h1
  exact h s ⟨hz, strip_of_zero hz htriv h1⟩

/-! ## E. The two named analytic obligations. -/

/-- **Obligation O1 (Gaussian transfer).**  For every real centre c and every lam > 0, the
Gaussian-derivative Hermitian transform G_{c,lam}(z) = (z - c)^2 exp (-2 lam (z - c)^2) is a limit
of Hermitian transforms of smooth compactly supported tests FOR THE ZERO-SIDE FUNCTIONAL: there
are Weil tests g_n with Re zeroSide (hermitianTransform g_n) -> Re zeroSide G_{c,lam}.
Intended witness: g_n = (frequency-shifted derivative of a Gaussian) times a smooth cutoff
chi(u/n); the transforms converge pointwise on the strip |Im z| <= 1/2 with a truncation-uniform
bound C/(1 + (Re z)^2)^2 (two integrations by parts), and Sum_rho m(rho)/(1+|gamma_rho|^2) < infty
(Zeta23.WeilEF.zero_sum_inv_sq) gives dominated convergence of the zero sum.  Independent of RH. -/
def GaussianTransfer : Prop :=
  ∀ (c lam : ℝ), 0 < lam → ∃ g : ℕ → (ℝ → ℂ), (∀ n, IsWeilTest (g n)) ∧
    Tendsto (fun n => (zeroSide (hermitianTransform (g n))).re) atTop
      (𝓝 (zeroSide (gaussTest c lam)).re)

/-- **Obligation O2 (Gaussian dominance).**  If rho_0 is a nontrivial zero off the critical line,
then for some real centre c and some lam > 0 the Gaussian-weighted zero sum
Sum_rho m(rho) (gamma_rho - c)^2 exp (-2 lam (gamma_rho - c)^2) has NEGATIVE real part.
Intended proof: choose c within |1/2 - Re rho_0| of Im rho_0 and generic; the maximiser of
(Im gamma)^2 - (Re gamma - c)^2 over the zeros is attained, off the line, unique up to the pair
rho <-> 1 - conj rho, and its pair term is -2 m y^2 e^{2 lam M} (x = 0) or has a phase
2 arg w - 4 lam x y that can be set to pi along lam_k -> infty; all other zeros contribute
o(e^{2 lam M}) by the local zero count.  A statement about the zeros of zeta alone; it is
vacuous under RH and its intended proof never uses RH. -/
def GaussianDominance : Prop :=
  ∀ ρ₀ : ℂ, IsNontrivialZero ρ₀ → ρ₀.re ≠ 1 / 2 →
    ∃ (c lam : ℝ), 0 < lam ∧ (zeroSide (gaussTest c lam)).re < 0

/-! ## F. The delivered theorem: Weil positivity implies RH, modulo O1 and O2. -/

theorem weil_positivity_implies_rh_of (hO1 : GaussianTransfer) (hO2 : GaussianDominance)
    (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis := by
  apply rh_of_all_on_line
  intro ρ₀ hρ₀
  by_contra hre
  obtain ⟨c, lam, hlam, hneg⟩ := hO2 ρ₀ hρ₀ hre
  obtain ⟨g, hg, hlim⟩ := hO1 c lam hlam
  have hnn : ∀ n, 0 ≤ (zeroSide (hermitianTransform (g n))).re := fun n => by
    rw [← weilForm_autocorr_eq_zeroSide (hg n)]
    exact hpos _ (hg n)
  have hlim_nn : 0 ≤ (zeroSide (gaussTest c lam)).re := ge_of_tendsto' hlim hnn
  linarith

/-- Weil's criterion, both halves, modulo O1 and O2 (the forward half is E6Bridge5). -/
theorem rh_iff_weil_positivity_of (hO1 : GaussianTransfer) (hO2 : GaussianDominance) :
    RiemannHypothesis ↔ ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  ⟨RvMBridge5.rh_implies_weil_positivity, weil_positivity_implies_rh_of hO1 hO2⟩

/-! ## G. Structure toward O2: the pair term isolated, the Gaussian on the off-line axis, and
summability of the Gaussian zero sum from the local zero count. -/

/-- 1 - conj rho != rho exactly off the line. -/
lemma reflect_ne_self {ρ : ℂ} (h : ρ.re ≠ 1 / 2) : reflect ρ ≠ ρ := by
  intro heq
  apply h
  have := congrArg Complex.re heq
  simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
  linarith

/-- The pair {rho_0, 1 - conj rho_0} isolated: for a Hermitian-symmetric summable transform, the
zero side is 2 m(rho_0) Re H(gamma_0) plus the sum over all other rho.  (The other two members
of the classical quadruple, conj rho_0 and 1 - rho_0, sit at ordinate -Im rho_0 and stay in the
remainder.) -/
theorem zeroSide_pair_split {H : ℂ → ℂ} (hH : ∀ z, H (conj z) = conj (H z))
    (hsum : Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ)))
    {ρ₀ : ℂ} (h₀ : ρ₀.re ≠ 1 / 2) :
    zeroSide H = 2 * (WeilExplicit.zeroMult ρ₀ : ℂ) * ((H (gammaOf ρ₀)).re : ℂ)
      + ∑' ρ : {ρ : ℂ // ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀},
          (WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ) := by
  classical
  set f : ℂ → ℂ := fun ρ => (WeilExplicit.zeroMult ρ : ℂ) * H (gammaOf ρ) with hf
  have hne : ρ₀ ≠ reflect ρ₀ := (reflect_ne_self h₀).symm
  have hsplit := hsum.sum_add_tsum_compl (s := {ρ₀, reflect ρ₀})
  rw [Finset.sum_pair hne] at hsplit
  have hset : ((↑({ρ₀, reflect ρ₀} : Finset ℂ) : Set ℂ)ᶜ)
      = {ρ : ℂ | ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀} := by
    ext ρ
    simp [not_or]
  have hpair : f ρ₀ + f (reflect ρ₀)
      = 2 * (WeilExplicit.zeroMult ρ₀ : ℂ) * ((H (gammaOf ρ₀)).re : ℂ) := by
    simp only [hf]
    rw [zeroMult_reflect, gammaOf_reflect, hH, ← mul_add, Complex.add_conj]
    push_cast
    ring
  unfold zeroSide
  rw [← hsplit, hpair, tsum_congr_set_coe f hset]
  rfl

/-- On the vertical axis through the centre, G_{c,lam}(c + i y) = -y^2 exp (2 lam y^2): a
NEGATIVE real number, exponentially large in lam.  This is the mechanism: an off-line zero at
rho = beta + i c has gamma_rho = c + i (1/2 - beta) on this axis. -/
lemma gaussTest_axis (c lam y : ℝ) :
    gaussTest c lam ((c : ℂ) + (y : ℂ) * I)
      = ((-(y ^ 2) * Real.exp (2 * lam * y ^ 2) : ℝ) : ℂ) := by
  unfold gaussTest
  have h1 : ((c : ℂ) + (y : ℂ) * I - c) = (y : ℂ) * I := by ring
  have h2 : ((y : ℂ) * I) ^ 2 = -((y : ℂ) ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [h1, h2]
  have h3 : -(2 * (lam : ℂ)) * -((y : ℂ) ^ 2) = ((2 * lam * y ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h3, ← Complex.ofReal_exp]
  push_cast
  ring

lemma gaussTest_axis_re_neg (c lam y : ℝ) (hy : y ≠ 0) :
    (gaussTest c lam ((c : ℂ) + (y : ℂ) * I)).re < 0 := by
  rw [gaussTest_axis, Complex.ofReal_re]
  have : 0 < y ^ 2 := by positivity
  have := Real.exp_pos (2 * lam * y ^ 2)
  nlinarith

/-- The Gaussian bound on the strip: for |Im z| <= 1/2 and lam > 0,
‖G_{c,lam}(z)‖ (1 + |z|^2) <= C(c, lam), C = e^{lam/2} (2 c^2 + 13/4) / min(1, lam)^2. -/
lemma norm_gaussTest_mul_le (c lam : ℝ) (hlam : 0 < lam) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖gaussTest c lam z‖ * (1 + Complex.normSq z)
      ≤ Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 lam) ^ 2 := by
  set x : ℝ := z.re - c with hx
  set y : ℝ := z.im with hy
  have hre : (-(2 * (lam : ℂ)) * (z - c) ^ 2).re = -(2 * lam) * (x ^ 2 - y ^ 2) := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, pow_two, Complex.sub_re, Complex.sub_im, hx, hy]
    ring
  have hsq : ‖z - c‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hx, hy]
    ring
  have hnorm : ‖gaussTest c lam z‖ = (x ^ 2 + y ^ 2) * Real.exp (-(2 * lam) * (x ^ 2 - y ^ 2)) := by
    unfold gaussTest
    rw [norm_mul, Complex.norm_pow, Complex.norm_exp, hsq, hre]
  have hnormSq : Complex.normSq z = (x + c) ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply, hx, hy]
    ring
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hz
    nlinarith [this.1, this.2]
  have hmin : 0 < min 1 lam := lt_min one_pos hlam
  -- exp (-2 lam (x^2 - y^2)) <= exp (lam/2) / (1 + lam x^2)^2 <= exp (lam/2) / (min 1 lam)^2 / (1 + x^2)^2
  have hexp1 : Real.exp (-(2 * lam) * (x ^ 2 - y ^ 2))
      = Real.exp (2 * lam * y ^ 2) * Real.exp (-(2 * lam * x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp2 : Real.exp (2 * lam * y ^ 2) ≤ Real.exp (lam / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp3 : (min 1 lam) ^ 2 * (1 + x ^ 2) ^ 2 * Real.exp (-(2 * lam * x ^ 2)) ≤ 1 := by
    have h1 : min 1 lam * (1 + x ^ 2) ≤ 1 + lam * x ^ 2 := by
      rcases le_total 1 lam with h | h
      · rw [min_eq_left h]
        nlinarith [sq_nonneg x]
      · rw [min_eq_right h]
        nlinarith [sq_nonneg x]
    have h2 : 1 + lam * x ^ 2 ≤ Real.exp (lam * x ^ 2) := by
      have := Real.add_one_le_exp (lam * x ^ 2)
      linarith
    have h3 : (min 1 lam * (1 + x ^ 2)) ^ 2 ≤ Real.exp (lam * x ^ 2) ^ 2 := by
      have h0 : 0 ≤ min 1 lam * (1 + x ^ 2) := by positivity
      exact pow_le_pow_left₀ h0 (h1.trans h2) 2
    have h4 : Real.exp (lam * x ^ 2) ^ 2 = Real.exp (2 * lam * x ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h5 : Real.exp (-(2 * lam * x ^ 2)) = (Real.exp (2 * lam * x ^ 2))⁻¹ := by
      rw [Real.exp_neg]
    rw [h5, ← mul_pow]
    have hpos : 0 < Real.exp (2 * lam * x ^ 2) := Real.exp_pos _
    rw [← div_eq_mul_inv, div_le_one hpos, ← h4]
    exact h3
  -- assemble
  have hA : (x ^ 2 + y ^ 2) * (1 + ((x + c) ^ 2 + y ^ 2)) ≤ (2 * c ^ 2 + 13 / 4) * (1 + x ^ 2) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg c, sq_nonneg (x + c), sq_nonneg (x - c), sq_nonneg y,
      mul_nonneg (sq_nonneg x) (sq_nonneg c), mul_nonneg (sq_nonneg x) (sq_nonneg x)]
  rw [hnorm, hnormSq, hexp1]
  have hE : 0 < Real.exp (-(2 * lam * x ^ 2)) := Real.exp_pos _
  have hE2 : 0 ≤ Real.exp (2 * lam * y ^ 2) := (Real.exp_pos _).le
  have hK : 0 ≤ 2 * c ^ 2 + 13 / 4 := by positivity
  rw [le_div_iff₀ (by positivity)]
  calc (x ^ 2 + y ^ 2) * (Real.exp (2 * lam * y ^ 2) * Real.exp (-(2 * lam * x ^ 2)))
        * (1 + ((x + c) ^ 2 + y ^ 2)) * (min 1 lam) ^ 2
      = Real.exp (2 * lam * y ^ 2) * ((x ^ 2 + y ^ 2) * (1 + ((x + c) ^ 2 + y ^ 2)))
        * ((min 1 lam) ^ 2 * Real.exp (-(2 * lam * x ^ 2))) := by ring
    _ ≤ Real.exp (lam / 2) * ((2 * c ^ 2 + 13 / 4) * (1 + x ^ 2) ^ 2)
        * ((min 1 lam) ^ 2 * Real.exp (-(2 * lam * x ^ 2))) := by
      gcongr
    _ = Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4)
        * ((min 1 lam) ^ 2 * (1 + x ^ 2) ^ 2 * Real.exp (-(2 * lam * x ^ 2))) := by ring
    _ ≤ Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) * 1 := by
      gcongr
    _ = Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) := by ring

/-! The weighted local-count majorant Sum_rho m(rho) C/(1 + |gamma_rho|^2) over ALL rho : C is the
prelude's RvMBridgeGauss.summable_mult_div_one_add_normSq (formerly here). -/

/-- The Gaussian zero sum converges absolutely for every centre c and every lam > 0
(so the tsum in GaussianDominance is a genuine sum, not the junk value 0). -/
theorem summable_gauss_zeroSide (c lam : ℝ) (hlam : 0 < lam) :
    Summable (fun ρ : ℂ => (WeilExplicit.zeroMult ρ : ℂ) * gaussTest c lam (gammaOf ρ)) := by
  set C : ℝ := Real.exp (lam / 2) * (2 * c ^ 2 + 13 / 4) / (min 1 lam) ^ 2 with hC
  refine Summable.of_norm_bounded (RvMBridgeGauss.summable_mult_div_one_add_normSq C) fun ρ => ?_
  rw [norm_mul, Complex.norm_natCast]
  by_cases h : IsNontrivialZero ρ
  · have hz : |(gammaOf ρ).im| ≤ 1 / 2 := (Zeta23.WeilEF.abs_gammaOf_im_lt h.2).le
    have hb := norm_gaussTest_mul_le c lam hlam hz
    have hpos : 0 < 1 + Complex.normSq (gammaOf ρ) := by
      have := Complex.normSq_nonneg (gammaOf ρ)
      linarith
    have : ‖gaussTest c lam (gammaOf ρ)‖ ≤ C / (1 + Complex.normSq (gammaOf ρ)) := by
      rw [le_div_iff₀ hpos]
      exact hb
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  · rw [RvMBridge4.zeroMult_eq_zero_of_not_nontrivial h]
    simp

/-- The Gaussian zero side is real (G_{c,lam} is Hermitian-symmetric). -/
theorem gauss_zeroSide_real (c lam : ℝ) : (zeroSide (gaussTest c lam)).im = 0 := by
  have h := zeroSide_conj (gaussTest_conj c lam)
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

/-- The pair term of an off-line zero rho_0 = beta_0 + i c with centre c = Im rho_0 in the
Gaussian zero sum is  -2 m(rho_0) delta_0^2 exp (2 lam delta_0^2)  with delta_0 = 1/2 - beta_0:
strictly negative and exponentially large in lam.  What O2 still needs is that the remainder
(all other zeros) is o(exp (2 lam delta_0^2)) along some lam -> infinity, which is false in
general for THIS centre (a nearby zero with larger |delta| wins) and is why the intended proof
moves the centre to a generic point and takes the maximiser (see the file header / memo). -/
theorem gauss_zeroSide_pair_split (lam : ℝ) (hlam : 0 < lam) {ρ₀ : ℂ} (h₀ : ρ₀.re ≠ 1 / 2) :
    zeroSide (gaussTest ρ₀.im lam)
      = ((-(2 * (WeilExplicit.zeroMult ρ₀ : ℝ) * (1 / 2 - ρ₀.re) ^ 2
            * Real.exp (2 * lam * (1 / 2 - ρ₀.re) ^ 2)) : ℝ) : ℂ)
        + ∑' ρ : {ρ : ℂ // ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀},
            (WeilExplicit.zeroMult ρ : ℂ) * gaussTest ρ₀.im lam (gammaOf ρ) := by
  rw [zeroSide_pair_split (gaussTest_conj _ _) (summable_gauss_zeroSide _ lam hlam) h₀]
  congr 1
  have hγ : gammaOf ρ₀ = ((ρ₀.im : ℝ) : ℂ) + ((1 / 2 - ρ₀.re : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [Zeta23.WeilEF.gammaOf_re]
      simp
    · rw [Zeta23.WeilEF.gammaOf_im]
      simp
  rw [hγ, gaussTest_axis, Complex.ofReal_re]
  push_cast
  ring

/-! ## H. O1 reduced to pure Fourier analysis: GaussianApprox (no zeros mentioned) implies
GaussianTransfer by Tannery's theorem against the local-count majorant. -/

/-- **Obligation O1' (Gaussian approximation on the strip), a statement about test functions
only.**  For every real centre c and lam > 0 there are Weil tests g_n whose Hermitian transforms
converge to G_{c,lam} pointwise on the strip |Im z| <= 1/2 with a truncation-uniform bound
C/(1 + |z|^2) there.  Intended witness: g_n(u) = e^{-icu} phi(u) chi(u/n) with phi the inverse
transform of (z - c) e^{-lam (z - c)^2} (a derivative of a Gaussian, Mathlib
integral_cexp_quadratic) and chi a smooth cutoff (ContDiffBump); the C/(1+x^2) bound is two
integrations by parts with derivatives of g_n bounded uniformly in n against e^{|u|/2}. -/
def GaussianApprox : Prop :=
  ∀ (c lam : ℝ), 0 < lam → ∃ g : ℕ → (ℝ → ℂ), (∀ n, IsWeilTest (g n)) ∧
    (∃ C : ℝ, ∀ n (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖hermitianTransform (g n) z‖ ≤ C / (1 + Complex.normSq z)) ∧
    (∀ z : ℂ, |z.im| ≤ 1 / 2 →
      Tendsto (fun n => hermitianTransform (g n) z) atTop (𝓝 (gaussTest c lam z)))

/-- Tannery: the strip approximation passes to the zero side (dominating function
m(rho) C/(1 + |gamma_rho|^2), summable by the local zero count). -/
theorem gaussianTransfer_of_approx (hA : GaussianApprox) : GaussianTransfer := by
  intro c lam hlam
  obtain ⟨g, hg, ⟨C, hC⟩, hlim⟩ := hA c lam hlam
  refine ⟨g, hg, ?_⟩
  have hT : Tendsto (fun n => zeroSide (hermitianTransform (g n))) atTop
      (𝓝 (zeroSide (gaussTest c lam))) := by
    unfold zeroSide
    exact RvMBridgeGauss.tendsto_tsum_zeroMult_of_strip_bound hC hlim
  exact (Complex.continuous_re.tendsto _).comp hT

/-- The delivered theorem with O1 replaced by the zero-free O1'. -/
theorem weil_positivity_implies_rh_of' (hA : GaussianApprox) (hO2 : GaussianDominance)
    (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g →
      0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis :=
  weil_positivity_implies_rh_of (gaussianTransfer_of_approx hA) hO2 hpos

end RvMBridge6
