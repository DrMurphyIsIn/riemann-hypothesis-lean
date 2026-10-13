/-
  E6Bridge3 -- routes-roadmap milestone E7 = A3 = B5 = D6 (2026-09-17): the RH registry node
  RH_corridor_bound (the classical GOOD-ORDINATE lemma: for every T >= 2 some height
  T' in [T, T+1] has a zero-free horizontal segment -1 <= sigma <= 2 on which
  |zeta'/zeta| <= C log^2 T; Davenport ch. 15-17, Titchmarsh 9.6) discharged from Anthropic's
  zeta-23-lean (Alpoege--Furman, arXiv:2608.13637; Apache-2.0; pinned in lakefile.toml).

  WHAT IS CONSUMED (all unconditional in the pinned Zeta23, #print axioms =
  [propext, Classical.choice, Quot.sound], see AxiomGuardRvMBridge.lean):
    Zeta23.WeilEF.zeta_logDeriv_partial_fraction  (Landau partial fraction about 2+it, |t| >= 6)
    Zeta23.RvM.zeta_local_zero_count              (N(t, t+1] <= A0 log(|t|+3))
    Zeta23.WeilEF.exists_far_point                (pigeonhole gap in [a, a+1], a REAL)
    Zeta23.WeilEF.logDeriv_completedZeta          (Lambda'/Lambda = Gamma_R'/Gamma_R + zeta'/zeta)
    Zeta23.WeilEF.logDeriv_completedZeta_one_sub  (Lambda'/Lambda(1-s) = -Lambda'/Lambda(s))
    Zeta23.RvM.logDeriv_Gammaℝ, Zeta23.StirlingVert.digamma_stirling (Gamma_R'/Gamma_R = O(log))
    Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact, Zeta23.Ncount_add, Zeta23.zerosIn_finite.

  WHY THIS IS NOT A COROLLARY OF THE STATED UPSTREAM THEOREMS: zeta-23-lean's own good-height
  lemma (Zeta23.WeilEF.good_heights_at) is stated at INTEGER heights j >= 7 with the window
  [j, j+1] and covers only 1/2 <= Re s <= 2. The node needs a real T (window [T, T+1]) and the
  full segment -1 <= sigma <= 2. So: (i) the good-height selection is re-run here at a real
  height (the upstream gap lemma already takes a real endpoint); (ii) the left half
  -1 <= sigma < 1/2 is reached through the functional equation Lambda(s) = Lambda(1-s) --
  zeta'/zeta(s) = -zeta'/zeta(1-s) - Gamma_R'/Gamma_R(1-s) - Gamma_R'/Gamma_R(s) -- with the
  Gamma_R log-derivative bounded by O(log |t|) via Stirling and the shift
  Gamma_R'/Gamma_R(u) = Gamma_R'/Gamma_R(u+2) - 1/u; (iii) the range 2 <= T < 7 is absorbed by
  compactness: on the closed set of points of [-1,2] x [2,8] whose ordinate is delta-far from
  the finitely many zero ordinates there, zeta'/zeta is continuous, hence bounded.

  The theorem line is the node statement of
  telperion/missions/rh/lean/Statements/RH_corridor_bound.lean verbatim (name and
  binder-free form), so the registry's normalized-containment grant gate matches
  (../generate.py --check).

  No RH progress is claimed: this is the classical good-ordinate lemma, machine-checked.
  conjecture1_proved = False.
-/
import Zeta23.WeilEF.GoodHeights
import Zeta23.WeilEF.XiLogDeriv
import Zeta23.RvM.NcountWindow
import Zeta23.RvM.GammaSide
import Zeta23.GammaFacts.StirlingVert

open Zeta23 Complex Set Filter Topology

noncomputable section

namespace RvMBridge3

/-! ## A. The Gamma_R log-derivative off the real axis.

Re-proved here (the upstream versions live in `Zeta23.XiPrime.*`, which is a separate challenge
tree not built on this island). -/

lemma ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := by
  intro h; apply hs; rw [h]; simp

lemma ne_one_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 1 := by
  intro h; apply hs; rw [h]; simp

lemma half_ne_neg_nat {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) : s / 2 ≠ -(m : ℂ) := by
  intro h; apply hs
  have : (s / 2).im = 0 := by rw [h]; simp
  simpa using this

lemma Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n h; apply hs; rw [h]; simp

/-- Gamma_R is complex-differentiable at every non-real point. -/
lemma differentiableAt_Gammaℝ_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    refine DifferentiableAt.const_cpow ?_ (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    exact (differentiableAt_id.neg).div_const 2
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma _ (half_ne_neg_nat hs)).comp s (differentiableAt_id.div_const 2)
  have : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := funext Gammaℝ_def
  rw [this]; exact h1.mul h2

lemma isOpen_im_ne_zero : IsOpen {s : ℂ | s.im ≠ 0} :=
  isOpen_ne_fun Complex.continuous_im continuous_const

/-- The shift `Gamma_R'/Gamma_R(u) = Gamma_R'/Gamma_R(u+2) - 1/u` off the real axis
(from `Gamma_R(u+2) = Gamma_R(u) u / (2 pi)`). -/
theorem logDeriv_Gammaℝ_shift {u : ℂ} (hu : u.im ≠ 0) :
    logDeriv Gammaℝ u = logDeriv Gammaℝ (u + 2) - 1 / u := by
  have hu0 := ne_zero_of_im_ne_zero hu
  have hu2 : (u + 2).im ≠ 0 := by simpa using hu
  have hev : (fun z => Gammaℝ (z + 2)) =ᶠ[𝓝 u] fun z => Gammaℝ z * (z / 2 / (Real.pi : ℂ)) := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hu] with z hz
    rw [Gammaℝ_add_two (ne_zero_of_im_ne_zero hz)]; ring
  have hd2 : DifferentiableAt ℂ Gammaℝ (u + 2) := differentiableAt_Gammaℝ_of_im_ne_zero hu2
  have hdu : DifferentiableAt ℂ Gammaℝ u := differentiableAt_Gammaℝ_of_im_ne_zero hu
  have hL : logDeriv (fun z => Gammaℝ (z + 2)) u = logDeriv Gammaℝ (u + 2) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_add_const]
  have hlin : DifferentiableAt ℂ (fun z : ℂ => z / 2 / (Real.pi : ℂ)) u := by fun_prop
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hR : logDeriv (fun z => Gammaℝ z * (z / 2 / (Real.pi : ℂ))) u
      = logDeriv Gammaℝ u + 1 / u := by
    rw [logDeriv_mul u (Gammaℝ_ne_zero_of_im_ne_zero hu) (by simp [hu0, hπ]) hdu hlin]
    congr 1
    rw [logDeriv_apply]
    have : deriv (fun z : ℂ => z / 2 / (Real.pi : ℂ)) u = 1 / 2 / (Real.pi : ℂ) := by
      rw [deriv_div_const, deriv_div_const, deriv_id'']
    rw [this]; field_simp
  have heq : logDeriv (fun z => Gammaℝ (z + 2)) u
      = logDeriv (fun z => Gammaℝ z * (z / 2 / (Real.pi : ℂ))) u := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [← hL, heq, hR]; ring

/-- `‖Gamma_R'/Gamma_R(s)‖ ≤ log(|Im s|+3) + 5` for `0 < Re s ≤ 4`, `|Im s| ≥ 2` (Stirling for psi). -/
lemma norm_logDeriv_Gammaℝ_le_log {s : ℂ} (hre : 0 < s.re) (hre' : s.re ≤ 4) (him : 2 ≤ |s.im|) :
    ‖logDeriv Gammaℝ s‖ ≤ Real.log (|s.im| + 3) + 5 := by
  rw [Zeta23.RvM.logDeriv_Gammaℝ hre]
  set w : ℂ := s / 2 with hw
  have hwre : 0 < w.re := by simp [hw]; linarith
  have hwim : w.im = s.im / 2 := by simp [hw]
  have hw' : 1 ≤ |w.im| := by rw [hwim, abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.digamma_stirling hwre (by linarith)
  have him2 : 1 ≤ w.im ^ 2 := by have := sq_abs w.im; nlinarith [abs_nonneg w.im]
  have h3 : 3 / w.im ^ 2 ≤ 3 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have hw1 : 1 ≤ ‖w‖ := le_trans hw' (Complex.abs_im_le_norm w)
  have hwle : ‖w‖ ≤ |s.im| + 3 := by
    have : ‖w‖ = ‖s‖ / 2 := by rw [hw, norm_div]; norm_num
    rw [this]
    have := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hre] at this
    linarith
  have hlog : ‖Complex.log w‖ ≤ Real.log (|s.im| + 3) + Real.pi := by
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖w‖| + |Complex.arg w| := by rw [Complex.log_re, Complex.log_im]
      _ ≤ Real.log (|s.im| + 3) + Real.pi := by
          apply add_le_add _ (Complex.abs_arg_le_pi w)
          rw [abs_of_nonneg (Real.log_nonneg hw1)]
          exact Real.log_le_log (by linarith) hwle
  have hinv : ‖(1 / 2 : ℂ) / w‖ ≤ 1 / 2 := by
    rw [norm_div]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, div_le_iff₀ (by linarith)]
    nlinarith
  have hψ : ‖Complex.digamma w‖ ≤ Real.log (|s.im| + 3) + Real.pi + 7 / 2 := by
    calc ‖Complex.digamma w‖
        = ‖(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w) + Complex.log w
            - (1 / 2 : ℂ) / w‖ := by ring_nf
      _ ≤ ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ + ‖Complex.log w‖
            + ‖(1 / 2 : ℂ) / w‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 3 + (Real.log (|s.im| + 3) + Real.pi) + 1 / 2 := by linarith
      _ = Real.log (|s.im| + 3) + Real.pi + 7 / 2 := by ring
  have hlogpi : ‖-(Real.log Real.pi : ℂ) / 2‖ ≤ 1 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have : Real.log Real.pi ≤ 2 := by
      have h4 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
      have h4' : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      linarith [Real.log_two_lt_d9]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]; linarith
  calc ‖-(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma w‖
      ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ + ‖(1 / 2 : ℂ) * Complex.digamma w‖ := norm_add_le _ _
    _ ≤ 1 + 1 / 2 * (Real.log (|s.im| + 3) + Real.pi + 7 / 2) := by
        gcongr
        rw [norm_mul]
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [this]
        gcongr
    _ ≤ Real.log (|s.im| + 3) + 5 := by
        have := Real.log_nonneg (by linarith [abs_nonneg s.im] : (1:ℝ) ≤ |s.im| + 3)
        nlinarith [Real.pi_lt_four]

/-- `‖Gamma_R'/Gamma_R(s)‖ ≤ log(|Im s|+3) + 6` on `-1 ≤ Re s ≤ 2`, `|Im s| ≥ 2` (one shift). -/
lemma norm_logDeriv_Gammaℝ_le_log_strip {s : ℂ} (hre : -1 ≤ s.re) (hre' : s.re ≤ 2)
    (him : 2 ≤ |s.im|) : ‖logDeriv Gammaℝ s‖ ≤ Real.log (|s.im| + 3) + 6 := by
  have hu : s.im ≠ 0 := by intro h; rw [h] at him; norm_num at him
  rw [logDeriv_Gammaℝ_shift hu]
  have h2 := norm_logDeriv_Gammaℝ_le_log (s := s + 2) (by simp; linarith) (by simp; linarith)
    (by simpa using him)
  have him' : (s + 2).im = s.im := by simp
  rw [him'] at h2
  have h3 : ‖(1 : ℂ) / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have := Complex.abs_im_le_norm s
    rw [div_le_one (by linarith)]
    linarith
  calc ‖logDeriv Gammaℝ (s + 2) - 1 / s‖
      ≤ ‖logDeriv Gammaℝ (s + 2)‖ + ‖(1 : ℂ) / s‖ := norm_sub_le _ _
    _ ≤ Real.log (|s.im| + 3) + 5 + 1 := add_le_add h2 h3
    _ = Real.log (|s.im| + 3) + 6 := by ring

/-! ## B. Reflection through the completed zeta function `Lambda(s) = Lambda(1-s)`. -/

/-- Off the real axis, `zeta(1-s) ≠ 0` forces `zeta(s) ≠ 0` (`Lambda(s) = Lambda(1-s)`,
`Gamma_R ≠ 0` off the real axis). -/
lemma zeta_ne_zero_of_reflect {s : ℂ} (hs : s.im ≠ 0) (hζ : riemannZeta (1 - s) ≠ 0) :
    riemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := ne_zero_of_im_ne_zero hs
  have h1s0 : 1 - s ≠ 0 := by
    intro h; apply hs
    have := congrArg Complex.im h; simpa using this
  intro h
  apply hζ
  rw [riemannZeta_def_of_ne_zero h1s0, completedRiemannZeta_one_sub]
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at h
  rcases h with h | h
  · rw [h, zero_div]
  · exact absurd h (Gammaℝ_ne_zero_of_im_ne_zero hs)

/-- The log-derivative functional equation:
`zeta'/zeta(s) = -zeta'/zeta(1-s) - Gamma_R'/Gamma_R(1-s) - Gamma_R'/Gamma_R(s)`
for `Im s ≠ 0`, `Re s < 1`, `zeta(1-s) ≠ 0`. -/
theorem logDeriv_zeta_reflect {s : ℂ} (hs : s.im ≠ 0) (hre : s.re < 1)
    (hζ : riemannZeta (1 - s) ≠ 0) :
    logDeriv riemannZeta s
      = -logDeriv riemannZeta (1 - s) - logDeriv Gammaℝ (1 - s) - logDeriv Gammaℝ s := by
  have hs0 : s ≠ 0 := ne_zero_of_im_ne_zero hs
  have hs1 : s ≠ 1 := ne_one_of_im_ne_zero hs
  have h1s0 : 1 - s ≠ 0 := by
    intro h; apply hs
    have := congrArg Complex.im h; simpa using this
  have h1s1 : 1 - s ≠ 1 := by
    intro h; apply hs0; linear_combination -h
  have h1sre : 0 < (1 - s).re := by simp; linarith
  -- zeta = Lambda / Gamma_R near s
  have hev : riemannZeta =ᶠ[𝓝 s] fun u => completedRiemannZeta u / Gammaℝ u := by
    filter_upwards [isOpen_ne.mem_nhds hs0] with u hu
    exact riemannZeta_def_of_ne_zero hu
  have hΛ : completedRiemannZeta s ≠ 0 := by
    rw [← completedRiemannZeta_one_sub]
    intro h; apply hζ
    rw [riemannZeta_def_of_ne_zero h1s0, h, zero_div]
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero hs
  have e1 : logDeriv riemannZeta s = logDeriv (fun u => completedRiemannZeta u / Gammaℝ u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have e2 : logDeriv (fun u => completedRiemannZeta u / Gammaℝ u) s
      = logDeriv completedRiemannZeta s - logDeriv Gammaℝ s :=
    logDeriv_div s hΛ hΓ (differentiableAt_completedZeta hs0 hs1)
      (differentiableAt_Gammaℝ_of_im_ne_zero hs)
  have e3 := Zeta23.WeilEF.logDeriv_completedZeta_one_sub s hs0 hs1
  have e4 := Zeta23.WeilEF.logDeriv_completedZeta (1 - s) h1s1 hζ h1sre
  rw [e1, e2]
  linear_combination e3 - e4

/-! ## C. Good heights at a REAL height `T ≥ 7` (window `[T, T+1]`, right half `1/2 ≤ Re s ≤ 2`).

Transcribed from `Zeta23.WeilEF.good_heights_at` (integer `j ≥ 7`), with the count of zero
ordinates near `±T` taken from six unit windows of the local count. -/

/-- `Ncount a a = 0` (empty window). -/
lemma Ncount_self (a : ℝ) : Ncount a a = 0 := by
  unfold Ncount
  have : zerosIn a a = ∅ := by
    ext ρ
    simp only [zerosIn, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, h1, h2⟩
    linarith
  simp [this]

/-- Unit windows: `N(a, a+k] = Σ_{i<k} N(a+i, a+i+1]`. -/
lemma Ncount_unit_windows (a : ℝ) (k : ℕ) :
    Ncount a (a + k) = ∑ i ∈ Finset.range k, Ncount (a + i) (a + i + 1) := by
  induction k with
  | zero => simp [Ncount_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : a + ((k + 1 : ℕ) : ℝ) = a + k + 1 := by push_cast; ring
    rw [e, Zeta23.Ncount_add (a := a) (b := a + k) (c := a + k + 1)
      (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith)]

/-- Six unit windows of the local count: `N(a, a+6] ≤ 6 A₀ log(|a| + 9)`. -/
lemma Ncount_six_windows {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) :
    (Ncount a (a + 6) : ℝ) ≤ 6 * (A₀ * Real.log (|a| + 9)) := by
  have h := Ncount_unit_windows a 6
  push_cast at h
  rw [h, Nat.cast_sum]
  have hterm : ∀ i ∈ Finset.range 6,
      (Ncount (a + i) (a + i + 1) : ℝ) ≤ A₀ * Real.log (|a| + 9) := by
    intro i hi
    have hi6 : (i : ℝ) < 6 := by exact_mod_cast Finset.mem_range.mp hi
    refine (hloc (a + i)).trans (mul_le_mul_of_nonneg_left ?_ hA₀)
    apply Real.log_le_log (by positivity)
    have h1 : |a + i| ≤ |a| + i := by
      calc |a + i| ≤ |a| + |(i : ℝ)| := abs_add_le _ _
        _ = |a| + i := by rw [Nat.abs_cast]
    linarith
  calc ∑ i ∈ Finset.range 6, (Ncount (a + i) (a + i + 1) : ℝ)
      ≤ ∑ i ∈ Finset.range 6, A₀ * Real.log (|a| + 9) := Finset.sum_le_sum hterm
    _ = 6 * (A₀ * Real.log (|a| + 9)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- The cardinality of a finite set of nontrivial zeros inside `(a, a+6]` is at most
`N(a, a+6]`. -/
lemma card_zerosIn_le (a b : ℝ) :
    (((zerosIn_finite a b).toFinset).card : ℝ) ≤ (Ncount a b : ℝ) := by
  have h1 : (zerosIn_finite a b).toFinset.card = (zerosIn a b).ncard :=
    (Set.ncard_eq_toFinset_card _ (zerosIn_finite a b)).symm
  have hsub : zerosIn a b ⊆ zetaZeroConfig.window a b := by
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨hρ, h1, h2⟩
  have h2 : (zerosIn a b).ncard ≤ ∑ᶠ ρ ∈ zerosIn a b, zetaZeroConfig.mult ρ :=
    zetaZeroConfig.ncard_le_finsum_mult a b hsub
  have h3 : ∑ᶠ ρ ∈ zerosIn a b, zetaZeroConfig.mult ρ = Ncount a b := rfl
  rw [h1]
  exact_mod_cast h2.trans_eq h3

set_option maxHeartbeats 800000 in
/-- **Good heights at a real height**: for every real `T ≥ 7` there is `R ∈ [T, T+1]` such that on
both horizontal segments `Im s = ±R`, `1/2 ≤ Re s ≤ 2`, `ζ(s) ≠ 0` and
`‖ζ'/ζ(s)‖ ≤ C log²(T+3)`. -/
theorem good_height_real : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 7 ≤ T →
    ∃ R : ℝ, T ≤ R ∧ R ≤ T + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C * (Real.log (T + 3)) ^ 2 := by
  classical
  obtain ⟨C, hC, hpf⟩ := Zeta23.WeilEF.zeta_logDeriv_partial_fraction
  obtain ⟨A₀, hA₀1, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  have hA₀ : 0 ≤ A₀ := by linarith
  refine ⟨2 * C * (48 * A₀ + 3), by positivity, fun T hT => ?_⟩
  set Lg : ℝ := Real.log (T + 3) with hLg
  have hLg1 : 1 ≤ Lg := by
    rw [hLg, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlog2 : Real.log 2 ≤ Lg := by
    rw [hLg]; exact Real.log_le_log (by norm_num) (by linarith)
  -- the two finite families of zeros near height ±T
  set Wp : Set ℂ := zerosIn (T - 3) (T - 3 + 6) with hWp
  set Wm : Set ℂ := zerosIn (-T - 4) (-T - 4 + 6) with hWm
  have hWpfin : Wp.Finite := zerosIn_finite _ _
  have hWmfin : Wm.Finite := zerosIn_finite _ _
  set S : Finset ℝ := hWpfin.toFinset.image (fun ρ : ℂ => ρ.im)
    ∪ hWmfin.toFinset.image (fun ρ : ℂ => -ρ.im) with hS
  -- count: |S| ≤ 24 A₀ Lg
  have hcountp : (hWpfin.toFinset.card : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    refine (card_zerosIn_le _ _).trans ((Ncount_six_windows hA₀ hloc (T - 3)).trans ?_)
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA₀) (by norm_num)
    rw [abs_of_nonneg (by linarith)]
    calc Real.log (T - 3 + 9) ≤ Real.log (2 * (T + 3)) :=
          Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 * Lg := by linarith
  have hcountm : (hWmfin.toFinset.card : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    refine (card_zerosIn_le _ _).trans ((Ncount_six_windows hA₀ hloc (-T - 4)).trans ?_)
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hA₀) (by norm_num)
    rw [abs_of_nonpos (by linarith)]
    calc Real.log (-(-T - 4) + 9) ≤ Real.log ((T + 3) ^ 2) := by
          apply Real.log_le_log (by linarith); nlinarith
      _ = 2 * Lg := by rw [Real.log_pow]; push_cast; ring
  have hcard : (S.card : ℝ) ≤ 24 * A₀ * Lg := by
    have h1 : S.card ≤ hWpfin.toFinset.card + hWmfin.toFinset.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have h1' : (S.card : ℝ) ≤ hWpfin.toFinset.card + hWmfin.toFinset.card := by exact_mod_cast h1
    linarith
  -- the good height
  obtain ⟨R, hR1, hR2, hfar⟩ := Zeta23.WeilEF.exists_far_point S T
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδinv : 1 / δ = 2 * ((S.card : ℝ) + 1) := by rw [hδ, one_div_one_div]
  refine ⟨R, hR1, hR2, fun s hs hσ1 hσ2 => ?_⟩
  have hR6 : (6 : ℝ) ≤ |R| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hR6' : (6 : ℝ) ≤ |-R| := by rwa [abs_neg]
  have hlogR : Real.log (|R| + 3) ≤ 2 * Lg := by
    rw [abs_of_nonneg (by linarith)]
    calc Real.log (R + 3) ≤ Real.log (2 * (T + 3)) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 * Lg := by linarith
  -- s in the conclusion ball of the partial fraction at t = s.im
  have hsball : s ∈ Metric.closedBall (2 + s.im * I) (3 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  -- every zero in the pf ball at height s.im = ±R has its (signed) ordinate in S
  have hordS : ∀ ρ : ℂ, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50)) →
      riemannZeta ρ = 0 → δ ≤ ‖s - ρ‖ := by
    intro ρ hρ hz
    have hnt := Zeta23.WeilEF.isNontrivialZero_of_mem_closedBall (by norm_num) hρ hz
    have him := Zeta23.WeilEF.im_mem_of_mem_closedBall hρ
    rw [abs_le] at him
    refine le_trans ?_ (Zeta23.WeilEF.abs_im_sub_le_norm_sub s ρ)
    rcases hs with hsR | hsR
    · have hmem : ρ ∈ hWpfin.toFinset := by
        rw [Set.Finite.mem_toFinset, hWp]
        refine ⟨hnt, ?_, ?_⟩ <;> rw [hsR] at him <;> linarith [him.1, him.2]
      have : ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; left
        exact Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩
      have := hfar _ this
      rwa [hsR]
    · have hmem : ρ ∈ hWmfin.toFinset := by
        rw [Set.Finite.mem_toFinset, hWm]
        refine ⟨hnt, ?_, ?_⟩ <;> rw [hsR] at him <;> linarith [him.1, him.2]
      have : -ρ.im ∈ S := by
        rw [hS, Finset.mem_union]; right
        exact Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩
      have := hfar _ this
      rw [hsR, show |(-R) - ρ.im| = |R - (-ρ.im)| by rw [← abs_neg]; ring_nf]
      exact this
  -- ζ(s) ≠ 0: s itself would be a zero in the ball at distance 0
  have hζ : riemannZeta s ≠ 0 := by
    intro hz
    have h0 := hordS s (Metric.closedBall_subset_closedBall (by norm_num) hsball) hz
    simp at h0; linarith
  refine ⟨hζ, ?_⟩
  -- apply the partial fraction at t := s.im
  have ht6 : (6 : ℝ) ≤ |s.im| := by rcases hs with h | h <;> rw [h] <;> assumption
  obtain ⟨Z, hZ, hZsum, hZpf⟩ := hpf s.im ht6
  have hZpf' := hZpf s hsball hζ
  have hlogt : Real.log (|s.im| + 3) ≤ 2 * Lg := by
    rcases hs with h | h
    · rw [h]; exact hlogR
    · rw [h, abs_neg]; exact hlogR
  -- the sum over Z
  have hZmem : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall (2 + s.im * I) (22/25 * (91/50))
      ∧ riemannZeta ρ = 0 := by
    intro ρ hρ
    have : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZ] at this
    exact this
  have hsumZ : ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
      ≤ (C * (2 * Lg)) * (1 / δ) := by
    calc ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / δ) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          obtain ⟨hρb, hρz⟩ := hZmem ρ hρ
          have hd := hordS ρ hρb hρz
          rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact one_div_le_one_div_of_le hδpos hd
      _ = (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) * (1 / δ) := by rw [Finset.sum_mul]
      _ ≤ (C * (2 * Lg)) * (1 / δ) := by
          refine mul_le_mul_of_nonneg_right (hZsum.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hlogt hC.le
  -- assemble
  have hmain : ‖logDeriv riemannZeta s‖ ≤ C * (2 * Lg) + (C * (2 * Lg)) * (1 / δ) := by
    have h1 : ‖logDeriv riemannZeta s‖
        ≤ ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          + ‖∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖ :=
      norm_le_norm_sub_add _ _
    have h2 := hZpf'.trans (mul_le_mul_of_nonneg_left hlogt hC.le)
    linarith [hsumZ]
  refine hmain.trans ?_
  rw [hδinv]
  have : C * (2 * Lg) + C * (2 * Lg) * (2 * ((S.card : ℝ) + 1))
      = 2 * C * Lg * (2 * (S.card : ℝ) + 3) := by ring
  rw [this]
  have hn : 2 * (S.card : ℝ) + 3 ≤ (48 * A₀ + 3) * Lg := by nlinarith
  calc 2 * C * Lg * (2 * (S.card : ℝ) + 3) ≤ 2 * C * Lg * ((48 * A₀ + 3) * Lg) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 2 * C * (48 * A₀ + 3) * Real.log (T + 3) ^ 2 := by rw [hLg]; ring

/-! ## D. The corridor bound for `T ≥ 7` on the full segment `-1 ≤ σ ≤ 2`.

Right half `σ ≥ 1/2`: the good height directly. Left half `σ < 1/2`: reflect to `u = 1 - s`
(`Re u ∈ (1/2, 2]`, `Im u = -R`, also covered by the good height) and bound the two `Gamma_R`
log-derivatives by `O(log T)`. -/

theorem corridor_large : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 7 ≤ T → ∃ T' ∈ Set.Icc T (T + 1),
    (∀ σ ∈ Set.Icc (-1 : ℝ) 2, riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0) ∧
    ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
      ‖logDeriv riemannZeta ((σ : ℂ) + (T' : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2 := by
  obtain ⟨C₁, hC₁, hgood⟩ := good_height_real
  refine ⟨4 * C₁ + 15, by positivity, fun T hT => ?_⟩
  obtain ⟨R, hR1, hR2, hR⟩ := hgood T hT
  have hT0 : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlogT0 : 0 ≤ Real.log T := by linarith
  have hLg : Real.log (T + 3) ≤ 2 * Real.log T := by
    calc Real.log (T + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hLg0 : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hLgsq : Real.log (T + 3) ^ 2 ≤ 4 * Real.log T ^ 2 := by nlinarith
  have hlogR : Real.log (R + 3) ≤ 2 * Real.log T := by
    calc Real.log (R + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have key : ∀ σ ∈ Set.Icc (-1 : ℝ) 2, riemannZeta ((σ : ℂ) + (R : ℂ) * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + (R : ℂ) * I)‖ ≤ (4 * C₁ + 15) * Real.log T ^ 2 := by
    intro σ hσ
    set s : ℂ := (σ : ℂ) + (R : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = R := by simp [hs]
    rcases le_or_gt (1 / 2 : ℝ) σ with hhalf | hhalf
    · -- right half: directly from the good height
      obtain ⟨h1, h2⟩ := hR s (Or.inl hsim) (by rw [hsre]; exact hhalf) (by rw [hsre]; exact hσ.2)
      refine ⟨h1, h2.trans ?_⟩
      calc C₁ * Real.log (T + 3) ^ 2 ≤ C₁ * (4 * Real.log T ^ 2) :=
            mul_le_mul_of_nonneg_left hLgsq hC₁.le
        _ ≤ (4 * C₁ + 15) * Real.log T ^ 2 := by nlinarith
    · -- left half: reflect to u = 1 - s, Im u = -R, 1/2 < Re u ≤ 2
      have hu_im : (1 - s).im = -R := by simp [hs]
      have hu_re : (1 - s).re = 1 - σ := by simp [hs]
      obtain ⟨h1, h2⟩ := hR (1 - s) (Or.inr hu_im) (by rw [hu_re]; linarith)
        (by rw [hu_re]; linarith [hσ.1])
      have hsim0 : s.im ≠ 0 := by rw [hsim]; linarith
      refine ⟨zeta_ne_zero_of_reflect hsim0 h1, ?_⟩
      rw [logDeriv_zeta_reflect hsim0 (by rw [hsre]; linarith) h1]
      have hg1 : ‖logDeriv Gammaℝ (1 - s)‖ ≤ Real.log (|(1 - s).im| + 3) + 5 :=
        norm_logDeriv_Gammaℝ_le_log (by rw [hu_re]; linarith) (by rw [hu_re]; linarith [hσ.1])
          (by rw [hu_im, abs_neg, abs_of_nonneg (by linarith)]; linarith)
      have hg2 : ‖logDeriv Gammaℝ s‖ ≤ Real.log (|s.im| + 3) + 6 :=
        norm_logDeriv_Gammaℝ_le_log_strip (by rw [hsre]; exact hσ.1) (by rw [hsre]; exact hσ.2)
          (by rw [hsim, abs_of_nonneg (by linarith)]; linarith)
      rw [hu_im, abs_neg, abs_of_nonneg (by linarith)] at hg1
      rw [hsim, abs_of_nonneg (by linarith)] at hg2
      have h2' : ‖-logDeriv riemannZeta (1 - s)‖ ≤ C₁ * Real.log (T + 3) ^ 2 := by
        rw [norm_neg]; exact h2
      calc ‖-logDeriv riemannZeta (1 - s) - logDeriv Gammaℝ (1 - s) - logDeriv Gammaℝ s‖
          ≤ ‖-logDeriv riemannZeta (1 - s) - logDeriv Gammaℝ (1 - s)‖ + ‖logDeriv Gammaℝ s‖ :=
            norm_sub_le _ _
        _ ≤ ‖-logDeriv riemannZeta (1 - s)‖ + ‖logDeriv Gammaℝ (1 - s)‖ + ‖logDeriv Gammaℝ s‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ C₁ * Real.log (T + 3) ^ 2 + (Real.log (R + 3) + 5) + (Real.log (R + 3) + 6) :=
            add_le_add (add_le_add h2' hg1) hg2
        _ ≤ C₁ * (4 * Real.log T ^ 2) + (2 * Real.log T + 5) + (2 * Real.log T + 6) := by
            have := mul_le_mul_of_nonneg_left hLgsq hC₁.le
            linarith
        _ ≤ (4 * C₁ + 15) * Real.log T ^ 2 := by nlinarith
  exact ⟨R, ⟨hR1, hR2⟩, fun σ hσ => (key σ hσ).1, fun σ hσ => (key σ hσ).2⟩

/-! ## E. The range `2 ≤ T ≤ 7` by compactness.

`K = [-1, 2] × [2, 8]` contains finitely many zeros; `S` is the finset of their ordinates and
`δ = 1/(2(|S|+1))`. On the compact set `K_δ` of points of `K` whose ordinate is `δ`-far from `S`,
`ζ ≠ 0`, so `ζ'/ζ` is continuous there and bounded by some `M`. The gap lemma puts a `δ`-far
`T' ∈ [T, T+1]` for every `T ∈ [2, 7]`. -/

theorem corridor_small : ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 2 ≤ T → T ≤ 7 → ∃ T' ∈ Set.Icc T (T + 1),
    (∀ σ ∈ Set.Icc (-1 : ℝ) 2, riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0) ∧
    ∀ σ ∈ Set.Icc (-1 : ℝ) 2, ‖logDeriv riemannZeta ((σ : ℂ) + (T' : ℂ) * I)‖ ≤ M := by
  classical
  set K : Set ℂ := Set.Icc (-1 : ℝ) 2 ×ℂ Set.Icc (2 : ℝ) 8 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin := Zeta23.RvM.riemannZeta_zeros_finite_of_isCompact hKc
  set S : Finset ℝ := hfin.toFinset.image (fun ρ : ℂ => ρ.im) with hS
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  set Kδ : Set ℂ := K ∩ {z | ∀ y ∈ S, δ ≤ |z.im - y|} with hKδ
  have hclosed : IsClosed {z : ℂ | ∀ y ∈ S, δ ≤ |z.im - y|} := by
    have e : {z : ℂ | ∀ y ∈ S, δ ≤ |z.im - y|}
        = ⋂ y ∈ (S : Set ℝ), {z : ℂ | δ ≤ |z.im - y|} := by
      ext z; simp
    rw [e]
    exact isClosed_biInter fun y _ =>
      isClosed_le continuous_const ((Complex.continuous_im.sub continuous_const).abs)
  have hKδc : IsCompact Kδ := hKc.inter_right hclosed
  have hne1 : ∀ z ∈ Kδ, z ≠ 1 := by
    rintro z ⟨hzK, -⟩ h
    have h2 : (2 : ℝ) ≤ z.im := hzK.2.1
    rw [h] at h2; simp at h2; linarith
  -- ζ ≠ 0 on Kδ
  have hne : ∀ z ∈ Kδ, riemannZeta z ≠ 0 := by
    intro z hz hzero
    have hz1 := hne1 z hz
    obtain ⟨hzK, hzfar⟩ := hz
    have hmem : z.im ∈ S := by
      rw [hS]
      exact Finset.mem_image.mpr ⟨z, hfin.mem_toFinset.mpr ⟨hzK, hz1, hzero⟩, rfl⟩
    have := hzfar z.im hmem
    simp at this; linarith
  have hcont : ContinuousOn (logDeriv riemannZeta) Kδ := by
    intro z hz
    have ha : AnalyticAt ℂ riemannZeta z := Zeta23.WeilEF.analyticAt_riemannZeta (hne1 z hz)
    have hc : ContinuousAt (logDeriv riemannZeta) z := by
      have := (ha.deriv.continuousAt).div ha.continuousAt (hne z hz)
      simpa only [logDeriv] using this
    exact hc.continuousWithinAt
  obtain ⟨M, hM⟩ := hKδc.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun T hT2 hT7 => ?_⟩
  obtain ⟨T', hT'1, hT'2, hfar⟩ := Zeta23.WeilEF.exists_far_point S T
  have hmemKδ : ∀ σ ∈ Set.Icc (-1 : ℝ) 2, ((σ : ℂ) + (T' : ℂ) * I) ∈ Kδ := by
    intro σ hσ
    have hre : ((σ : ℂ) + (T' : ℂ) * I).re = σ := by simp
    have him : ((σ : ℂ) + (T' : ℂ) * I).im = T' := by simp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show ((σ : ℂ) + (T' : ℂ) * I).re ∈ Set.Icc (-1 : ℝ) 2
      rw [hre]; exact hσ
    · show ((σ : ℂ) + (T' : ℂ) * I).im ∈ Set.Icc (2 : ℝ) 8
      rw [him]; constructor <;> linarith
    · intro y hy
      show δ ≤ |((σ : ℂ) + (T' : ℂ) * I).im - y|
      rw [him]; exact hfar y hy
  refine ⟨T', ⟨hT'1, hT'2⟩, fun σ hσ => hne _ (hmemKδ σ hσ), fun σ hσ => ?_⟩
  exact (hM _ (hmemKδ σ hσ)).trans (le_max_left _ _)

/-! ## F. The registry node statement, verbatim. -/

/-- The RH registry node `RH_corridor_bound`, verbatim (name and binder-free form): the
classical good-ordinate lemma. `T ≥ 7` from `corridor_large`, `2 ≤ T < 7` from
`corridor_small` (its constant absorbed by `log T ≥ log 2 > 0`). -/
theorem corridor_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ T' ∈ Set.Icc T (T + 1),
      (∀ σ ∈ Set.Icc (-1 : ℝ) 2, riemannZeta ((σ : ℂ) + (T' : ℂ) * I) ≠ 0) ∧
      ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
        ‖logDeriv riemannZeta ((σ : ℂ) + (T' : ℂ) * I)‖ ≤ C * (Real.log T) ^ 2 := by
  obtain ⟨C₁, hC₁, hlarge⟩ := corridor_large
  obtain ⟨M, hM0, hsmall⟩ := corridor_small
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmax0 : 0 ≤ max C₁ (M / Real.log 2 ^ 2) := le_trans hC₁.le (le_max_left _ _)
  refine ⟨max C₁ (M / Real.log 2 ^ 2) + 1, by linarith, fun T hT => ?_⟩
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT0 : 0 ≤ Real.log T := by linarith
  have hsq : 0 ≤ Real.log T ^ 2 := by positivity
  rcases le_or_gt 7 T with h7 | h7
  · obtain ⟨T', hT', h1, h2⟩ := hlarge T h7
    refine ⟨T', hT', h1, fun σ hσ => (h2 σ hσ).trans ?_⟩
    calc C₁ * Real.log T ^ 2 ≤ max C₁ (M / Real.log 2 ^ 2) * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hsq
      _ ≤ (max C₁ (M / Real.log 2 ^ 2) + 1) * Real.log T ^ 2 := by nlinarith
  · obtain ⟨T', hT', h1, h2⟩ := hsmall T hT h7.le
    refine ⟨T', hT', h1, fun σ hσ => (h2 σ hσ).trans ?_⟩
    have hMlog : M ≤ (M / Real.log 2 ^ 2) * Real.log T ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : Real.log 2 ^ 2 ≤ Real.log T ^ 2 := by nlinarith
      nlinarith
    calc M ≤ (M / Real.log 2 ^ 2) * Real.log T ^ 2 := hMlog
      _ ≤ max C₁ (M / Real.log 2 ^ 2) * Real.log T ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hsq
      _ ≤ (max C₁ (M / Real.log 2 ^ 2) + 1) * Real.log T ^ 2 := by nlinarith

end RvMBridge3
