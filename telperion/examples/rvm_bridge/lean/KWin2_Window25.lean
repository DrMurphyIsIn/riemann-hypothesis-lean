/-
  KWin2_Window25 -- THE WINDOW FLOOR AT L = 2/5, past the prime-free boundary, on the goal node's
  full test class, with no Arb seam (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH.  PR #604
  recorded that at the prime-free edge the full-class margin is zero content (on a window the Weil
  form IS the zero sum; certifying its margin says nothing new about the zeros); the same caveat
  holds here: at 2L = 0.8 the numerical window floor is lambda*(2/5) ~ 1.82e-4 (Rayleigh-Ritz,
  u-domain Legendre Galerkin), and a positive floor samples the low zeros, it constrains none of
  them.  Nor is this Connes-Consani (arXiv 2006.13771) or Yoshida: their theorems are for the
  pole-free class and stop at 2L = log 2; this statement keeps the pole terms and is past log 2.

  WHAT IS NEW AGAINST KWin.  At 2L = 0.8 > log 2 the prime comb of the Weil symbol is present:
      weilSymbol (2/5) t = Re psi(1/4 + it/2) - log pi - (2 Lambda(2)/sqrt 2) cos(t log 2).
  The certificate keeps it exactly on [0, T] (T = 24) inside the kernel-evaluated minorant (a
  rational upper polynomial of c2 cos(t log 2), with log 2 and sqrt 2 enclosed in rationals by the
  kernel-checked series log 2 = sum 2^-i / i and squares), and bounds it by its mass only beyond T
  (beta0 = 0.318 <= betaStar(2/5, 24)).

  PROVED HERE, hypothesis-free (every numeric fact kernel-checked; the guard prints only
  propext / Classical.choice / Quot.sound):
    * evenSectorFloor25 / oddSectorFloor25: Zhu's sector floors at L = 2/5 with lam = 4e-5;
    * windowFloor25 : WeilWindow.WindowFloor (2/5) (1/25000);
    * weil_positivity_window_two_fifths: the explicit-binder positivity, in the shape of
      weil_positivity_prime_free_window: for all g, L with L <= 2/5 and tsupport g in [-L, L],
      0 <= Re weilForm (autocorr g)   (this contains the prime-free window, log 2 / 2 < 2/5).
  THE ROUTE: Q(v) >= Rb v v (KWin2_Split, with the comb) >= (4e-5) int v^2 (KWin2_Tail: head
  certificate KWin2_Cert25 + projection tail), then Zhu Lemma 6.1 (windowFloor_of_sectors).
  No `sorry`.
-/
import KWin2_Split
import KWin2_Cert25
import KWin2_Consts

open Real MeasureTheory Set Finset

noncomputable section

namespace KWin2
open KWin (Psi epsR ip continuous_v gammaUpQ logPiUpQ gamma_le log_pi_le one_le_log_pi piHiQ pi_lt_Q psdCert
  pi_gt_Q)
open WeilWindow RvMBridgeZhu WeilExplicit RvMBridge11 RvMBridge30

/-! ## A. Rational halves of the real side conditions (kernel). -/

theorem log2S_near : |log2S - P25.a0| + (1 / 2) ^ 60 ≤ P25.da := by decide +kernel

/-- `c2 = 2 log 2 / sqrt 2` squeezed around `c0`. -/
theorem c2_lo_q : P25.c0 - P25.dc ≤ 2 * (log2S - (1 / 2) ^ 60) / sq2hi := by decide +kernel
theorem c2_hi_q : 2 * (log2S + (1 / 2) ^ 60) / sq2lo ≤ P25.c0 + P25.dc := by decide +kernel

/-- `beta0 + 1/24 + c0 + dc`, the point where `exp` is bounded above. -/
def qBeta25 : ℚ := P25.beta0 + 1 / 24 + P25.c0 + P25.dc
theorem qBeta25_le : qBeta25 / 2 ≤ 1 := by decide +kernel
theorem qBeta25_nonneg : 0 ≤ qBeta25 / 2 := by decide +kernel

/-- `exp(q/2)^2 * pi_hi <= 12` (Taylor upper bound, 12 terms). -/
theorem beta25_q : ((∑ m ∈ range 12, (qBeta25 / 2) ^ m / (m.factorial : ℚ))
    + (qBeta25 / 2) ^ 12 * (12 + 1) / ((Nat.factorial 12 : ℚ) * 12)) ^ 2 * piHiQ ≤ 12 := by
  decide +kernel

/-- `12 <= exp(2.485)` (Taylor lower bound, 30 terms): `log 12 <= 2.485`. -/
theorem log12_q : (12 : ℚ) ≤ ∑ i ∈ range 30, (2485 / 1000 : ℚ) ^ i / (i.factorial : ℚ) := by
  decide +kernel

/-- `exp(1/50) <= Cp` (Taylor upper bound, 4 terms). -/
theorem cosh25_q : (∑ m ∈ range 4, (1 / 50 : ℚ) ^ m / (m.factorial : ℚ))
    + (1 / 50 : ℚ) ^ 4 * (4 + 1) / ((Nat.factorial 4 : ℚ) * 4) ≤ P25.Cp := by decide +kernel

/-- The two ends of `|Psi_{2/5} - beta0| <= S0` as rational inequalities. -/
theorem S0_lo_q : -(8463 / 2000 : ℚ) - logPiUpQ - (P25.c0 + P25.dc) - P25.beta0 ≥ -P25.S0 := by
  decide +kernel
theorem S0_hi_q : (2485 / 1000 : ℚ) + 13 / 24 ^ 2 - 1 + (P25.c0 + P25.dc) - P25.beta0 ≤ P25.S0 := by
  decide +kernel

/-! ## B. The real side conditions. -/

lemma P25_ell : ((P25.ell : ℚ) : ℝ) = 2 / 5 := by norm_num [P25]
lemma P25_T : ((P25.T : ℚ) : ℝ) = 24 := by norm_num [P25]

lemma lR25 : lR P25 = 2 / 5 := P25_ell
lemma TR25 : TR P25 = 24 := P25_T

lemma log_two_lt_45 : Real.log 2 < 2 * (2 / 5 : ℝ) := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma twoL_le_log_three : 2 * (2 / 5 : ℝ) ≤ Real.log 3 := by
  have h : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  linarith

/-- **`|log 2 - a0| <= da`.** -/
theorem log2_near25 : |Real.log 2 - ((P25.a0 : ℚ) : ℝ)| ≤ ((P25.da : ℚ) : ℝ) := by
  have h1 := log2_near_S
  have h2 : |((log2S : ℚ) : ℝ) - ((P25.a0 : ℚ) : ℝ)| + (1 / 2) ^ 60 ≤ ((P25.da : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr log2S_near
    push_cast at this
    exact this
  calc |Real.log 2 - ((P25.a0 : ℚ) : ℝ)|
      ≤ |Real.log 2 - ((log2S : ℚ) : ℝ)| + |((log2S : ℚ) : ℝ) - ((P25.a0 : ℚ) : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ (1 / 2) ^ 60 + |((log2S : ℚ) : ℝ) - ((P25.a0 : ℚ) : ℝ)| := by linarith
    _ ≤ ((P25.da : ℚ) : ℝ) := by linarith

/-- **`|c2 - c0| <= dc`**, `c2 = 2 Lambda(2)/sqrt 2`. -/
theorem c2_near25 : |c2 - ((P25.c0 : ℚ) : ℝ)| ≤ ((P25.dc : ℚ) : ℝ) := by
  rw [c2_eq]
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds
  have hl := abs_le.mp log2_near_S
  have hslo : (0 : ℝ) < ((sq2lo : ℚ) : ℝ) := by exact_mod_cast sq2lo_pos
  have hsq : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hshi : (0 : ℝ) < ((sq2hi : ℚ) : ℝ) := by linarith
  set S : ℝ := ((log2S : ℚ) : ℝ) with hSdef
  set ε : ℝ := (1 / 2) ^ 60 with hε
  have hSε : 0 ≤ S - ε := by
    have := (Rat.cast_le (K := ℝ)).mpr log2S_ge
    push_cast at this
    rw [hSdef, hε]; linarith
  have hlo : 2 * (S - ε) / ((sq2hi : ℚ) : ℝ) ≤ 2 * Real.log 2 / Real.sqrt 2 := by
    rw [div_le_div_iff₀ hshi hsq]
    have h1 : S - ε ≤ Real.log 2 := by linarith [hl.1]
    have h2 : (S - ε) * Real.sqrt 2 ≤ Real.log 2 * ((sq2hi : ℚ) : ℝ) := by
      calc (S - ε) * Real.sqrt 2 ≤ Real.log 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_right h1 hsq.le
        _ ≤ Real.log 2 * ((sq2hi : ℚ) : ℝ) :=
            mul_le_mul_of_nonneg_left hs2 (by linarith)
    linarith
  have hhi : 2 * Real.log 2 / Real.sqrt 2 ≤ 2 * (S + ε) / ((sq2lo : ℚ) : ℝ) := by
    rw [div_le_div_iff₀ hsq hslo]
    have h1 : Real.log 2 ≤ S + ε := by linarith [hl.2]
    have h2 : Real.log 2 * ((sq2lo : ℚ) : ℝ) ≤ (S + ε) * Real.sqrt 2 := by
      calc Real.log 2 * ((sq2lo : ℚ) : ℝ) ≤ Real.log 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left hs1 (Real.log_nonneg (by norm_num))
        _ ≤ (S + ε) * Real.sqrt 2 := mul_le_mul_of_nonneg_right h1 hsq.le
    linarith
  have hq1 : ((P25.c0 : ℚ) : ℝ) - ((P25.dc : ℚ) : ℝ) ≤ 2 * (S - ε) / ((sq2hi : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr c2_lo_q
    push_cast at this
    rw [hSdef, hε]; exact this
  have hq2 : 2 * (S + ε) / ((sq2lo : ℚ) : ℝ) ≤ ((P25.c0 : ℚ) : ℝ) + ((P25.dc : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr c2_hi_q
    push_cast at this
    rw [hSdef, hε]; exact this
  rw [abs_le]
  constructor <;> linarith

lemma c2_le25 : c2 ≤ ((P25.c0 : ℚ) : ℝ) + ((P25.dc : ℚ) : ℝ) := by
  have := (abs_le.mp c2_near25).2; linarith

/-- **`beta0 <= betaStar(2/5, 24)`.** -/
theorem beta0_le_betaStar25 : b0R P25 ≤ betaStar (2 / 5) (TR P25) := by
  unfold betaStar
  rw [combMass_eq_two log_two_lt_45 twoL_le_log_three, TR25]
  have hc := c2_le25
  have hq : ((qBeta25 : ℚ) : ℝ) ≤ Real.log (24 / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hx0 : 0 ≤ ((qBeta25 : ℚ) : ℝ) / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr qBeta25_nonneg; push_cast at this; exact this
    have hx1 : ((qBeta25 : ℚ) : ℝ) / 2 ≤ 1 := by
      have := (Rat.cast_le (K := ℝ)).mpr qBeta25_le; push_cast at this; exact this
    have e1 : Real.exp ((qBeta25 : ℚ) : ℝ) = Real.exp (((qBeta25 : ℚ) : ℝ) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 := Real.exp_bound' hx0 hx1 (n := 12) (by norm_num)
    have hTq := (Rat.cast_le (K := ℝ)).mpr beta25_q
    push_cast at hTq e2
    set Ts : ℝ := (∑ m ∈ range 12, (((qBeta25 : ℚ) : ℝ) / 2) ^ m / (m.factorial : ℝ))
      + (((qBeta25 : ℚ) : ℝ) / 2) ^ 12 * (12 + 1) / ((Nat.factorial 12 : ℝ) * 12) with hTs
    have hpos : 0 ≤ Real.exp (((qBeta25 : ℚ) : ℝ) / 2) := (Real.exp_pos _).le
    have hsq : Real.exp (((qBeta25 : ℚ) : ℝ) / 2) ^ 2 ≤ Ts ^ 2 := pow_le_pow_left₀ hpos e2 2
    have hpi := pi_lt_Q
    have hpi0 := Real.pi_pos
    rw [e1, show (24 : ℝ) / (2 * Real.pi) = 12 / Real.pi by field_simp; ring, le_div_iff₀ hpi0]
    have h1 : Real.exp (((qBeta25 : ℚ) : ℝ) / 2) ^ 2 * Real.pi ≤ Ts ^ 2 * Real.pi :=
      mul_le_mul_of_nonneg_right hsq hpi0.le
    have h2 : Ts ^ 2 * Real.pi ≤ Ts ^ 2 * ((piHiQ : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpi.le (sq_nonneg _)
    linarith
  have hqd : ((qBeta25 : ℚ) : ℝ) = b0R P25 + 1 / 24 + ((P25.c0 : ℚ) : ℝ) + ((P25.dc : ℚ) : ℝ) := by
    unfold qBeta25 b0R; push_cast; ring
  rw [hqd] at hq
  linarith

/-- **`|weilSymbol (2/5) - beta0| <= S0` on `[0, 24]`.** -/
theorem sym_bound25 : ∀ t, 0 ≤ t → t ≤ TR P25 →
    |weilSymbol (2 / 5) t - b0R P25| ≤ ((P25.S0 : ℚ) : ℝ) := by
  intro t ht0 htT
  rw [TR25] at htT
  rw [weilSymbol_eq_two log_two_lt_45 twoL_le_log_three]
  unfold Psi
  have hlow : psiR 0 ≤ psiR t := psiR_mono le_rfl (by rw [abs_of_nonneg ht0]; exact ht0)
  have hup : psiR t ≤ psiR 24 := psiR_mono ht0 (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 24)]; exact htT)
  have hfl := psiR_floor_0
  have hst := psiR_le_stirling (t := 24) (by norm_num)
  have h12 : Real.log ((24 : ℝ) / 2) = Real.log 12 := by norm_num
  rw [h12] at hst
  have hl12 : Real.log 12 ≤ 2485 / 1000 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.sum_le_exp_of_nonneg (x := 2485 / 1000) (by norm_num) 30
    have hq' : (12 : ℝ) ≤ ∑ i ∈ range 30, (2485 / 1000 : ℝ) ^ i / (i.factorial : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr log12_q
      push_cast at this
      exact this
    linarith
  have hlp := log_pi_le
  have hlp1 := one_le_log_pi
  have hc := c2_near25
  have hc0 := c2_nonneg
  have hcos1 := Real.cos_le_one (t * Real.log 2)
  have hcos2 := Real.neg_one_le_cos (t * Real.log 2)
  have hccos1 : c2 * Real.cos (t * Real.log 2) ≤ c2 := by nlinarith
  have hccos2 : -c2 ≤ c2 * Real.cos (t * Real.log 2) := by nlinarith
  have hc2 := c2_le25
  have hlo := (Rat.cast_le (K := ℝ)).mpr S0_lo_q
  have hhi := (Rat.cast_le (K := ℝ)).mpr S0_hi_q
  push_cast at hlo hhi
  unfold b0R
  rw [abs_le]
  constructor <;> nlinarith

/-- **`cosh(l/2) <= Cp`.** -/
theorem cosh25 : Real.cosh (lR P25 / 2) ≤ ((P25.Cp : ℚ) : ℝ) := by
  rw [lR25]
  have h := Real.cosh_le_exp_half_sq ((2 / 5 : ℝ) / 2)
  have hx : ((2 / 5 : ℝ) / 2) ^ 2 / 2 = 1 / 50 := by norm_num
  rw [hx] at h
  have e2 := Real.exp_bound' (x := 1 / 50) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  have hq := (Rat.cast_le (K := ℝ)).mpr cosh25_q
  push_cast at hq
  linarith

/-- **The symbol hypotheses at L = 2/5.** -/
theorem symHyp25 : SymHyp P25 (weilSymbol (2 / 5)) where
  cont := continuous_weilSymbol_two log_two_lt_45 twoL_le_log_three
  bound := sym_bound25
  minor := by
    intro i hi t hti hti'
    have h := sym_minorant P25 brk25 piece25 min25 comb25 gamma_le log_pi_le log2_near25 c2_near25
      hi hti hti'
    rw [weilSymbol_eq_two log_two_lt_45 twoL_le_log_three]
    exact h
  cosh := cosh25

/-! ## C. The sector floors and the window floor. -/

lemma lamFloor25_cast : ((P25.lamFloor : ℚ) : ℝ) = 1 / 25000 := by norm_num [P25]

/-- A real sector test at L = 2/5: the common core of both sector floors. -/
theorem sector_floor_core25 {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam : ℚ}
    (htail : tailCond P25 par N lam = true) (hcert : psdCert (headMat P25 par N lam) N = true)
    (hginv : ginvCheck P25 par N = true) {f : ℝ → ℂ} (hf : IsWeilTest f) (hre : ∀ x, (f x).im = 0)
    (hpf : ∀ x, f (-x) = (epsR par : ℂ) * f x) (hs : tsupport f ⊆ Icc (-(2 / 5)) (2 / 5)) :
    (1 / 25000 : ℝ) * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re := by
  set v : ℝ → ℝ := fun u => (f u).re with hvdef
  have hfv : f = fun u => (v u : ℂ) := by
    funext u; exact Complex.ext (by simp [hvdef]) (by simp [hvdef, hre u])
  rw [hfv] at hf hs ⊢
  have hev : ∀ u, v (-u) = epsR par * v u := by
    intro u
    have h := congrArg Complex.re (hpf u)
    rw [hfv] at h
    simpa [epsR] using h
  have hLl : (2 / 5 : ℝ) ≤ lR P25 := by rw [lR25]
  have hT : (15 / 4 : ℝ) ≤ TR P25 := by rw [TR25]; norm_num
  have hQ := Q_ge_Rb P25 par25 log_two_lt_45 twoL_le_log_three hLl hT beta0_le_betaStar25 hpar hf hev hs
  have hR := Rb_floor P25 symHyp25 par25 brk25 hpar htail (headPSD_of_psdCert hcert) hginv
    (continuous_v hf)
  have hl : (0 : ℝ) < lR P25 := lR_pos P25 par25
  have hip : ip (lR P25) v v = ∫ x : ℝ, ‖(v x : ℂ)‖ ^ 2 := by
    unfold ip
    rw [← integral_eq_interval' hf hl hLl hs]
    congr 1; funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
  rw [lamFloor25_cast, hip] at hR
  linarith

theorem evenSectorFloor25 : WeilWindow.EvenSectorFloor (2 / 5) (1 / 25000) := by
  intro f hf hre hev hs
  exact sector_floor_core25 (par := 0) (N := 16) (Or.inl rfl) tailE25 certE25 ginvE25 hf hre
    (fun x => by rw [hev x]; simp [epsR]) hs

theorem oddSectorFloor25 : WeilWindow.OddSectorFloor (2 / 5) (1 / 25000) := by
  intro f hf hre hodd hs
  exact sector_floor_core25 (par := 1) (N := 14) (Or.inr rfl) tailO25 certO25 ginvO25 hf hre
    (fun x => by rw [hodd x]; simp [epsR]) hs

/-- **THE WINDOW FLOOR AT L = 2/5** (past the prime-free boundary, comb term n = 2 present): every
smooth compactly supported test `f` (complex, no parity) supported in `[-2/5, 2/5]` has
`Re weilForm (autocorr f) >= (1/25000) ||f||_2^2`.  Hypothesis-free, no Arb seam. -/
theorem windowFloor25 : WeilWindow.WindowFloor (2 / 5) (1 / 25000) :=
  windowFloor_of_sectors evenSectorFloor25 oddSectorFloor25

/-! ## D. The explicit-binder positivity. -/

/-- **Weil positivity on every window with L <= 2/5** (the goal node's full test class, pole terms
kept), in the explicit-binder shape of `weil_positivity_prime_free_window`.  It contains the
prime-free window (log 2 / 2 < 2/5). -/
theorem weil_positivity_window_two_fifths (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L : ℝ)
    (hL : L ≤ 2 / 5) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  have hs' : tsupport g ⊆ Icc (-(2 / 5)) (2 / 5) := hsupp.trans (Icc_subset_Icc (by linarith) hL)
  have h := windowFloor25 g hg hs'
  have hm : 0 ≤ ∫ x : ℝ, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
  have h2 : (0 : ℝ) ≤ (1 / 25000) * ∫ x : ℝ, ‖g x‖ ^ 2 := by positivity
  rw [weilForm_autocorr_eq] at h
  linarith

/-- The prime-free window as a corollary (2L <= log 2 implies L <= 2/5). -/
theorem weil_positivity_prime_free_window_of_two_fifths (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g)
    (L : ℝ) (hL : 2 * L ≤ Real.log 2) (hsupp : tsupport g ⊆ Set.Icc (-L) L) :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re :=
  weil_positivity_window_two_fifths g hg L (by linarith [log_two_lt_45]) hsupp

end KWin2

end
