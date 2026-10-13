/-
  KWin2_Window -- the generic assembly: a KWin2 certificate whose kernel checks all evaluate to
  `true` proves Zhu's window floor, for every window with log 2 < 2L <= log 3 (prime comb {2})
  (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  A finite-window Weil positivity statement is NOT RH; not
  Connes-Consani (pole terms kept); cf. PR #604.

  `windowFloor_of_cert`: given a KPar P, the head levels / sizes of both sectors, and
    * the structural and head checks (parCheck, brkCheck, pieceCheck, minCheck, combCheck,
      tailCond, ginvCheck) -- evaluated by the kernel per instance -- and the PSD property of both
      head matrices (`HeadPSD`, from psdCert or psdCertR, also kernel-evaluated),
    * `sideCheck P xT` -- the RATIONAL halves of the real side conditions, also kernel-evaluated:
      |S - a0| + 2^-60 <= da (log 2 by its series), the sqrt 2 squeeze of c2 around c0, the
      exp Taylor bound behind beta0 <= betaStar L T, the two ends of |Psi_L - beta0| <= S0 on
      [0, T] (psiR monotone, the island's psiR(0) floor and Stirling at T, log(T/2) <= xT), and
      cosh(l/2) <= Cp,
    * gamma <= gamUp and log pi <= logPiUp (real facts, supplied per instance),
  it returns WeilWindow.WindowFloor L lamFloor; `weil_positivity_of_windowFloor` turns a window
  floor into the explicit-binder positivity for every smaller window.  No `sorry`.
-/
import KWin2_Split
import KWin2_Consts

open Real MeasureTheory Set Finset

noncomputable section

namespace KWin2
open KWin (Psi epsR ip continuous_v piHiQ pi_lt_Q psdCert one_le_log_pi)
open WeilWindow RvMBridgeZhu WeilExplicit RvMBridge11 RvMBridge30

/-! ## A. The rational side conditions. -/

/-- The point where `exp` is bounded above for `beta0 <= betaStar`. -/
def qBeta (P : KPar) : ℚ := P.beta0 + 1 / P.T + P.c0 + P.dc

/-- Taylor upper polynomial of `exp` at `x in [0, 1]` with `n` terms (Mathlib's `exp_bound'`). -/
def expUp (x : ℚ) (n : ℕ) : ℚ :=
  (∑ m ∈ range n, x ^ m / (m.factorial : ℚ)) + x ^ n * (n + 1) / ((n.factorial : ℚ) * n)

/-- Taylor lower polynomial of `exp` at `x >= 0` with `n` terms. -/
def expLo (x : ℚ) (n : ℕ) : ℚ := ∑ i ∈ range n, x ^ i / (i.factorial : ℚ)

/-- The rational halves of the real side conditions, one Boolean. -/
def sideCheck (P : KPar) (xT : ℚ) : Bool :=
  decide (|log2S - P.a0| + (1 / 2) ^ 60 ≤ P.da) &&
  decide (P.c0 - P.dc ≤ 2 * (log2S - (1 / 2) ^ 60) / sq2hi) &&
  decide (2 * (log2S + (1 / 2) ^ 60) / sq2lo ≤ P.c0 + P.dc) &&
  decide (0 ≤ qBeta P / 4) && decide (qBeta P / 4 ≤ 1) &&
  decide (expUp (qBeta P / 4) 16 ^ 4 * (2 * piHiQ) ≤ P.T) &&
  decide (15 / 4 ≤ P.T) &&
  decide (-(8463 / 2000 : ℚ) - P.logPiUp - (P.c0 + P.dc) - P.beta0 ≥ -P.S0) &&
  decide (0 ≤ xT) && decide (P.T / 2 ≤ expLo xT 40) &&
  decide (xT + 13 / P.T ^ 2 - 1 + (P.c0 + P.dc) - P.beta0 ≤ P.S0) &&
  decide (P.ell ^ 2 / 8 ≤ 1) && decide (expUp (P.ell ^ 2 / 8) 6 ≤ P.Cp)

theorem sideCheck_sound {P : KPar} {xT : ℚ} (h : sideCheck P xT = true) :
    |log2S - P.a0| + (1 / 2) ^ 60 ≤ P.da
    ∧ P.c0 - P.dc ≤ 2 * (log2S - (1 / 2) ^ 60) / sq2hi
    ∧ 2 * (log2S + (1 / 2) ^ 60) / sq2lo ≤ P.c0 + P.dc
    ∧ 0 ≤ qBeta P / 4 ∧ qBeta P / 4 ≤ 1
    ∧ expUp (qBeta P / 4) 16 ^ 4 * (2 * piHiQ) ≤ P.T
    ∧ 15 / 4 ≤ P.T
    ∧ -(8463 / 2000 : ℚ) - P.logPiUp - (P.c0 + P.dc) - P.beta0 ≥ -P.S0
    ∧ 0 ≤ xT ∧ P.T / 2 ≤ expLo xT 40
    ∧ xT + 13 / P.T ^ 2 - 1 + (P.c0 + P.dc) - P.beta0 ≤ P.S0
    ∧ P.ell ^ 2 / 8 ≤ 1 ∧ expUp (P.ell ^ 2 / 8) 6 ≤ P.Cp := by
  unfold sideCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

lemma expUp_cast (x : ℚ) (n : ℕ) :
    ((expUp x n : ℚ) : ℝ) = (∑ m ∈ range n, (x : ℝ) ^ m / (m.factorial : ℝ))
      + (x : ℝ) ^ n * (n + 1) / ((n.factorial : ℝ) * n) := by
  unfold expUp; push_cast; rfl

lemma exp_le_expUp {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp (x : ℝ) ≤ ((expUp x n : ℚ) : ℝ) := by
  rw [expUp_cast]
  exact Real.exp_bound' (by exact_mod_cast h0) (by exact_mod_cast h1) hn

lemma expLo_le_exp {x : ℚ} (h0 : 0 ≤ x) (n : ℕ) : ((expLo x n : ℚ) : ℝ) ≤ Real.exp (x : ℝ) := by
  unfold expLo
  push_cast
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast h0) n

/-! ## B. The real side conditions from `sideCheck`. -/

section Side
variable {P : KPar} {xT : ℚ} (hs : sideCheck P xT = true)
include hs

theorem log2_near_of : |Real.log 2 - ((P.a0 : ℚ) : ℝ)| ≤ ((P.da : ℚ) : ℝ) := by
  have h1 := log2_near_S
  have h2 : |((log2S : ℚ) : ℝ) - ((P.a0 : ℚ) : ℝ)| + (1 / 2) ^ 60 ≤ ((P.da : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr (sideCheck_sound hs).1
    push_cast at this
    exact this
  calc |Real.log 2 - ((P.a0 : ℚ) : ℝ)|
      ≤ |Real.log 2 - ((log2S : ℚ) : ℝ)| + |((log2S : ℚ) : ℝ) - ((P.a0 : ℚ) : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ (1 / 2) ^ 60 + |((log2S : ℚ) : ℝ) - ((P.a0 : ℚ) : ℝ)| := by linarith
    _ ≤ ((P.da : ℚ) : ℝ) := by linarith

theorem c2_near_of : |c2 - ((P.c0 : ℚ) : ℝ)| ≤ ((P.dc : ℚ) : ℝ) := by
  obtain ⟨_, hlo_q, hhi_q, _⟩ := sideCheck_sound hs
  rw [c2_eq]
  obtain ⟨hs1, hs2⟩ := sqrt2_bounds
  have hl := abs_le.mp log2_near_S
  have hslo : (0 : ℝ) < ((sq2lo : ℚ) : ℝ) := by exact_mod_cast sq2lo_pos
  have hsq : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hshi : (0 : ℝ) < ((sq2hi : ℚ) : ℝ) := by linarith
  set S : ℝ := ((log2S : ℚ) : ℝ) with hSdef
  set ε : ℝ := (1 / 2) ^ 60 with hε
  have hlo : 2 * (S - ε) / ((sq2hi : ℚ) : ℝ) ≤ 2 * Real.log 2 / Real.sqrt 2 := by
    rw [div_le_div_iff₀ hshi hsq]
    have h1 : S - ε ≤ Real.log 2 := by linarith [hl.1]
    have h2 : (S - ε) * Real.sqrt 2 ≤ Real.log 2 * ((sq2hi : ℚ) : ℝ) := by
      calc (S - ε) * Real.sqrt 2 ≤ Real.log 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_right h1 hsq.le
        _ ≤ Real.log 2 * ((sq2hi : ℚ) : ℝ) :=
            mul_le_mul_of_nonneg_left hs2 (Real.log_nonneg (by norm_num))
    linarith
  have hhi : 2 * Real.log 2 / Real.sqrt 2 ≤ 2 * (S + ε) / ((sq2lo : ℚ) : ℝ) := by
    rw [div_le_div_iff₀ hsq hslo]
    have h1 : Real.log 2 ≤ S + ε := by linarith [hl.2]
    have h2 : Real.log 2 * ((sq2lo : ℚ) : ℝ) ≤ (S + ε) * Real.sqrt 2 := by
      calc Real.log 2 * ((sq2lo : ℚ) : ℝ) ≤ Real.log 2 * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left hs1 (Real.log_nonneg (by norm_num))
        _ ≤ (S + ε) * Real.sqrt 2 := mul_le_mul_of_nonneg_right h1 hsq.le
    linarith
  have hq1 : ((P.c0 : ℚ) : ℝ) - ((P.dc : ℚ) : ℝ) ≤ 2 * (S - ε) / ((sq2hi : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hlo_q
    push_cast at this
    rw [hSdef, hε]; exact this
  have hq2 : 2 * (S + ε) / ((sq2lo : ℚ) : ℝ) ≤ ((P.c0 : ℚ) : ℝ) + ((P.dc : ℚ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hhi_q
    push_cast at this
    rw [hSdef, hε]; exact this
  rw [abs_le]
  constructor <;> linarith

lemma c2_le_of : c2 ≤ ((P.c0 : ℚ) : ℝ) + ((P.dc : ℚ) : ℝ) := by
  have := (abs_le.mp (c2_near_of hs)).2; linarith

lemma TR_ge_of : (15 / 4 : ℝ) ≤ TR P := by
  have := (Rat.cast_le (K := ℝ)).mpr (sideCheck_sound hs).2.2.2.2.2.2.1
  push_cast at this
  unfold TR; exact this

theorem beta0_le_betaStar_of {L : ℝ} (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) :
    b0R P ≤ betaStar L (TR P) := by
  obtain ⟨_, _, _, hq0, hq1, hqT, hT, _⟩ := sideCheck_sound hs
  unfold betaStar
  rw [combMass_eq_two hL1 hL2]
  have hc := c2_le_of hs
  have hTpos : (0 : ℝ) < TR P := by have := TR_ge_of hs; linarith
  have hq : ((qBeta P : ℚ) : ℝ) ≤ Real.log (TR P / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have e1 : Real.exp ((qBeta P : ℚ) : ℝ) = Real.exp (((qBeta P / 4 : ℚ) : ℝ)) ^ 4 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 := exp_le_expUp hq0 hq1 (n := 16) (by norm_num)
    have hpos : 0 ≤ Real.exp (((qBeta P / 4 : ℚ) : ℝ)) := (Real.exp_pos _).le
    have hsq : Real.exp (((qBeta P / 4 : ℚ) : ℝ)) ^ 4 ≤ ((expUp (qBeta P / 4) 16 : ℚ) : ℝ) ^ 4 :=
      pow_le_pow_left₀ hpos e2 4
    have hTq : ((expUp (qBeta P / 4) 16 : ℚ) : ℝ) ^ 4 * (2 * ((piHiQ : ℚ) : ℝ)) ≤ TR P := by
      have := (Rat.cast_le (K := ℝ)).mpr hqT
      push_cast at this
      unfold TR; exact this
    have hpi := pi_lt_Q
    have hpi0 := Real.pi_pos
    rw [e1, le_div_iff₀ (by positivity)]
    have h1 : Real.exp (((qBeta P / 4 : ℚ) : ℝ)) ^ 4 * (2 * Real.pi)
        ≤ ((expUp (qBeta P / 4) 16 : ℚ) : ℝ) ^ 4 * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    have h2 : ((expUp (qBeta P / 4) 16 : ℚ) : ℝ) ^ 4 * (2 * Real.pi)
        ≤ ((expUp (qBeta P / 4) 16 : ℚ) : ℝ) ^ 4 * (2 * ((piHiQ : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hqd : ((qBeta P : ℚ) : ℝ) = b0R P + 1 / TR P + ((P.c0 : ℚ) : ℝ) + ((P.dc : ℚ) : ℝ) := by
    unfold qBeta b0R TR; push_cast; ring
  rw [hqd] at hq
  linarith

theorem sym_bound_of (hlp : Real.log Real.pi ≤ ((P.logPiUp : ℚ) : ℝ)) {L : ℝ}
    (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) :
    ∀ t, 0 ≤ t → t ≤ TR P → |weilSymbol L t - b0R P| ≤ ((P.S0 : ℚ) : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, hlo_q, hx0, hxT, hhi_q, _⟩ := sideCheck_sound hs
  intro t ht0 htT
  have hT := TR_ge_of hs
  rw [weilSymbol_eq_two hL1 hL2]
  unfold Psi
  have hlow : psiR 0 ≤ psiR t := psiR_mono le_rfl (by rw [abs_of_nonneg ht0]; exact ht0)
  have hup : psiR t ≤ psiR (TR P) :=
    psiR_mono ht0 (by rw [abs_of_pos (by linarith : (0 : ℝ) < TR P)]; exact htT)
  have hfl := psiR_floor_0
  have hst := psiR_le_stirling (t := TR P) (by linarith)
  have hlT : Real.log (TR P / 2) ≤ ((xT : ℚ) : ℝ) := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    have h1 := expLo_le_exp hx0 40
    have h2 : TR P / 2 ≤ ((expLo xT 40 : ℚ) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr hxT
      push_cast at this
      unfold TR; exact this
    linarith
  have hlp1 := one_le_log_pi
  have hc0 := c2_nonneg
  have hcos1 := Real.cos_le_one (t * Real.log 2)
  have hcos2 := Real.neg_one_le_cos (t * Real.log 2)
  have hccos1 : c2 * Real.cos (t * Real.log 2) ≤ c2 := by nlinarith
  have hccos2 : -c2 ≤ c2 * Real.cos (t * Real.log 2) := by nlinarith
  have hc2 := c2_le_of hs
  have hlo := (Rat.cast_le (K := ℝ)).mpr hlo_q
  have hhi := (Rat.cast_le (K := ℝ)).mpr hhi_q
  push_cast at hlo hhi
  have hTT : ((P.T : ℚ) : ℝ) = TR P := rfl
  rw [hTT] at hhi
  unfold b0R
  rw [abs_le]
  constructor <;> nlinarith

theorem cosh_of : Real.cosh (lR P / 2) ≤ ((P.Cp : ℚ) : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hl1, hcp⟩ := sideCheck_sound hs
  have h := Real.cosh_le_exp_half_sq (lR P / 2)
  have hx : (lR P / 2) ^ 2 / 2 = (((P.ell ^ 2 / 8 : ℚ)) : ℝ) := by unfold lR; push_cast; ring
  rw [hx] at h
  have e2 := exp_le_expUp (x := P.ell ^ 2 / 8) (by positivity) hl1 (n := 6) (by norm_num)
  have hq : ((expUp (P.ell ^ 2 / 8) 6 : ℚ) : ℝ) ≤ ((P.Cp : ℚ) : ℝ) := by exact_mod_cast hcp
  linarith

end Side

/-! ## C. The assembly. -/

/-- A real sector test: the common core of both sector floors. -/
theorem sector_floor_core_of {P : KPar} {L : ℝ} {sym : ℝ → ℝ} (hsym : sym = weilSymbol L)
    (hS : SymHyp P sym) (hpc : parCheck P = true) (hb : brkCheck P = true)
    (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) (hLl : L ≤ lR P) (hT : 15 / 4 ≤ TR P)
    (hβ : b0R P ≤ betaStar L (TR P)) {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam : ℚ}
    (htail : tailCond P par N lam = true) (hcert : HeadPSD (headMat P par N lam) N)
    (hginv : ginvCheck P par N = true) {f : ℝ → ℂ} (hf : IsWeilTest f) (hre : ∀ x, (f x).im = 0)
    (hpf : ∀ x, f (-x) = (epsR par : ℂ) * f x) (hs : tsupport f ⊆ Icc (-L) L) :
    ((P.lamFloor : ℚ) : ℝ) * (∫ x : ℝ, ‖f x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr f)).re := by
  subst hsym
  set v : ℝ → ℝ := fun u => (f u).re with hvdef
  have hfv : f = fun u => (v u : ℂ) := by
    funext u; exact Complex.ext (by simp [hvdef]) (by simp [hvdef, hre u])
  rw [hfv] at hf hs ⊢
  have hev : ∀ u, v (-u) = epsR par * v u := by
    intro u
    have h := congrArg Complex.re (hpf u)
    rw [hfv] at h
    simpa [epsR] using h
  have hQ := Q_ge_Rb P hpc hL1 hL2 hLl hT hβ hpar hf hev hs
  have hR := Rb_floor P hS hpc hb hpar htail hcert hginv (continuous_v hf)
  have hl : (0 : ℝ) < lR P := lR_pos P hpc
  have hip : ip (lR P) v v = ∫ x : ℝ, ‖(v x : ℂ)‖ ^ 2 := by
    unfold ip
    rw [← integral_eq_interval' hf hl hLl hs]
    congr 1; funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
  rw [hip] at hR
  linarith

/-- **The generic window floor**: a KWin2 certificate whose kernel checks evaluate to `true`
proves `WindowFloor L lamFloor` for every window with log 2 < 2L <= log 3 inside [-l, l]. -/
theorem windowFloor_of_cert (P : KPar) {L : ℝ} (NE NO : ℕ) (lamE lamO : ℚ) (xT : ℚ)
    (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3) (hLl : L ≤ lR P)
    (hγ : Real.eulerMascheroniConstant ≤ ((P.gamUp : ℚ) : ℝ))
    (hlp : Real.log Real.pi ≤ ((P.logPiUp : ℚ) : ℝ))
    (hside : sideCheck P xT = true) (hpc : parCheck P = true) (hb : brkCheck P = true)
    (hpcs : pieceCheck P = true) (hm : minCheck P = true) (hcc : combCheck P = true)
    (htE : tailCond P 0 NE lamE = true) (htO : tailCond P 1 NO lamO = true)
    (hgE : ginvCheck P 0 NE = true) (hgO : ginvCheck P 1 NO = true)
    (hcE : HeadPSD (headMat P 0 NE lamE) NE) (hcO : HeadPSD (headMat P 1 NO lamO) NO) :
    WeilWindow.WindowFloor L ((P.lamFloor : ℚ) : ℝ) := by
  have hS : SymHyp P (weilSymbol L) :=
    { cont := continuous_weilSymbol_two hL1 hL2
      bound := sym_bound_of hside hlp hL1 hL2
      minor := by
        intro i hi t hti hti'
        have h := sym_minorant P hb hpcs hm hcc hγ hlp (log2_near_of hside) (c2_near_of hside)
          hi hti hti'
        rw [weilSymbol_eq_two hL1 hL2]
        exact h
      cosh := cosh_of hside }
  have hT := TR_ge_of hside
  have hβ := beta0_le_betaStar_of hside hL1 hL2
  have hE : WeilWindow.EvenSectorFloor L ((P.lamFloor : ℚ) : ℝ) := by
    intro f hf hre hev hs
    exact sector_floor_core_of rfl hS hpc hb hL1 hL2 hLl hT hβ (par := 0) (Or.inl rfl) htE hcE hgE hf
      hre (fun x => by rw [hev x]; simp [epsR]) hs
  have hO : WeilWindow.OddSectorFloor L ((P.lamFloor : ℚ) : ℝ) := by
    intro f hf hre hodd hs
    exact sector_floor_core_of rfl hS hpc hb hL1 hL2 hLl hT hβ (par := 1) (Or.inr rfl) htO hcO hgO hf
      hre (fun x => by rw [hodd x]; simp [epsR]) hs
  exact windowFloor_of_sectors hE hO

/-- A window floor with `lam >= 0` gives Weil positivity on every smaller window. -/
theorem weil_positivity_of_windowFloor {L lam : ℝ} (hlam : 0 ≤ lam) (h : WeilWindow.WindowFloor L lam)
    (g : ℝ → ℂ) (hg : WeilExplicit.IsWeilTest g) (L' : ℝ) (hL' : L' ≤ L)
    (hsupp : tsupport g ⊆ Set.Icc (-L') L') :
    0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re := by
  have hs' : tsupport g ⊆ Icc (-L) L := hsupp.trans (Icc_subset_Icc (by linarith) hL')
  have h1 := h g hg hs'
  have hm : 0 ≤ ∫ x : ℝ, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
  have h2 : (0 : ℝ) ≤ lam * ∫ x : ℝ, ‖g x‖ ^ 2 := mul_nonneg hlam hm
  rw [weilForm_autocorr_eq] at h1
  linarith

end KWin2

end
