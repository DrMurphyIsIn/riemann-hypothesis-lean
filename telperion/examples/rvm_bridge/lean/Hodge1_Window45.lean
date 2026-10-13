/-
  Hodge1_Window45 -- THE ARCHIMEDEAN STRIP INEQUALITY (ARCH) AT l = 9/20, and Weil positivity on the
  two-condition pole-free class for L <= 9/20, end to end (2026-10-12, HODGE-1 Phase 1b-A).

  conjecture1_proved = False.  (ARCH) contains no prime and no zero: it is an archimedean uncertainty
  inequality.  The positivity corollary is NOT a new positivity range: main's KWin2_BridgeHeavy already
  proves 0 <= Re weilForm (autocorr g) for every IsWeilTest g with L <= 1/2 (pole terms kept), and
  PoleFree2 is a subclass (design.md section 3(a)).  What is new is the STRUCTURE: Weil positivity
  with the prime p = 2 inside the window, proved as
      Re weilForm >= archW - (log 2/sqrt 2) int_S |g|^2        (Hodge1_Reduction: strip lemma,
                                                              n = 2 prime side, no numerics)
      archW >= (3/100) int |g|^2 + (log 2/sqrt 2) int_S |g|^2  (this file: prime-free certificate)
  i.e. "CC Theorem 1 plus one prime", with the only numerical input free of primes, and a margin of
  3/100 ||g||^2 in (ARCH).  (For scale only, a different statement: KWin2_Window920's full-class
  Weil-form floor at 9/20 is 4.5e-6 ||g||^2.)

  PROVED HERE (every numeric fact kernel-checked; Hodge1_Guard prints only propext / Classical.choice /
  Quot.sound):
    * evenStrip45 / oddStrip45: the real sector inequalities on pieces with vanishing pole functional,
        (3/100) int v^2 + w2up int_{6/25 <= |x| <= 9/20} v^2 <= archW v,
      from RbP_floor (head certificates Hodge1_Cert45E/O + projection tail) and RbP_le_archW;
    * arch_strip_window45 (ARCH WITH MARGIN): for IsWeilTest g in PoleFree2 with tsupport g in [-L, L],
      L <= 9/20:   (3/100) int |g|^2 + (log 2/sqrt 2) int_{stripSet L} |g|^2 <= archW g;
    * hArch_window45: the hypothesis hArch of Hodge1.weil_positivity_poleFree2_of_arch, discharged;
    * weil_positivity_poleFree2_window45: 0 <= Re weilForm (autocorr g) for those g.
  Side conditions (kernel + Mathlib): w2 = log 2/sqrt 2 <= 49013/100000; 6/25 <= log 2 - 9/20;
  649/500 <= log(24/2pi) - 1/24; |Psi - 649/500| <= 167/25 on [0, 24]; cosh(9/40) <= 10257/10000.
  No `sorry`.
-/
import Hodge1_ArchSectors
import Hodge1_Cert45E
import Hodge1_Cert45O
import KWin2_Consts

open Real MeasureTheory Set Finset

noncomputable section

namespace Hodge1
open KWin (Psi epsR ip continuous_v gammaUpQ logPiUpQ gamma_le log_pi_le one_le_log_pi piHiQ pi_lt_Q
  Pl continuous_Psi)
open KWin2 WeilExplicit RvMBridgeZhu RvMBridge11 RvMBridge30

/-! ## A. Rational halves of the side conditions (kernel). -/

/-- `w2 <= w2up`: `(log2S + 2^-60) / sq2lo <= 49013/100000`. -/
theorem w2up45_q : (log2S + (1 / 2) ^ 60) / sq2lo ≤ 49013 / 100000 := by decide +kernel

/-- `s0 <= log 2 - l`: `6/25 + 9/20 <= log2S - 2^-60`. -/
theorem s045_q : (6 / 25 : ℚ) + 9 / 20 ≤ log2S - (1 / 2) ^ 60 := by decide +kernel

/-- `beta0 + 1/24`, where `exp` is bounded above. -/
def qBeta45 : ℚ := P45.beta0 + 1 / 24
theorem qBeta45_le : qBeta45 / 2 ≤ 1 := by decide +kernel
theorem qBeta45_nonneg : 0 ≤ qBeta45 / 2 := by decide +kernel

/-- `exp(q/2)^2 * pi_hi <= 12` (Taylor upper bound, 12 terms). -/
theorem beta45_q : ((∑ m ∈ range 12, (qBeta45 / 2) ^ m / (m.factorial : ℚ))
    + (qBeta45 / 2) ^ 12 * (12 + 1) / ((Nat.factorial 12 : ℚ) * 12)) ^ 2 * piHiQ ≤ 12 := by
  decide +kernel

/-- `12 <= exp(2.485)` (Taylor lower bound, 30 terms). -/
theorem log12_q45 : (12 : ℚ) ≤ ∑ i ∈ range 30, (2485 / 1000 : ℚ) ^ i / (i.factorial : ℚ) := by
  decide +kernel

/-- `exp(81/3200) <= Cp` (Taylor upper bound, 4 terms): `cosh(9/40) <= exp((9/40)^2/2)`. -/
theorem cosh45_q : (∑ m ∈ range 4, (81 / 3200 : ℚ) ^ m / (m.factorial : ℚ))
    + (81 / 3200 : ℚ) ^ 4 * (4 + 1) / ((Nat.factorial 4 : ℚ) * 4) ≤ P45.Cp := by decide +kernel

/-- The two ends of `|Psi - beta0| <= S0` as rational inequalities. -/
theorem S0_lo_q45 : -(8463 / 2000 : ℚ) - logPiUpQ - P45.beta0 ≥ -P45.S0 := by decide +kernel
theorem S0_hi_q45 : (2485 / 1000 : ℚ) + 13 / 24 ^ 2 - 1 - P45.beta0 ≤ P45.S0 := by decide +kernel

/-! ## B. The real side conditions. -/

lemma P45_ell : ((P45.ell : ℚ) : ℝ) = 9 / 20 := by norm_num [P45]
lemma P45_T : ((P45.T : ℚ) : ℝ) = 24 := by norm_num [P45]
lemma lR45 : lR P45 = 9 / 20 := P45_ell
lemma TR45 : TR P45 = 24 := P45_T
lemma H45_K : H45.K = P45 := rfl

lemma w2_le_w2up45 : Real.log 2 / Real.sqrt 2 ≤ w2R H45 := by
  obtain ⟨hs1, _⟩ := sqrt2_bounds
  have hl := abs_le.mp log2_near_S
  have hslo : (0 : ℝ) < ((sq2lo : ℚ) : ℝ) := by exact_mod_cast sq2lo_pos
  have hsq : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hq := (Rat.cast_le (K := ℝ)).mpr w2up45_q
  push_cast at hq
  have hw : w2R H45 = 49013 / 100000 := by norm_num [w2R, H45]
  rw [hw]
  have h1 : Real.log 2 ≤ ((log2S : ℚ) : ℝ) + (1 / 2) ^ 60 := by linarith [hl.2]
  have h2 : Real.log 2 / Real.sqrt 2 ≤ (((log2S : ℚ) : ℝ) + (1 / 2) ^ 60) / ((sq2lo : ℚ) : ℝ) := by
    rw [div_le_div_iff₀ hsq hslo]
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc Real.log 2 * ((sq2lo : ℚ) : ℝ) ≤ Real.log 2 * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left hs1 hlog0
      _ ≤ (((log2S : ℚ) : ℝ) + (1 / 2) ^ 60) * Real.sqrt 2 := mul_le_mul_of_nonneg_right h1 hsq.le
  linarith

lemma s0R45 : s0R H45 = 6 / 25 := by norm_num [s0R, H45]

lemma s0_le_log2_45 : s0R H45 ≤ Real.log 2 - lR P45 := by
  have hl := abs_le.mp log2_near_S
  have hq := (Rat.cast_le (K := ℝ)).mpr s045_q
  push_cast at hq
  rw [s0R45, lR45]
  linarith [hl.1]

/-- **`beta0 <= log(24/2pi) - 1/24`.** -/
theorem beta0_le_env45 : b0R P45 ≤ Real.log (TR P45 / (2 * Real.pi)) - 1 / TR P45 := by
  rw [TR45]
  have hq : ((qBeta45 : ℚ) : ℝ) ≤ Real.log (24 / (2 * Real.pi)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have hx0 : 0 ≤ ((qBeta45 : ℚ) : ℝ) / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr qBeta45_nonneg; push_cast at this; exact this
    have hx1 : ((qBeta45 : ℚ) : ℝ) / 2 ≤ 1 := by
      have := (Rat.cast_le (K := ℝ)).mpr qBeta45_le; push_cast at this; exact this
    have e1 : Real.exp ((qBeta45 : ℚ) : ℝ) = Real.exp (((qBeta45 : ℚ) : ℝ) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e2 := Real.exp_bound' hx0 hx1 (n := 12) (by norm_num)
    have hTq := (Rat.cast_le (K := ℝ)).mpr beta45_q
    push_cast at hTq e2
    set Ts : ℝ := (∑ m ∈ range 12, (((qBeta45 : ℚ) : ℝ) / 2) ^ m / (m.factorial : ℝ))
      + (((qBeta45 : ℚ) : ℝ) / 2) ^ 12 * (12 + 1) / ((Nat.factorial 12 : ℝ) * 12) with hTs
    have hpos : 0 ≤ Real.exp (((qBeta45 : ℚ) : ℝ) / 2) := (Real.exp_pos _).le
    have hsq : Real.exp (((qBeta45 : ℚ) : ℝ) / 2) ^ 2 ≤ Ts ^ 2 := pow_le_pow_left₀ hpos e2 2
    have hpi := pi_lt_Q
    have hpi0 := Real.pi_pos
    rw [e1, show (24 : ℝ) / (2 * Real.pi) = 12 / Real.pi by field_simp; ring, le_div_iff₀ hpi0]
    have h1 : Real.exp (((qBeta45 : ℚ) : ℝ) / 2) ^ 2 * Real.pi ≤ Ts ^ 2 * Real.pi :=
      mul_le_mul_of_nonneg_right hsq hpi0.le
    have h2 : Ts ^ 2 * Real.pi ≤ Ts ^ 2 * ((piHiQ : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hpi.le (sq_nonneg _)
    linarith
  have hqd : ((qBeta45 : ℚ) : ℝ) = b0R P45 + 1 / 24 := by
    unfold qBeta45 b0R; push_cast; ring
  rw [hqd] at hq
  linarith

/-- **`|Psi - beta0| <= S0` on `[0, 24]`.** -/
theorem sym_bound45 : ∀ t, 0 ≤ t → t ≤ TR P45 → |Psi t - b0R P45| ≤ ((P45.S0 : ℚ) : ℝ) := by
  intro t ht0 htT
  rw [TR45] at htT
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
      have := (Rat.cast_le (K := ℝ)).mpr log12_q45
      push_cast at this
      exact this
    linarith
  have hlp := log_pi_le
  have hlp1 := one_le_log_pi
  have hlo := (Rat.cast_le (K := ℝ)).mpr S0_lo_q45
  have hhi := (Rat.cast_le (K := ℝ)).mpr S0_hi_q45
  push_cast at hlo hhi
  unfold b0R
  rw [abs_le]
  constructor <;> nlinarith

/-- **`cosh(l/2) <= Cp`.** -/
theorem cosh45 : Real.cosh (lR P45 / 2) ≤ ((P45.Cp : ℚ) : ℝ) := by
  rw [lR45]
  have h := Real.cosh_le_exp_half_sq ((9 / 20 : ℝ) / 2)
  have hx : ((9 / 20 : ℝ) / 2) ^ 2 / 2 = 81 / 3200 := by norm_num
  rw [hx] at h
  have e2 := Real.exp_bound' (x := 81 / 3200) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  have hq := (Rat.cast_le (K := ℝ)).mpr cosh45_q
  push_cast at hq
  linarith

lemma a0_45 : |(0 : ℝ) - ((P45.a0 : ℚ) : ℝ)| ≤ ((P45.da : ℚ) : ℝ) := by norm_num [P45]
lemma c0_45 : |(0 : ℝ) - ((P45.c0 : ℚ) : ℝ)| ≤ ((P45.dc : ℚ) : ℝ) := by norm_num [P45]

/-- **The symbol hypotheses at l = 9/20** for the archimedean symbol Psi (no comb). -/
theorem symHyp45 : SymHyp P45 Psi where
  cont := continuous_Psi
  bound := sym_bound45
  minor := by
    intro i hi t hti hti'
    have h := sym_minorant P45 brk45 piece45 min45 comb45 gamma_le log_pi_le a0_45 c0_45 hi hti hti'
    simpa using h
  cosh := cosh45

/-! ## C. The real sector inequalities. -/

lemma lamFloor45_cast : ((P45.lamFloor : ℚ) : ℝ) = 3 / 100 := by norm_num [P45]

/-- The common core of both sectors: the strip sector floor plus the archimedean split. -/
theorem strip_sector_core45 {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam eta : ℚ}
    (htail : tailCondP H45 par N lam eta = true) {D : List (List ℚ)}
    (hcert : psdCertR (headMatP H45 par N lam eta D) N R45 = true) (hginv : ginvCheck P45 par N = true)
    {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u)
    (hs : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-lR P45) (lR P45)) (hPl : Pl (lR P45) par v = 0) :
    (3 / 100 : ℝ) * (∫ x, v x ^ 2) + w2R H45 * Sform (s0R H45) (lR P45) v v
      ≤ ArchS3.archW (fun u => (v u : ℂ)) := by
  have hl : (0 : ℝ) < lR P45 := lR_pos P45 par45
  have hR := RbP_floor H45 symHyp45 par45 brk45 hpar htail (headPSD_of_psdCertR hcert) hginv
    (continuous_v hf)
  have hA := RbP_le_archW H45 par45 (by rw [H45_K, TR45]; norm_num) beta0_le_env45 hpar hf hev le_rfl hs hPl
  have hip : ip (lR P45) v v = ∫ x, v x ^ 2 := by
    unfold ip
    rw [← integral_eq_interval' hf hl le_rfl hs]
    congr 1; funext x; ring
  rw [H45_K, lamFloor45_cast, hip] at hR
  linarith

theorem evenStrip45 : ∀ v : ℝ → ℝ, IsWeilTest (fun u => (v u : ℂ)) → (∀ u, v (-u) = v u) →
    tsupport (fun u => (v u : ℂ)) ⊆ Icc (-lR P45) (lR P45) → Pl (lR P45) 0 v = 0 →
    (3 / 100 : ℝ) * (∫ x, v x ^ 2) + w2R H45 * Sform (s0R H45) (lR P45) v v
      ≤ ArchS3.archW (fun u => (v u : ℂ)) := by
  intro v hf hev hs hPl
  exact strip_sector_core45 (par := 0) (N := NE45) (Or.inl rfl) tailE45 certE45 ginvE45 hf
    (fun u => by rw [hev u]; simp [epsR]) hs hPl

theorem oddStrip45 : ∀ v : ℝ → ℝ, IsWeilTest (fun u => (v u : ℂ)) → (∀ u, v (-u) = -v u) →
    tsupport (fun u => (v u : ℂ)) ⊆ Icc (-lR P45) (lR P45) → Pl (lR P45) 1 v = 0 →
    (3 / 100 : ℝ) * (∫ x, v x ^ 2) + w2R H45 * Sform (s0R H45) (lR P45) v v
      ≤ ArchS3.archW (fun u => (v u : ℂ)) := by
  intro v hf hodd hs hPl
  exact strip_sector_core45 (par := 1) (N := NO45) (Or.inr rfl) tailO45 certO45 ginvO45 hf
    (fun u => by rw [hodd u]; simp [epsR]) hs hPl

/-! ## D. (ARCH) with margin, and the Weil positivity corollary. -/

/-- **(ARCH) AT l = 9/20, WITH MARGIN.** For every smooth compactly supported g on the two-condition
pole-free class (int g e^{u/2} = int g e^{-u/2} = 0) supported in [-L, L], L <= 9/20:
    (3/100) int |g|^2 + (log 2 / sqrt 2) int_{stripSet L} |g|^2 <= archW g.
No prime and no zero enters: this is a statement about the archimedean form alone. -/
theorem arch_strip_window45 (g : ℝ → ℂ) (hg : IsWeilTest g) (hP : PoleFree2 g) (L : ℝ)
    (hL : L ≤ 9 / 20) (hsupp : tsupport g ⊆ Icc (-L) L) :
    (3 / 100 : ℝ) * (∫ x, ‖g x‖ ^ 2) + (Real.log 2 / Real.sqrt 2) * ∫ u in stripSet L, ‖g u‖ ^ 2
      ≤ ArchS3.archW g := by
  have hl : (0 : ℝ) < lR P45 := lR_pos P45 par45
  have hLl : L ≤ lR P45 := by rw [lR45]; exact hL
  have hs' : tsupport g ⊆ Icc (-lR P45) (lR P45) := hsupp.trans (Icc_subset_Icc (by linarith) hLl)
  have hmain := archW_ge_of_sectors hl evenStrip45 oddStrip45 hg hP hs'
  have hs0 : (0 : ℝ) < s0R H45 := by rw [s0R45]; norm_num
  have hs0l : s0R H45 ≤ lR P45 := by rw [s0R45, lR45]; norm_num
  have hstrip := stripSet_le_SformC hg hLl hs0 s0_le_log2_45 hs0l
  have hS0 : 0 ≤ SformC (s0R H45) (lR P45) g :=
    intervalIntegral.integral_nonneg hs0l fun x _ => by positivity
  have hset0 : 0 ≤ ∫ u in stripSet L, ‖g u‖ ^ 2 := setIntegral_nonneg (measurableSet_stripSet L)
    fun x _ => by positivity
  have hw := w2_le_w2up45
  have hw0 : 0 ≤ Real.log 2 / Real.sqrt 2 := w2_nonneg
  have h1 : (Real.log 2 / Real.sqrt 2) * ∫ u in stripSet L, ‖g u‖ ^ 2
      ≤ (Real.log 2 / Real.sqrt 2) * SformC (s0R H45) (lR P45) g :=
    mul_le_mul_of_nonneg_left hstrip hw0
  have h2 : (Real.log 2 / Real.sqrt 2) * SformC (s0R H45) (lR P45) g
      ≤ w2R H45 * SformC (s0R H45) (lR P45) g := mul_le_mul_of_nonneg_right hw hS0
  linarith

/-- **hArch discharged at l = 9/20**: the hypothesis of `weil_positivity_poleFree2_of_arch`. -/
theorem hArch_window45 (g : ℝ → ℂ) (hg : IsWeilTest g) (hP : PoleFree2 g) (L : ℝ) (hL : L ≤ 9 / 20)
    (hsupp : tsupport g ⊆ Icc (-L) L) :
    (Real.log 2 / Real.sqrt 2) * ∫ u in stripSet L, ‖g u‖ ^ 2 ≤ ArchS3.archW g := by
  have h := arch_strip_window45 g hg hP L hL hsupp
  have hm : 0 ≤ (3 / 100 : ℝ) * (∫ x, ‖g x‖ ^ 2) :=
    mul_nonneg (by norm_num) (integral_nonneg fun x => by positivity)
  linarith

lemma twoL_le_log_three45 {L : ℝ} (hL : L ≤ 9 / 20) : 2 * L ≤ Real.log 3 := by
  have h : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  linarith

/-- **WEIL POSITIVITY ON THE TWO-CONDITION POLE-FREE CLASS FOR L <= 9/20**, with the prime p = 2
inside the window when (log 2)/2 < L: the strip reduction (Hodge1_Reduction) plus (ARCH)
(arch_strip_window45).  No lower bound on L is needed. -/
theorem weil_positivity_poleFree2_window45 (g : ℝ → ℂ) (hg : IsWeilTest g) (hP : PoleFree2 g)
    (L : ℝ) (hL : L ≤ 9 / 20) (hsupp : tsupport g ⊆ Icc (-L) L) :
    0 ≤ (weilForm (autocorr g)).re :=
  weil_positivity_poleFree2_of_arch hg hsupp (twoL_le_log_three45 hL) hP
    (hArch_window45 g hg hP L hL hsupp)

end Hodge1

end
