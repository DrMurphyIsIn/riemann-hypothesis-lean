/-
  ArchS9_Prolate -- CERTIFIED EVEN PROLATE EIGEN-DATA, c = 2 pi, n = 0 .. 12
  (archimedean stage S9, rvm_bridge island, 2026-10-11).

  The operator is the time-band limiting operator of Connes-Consani arXiv:2006.13771 (68) on even
  functions, written on [0, 1] (`ArchS9.T`):  T f ω = ∫_0^1 2 cos(2 pi x ω) f(x) dx,
  with CC's normalisation ∫_0^1 ξ² = 1 (`ip ξ ξ = 1`).  For EVERY continuous unit eigenfunction
  ξ (T ξ = λ ξ) we prove:
    * `prolate_localization` : |λ| ≤ d0Q (≈ 9.70e-22) or λ lies in one of the 13 windows
      |λ - θ n| ≤ w0q n, n = 0 .. 12;
    * `prolate_window` : in window n, |λ - θ n| ≤ w2q n (≈ 6.73e-43), (ip ξ ψ_n)² ≥ pi1q n
      (1 - pi1q n ≤ 1.3e-23), and for one sign s = ±1, for all ω ∈ [0, 2]:
        |λ ξ(ω) - s θ_n ψ_n(ω)| ≤ Vq n   and   |λ ξ'(ω) - s θ_n ψ_n'(ω)| ≤ Vdq n,
      where ψ_n = `psiS n` is an explicit even polynomial of degree 78 with rational coefficients
      (`Data.tabB`), θ_n = `Data.thq n` a rational;  Vq n ≤ 1.6e-26, Vdq n ≤ 1.9e-25;
    * `prolate_simple` : two unit eigenfunctions in the same window are not orthogonal
      (each certified eigenvalue is simple).
  NOT proved here (recorded in telperion/docs/ARCH_S9_NOTES.md): EXISTENCE of an eigenfunction
  in each window (needs the spectral theorem for the compact operator T, stage S6), and the
  identification of these eigenfunctions with Slepian's PS_{2n,0}(2 pi, ·) (not needed by CC).
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS9_Frame
import ArchS9_Pi
import ArchS9_CertGram1
import ArchS9_CertGram2
import ArchS9_CertGram3
import ArchS9_CertGram4
import ArchS9_CertE
import ArchS9_CertMisc

noncomputable section

namespace ArchS9

open Real Finset MeasureTheory intervalIntegral

/-! ## A. The certified data, as real functions. -/

/-- Monomial coefficients of the certified approximate prolates. -/
def BR (n k : ℕ) : ℝ := (Data.Bq n k : ℝ)
/-- The certified eigenvalue centres θ n. -/
def thR (n : ℕ) : ℝ := (Data.thq n : ℝ)
/-- The rational Taylor coefficients aR j ≈ aC j. -/
def aRR (j : ℕ) : ℝ := (Data.aRq j : ℝ)

/-- The certified approximate prolate `ψ_n(x) = Σ_{k<40} Bq n k x^(2k)`. -/
def psiS (n : ℕ) : ℝ → ℝ := psi Data.Jd BR n
/-- Its derivative. -/
def psidS (n : ℕ) : ℝ → ℝ := psid Data.Jd BR n

lemma Jd_eq : Data.Jd = 39 + 1 := rfl

/-! ## B. Unpacking the kernel checks. -/

lemma all_range' {f : ℕ → Bool} {a b : ℕ} (h : (List.range' a b).all f = true) {i : ℕ}
    (h1 : a ≤ i) (h2 : i < a + b) : f i = true := by
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)

lemma gram_row (n : ℕ) (hn : n < Data.Jd) : Data.gramRowOK n = true := by
  have hJ : Data.Jd = 40 := rfl
  rw [hJ] at hn
  rcases lt_or_ge n 6 with h | h
  · exact all_range' Data.gram_rows_1 (by omega) (by omega)
  rcases lt_or_ge n 13 with h' | h'
  · exact all_range' Data.gram_rows_2 (by omega) (by omega)
  rcases lt_or_ge n 22 with h'' | h''
  · exact all_range' Data.gram_rows_3 (by omega) (by omega)
  · exact all_range' Data.gram_rows_4 (by omega) (by omega)

lemma e_row (j : ℕ) (hj : j < Data.Jd) : Data.eRowOK j = true := by
  have hJ : Data.Jd = 40 := rfl
  rw [hJ] at hj
  rcases lt_or_ge j 20 with h | h
  · exact all_range' Data.e_rows_1 (by omega) (by omega)
  · exact all_range' Data.e_rows_2 (by omega) (by omega)

lemma lc_dvd (d : ℕ) (hd : d < 2 * Data.Jd - 1) : (2 * d + 1) ∣ Data.Lc := by
  have h := Data.lc_ok
  unfold Data.lcOK at h
  rw [List.all_eq_true] at h
  have := h d (List.mem_range.mpr hd)
  simp only [decide_eq_true_eq] at this
  exact Nat.dvd_of_mod_eq_zero this

/-- The Boolean constant checks, unpacked. -/
lemma const_facts :
    4 * (2 * Data.piHiQ) ^ (2 * Data.Jd) / ((2 * Data.Jd).factorial : ℚ) ≤ Data.eta1Q ∧
    4 * (4 * Data.piHiQ) ^ (2 * Data.Jd) / ((2 * Data.Jd).factorial : ℚ) ≤ Data.eta2Q ∧
    8 * Data.piHiQ * (4 * Data.piHiQ) ^ (2 * Data.Jd - 1) / ((2 * Data.Jd - 1).factorial : ℚ)
      ≤ Data.etad2Q ∧
    (∑ j ∈ range Data.Jd, Data.dAq j * Data.wX 1 j) ≤ Data.dA1Q ∧
    (∑ j ∈ range Data.Jd, Data.dAq j * Data.wX 2 j) ≤ Data.dA2Q ∧
    (∑ j ∈ range Data.Jd, Data.dAq j * Data.wXd 2 j) ≤ Data.dAd2Q ∧
    (∑ j ∈ range Data.Jd, Data.eRq j * Data.wX 1 j) ≤ Data.E1Q ∧
    (∑ j ∈ range Data.Jd, Data.eRq j * Data.wX 2 j) ≤ Data.E2Q ∧
    (∑ j ∈ range Data.Jd, Data.eRq j * Data.wXd 2 j) ≤ Data.Ed2Q ∧
    Data.eta1Q + Data.dA1Q + Data.E1Q ≤ Data.zeta1Q ∧
    Data.eta2Q + Data.dA2Q + Data.E2Q ≤ Data.zeta2Q ∧
    Data.etad2Q + Data.dAd2Q + Data.Ed2Q ≤ Data.zetad2Q ∧
    (∑ n ∈ range Data.Jd, |Data.thq n|) ≤ Data.Th1Q ∧
    (Data.gamQ * Data.Th1Q + Data.zeta1Q) * (1 + Data.gamQ) ≤ Data.epsQ ∧
    Data.gamQ * (Data.Th1Q * (1 + Data.gamQ)) ^ 2 ≤ Data.CQ ∧
    0 ≤ Data.gamQ ∧ Data.gamQ < 1 / 1000 ∧ 0 ≤ Data.zeta1Q := by
  have h := Data.const_ok
  simp only [Data.constOK, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

/-! ## C. Soundness of the exact checks. -/

lemma Wz_cast (d : ℕ) (h : (2 * d + 1) ∣ Data.Lc) :
    ((Data.Wz d : ℤ) : ℚ) = (Data.Lc : ℚ) / (2 * d + 1) := by
  unfold Data.Wz
  rw [Int.cast_natCast, Nat.cast_div h (by positivity)]
  push_cast; ring

/-- The Gram entries in integers. -/
lemma gram_q (n m : ℕ) :
    (∑ k ∈ range Data.Jd, ∑ l ∈ range Data.Jd, Data.Bq n k * Data.Bq m l / (2 * k + 2 * l + 1 : ℚ))
      = (Data.gz n m : ℚ) / Data.DDL := by
  unfold Data.gz
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hk' := Finset.mem_range.mp hk
  have hl' := Finset.mem_range.mp hl
  have hdvd := lc_dvd (k + l) (by have : Data.Jd = 40 := rfl; omega)
  rw [Wz_cast _ hdvd]
  have hL : (Data.Lc : ℚ) ≠ 0 := by
    have : 0 < Data.Lc := Nat.pos_of_ne_zero (by decide)
    exact_mod_cast this.ne'
  have hDB : (Data.DB : ℚ) ≠ 0 := by unfold Data.DB; positivity
  unfold Data.Bq Data.DDL
  push_cast
  field_simp
  try ring

lemma gram_sound_le {n m : ℕ} (hnm : n ≤ m) (hm : m < Data.Jd) :
    |ip (psiS n) (psiS m) - if n = m then 1 else 0| ≤ (Data.gamQ : ℝ) := by
  have hrow := gram_row n (lt_of_le_of_lt hnm hm)
  unfold Data.gramRowOK at hrow
  have h := all_range' hrow (i := m) hnm (by omega)
  simp only [decide_eq_true_eq] at h
  have hDDL : (0 : ℚ) < Data.DDL := by unfold Data.DDL Data.DB Data.Lc; positivity
  have hq : |(Data.gz n m : ℚ) / Data.DDL - (if n = m then 1 else 0)| ≤ Data.gamQ := by
    have e : (Data.gz n m : ℚ) / Data.DDL - (if n = m then 1 else 0)
        = ((Data.gz n m : ℚ) - (if n = m then Data.DDL else 0)) / Data.DDL := by
      split_ifs
      · field_simp
      · simp
    rw [e, abs_div, abs_of_pos hDDL, div_le_iff₀ hDDL]
    exact h
  have hip : ip (psiS n) (psiS m) = (((Data.gz n m : ℚ) / Data.DDL : ℚ) : ℝ) := by
    unfold psiS
    rw [ip_psi_psi, ← gram_q]
    unfold BR
    push_cast
    rfl
  rw [hip]
  split_ifs at hq ⊢ <;> exact_mod_cast hq

theorem gram_sound {n m : ℕ} (hn : n < Data.Jd) (hm : m < Data.Jd) :
    |ip (psiS n) (psiS m) - if n = m then 1 else 0| ≤ (Data.gamQ : ℝ) := by
  rcases le_total n m with h | h
  · exact gram_sound_le h hm
  · have := gram_sound_le h hn
    rw [ip_comm]
    by_cases e : n = m
    · subst e; simpa using this
    · rw [if_neg e]; rw [if_neg (Ne.symm e)] at this; exact this

/-- The entries of `E` in integers. -/
lemma Em_eq (j k : ℕ) :
    Em Data.Jd BR thR aRR j k = (((Data.Ez j k : ℚ) / Data.EDEN : ℚ) : ℝ) := by
  have hDB : (Data.DB : ℚ) ≠ 0 := by unfold Data.DB; positivity
  have hDT : (Data.DT : ℚ) ≠ 0 := by unfold Data.DT; positivity
  have hDA : (Data.DA : ℚ) ≠ 0 := by unfold Data.DA; positivity
  have hs : (∑ n ∈ range Data.Jd, Data.thq n * Data.Bq n j * Data.Bq n k)
      = (∑ n ∈ range Data.Jd, (Data.Tz n : ℚ) * Data.Bz n j * Data.Bz n k)
          / ((Data.DT : ℚ) * (Data.DB : ℚ) ^ 2) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold Data.thq Data.Bq
    field_simp
  have hq : (if j = k then Data.aRq j else 0) - ∑ n ∈ range Data.Jd, Data.thq n * Data.Bq n j * Data.Bq n k
      = (Data.Ez j k : ℚ) / Data.EDEN := by
    rw [hs]
    unfold Data.Ez Data.EDEN Data.aRq
    push_cast
    split_ifs <;> field_simp <;> ring
  unfold Em BR thR aRR
  rw [← hq]
  push_cast
  split_ifs <;> simp

lemma Erow_sound (j : ℕ) (hj : j < Data.Jd) :
    ∑ k ∈ range Data.Jd, |Em Data.Jd BR thR aRR j k| ≤ (Data.eRq j : ℝ) := by
  have h := e_row j hj
  simp only [Data.eRowOK, decide_eq_true_eq] at h
  have hE : (0 : ℚ) < Data.EDEN := by unfold Data.EDEN Data.DA Data.DT Data.DB; positivity
  have hq : ∑ k ∈ range Data.Jd, |(Data.Ez j k : ℚ) / Data.EDEN| ≤ Data.eRq j := by
    simp_rw [abs_div, abs_of_pos hE, ← Finset.sum_div]
    rw [div_le_iff₀ hE]; exact h
  simp_rw [Em_eq]
  exact_mod_cast hq

lemma E_sound (U : ℕ → ℝ) (hU : ∀ j, 0 ≤ U j) :
    ∑ j ∈ range Data.Jd, ∑ k ∈ range Data.Jd, |Em Data.Jd BR thR aRR j k| * U j
      ≤ ∑ j ∈ range Data.Jd, (Data.eRq j : ℝ) * U j := by
  refine Finset.sum_le_sum fun j hj => ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (Erow_sound j (Finset.mem_range.mp hj)) (hU j)

/-- The pi enclosure, cast. -/
lemma piLo_lt : (Data.piLoQ : ℝ) < π := by
  have h := pi_gt_d45
  have e : (Data.piLoQ : ℝ) = (3141592653589793238462643383279502884197169399 : ℝ) / 10 ^ 45 := by
    unfold Data.piLoQ; push_cast; norm_num
  rw [e]; exact h

lemma pi_lt_Hi : π < (Data.piHiQ : ℝ) := by
  have h := pi_lt_d45
  have e : (Data.piHiQ : ℝ) = (3141592653589793238462643383279502884197169400 : ℝ) / 10 ^ 45 := by
    unfold Data.piHiQ; push_cast; norm_num
  rw [e]; exact h

lemma abs_lin_le_max {κ t a b r : ℝ} (ha : a ≤ t) (hb : t ≤ b) :
    |κ * t - r| ≤ max |κ * a - r| |κ * b - r| := by
  rcases le_total 0 κ with hk | hk
  · have h1 : κ * a ≤ κ * t := mul_le_mul_of_nonneg_left ha hk
    have h2 : κ * t ≤ κ * b := mul_le_mul_of_nonneg_left hb hk
    rw [abs_le]
    constructor
    · have := neg_abs_le (κ * a - r); have := le_max_left |κ * a - r| |κ * b - r|; linarith
    · have := le_abs_self (κ * b - r); have := le_max_right |κ * a - r| |κ * b - r|; linarith
  · have h1 : κ * t ≤ κ * a := mul_le_mul_of_nonpos_left ha hk
    have h2 : κ * b ≤ κ * t := mul_le_mul_of_nonpos_left hb hk
    rw [abs_le]
    constructor
    · have := neg_abs_le (κ * b - r); have := le_max_right |κ * a - r| |κ * b - r|; linarith
    · have := le_abs_self (κ * a - r); have := le_max_left |κ * a - r| |κ * b - r|; linarith

lemma dA_sound (j : ℕ) : |aC j - aRR j| ≤ (Data.dAq j : ℝ) := by
  have hpl := piLo_lt
  have hph := pi_lt_Hi
  have hlo0 : (0 : ℝ) ≤ Data.piLoQ := by unfold Data.piLoQ; norm_num
  set κ : ℝ := 2 * (-1) ^ j / ((2 * j).factorial : ℝ)
  have e : aC j = κ * (2 * π) ^ (2 * j) := by unfold aC; ring
  have h := abs_lin_le_max (κ := κ) (r := aRR j)
    (pow_le_pow_left₀ (by positivity) (by linarith : 2 * (Data.piLoQ : ℝ) ≤ 2 * π) (2 * j))
    (pow_le_pow_left₀ (by positivity) (by linarith : 2 * π ≤ 2 * (Data.piHiQ : ℝ)) (2 * j))
  rw [e]
  refine h.trans (le_of_eq ?_)
  unfold Data.dAq Data.aEnd aRR
  push_cast
  congr 2 <;> ring

lemma dA_total (U : ℕ → ℝ) (hU : ∀ j, 0 ≤ U j) :
    ∑ j ∈ range Data.Jd, |aC j - aRR j| * U j ≤ ∑ j ∈ range Data.Jd, (Data.dAq j : ℝ) * U j :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (dA_sound j) (hU j)

/-! ## D. The error bounds `ζ1` on [0,1], `ζ2` and `ζd2` on [0,2]. -/

lemma two_pi_le : 2 * π * 2 ≤ (2 * 39 + 1 + 1) / 2 := by
  have := pi_lt_four; nlinarith

theorem errF_le_one {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) :
    |errF Data.Jd BR thR f ω| ≤ (Data.zeta1Q : ℝ) * L1 f := by
  obtain ⟨he1, -, -, hd1, -, -, hE1, -, -, hz1, -⟩ := const_facts
  have hph := pi_lt_Hi
  have hJ : (Data.Jd : ℝ) = 40 := by norm_num [Data.Jd]
  have h := abs_errF_le Data.Jd BR thR aRR hf (X := 1) (η := Data.eta1Q) (dA := Data.dA1Q)
    (EE := Data.E1Q) (by rw [hJ]; have := pi_lt_four; nlinarith)
    (by
      have hr : ((4 * (2 * Data.piHiQ) ^ (2 * Data.Jd) / ((2 * Data.Jd).factorial : ℚ) : ℚ) : ℝ) ≤ Data.eta1Q := by exact_mod_cast he1
      refine le_trans ?_ hr
      rw [show 2 * π * 1 = 2 * π by ring]
      push_cast
      gcongr
      all_goals linarith)
    (by
      refine (dA_total _ (fun j => by positivity)).trans ?_
      have := (show ((∑ j ∈ range Data.Jd, Data.dAq j * Data.wX 1 j : ℚ) : ℝ) ≤ Data.dA1Q by
        exact_mod_cast hd1)
      push_cast [Data.wX] at this
      simpa using this)
    (by
      refine (E_sound _ (fun j => by positivity)).trans ?_
      have := (show ((∑ j ∈ range Data.Jd, Data.eRq j * Data.wX 1 j : ℚ) : ℝ) ≤ Data.E1Q by
        exact_mod_cast hE1)
      push_cast [Data.wX] at this
      simpa using this) hω hω1
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (L1_nonneg f))
  exact_mod_cast hz1

theorem errF_le_two {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : 0 ≤ ω) (hω2 : ω ≤ 2) :
    |errF Data.Jd BR thR f ω| ≤ (Data.zeta2Q : ℝ) * L1 f := by
  obtain ⟨-, he2, -, -, hd2, -, -, hE2, -, -, hz2, -⟩ := const_facts
  have hph := pi_lt_Hi
  have hJ : (Data.Jd : ℝ) = 40 := by norm_num [Data.Jd]
  have h := abs_errF_le Data.Jd BR thR aRR hf (X := 2) (η := Data.eta2Q) (dA := Data.dA2Q)
    (EE := Data.E2Q) (by rw [hJ]; have := pi_lt_four; nlinarith)
    (by
      have hr : ((4 * (4 * Data.piHiQ) ^ (2 * Data.Jd) / ((2 * Data.Jd).factorial : ℚ) : ℚ) : ℝ) ≤ Data.eta2Q := by exact_mod_cast he2
      refine le_trans ?_ hr
      rw [show 2 * π * 2 = 4 * π by ring]
      push_cast
      gcongr
      all_goals linarith)
    (by
      refine (dA_total _ (fun j => by positivity)).trans ?_
      have := (show ((∑ j ∈ range Data.Jd, Data.dAq j * Data.wX 2 j : ℚ) : ℝ) ≤ Data.dA2Q by
        exact_mod_cast hd2)
      push_cast [Data.wX] at this
      exact this)
    (by
      refine (E_sound _ (fun j => by positivity)).trans ?_
      have := (show ((∑ j ∈ range Data.Jd, Data.eRq j * Data.wX 2 j : ℚ) : ℝ) ≤ Data.E2Q by
        exact_mod_cast hE2)
      push_cast [Data.wX] at this
      exact this) hω hω2
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (L1_nonneg f))
  exact_mod_cast hz2

theorem errdF_le_two {f : ℝ → ℝ} (hf : Continuous f) {ω : ℝ} (hω : 0 ≤ ω) (hω2 : ω ≤ 2) :
    |errdF Data.Jd BR thR f ω| ≤ (Data.zetad2Q : ℝ) * L1 f := by
  obtain ⟨-, -, hed, -, -, hdd, -, -, hEd, -, -, hzd, -⟩ := const_facts
  have hph := pi_lt_Hi
  have h := abs_errdF_le Data.Jd BR thR aRR 39 Jd_eq hf (X := 2) (η := Data.etad2Q)
    (dA := Data.dAd2Q) (EE := Data.Ed2Q) (by push_cast; have := pi_lt_four; nlinarith)
    (by
      have hr : ((8 * Data.piHiQ * (4 * Data.piHiQ) ^ (2 * Data.Jd - 1)
          / ((2 * Data.Jd - 1).factorial : ℚ) : ℚ) : ℝ) ≤ Data.etad2Q := by exact_mod_cast hed
      refine le_trans ?_ hr
      have e1 : (2 * Data.Jd - 1) = 2 * 39 + 1 := rfl
      rw [e1, show 2 * π * 2 = 4 * π by ring]
      push_cast
      have hπ0 := Real.pi_pos
      gcongr <;> linarith)
    (by
      refine (dA_total _ (fun j => by positivity)).trans ?_
      have := (show ((∑ j ∈ range Data.Jd, Data.dAq j * Data.wXd 2 j : ℚ) : ℝ) ≤ Data.dAd2Q by
        exact_mod_cast hdd)
      push_cast [Data.wXd] at this
      exact this)
    (by
      refine (E_sound _ (fun j => by positivity)).trans ?_
      have := (show ((∑ j ∈ range Data.Jd, Data.eRq j * Data.wXd 2 j : ℚ) : ℝ) ≤ Data.Ed2Q by
        exact_mod_cast hEd)
      push_cast [Data.wXd] at this
      exact this) hω hω2
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (L1_nonneg f))
  exact_mod_cast hzd

/-! ## E. The certified eigen-data. -/

section Main

lemma window_facts {n : ℕ} (hn : n ≤ Data.NCw) : Data.windowOK n = true := by
  have h := Data.windows_ok
  rw [List.all_eq_true] at h
  exact h n (List.mem_range.mpr (Nat.lt_succ_of_le hn))

lemma gap_real {n : ℕ} {w : ℚ} (h : Data.gapOK n w = true) :
    ∀ m < Data.Jd, m ≠ n → 0 < |thR n - thR m| - (w : ℝ) := by
  intro m hm hmn
  unfold Data.gapOK at h
  rw [List.all_eq_true] at h
  have := h m (List.mem_range.mpr hm)
  simp only [decide_eq_true_eq] at this
  have := this hmn
  unfold thR
  exact_mod_cast this

lemma Rsum_real {n : ℕ} {w R : ℚ} (h : Data.Rsum n w ≤ R) :
    ∑ m ∈ (range Data.Jd).erase n, thR m ^ 2 * (Data.epsQ : ℝ) ^ 2 / (|thR n - thR m| - (w : ℝ)) ^ 2
      ≤ (R : ℝ) := by
  unfold Data.Rsum at h
  unfold thR
  exact_mod_cast h

variable {ξ : ℝ → ℝ} {lam : ℝ}

lemma eig_zeta (hξ : Continuous ξ) (hn : ip ξ ξ = 1) :
    ∀ ω ∈ Set.Icc (0 : ℝ) 1, |errF Data.Jd BR thR ξ ω| ≤ (Data.zeta1Q : ℝ) := by
  intro ω hω
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz0⟩ := const_facts
  have hL : L1 ξ ≤ 1 := by have := L1_le_sqrt hξ; rwa [hn, Real.sqrt_one] at this
  have hz : (0 : ℝ) ≤ Data.zeta1Q := by exact_mod_cast hz0
  refine (errF_le_one hξ hω.1 hω.2).trans ?_
  nlinarith [L1_nonneg ξ]

lemma theta_sum : ∑ n ∈ range Data.Jd, |thR n| ≤ (Data.Th1Q : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := const_facts
  unfold thR; exact_mod_cast h

lemma eig_P2 (hξ : Continuous ξ) (heig : ∀ ω, T ξ ω = lam * ξ ω) (hn : ip ξ ξ = 1) :
    ∀ m < Data.Jd, |(lam - thR m) * ip ξ (psiS m)| ≤ (Data.epsQ : ℝ) := by
  intro m hm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hε, -, hγ0, -⟩ := const_facts
  exact P2 Data.Jd BR thR hξ heig hn (by exact_mod_cast hγ0)
    (fun n hn' m hm' => gram_sound hn' hm') theta_sum (eig_zeta hξ hn) (by exact_mod_cast hε) hm

lemma eig_P3 (hξ : Continuous ξ) (heig : ∀ ω, T ξ ω = lam * ξ ω) (hn : ip ξ ξ = 1) :
    (Data.zeta1Q : ℝ) ≤ |lam| →
      (|lam| - Data.zeta1Q) ^ 2 ≤ ∑ m ∈ range Data.Jd, thR m ^ 2 * ip ξ (psiS m) ^ 2 + Data.CQ := by
  intro hl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hC, hγ0, -⟩ := const_facts
  exact P3 Data.Jd BR thR hξ heig hn (by exact_mod_cast hγ0)
    (fun n hn' m hm' => gram_sound hn' hm') theta_sum (eig_zeta hξ hn) (by exact_mod_cast hC) hl

/-- **Localization.**  Every eigenvalue of `T` (with a continuous unit eigenfunction) is either
tiny, `|λ| ≤ d0Q ≈ 9.70e-22`, or lies in one of the 13 certified windows. -/
theorem prolate_localization (hξ : Continuous ξ) (heig : ∀ ω, T ξ ω = lam * ξ ω)
    (hn : ip ξ ξ = 1) :
    |lam| ≤ (Data.d0Q : ℝ) ∨ ∃ n ≤ Data.NCw, |lam - thR n| ≤ (Data.w0q n : ℝ) := by
  by_cases h : ∃ n ≤ Data.NCw, |lam - thR n| ≤ (Data.w0q n : ℝ)
  · exact Or.inr h
  left
  push Not at h
  have hl := Data.loc_ok
  simp only [Data.locOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hl
  obtain ⟨hcut, hδ, hζ, hSA, hfin, hw0⟩ := hl
  rw [List.all_eq_true] at hcut hw0
  refine localize (J := Data.Jd) (Nc := Data.NCw) (θ := thR) (p := fun m => ip ξ (psiS m))
    (w := fun n => (Data.w0q n : ℝ)) (ε := Data.epsQ) (ζ1 := Data.zeta1Q) (C := Data.CQ)
    (θc := Data.thcQ) (SA := Data.SAQ)
    (eig_P2 hξ heig hn) (eig_P3 hξ heig hn) h
    (fun n hn' => by
      have := hw0 n (List.mem_range.mpr (Nat.lt_succ_of_le hn'))
      simp only [decide_eq_true_eq] at this; exact_mod_cast this)
    (fun m hm hlt => by
      have := hcut m (List.mem_range.mpr hm)
      simp only [decide_eq_true_eq] at this
      unfold thR; exact_mod_cast this hlt)
    (by exact_mod_cast hδ) (by exact_mod_cast hζ) ?_ (by exact_mod_cast hfin)
  have e : (∑ m ∈ range Data.Jd, (if m ≤ Data.NCw then thR m ^ 2 * (Data.epsQ : ℝ) ^ 2 /
      (Data.w0q m : ℝ) ^ 2 else thR m ^ 2 * (Data.epsQ : ℝ) ^ 2 / ((Data.d0Q : ℝ) - Data.thcQ) ^ 2))
      = ((∑ m ∈ range Data.Jd, (if m ≤ Data.NCw then Data.thq m ^ 2 * Data.epsQ ^ 2 / Data.w0q m ^ 2
      else Data.thq m ^ 2 * Data.epsQ ^ 2 / (Data.d0Q - Data.thcQ) ^ 2) : ℚ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold thR
    split_ifs <;> push_cast <;> rfl
  rw [e]
  exact_mod_cast hSA

/-- **The certified window theorem.** -/
theorem prolate_window (hξ : Continuous ξ) (heig : ∀ ω, T ξ ω = lam * ξ ω) (hn : ip ξ ξ = 1)
    {n : ℕ} (hnN : n ≤ Data.NCw) (hw : |lam - thR n| ≤ (Data.w0q n : ℝ)) :
    |lam - thR n| ≤ (Data.w2q n : ℝ) ∧ (Data.pi1q n : ℝ) ≤ ip ξ (psiS n) ^ 2 ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ω : ℝ, 0 ≤ ω → ω ≤ 2 →
        |lam * ξ ω - s * thR n * psiS n ω| ≤ (Data.Vq n : ℝ) ∧
        |lam * deriv ξ ω - s * thR n * psidS n ω| ≤ (Data.Vdq n : ℝ) := by
  have hnJ : n < Data.Jd := lt_of_le_of_lt hnN (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hγ0, hγ1, hz0⟩ := const_facts
  have hγ0r : (0 : ℝ) ≤ Data.gamQ := by exact_mod_cast hγ0
  have hz0r : (0 : ℝ) ≤ Data.zeta1Q := by exact_mod_cast hz0
  have hW := window_facts hnN
  simp only [Data.windowOK, Data.roundOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hW
  obtain ⟨g1, R1, l1, p1, p1pos, e1, w1nn, w0nn, g2, R2, l2, p2, p2pos, e2, w2nn, -, hgap2,
    hpi1le, hhalf, hV, hVd⟩ := hW
  have hP2 := eig_P2 hξ heig hn
  have hP3 := eig_P3 hξ heig hn
  have step1 := round_step (J := Data.Jd) (θ := thR) (p := fun m => ip ξ (psiS m))
    (ε := Data.epsQ) (ζ1 := Data.zeta1Q) (C := Data.CQ) (w := Data.w0q n) (R := Data.R0q n)
    (π0 := Data.pi0q n) (w1 := Data.w1q n) hnJ hP2 hP3 hw
    (gap_real g1) (Rsum_real R1) (by unfold thR; exact_mod_cast l1)
    (by unfold thR; exact_mod_cast p1) (by exact_mod_cast p1pos) (by exact_mod_cast e1)
    (by exact_mod_cast w1nn) hz0r
  have step2 := round_step (J := Data.Jd) (θ := thR) (p := fun m => ip ξ (psiS m))
    (ε := Data.epsQ) (ζ1 := Data.zeta1Q) (C := Data.CQ) (w := Data.w1q n) (R := Data.R1q n)
    (π0 := Data.pi1q n) (w1 := Data.w2q n) hnJ hP2 hP3
    step1.2 (gap_real g2) (Rsum_real R2) (by unfold thR; exact_mod_cast l2)
    (by unfold thR; exact_mod_cast p2) (by exact_mod_cast p2pos) (by exact_mod_cast e2)
    (by exact_mod_cast w2nn) hz0r
  refine ⟨step2.2, step2.1, ?_⟩
  -- the sign
  set pn := ip ξ (psiS n)
  have hpn : |pn| ≤ 1 + (Data.gamQ : ℝ) := by
    have := gram_sound hnJ hnJ
    simp only [if_true] at this
    exact P1 Data.Jd BR hξ hn hγ0r this
  have hs := abs_sub_sign_le step2.1 (by exact_mod_cast hpi1le) hγ0r hpn
  refine ⟨if 0 ≤ pn then 1 else -1, by split_ifs <;> simp, fun ω hω0 hω2 => ?_⟩
  have hL : L1 ξ ≤ 1 := by have := L1_le_sqrt hξ; rwa [hn, Real.sqrt_one] at this
  have hωa : |ω| ≤ 2 := by rw [abs_of_nonneg hω0]; exact hω2
  -- λ ≠ 0
  have hlam : lam ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hw
    have : (0 : ℝ) < |thR n| - Data.w0q n - Data.zeta1Q := by unfold thR; exact_mod_cast l1
    linarith
  constructor
  · -- values
    have hz2 : (0 : ℝ) ≤ Data.zeta2Q := by
      have : (0 : ℚ) ≤ Data.zeta2Q := by unfold Data.zeta2Q; norm_num
      exact_mod_cast this
    refine value_bound (J := Data.Jd) (θ := thR) (p := fun m => ip ξ (psiS m))
      (ψv := fun m => psiS m ω) (Ψ := fun m => (Data.PsiQ m : ℝ)) (lam := lam)
      (ε := Data.epsQ) (γ := Data.gamQ) (π1 := Data.pi1q n) (w2 := Data.w2q n)
      (ζ := Data.zeta2Q) (err := errF Data.Jd BR thR ξ ω) hnJ ?_ ?_ ?_ hP2 step2.2 (gap_real hgap2)
      hs ?_
    · rw [← heig ω]; unfold errF psiS; ring
    · refine (errF_le_two hξ hω0 hω2).trans ?_
      nlinarith [L1_nonneg ξ]
    · intro m _
      refine (abs_psi_le Data.Jd BR m hωa).trans (le_of_eq ?_)
      unfold Data.PsiQ BR
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_mul]; norm_num
    · unfold Data.valSum at hV
      unfold thR
      exact_mod_cast hV
  · -- derivatives
    have hd : deriv ξ ω = Td ξ ω / lam := (hasDerivAt_eig hξ hlam heig ω).deriv
    have hzd : (0 : ℝ) ≤ Data.zetad2Q := by
      have : (0 : ℚ) ≤ Data.zetad2Q := by unfold Data.zetad2Q; norm_num
      exact_mod_cast this
    refine value_bound (J := Data.Jd) (θ := thR) (p := fun m => ip ξ (psiS m))
      (ψv := fun m => psidS m ω) (Ψ := fun m => (Data.PsidQ m : ℝ)) (lam := lam)
      (ε := Data.epsQ) (γ := Data.gamQ) (π1 := Data.pi1q n) (w2 := Data.w2q n)
      (ζ := Data.zetad2Q) (err := errdF Data.Jd BR thR ξ ω) hnJ ?_ ?_ ?_ hP2 step2.2
      (gap_real hgap2) hs ?_
    · rw [hd, mul_div_cancel₀ _ hlam]; unfold errdF psidS psiS; ring
    · refine (errdF_le_two hξ hω0 hω2).trans ?_
      nlinarith [L1_nonneg ξ]
    · intro m _
      refine (abs_psid_le Data.Jd BR m hωa).trans (le_of_eq ?_)
      unfold Data.PsidQ BR
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · unfold Data.valSum at hVd
      unfold thR
      exact_mod_cast hVd

/-- **Simplicity.**  Two unit eigenfunctions whose eigenvalues lie in the same certified window
are not orthogonal; so each window carries a one-dimensional eigenspace. -/
theorem prolate_simple {η : ℝ → ℝ} {mu : ℝ} (hξ : Continuous ξ) (heig : ∀ ω, T ξ ω = lam * ξ ω)
    (hn : ip ξ ξ = 1) (hη : Continuous η) (heig' : ∀ ω, T η ω = mu * η ω) (hn' : ip η η = 1)
    {n : ℕ} (hnN : n ≤ Data.NCw) (hw : |lam - thR n| ≤ (Data.w0q n : ℝ))
    (hw' : |mu - thR n| ≤ (Data.w0q n : ℝ)) : ip ξ η ≠ 0 := by
  have hnJ : n < Data.Jd := lt_of_le_of_lt hnN (by decide)
  have h1 := (prolate_window hξ heig hn hnN hw).2.1
  have h2 := (prolate_window hη heig' hn' hnN hw').2.1
  have hW := window_facts hnN
  simp only [Data.windowOK, Data.roundOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hhalf, -, -⟩ := hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hγ1, -⟩ := const_facts
  have hG := gram_sound hnJ hnJ
  simp only [if_true] at hG
  exact ip_ne_zero_of_overlap hξ hη (continuous_psi Data.Jd BR n) hn hn'
    (by have h1 : ((Data.gamQ : ℚ) : ℝ) < ((1 / 1000 : ℚ) : ℝ) := Rat.cast_lt.mpr hγ1
        norm_num at h1
        linarith) hG h1 h2 (by
      have h := (Rat.cast_lt (K := ℝ)).mpr hhalf
      push_cast at h ⊢
      linarith)

end Main

end ArchS9

end
