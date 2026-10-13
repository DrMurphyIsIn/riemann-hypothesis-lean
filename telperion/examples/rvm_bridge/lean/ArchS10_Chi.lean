/-
  ArchS10_Chi -- stage S10 of the archimedean conceptual blueprint (2026-10-11), the assembly:
  a CERTIFIED ENCLOSURE OF CONNES-CONSANI'S KERNEL χ ON [0, log 2] (arXiv:2006.13771, (104)).

  Input: S8's abstract `D : ArchS8.ProlateDataNat` (= ProlateData ℕ) together with `CertBasis D`, which says that the
  `D.phi n` are an orthonormal family (on [0,1]) of everywhere-eigenfunctions of S9's operator
  T f(ω) = ∫_0^1 2cos(2πxω) f(x) dx with eigenvalues `D.lam n`, the first 13 of which lie in S9's
  windows (n ≤ 12), and that `D.T > log 2`.  This is exactly what S6's eigenbasis, enumerated with
  S9's completeness theorem, provides.  NO bound on the eigenfunctions of index n > 12 is assumed:
  their eigenvalues are ≤ d0Q ≈ 9.7e-22 by S9's localization + simplicity + orthogonality
  (`tail_small`), and their contribution is bounded by Bessel (ArchS10_Tail).

  Results (namespace `ArchS10`):
    eps1_enclosure   |ε'(1⁺) - EQ| ≤ deltaE,  EQ = 22.99647568387053…, deltaE = 1.19e-22
    eps1_pos         0 < ε'(1⁺)       (so S8's `prop55_KI` applies)
    Qeps_expsum      |(Qε)(e^t) - Σ_{l<40} d_l (e^{(2l+1/2)t} - e^{-(2l+1/2)t})| ≤ dQtot = 6.45e-6
    Qeps_poly        |(Qε)(e^t) - P(t)| ≤ dQtot + deltaP           (t ∈ [0, log 2])
    chi_enclosure    |χ(v) - chiPoly v| ≤ deltaChi = 1.41e-7        (|v| ≤ log 2)
    chi_L1           ∫_0^{log 2} |χ - chiPoly| ≤ deltaChi · log 2
    chiPoly_zero     chiPoly 0 = 0 = χ(0)                          (CC Rem 5.6 consistency)
  where chiPoly v = Σ_{i<67} chiCo i |v|^i with explicit rational coefficients `Data.chiCo`
  (only odd i are nonzero).  All constants are checked by `decide +kernel` in ArchS10_Cert.
  No sorry, no axiom.  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS10_Tail
import ArchS8_Kernel

open MeasureTheory Set Finset
open scoped Interval

noncomputable section

namespace ArchS10

open ArchS9

/-! ## The hypotheses on `D`. -/

/-- What S6 (+ S9 completeness) must supply about `D`: an orthonormal family of eigenfunctions of
`T`, the first 13 in S9's windows, and the additive range covering `[0, log 2]`. -/
structure CertBasis (D : ArchS8.ProlateDataNat) : Prop where
  eig : ∀ n ω, T (D.phi n) ω = D.lam n * D.phi n ω
  orth : ∀ n m, ip (D.phi n) (D.phi m) = if n = m then 1 else 0
  window : ∀ n ≤ Data.NCw, |D.lam n - thR n| ≤ (Data.w0q n : ℝ)
  T_gt : Real.log 2 < D.T

variable {D : ArchS8.ProlateDataNat}

namespace CertBasis

variable (hB : CertBasis D)
include hB

set_option linter.unusedSectionVars false in
lemma cont (n : ℕ) : Continuous (D.phi n) := D.cont_phi n

lemma unit (n : ℕ) : ip (D.phi n) (D.phi n) = 1 := by rw [hB.orth]; simp

/-- `λ φ' = Td φ` everywhere (also when `λ = 0`). -/
lemma lam_deriv (n : ℕ) (ω : ℝ) : D.lam n * deriv (D.phi n) ω = Td (D.phi n) ω := by
  by_cases hl : D.lam n = 0
  · have hT : T (D.phi n) = fun _ => 0 := funext fun w => by rw [hB.eig, hl, zero_mul]
    have h := hasDerivAt_T (hB.cont n) ω
    rw [hT] at h
    rw [hl, zero_mul, h.unique (hasDerivAt_const ω 0)]
  · rw [(hasDerivAt_eig (hB.cont n) hl (hB.eig n) ω).deriv]
    field_simp

/-- `w_n C_n = C(λφ, λφ')/(1 - λ²) = C(Tφ, Tdφ)/(1 - λ²)`. -/
lemma wC_eq (n : ℕ) (t : ℝ) :
    D.w n * D.Cn n t = CC (T (D.phi n)) (Td (D.phi n)) t / (1 - D.lam n ^ 2) := by
  have h1 : T (D.phi n) = fun x => D.lam n * D.phi n x := funext (hB.eig n)
  have h2 : Td (D.phi n) = fun x => D.lam n * deriv (D.phi n) x :=
    funext fun x => (hB.lam_deriv n x).symm
  rw [h1, h2, CC_smul, Cn_eq_CC]
  unfold ArchS8.ProlateData.w
  ring

lemma w_phi_one (n : ℕ) :
    D.w n * D.phi n 1 ^ 2 = T (D.phi n) 1 ^ 2 / (1 - D.lam n ^ 2) := by
  rw [hB.eig]; unfold ArchS8.ProlateData.w; ring

/-- Every index `n > 12` has `|λ_n| ≤ d0Q`: it is not in a window (simplicity + orthogonality). -/
lemma tail_small {n : ℕ} (hn : Data.NCw < n) : |D.lam n| ≤ (Data.d0Q : ℝ) := by
  rcases prolate_localization (hB.cont n) (hB.eig n) (hB.unit n) with h | ⟨m, hm, hw⟩
  · exact h
  · exfalso
    have := prolate_simple (hB.cont n) (hB.eig n) (hB.unit n) (hB.cont m) (hB.eig m) (hB.unit m)
      hm hw (hB.window m hm)
    rw [hB.orth, if_neg (by omega)] at this
    exact this rfl

lemma tailFam : TailFam (fun k => D.phi (k + (Data.NCw + 1))) (fun k => D.lam (k + (Data.NCw + 1))) where
  cont k := hB.cont _
  eig k := hB.eig _
  orth k l := by
    rw [hB.orth]
    by_cases h : k = l
    · simp [h]
    · rw [if_neg h, if_neg (by omega)]
  small k := hB.tail_small (by omega)

end CertBasis

/-! ## Generic algebra. -/

lemma div_perturb {a b lam th w2 e B : ℝ} (hlam : |lam - th| ≤ w2) (hlo0 : 0 < 1 - (|th| + w2) ^ 2)
    (hth : th ^ 2 < 1) (hab : |a - b| ≤ e) (hb : |b| ≤ B) :
    |a / (1 - lam ^ 2) - b / (1 - th ^ 2)|
      ≤ e / (1 - (|th| + w2) ^ 2)
        + B * (w2 * (2 * |th| + w2)) / ((1 - (|th| + w2) ^ 2) * (1 - th ^ 2)) := by
  set lo := 1 - (|th| + w2) ^ 2
  have hw0 : 0 ≤ w2 := (abs_nonneg _).trans hlam
  have hlabs : |lam| ≤ |th| + w2 := by
    have := abs_sub_abs_le_abs_sub lam th; linarith
  have hl2 : lam ^ 2 ≤ (|th| + w2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hlabs 2
  have hden1 : lo ≤ 1 - lam ^ 2 := by simp only [lo]; linarith
  have hd1 : 0 < 1 - lam ^ 2 := lt_of_lt_of_le hlo0 hden1
  have hd2 : 0 < 1 - th ^ 2 := by linarith
  have hsq : |lam ^ 2 - th ^ 2| ≤ w2 * (2 * |th| + w2) := by
    have e1 : lam ^ 2 - th ^ 2 = (lam - th) * (lam + th) := by ring
    rw [e1, abs_mul]
    have : |lam + th| ≤ 2 * |th| + w2 := by
      have := abs_add_le lam th; linarith
    exact mul_le_mul hlam this (abs_nonneg _) hw0
  have e2 : a / (1 - lam ^ 2) - b / (1 - th ^ 2)
      = (a - b) / (1 - lam ^ 2) + b * (lam ^ 2 - th ^ 2) / ((1 - lam ^ 2) * (1 - th ^ 2)) := by
    field_simp; ring
  rw [e2]
  have he0 : 0 ≤ e := (abs_nonneg _).trans hab
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hb
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hd1]
    exact div_le_div₀ he0 hab hlo0 hden1
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hd1 hd2)]
    apply div_le_div₀ (by positivity) (mul_le_mul hb hsq (abs_nonneg _) hB0) (by positivity)
    exact mul_le_mul_of_nonneg_right hden1 hd2.le

/-! ## Unpacking the head checks. -/

/-- `θ_n²/(1 - θ_n²)`. -/
def Wth (n : ℕ) : ℝ := thR n ^ 2 / (1 - thR n ^ 2)

lemma head_facts {n : ℕ} (hn : n ≤ Data.NCw) :
    0 < 1 - (|thR n| + Data.w2q n) ^ 2 ∧ thR n ^ 2 < 1 ∧
    (4 * (Data.Vdq n * (|thR n| * Data.PsidQ n + Data.Vdq n) + |thR n| * Data.PsidQ n * Data.Vdq n)
        + (Data.Vdq n * (|thR n| * Data.PsiQ n + Data.Vq n) + |thR n| * Data.PsidQ n * Data.Vq n)
        + 4 * (Data.Vq n * (|thR n| * Data.PsidQ n + Data.Vdq n) + |thR n| * Data.PsiQ n * Data.Vdq n)
        : ℝ) / (1 - (|thR n| + Data.w2q n) ^ 2)
      + (4 * (|thR n| * Data.PsidQ n) ^ 2 + 5 * (|thR n| * Data.PsiQ n) * (|thR n| * Data.PsidQ n))
        * (Data.w2q n * (2 * |thR n| + Data.w2q n))
        / ((1 - (|thR n| + Data.w2q n) ^ 2) * (1 - thR n ^ 2)) ≤ (ArchS10.Data.errHq n : ℝ) ∧
    (Data.Vq n * (2 * |thR n * ∑ k ∈ range Data.Jd, BR n k| + Data.Vq n) : ℝ)
        / (1 - (|thR n| + Data.w2q n) ^ 2)
      + |thR n * ∑ k ∈ range Data.Jd, BR n k| ^ 2 * (Data.w2q n * (2 * |thR n| + Data.w2q n))
        / ((1 - (|thR n| + Data.w2q n) ^ 2) * (1 - thR n ^ 2)) ≤ (ArchS10.Data.errEq n : ℝ) := by
  have h := ArchS10.Data.head_ok
  simp only [ArchS10.Data.headOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h n (Nat.lt_succ_of_le hn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (Rat.cast_lt (K := ℝ)).2 h1
    unfold ArchS10.Data.loq at this; push_cast at this; unfold thR; exact this
  · have := (Rat.cast_lt (K := ℝ)).2 h2
    push_cast at this; unfold thR; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h3
    unfold ArchS10.Data.bndq ArchS10.Data.loq ArchS10.Data.G0q ArchS10.Data.G1q at this
    push_cast at this; unfold thR; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h4
    unfold ArchS10.Data.loq ArchS10.Data.gq ArchS10.Data.psi1q at this
    push_cast at this; unfold thR BR; exact this

lemma hhq_cast (n l : ℕ) (hl : l < Data.Jd) :
    ((ArchS10.Data.hhq n l : ℚ) : ℝ) = hhR Data.Jd BR n l := by
  have hL : (Data.Lc : ℚ) ≠ 0 := by
    have : 0 < Data.Lc := Nat.pos_of_ne_zero (by decide)
    exact_mod_cast this.ne'
  have hDB : (Data.DB : ℚ) ≠ 0 := by unfold Data.DB; positivity
  have hq : ArchS10.Data.hhq n l = (∑ k ∈ range Data.Jd, 4 * (k : ℚ) * l * Data.Bq n k * Data.Bq n l
        / (2 * k + 2 * l + 1)) - (∑ k ∈ range Data.Jd, Data.Bq n k) * (2 * l) * Data.Bq n l := by
    unfold ArchS10.Data.hhq ArchS10.Data.hhz
    push_cast
    rw [sub_div, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [Wz_cast _ (lc_dvd (k + l) (by have : Data.Jd = 40 := rfl; omega))]
      unfold Data.Bq
      field_simp
      push_cast; ring
    · unfold Data.Bq
      rw [← Finset.sum_div]
      field_simp
  rw [hq]; unfold hhR BR; push_cast; rfl

lemma round_facts {n l : ℕ} (hn : n < ArchS10.Data.NH) (hl : l < Data.Jd) :
    |Wth n * hhR Data.Jd BR n l - (ArchS10.Data.Dq n l : ℝ)| ≤ (ArchS10.Data.eDQ : ℝ) := by
  have h := ArchS10.Data.round_ok
  simp only [List.all_eq_true, List.mem_range] at h
  have h2 := h n hn
  simp only [ArchS10.Data.roundRowOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h2
  have h3 := (Rat.cast_le (K := ℝ)).2 (h2 l hl)
  push_cast at h3
  rw [← hhq_cast n l hl]
  unfold Wth thR
  unfold ArchS10.Data.Wthq at h3
  push_cast at h3
  exact h3

/-! ## The head, term by term. -/

lemma abs_psidS_le_two' (m : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h2 : ω ≤ 2) :
    |psidS m ω| ≤ (Data.PsidQ m : ℝ) := abs_psidS_le_two m h0 h2

/-- **Head, one term**: `|w_n C_n(t) - θ²/(1-θ²) Σ_l hh_{n,l} ex_l(t)| ≤ errHq n` on `[0, log 2]`. -/
theorem head_term (hB : CertBasis D) {n : ℕ} (hn : n ≤ Data.NCw) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ Real.log 2) :
    |D.w n * D.Cn n t - Wth n * ∑ l ∈ range Data.Jd, hhR Data.Jd BR n l * ex l t|
      ≤ (ArchS10.Data.errHq n : ℝ) := by
  obtain ⟨hlo, hth, hH, -⟩ := head_facts hn
  obtain ⟨hw2, -, s, hs, hval⟩ := prolate_window (hB.cont n) (hB.eig n) (hB.unit n) hn
    (hB.window n hn)
  have hs1 : |s| = 1 := by rcases hs with h | h <;> simp [h]
  have hs2 : s ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  set g : ℝ → ℝ := fun x => (s * thR n) * psiS n x with hg
  set g' : ℝ → ℝ := fun x => (s * thR n) * psidS n x with hg'
  have cg' : Continuous g' := continuous_const.mul (by
    unfold psidS psid; fun_prop)
  have h0 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |T (D.phi n) x - g x| ≤ (Data.Vq n : ℝ) := fun x hx => by
    rw [hB.eig]; exact (hval x (by linarith [hx.1]) hx.2).1
  have h1 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |Td (D.phi n) x - g' x| ≤ (Data.Vdq n : ℝ) := fun x hx => by
    rw [← hB.lam_deriv]; exact (hval x (by linarith [hx.1]) hx.2).2
  have hG0 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |g x| ≤ |thR n| * Data.PsiQ n := fun x hx => by
    simp only [hg, abs_mul, hs1, one_mul]
    exact mul_le_mul_of_nonneg_left (abs_psiS_le_two n (by linarith [hx.1]) hx.2) (abs_nonneg _)
  have hG1 : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |g' x| ≤ |thR n| * Data.PsidQ n := fun x hx => by
    simp only [hg', abs_mul, hs1, one_mul]
    exact mul_le_mul_of_nonneg_left (abs_psidS_le_two n (by linarith [hx.1]) hx.2) (abs_nonneg _)
  have hpert := abs_CC_sub_le (continuous_Td (hB.cont n)) cg' h0 h1 hG0 hG1 ht0 ht
  have hsize := abs_CC_le cg' hG0 hG1 ht0 ht
  have hCg : CC g g' t = thR n ^ 2 * ∑ l ∈ range Data.Jd, hhR Data.Jd BR n l * ex l t := by
    rw [hg, hg', CC_smul]
    unfold psiS psidS
    rw [CC_psi, mul_pow, hs2, one_mul]
  have hmain : Wth n * ∑ l ∈ range Data.Jd, hhR Data.Jd BR n l * ex l t
      = CC g g' t / (1 - thR n ^ 2) := by
    rw [hCg]; unfold Wth; ring
  rw [hB.wC_eq, hmain]
  have hw0 := hB.window n hn
  have hw2' : |D.lam n - thR n| ≤ (Data.w2q n : ℝ) := hw2
  exact (div_perturb hw2' hlo hth hpert hsize).trans hH

/-- **Head of ε'(1⁺), one term**. -/
theorem head_eps_term (hB : CertBasis D) {n : ℕ} (hn : n ≤ Data.NCw) :
    |D.w n * D.phi n 1 ^ 2 - Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2| ≤ (ArchS10.Data.errEq n : ℝ) := by
  obtain ⟨hlo, hth, -, hE⟩ := head_facts hn
  obtain ⟨hw2, -, s, hs, hval⟩ := prolate_window (hB.cont n) (hB.eig n) (hB.unit n) hn
    (hB.window n hn)
  have hs1 : |s| = 1 := by rcases hs with h | h <;> simp [h]
  have hs2 : s ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  set gv := s * thR n * psiS n 1
  have hp1 : psiS n 1 = ∑ k ∈ range Data.Jd, BR n k := by unfold psiS; exact psi_one _ _ _
  have hgv : |gv| = |thR n * ∑ k ∈ range Data.Jd, BR n k| := by
    simp only [gv, abs_mul, hs1, one_mul, hp1]
  have hv : |T (D.phi n) 1 - gv| ≤ (Data.Vq n : ℝ) := by
    rw [hB.eig]; exact (hval 1 (by norm_num) (by norm_num)).1
  have hab := abs_mul_sub_mul_le hv hv (le_of_eq hgv) (le_of_eq hgv)
  have hb : |gv * gv| ≤ |thR n * ∑ k ∈ range Data.Jd, BR n k| ^ 2 := by
    rw [abs_mul, hgv, sq]
  have hmain : Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2 = gv * gv / (1 - thR n ^ 2) := by
    simp only [gv, hp1]
    unfold Wth
    rw [show s * thR n * (∑ k ∈ range Data.Jd, BR n k) * (s * thR n * (∑ k ∈ range Data.Jd, BR n k))
        = s ^ 2 * (thR n ^ 2 * (∑ k ∈ range Data.Jd, BR n k) ^ 2) by ring, hs2, one_mul]
    ring
  rw [hB.w_phi_one, hmain, sq]
  refine (div_perturb hw2 hlo hth hab hb).trans (le_of_eq_of_le ?_ hE)
  ring

/-! ## The series. -/

lemma summable_wC (D : ArchS8.ProlateDataNat) {t : ℝ} (ht : t ∈ Ioo (-D.T) D.T) :
    Summable fun n => D.w n * D.Cn n t := by
  refine Summable.of_norm_bounded (D.summable_wB.mul_left (5 / 4)) fun n => ?_
  obtain ⟨h0, -, h2⟩ := D.norm_w_le n ht
  rw [← D.Qkn_eq_Cn]
  have e : D.w n * (-(D.kn2 n t) + D.kn n t / 4) = -(D.w n * D.kn2 n t) + (D.w n * D.kn n t) / 4 := by
    ring
  rw [e]
  calc ‖-(D.w n * D.kn2 n t) + (D.w n * D.kn n t) / 4‖
      ≤ ‖D.w n * D.kn2 n t‖ + ‖D.w n * D.kn n t‖ / 4 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg, norm_div]; simp
    _ ≤ D.w n * D.B n + D.w n * D.B n / 4 := by gcongr
    _ = 5 / 4 * (D.w n * D.B n) := by ring

/-- The head coefficient `d_l = Σ_{n≤12} Dq n l` as a real. -/
def dR (l : ℕ) : ℝ := (ArchS10.Data.dq l : ℝ)

lemma NH_eq : ArchS10.Data.NH = Data.NCw + 1 := rfl

theorem head_sum (hB : CertBasis D) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |∑ n ∈ range (Data.NCw + 1), D.w n * D.Cn n t - ∑ l ∈ range Data.Jd, dR l * ex l t|
      ≤ (∑ n ∈ range ArchS10.Data.NH, (ArchS10.Data.errHq n : ℝ))
        + ∑ l ∈ range Data.Jd, (ArchS10.Data.NH : ℝ) * ArchS10.Data.eDQ * (2 ^ (2 * l + 1) + 1) := by
  set M : ℕ → ℝ := fun n => Wth n * ∑ l ∈ range Data.Jd, hhR Data.Jd BR n l * ex l t
  have e1 : ∑ n ∈ range (Data.NCw + 1), D.w n * D.Cn n t - ∑ l ∈ range Data.Jd, dR l * ex l t
      = ∑ n ∈ range (Data.NCw + 1), (D.w n * D.Cn n t - M n)
        + ∑ l ∈ range Data.Jd, (∑ n ∈ range (Data.NCw + 1), Wth n * hhR Data.Jd BR n l - dR l)
          * ex l t := by
    have : ∑ n ∈ range (Data.NCw + 1), M n
        = ∑ l ∈ range Data.Jd, (∑ n ∈ range (Data.NCw + 1), Wth n * hhR Data.Jd BR n l) * ex l t := by
      simp only [M, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [Finset.sum_sub_distrib, this]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [e1, ← NH_eq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    exact head_term hB (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) ht0 ht
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    have hl' := Finset.mem_range.mp hl
    rw [abs_mul]
    have hd : |∑ n ∈ range ArchS10.Data.NH, Wth n * hhR Data.Jd BR n l - dR l|
        ≤ (ArchS10.Data.NH : ℝ) * ArchS10.Data.eDQ := by
      have e2 : ∑ n ∈ range ArchS10.Data.NH, Wth n * hhR Data.Jd BR n l - dR l
          = ∑ n ∈ range ArchS10.Data.NH, (Wth n * hhR Data.Jd BR n l - (ArchS10.Data.Dq n l : ℝ)) := by
        unfold dR ArchS10.Data.dq; push_cast; rw [Finset.sum_sub_distrib]
      rw [e2]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_sum (s := range ArchS10.Data.NH) fun n hn =>
        round_facts (Finset.mem_range.mp hn) hl'
      simpa using this
    have hex := abs_ex_le l ht0 ht
    have heD : (0 : ℝ) ≤ ArchS10.Data.eDQ := by
      have : (0 : ℚ) ≤ ArchS10.Data.eDQ := by unfold ArchS10.Data.eDQ; norm_num
      exact_mod_cast this
    exact mul_le_mul hd hex (abs_nonneg _) (mul_nonneg (by positivity) heD)

lemma total_facts :
    (∑ n ∈ range ArchS10.Data.NH, (ArchS10.Data.errHq n : ℝ))
        + (∑ l ∈ range Data.Jd, (ArchS10.Data.NH : ℝ) * ArchS10.Data.eDQ * (2 ^ (2 * l + 1) + 1))
        + ArchS10.Data.tauQ ≤ ArchS10.Data.dQtot ∧
    (∑ n ∈ range ArchS10.Data.NH, (ArchS10.Data.errEq n : ℝ)) + ArchS10.Data.eEQ
        + ArchS10.Data.tauE ≤ ArchS10.Data.deltaE ∧
    (0 : ℝ) < ArchS10.Data.EQ - ArchS10.Data.deltaE ∧
    ((ArchS10.Data.dQtot : ℝ) + ArchS10.Data.deltaP) / (2 * (ArchS10.Data.EQ - ArchS10.Data.deltaE))
        + ArchS10.Data.Pmax * ArchS10.Data.deltaE
          / (2 * (ArchS10.Data.EQ - ArchS10.Data.deltaE) * ArchS10.Data.EQ)
      ≤ ArchS10.Data.deltaChi := by
  have h := ArchS10.Data.total_ok
  simp only [ArchS10.Data.totalOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).2 h1; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h2; push_cast at this; exact this
  · have := (Rat.cast_lt (K := ℝ)).2 h3; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h4; push_cast at this; exact this

lemma mem_Ioo_T (hB : CertBasis D) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    t ∈ Ioo (-D.T) D.T :=
  ⟨by linarith [D.T_pos], lt_of_le_of_lt ht hB.T_gt⟩

/-- **(Qε)(e^t) as a finite sinh series**, t ∈ [0, log 2]. -/
theorem Qeps_expsum (hB : CertBasis D) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |D.Qeps t - ∑ l ∈ range Data.Jd, dR l * ex l t| ≤ (ArchS10.Data.dQtot : ℝ) := by
  have htT := mem_Ioo_T hB ht0 ht
  have hsum := summable_wC D htT
  rw [(D.prop53 htT).2.2, ← hsum.sum_add_tsum_nat_add (Data.NCw + 1)]
  set f := fun n => D.w n * D.Cn n t
  -- the tail
  have htail : |∑' k, f (k + (Data.NCw + 1))| ≤ (ArchS10.Data.tauQ : ℝ) := by
    have hs : Summable fun k => f (k + (Data.NCw + 1)) :=
      (summable_nat_add_iff (Data.NCw + 1)).2 hsum
    refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
    refine Real.tsum_le_of_sum_le (fun k => norm_nonneg _) fun S => ?_
    have := tail_CC_sum_le hB.tailFam S ht0 ht
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [f, Real.norm_eq_abs]
    rw [hB.wC_eq, abs_div]
    congr 1
    have h1 := hB.tail_small (n := k + (Data.NCw + 1)) (by omega)
    have hd : (Data.d0Q : ℝ) < 1 := by
      have : (Data.d0Q : ℚ) < 1 := by unfold Data.d0Q; norm_num
      exact_mod_cast this
    have : D.lam (k + (Data.NCw + 1)) ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (D.lam (k + (Data.NCw + 1)))]
    exact abs_of_pos (by linarith)
  have hhead := head_sum hB ht0 ht
  obtain ⟨htot, -⟩ := total_facts
  have e : ∑ n ∈ range (Data.NCw + 1), f n + ∑' k, f (k + (Data.NCw + 1))
      - ∑ l ∈ range Data.Jd, dR l * ex l t
      = (∑ n ∈ range (Data.NCw + 1), f n - ∑ l ∈ range Data.Jd, dR l * ex l t)
        + ∑' k, f (k + (Data.NCw + 1)) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (by linarith)

/-- **ε'(1⁺) certified**: `|ε'(1⁺) - EQ| ≤ deltaE` with `EQ = 22.9964756838…`, `deltaE ≈ 1.2e-22`. -/
theorem eps1_enclosure (hB : CertBasis D) :
    |D.eps1 0 - ArchS10.Data.EQ| ≤ (ArchS10.Data.deltaE : ℝ) := by
  have hsum := D.summable_w_phi_one
  rw [D.eps1_zero, ← hsum.sum_add_tsum_nat_add (Data.NCw + 1)]
  set f := fun n => D.w n * D.phi n 1 ^ 2
  have htail0 : 0 ≤ ∑' k, f (k + (Data.NCw + 1)) :=
    tsum_nonneg fun k => mul_nonneg (D.w_nonneg _) (sq_nonneg _)
  have htail : ∑' k, f (k + (Data.NCw + 1)) ≤ (ArchS10.Data.tauE : ℝ) := by
    refine Real.tsum_le_of_sum_le (fun k => mul_nonneg (D.w_nonneg _) (sq_nonneg _)) fun S => ?_
    refine le_trans (le_of_eq ?_) (tail_eps_sum_le hB.tailFam S)
    exact Finset.sum_congr rfl fun k _ => hB.w_phi_one _
  have hhead : |∑ n ∈ range (Data.NCw + 1), f n
      - ∑ n ∈ range (Data.NCw + 1), Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2|
      ≤ ∑ n ∈ range ArchS10.Data.NH, (ArchS10.Data.errEq n : ℝ) := by
    rw [← Finset.sum_sub_distrib, ← NH_eq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    exact head_eps_term hB (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hEQ : |∑ n ∈ range (Data.NCw + 1), Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2
      - ArchS10.Data.EQ| ≤ (ArchS10.Data.eEQ : ℝ) := by
    have h := ArchS10.Data.epsHead_ok
    simp only [ArchS10.Data.epsHeadOK, decide_eq_true_eq] at h
    have h2 := (Rat.cast_le (K := ℝ)).2 h
    unfold ArchS10.Data.Wthq ArchS10.Data.psi1q at h2
    push_cast at h2
    unfold Wth thR BR
    rw [← NH_eq]
    exact h2
  obtain ⟨-, htot, -⟩ := total_facts
  have e : ∑ n ∈ range (Data.NCw + 1), f n + ∑' k, f (k + (Data.NCw + 1)) - ArchS10.Data.EQ
      = (∑ n ∈ range (Data.NCw + 1), f n
          - ∑ n ∈ range (Data.NCw + 1), Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2)
        + (∑ n ∈ range (Data.NCw + 1), Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2
          - ArchS10.Data.EQ) + ∑' k, f (k + (Data.NCw + 1)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg htail0]
  have := abs_add_le (∑ n ∈ range (Data.NCw + 1), f n
          - ∑ n ∈ range (Data.NCw + 1), Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2)
        (∑ n ∈ range (Data.NCw + 1), Wth n * (∑ k ∈ range Data.Jd, BR n k) ^ 2 - ArchS10.Data.EQ)
  linarith

theorem eps1_pos (hB : CertBasis D) : 0 < D.eps1 0 := by
  have h := eps1_enclosure hB
  obtain ⟨-, -, hpos, -⟩ := total_facts
  have := (abs_le.mp h).1
  linarith

theorem eps1_ne_zero (hB : CertBasis D) : D.eps1 0 ≠ 0 := (eps1_pos hB).ne'

/-! ## The polynomial. -/

/-- `P(t) = Σ_{i<NP} pco i t^i`. -/
def Ppoly (t : ℝ) : ℝ := ∑ i ∈ range ArchS10.Data.NP, (ArchS10.Data.pco i : ℝ) * t ^ i

/-- The certified polynomial for χ (only odd powers of `|v|` occur). -/
def chiPoly (v : ℝ) : ℝ := ∑ i ∈ range ArchS10.Data.NP, (ArchS10.Data.chiCo i : ℝ) * |v| ^ i

lemma chiPoly_eq (v : ℝ) : chiPoly v = Ppoly |v| / (2 * ArchS10.Data.EQ) := by
  unfold chiPoly Ppoly ArchS10.Data.chiCo
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem chiPoly_zero : chiPoly 0 = 0 := by
  unfold chiPoly
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases i with _ | i
  · simp [ArchS10.Data.chiCo, ArchS10.Data.pco]
  · simp

lemma poly_facts :
    (∀ l < ArchS10.Data.L0, (2 * (l : ℝ) + 1 / 2) * ArchS10.Data.bQ ≤ ((ArchS10.Data.NP : ℝ) + 1) / 2) ∧
    (∑ l ∈ range ArchS10.Data.L0, |dR l| * 4 * ((2 * (l : ℝ) + 1 / 2) * ArchS10.Data.bQ) ^ ArchS10.Data.NP
        / (ArchS10.Data.NP.factorial : ℝ))
      + (∑ l ∈ range (Data.Jd - ArchS10.Data.L0), |dR (ArchS10.Data.L0 + l)|
          * (2 ^ (2 * (ArchS10.Data.L0 + l) + 1) + 1)) ≤ ArchS10.Data.deltaP ∧
    (∑ i ∈ range ArchS10.Data.NP, |(ArchS10.Data.pco i : ℝ)| * (ArchS10.Data.bQ : ℝ) ^ i)
      ≤ ArchS10.Data.Pmax := by
  have h := ArchS10.Data.poly_ok
  simp only [ArchS10.Data.polyOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun l hl => ?_, ?_, ?_⟩
  · have := (Rat.cast_le (K := ℝ)).2 (h1 l hl)
    unfold ArchS10.Data.bet at this; push_cast at this; linarith
  · have := (Rat.cast_le (K := ℝ)).2 h2
    unfold ArchS10.Data.bet at this; push_cast at this
    simp only [show ∀ x : ℝ, (4 * x + 1) / 2 = 2 * x + 1 / 2 from fun x => by ring] at this
    unfold dR
    exact this
  · have := (Rat.cast_le (K := ℝ)).2 h3; push_cast at this; exact this

lemma log_two_le_bQ : Real.log 2 ≤ (ArchS10.Data.bQ : ℝ) := by
  have h := Real.log_two_lt_d9
  have : (ArchS10.Data.bQ : ℝ) = 0.6931471808 := by
    unfold ArchS10.Data.bQ; push_cast; norm_num
  rw [this]; exact h.le

lemma taylor_diff (b t : ℝ) (N : ℕ) :
    ∑ m ∈ range N, ((b * t) ^ m / (m.factorial : ℝ) - (-(b * t)) ^ m / (m.factorial : ℝ))
      = ∑ m ∈ range N, (b ^ m - (-b) ^ m) / (m.factorial : ℝ) * t ^ m :=
  Finset.sum_congr rfl fun m _ => by rw [mul_pow, neg_pow, neg_pow b, mul_pow]; ring

/-- **The sinh series vs the polynomial**: `|Σ_{l<40} d_l ex_l(t) - P(t)| ≤ deltaP` on `[0, log 2]`. -/
theorem expsum_sub_poly {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |∑ l ∈ range Data.Jd, dR l * ex l t - Ppoly t| ≤ (ArchS10.Data.deltaP : ℝ) := by
  obtain ⟨hN, hrem, -⟩ := poly_facts
  have hb := log_two_le_bQ
  set L0 := ArchS10.Data.L0
  set N := ArchS10.Data.NP
  have hsplit : Data.Jd = L0 + (Data.Jd - L0) := rfl
  set TN : ℝ → ℝ := fun x => ∑ m ∈ range N, x ^ m / (m.factorial : ℝ) with hTN
  have hP : Ppoly t = ∑ l ∈ range L0, dR l * (TN ((2 * l + 1 / 2) * t) - TN (-((2 * l + 1 / 2) * t))) := by
    unfold Ppoly ArchS10.Data.pco
    symm
    simp only [hTN]
    simp_rw [← Finset.sum_sub_distrib, taylor_diff, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold ArchS10.Data.bet
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold dR; ring
  rw [hP, hsplit, Finset.sum_range_add]
  have e : ∑ l ∈ range L0, dR l * ex l t + ∑ l ∈ range (Data.Jd - L0), dR (L0 + l) * ex (L0 + l) t
        - ∑ l ∈ range L0, dR l * (TN ((2 * l + 1 / 2) * t) - TN (-((2 * l + 1 / 2) * t)))
      = ∑ l ∈ range L0, dR l * ((Real.exp ((2 * l + 1 / 2) * t) - TN ((2 * l + 1 / 2) * t))
          - (Real.exp (-((2 * l + 1 / 2) * t)) - TN (-((2 * l + 1 / 2) * t))))
        + ∑ l ∈ range (Data.Jd - L0), dR (L0 + l) * ex (L0 + l) t := by
    rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold ex; ring
  rw [e]
  refine (abs_add_le _ _).trans (le_trans (add_le_add ?_ ?_) hrem)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
    have hl' := Finset.mem_range.mp hl
    have hβ := hN l hl'
    set β : ℝ := 2 * l + 1 / 2
    have hβ0 : 0 ≤ β := by positivity
    have hx : β * t ≤ β * ArchS10.Data.bQ := mul_le_mul_of_nonneg_left (ht.trans hb) hβ0
    have hx0 : 0 ≤ β * t := mul_nonneg hβ0 ht0
    have hxN : |β * t| ≤ ((N : ℝ) + 1) / 2 := by rw [abs_of_nonneg hx0]; linarith
    have hxN' : |-(β * t)| ≤ ((N : ℝ) + 1) / 2 := by rw [abs_neg]; exact hxN
    have e1 := abs_exp_sub_taylor_le hxN
    have e2 := abs_exp_sub_taylor_le hxN'
    rw [abs_neg, abs_of_nonneg hx0] at e2
    rw [abs_of_nonneg hx0] at e1
    have hpow : (β * t) ^ N ≤ (β * ArchS10.Data.bQ) ^ N := pow_le_pow_left₀ hx0 hx N
    have hf : (0 : ℝ) < N.factorial := by positivity
    rw [abs_mul]
    calc |dR l| * |(Real.exp (β * t) - TN (β * t)) - (Real.exp (-(β * t)) - TN (-(β * t)))|
        ≤ |dR l| * ((β * t) ^ N / (N.factorial : ℝ) * 2 + (β * t) ^ N / (N.factorial : ℝ) * 2) := by
          gcongr
          exact (abs_sub _ _).trans (add_le_add e1 e2)
      _ ≤ |dR l| * ((β * ArchS10.Data.bQ) ^ N / (N.factorial : ℝ) * 2
            + (β * ArchS10.Data.bQ) ^ N / (N.factorial : ℝ) * 2) := by gcongr
      _ = |dR l| * 4 * (β * ArchS10.Data.bQ) ^ N / (N.factorial : ℝ) := by ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_ex_le _ ht0 ht) (abs_nonneg _)

theorem abs_Ppoly_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |Ppoly t| ≤ (ArchS10.Data.Pmax : ℝ) := by
  obtain ⟨-, -, h⟩ := poly_facts
  have hb := log_two_le_bQ
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (Finset.sum_le_sum fun i _ => ?_) h)
  rw [abs_mul, abs_pow, abs_of_nonneg ht0]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 (ht.trans hb) i) (abs_nonneg _)

/-- **(Qε)(e^t) against the explicit polynomial**, t ∈ [0, log 2]. -/
theorem Qeps_poly (hB : CertBasis D) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ Real.log 2) :
    |D.Qeps t - Ppoly t| ≤ (ArchS10.Data.dQtot : ℝ) + ArchS10.Data.deltaP := by
  have h1 := Qeps_expsum hB ht0 ht
  have h2 := expsum_sub_poly ht0 ht
  have e : D.Qeps t - Ppoly t = (D.Qeps t - ∑ l ∈ range Data.Jd, dR l * ex l t)
      + (∑ l ∈ range Data.Jd, dR l * ex l t - Ppoly t) := by ring
  rw [e]; exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ## The kernel χ. -/

/-- **THE CERTIFIED KERNEL.**  For `|v| ≤ log 2`, `|χ(v) - chiPoly v| ≤ deltaChi ≈ 1.41e-7`, where
`χ = D.chi` is CC's kernel of `K_I` (S8) and `chiPoly v = Σ_{i<67} chiCo i |v|^i` is explicit. -/
theorem chi_enclosure (hB : CertBasis D) {v : ℝ} (hv : |v| ≤ Real.log 2) :
    |D.chi v - chiPoly v| ≤ (ArchS10.Data.deltaChi : ℝ) := by
  have ht0 := abs_nonneg v
  have hQ := Qeps_poly hB ht0 hv
  have hE := eps1_enclosure hB
  have hPm := abs_Ppoly_le ht0 hv
  obtain ⟨-, -, hpos, hfin⟩ := total_facts
  set Q := D.Qeps |v|
  set P := Ppoly |v|
  set E := D.eps1 0
  set Et : ℝ := (ArchS10.Data.EQ : ℝ)
  set dE : ℝ := (ArchS10.Data.deltaE : ℝ)
  have hdE0 : 0 ≤ dE := (abs_nonneg _).trans hE
  have hElo : Et - dE ≤ E := by have := (abs_le.mp hE).1; linarith
  have hE0 : 0 < E := lt_of_lt_of_le hpos hElo
  have hEt0 : 0 < Et := by linarith
  have hchi : D.chi v = Q / (2 * E) := rfl
  rw [hchi, chiPoly_eq]
  have e : Q / (2 * E) - P / (2 * Et) = (Q - P) / (2 * E) + P * (Et - E) / (2 * E * Et) := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (le_trans (add_le_add ?_ ?_) hfin)
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * E)]
    exact div_le_div₀ ((abs_nonneg _).trans hQ) hQ (by linarith) (by linarith)
  · rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * E * Et), abs_sub_comm]
    have hP0 : 0 ≤ (ArchS10.Data.Pmax : ℝ) := (abs_nonneg _).trans hPm
    apply div_le_div₀ (by positivity) (mul_le_mul hPm hE (abs_nonneg _) hP0) (by positivity)
    have : 2 * (Et - dE) * Et ≤ 2 * E * Et := by nlinarith
    exact this

/-- `χ` is even, so the enclosure covers `[-log 2, log 2]`, the range of `y - x` for `x, y ∈ I`,
`|I| ≤ log 2`. -/
theorem chi_neg (v : ℝ) : D.chi (-v) = D.chi v := by
  simp [ArchS8.ProlateData.chi, abs_neg]

/-- **L¹ form**: `∫_0^{log 2} |χ - chiPoly| ≤ deltaChi · log 2 ≈ 9.8e-8`. -/
theorem chi_L1 (hB : CertBasis D) :
    ∫ v in (0 : ℝ)..Real.log 2, |D.chi v - chiPoly v|
      ≤ (ArchS10.Data.deltaChi : ℝ) * Real.log 2 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases hi : IntervalIntegrable (fun v => |D.chi v - chiPoly v|) volume 0 (Real.log 2)
  · have := intervalIntegral.integral_mono_on hl hi intervalIntegrable_const
      (fun v hv => chi_enclosure hB (by rw [abs_of_nonneg hv.1]; exact hv.2))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  · rw [intervalIntegral.integral_undef hi]
    have : (0 : ℝ) ≤ ArchS10.Data.deltaChi := by
      have : (0 : ℚ) ≤ ArchS10.Data.deltaChi := by unfold ArchS10.Data.deltaChi; norm_num
      exact_mod_cast this
    positivity

/-- **CC Remark 5.6 consistency**: the polynomial vanishes at 0, as χ does. -/
theorem chi_zero_consistent : D.chi 0 = chiPoly 0 := by rw [D.chi_zero, chiPoly_zero]

end ArchS10
