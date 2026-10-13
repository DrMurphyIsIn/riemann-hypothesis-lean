/-
  ArchS12_Main -- STAGE S12, the final assembly of Connes-Consani's conceptual (Sonin/prolate)
  archimedean Weil positivity (arXiv:2006.13771) in the island's conventions (rvm_bridge, 2026-10-11).
  conjecture1_proved = False.  Nothing here is RH progress.

  Chain (ARCH_S12_NOTES.md §1; g = h' - h/2 with h = S2's `qLift g L`, ε' = ε'(1⁺) = `D.eps1 0`):
    Re weilForm(autocorr g) = archW g                                (S3, pole-free, prime-free window)
    SoninTr(g) := Σ_k ‖S ϑ(g) e_k‖² = archW g + Re E                (S7 `cc_thm47`, CC Thm 4.7)
    -Re E = 2ε' (‖h‖² - re ⟨h, K_I h⟩)                               (S8 `prop55_lift`, CC Prop 5.5)
    re ⟨h, K_I h⟩ ≤ 0.95921 ‖h‖²  (|I| = 1/2)                        (S11 T1 via `form_chi_half`)
    re ⟨h, K_I h⟩ ≤ 0.9995 ‖h‖² + 0.058 |∫h|²/log 2  (|I| = log 2)   (S11 T2 via `form_chi_log2`)
  with `D = prolateData bR σ` for a certified enumeration σ (A3, `exists_certified_prolate`).

  S12a (one condition, L ≤ 1/4):   Re weilForm ≥ SoninTr + 1.87 ‖h‖² ≥ 0.
  S12b (CC Thm 1, 2L ≤ log 2, paperFT g (I/2) = 0 = paperFT g 0):  archW g ≥ SoninTr + 0.0229 ‖h‖²,
        so W∞ ≥ SoninTr ≥ 0 and 0 ≤ Re weilForm.
  CC Thm 6.11 (2L ≤ log 2, one condition):  archW g ≥ SoninTr - c |paperFT g 0|², c = 8·0.058·ε'/log 2
        (= 4γ/log 2 with γ = 2ε'·0.058 ≈ 2.6676), c ∈ [15.39, 15.40]; stated with c = 15.4.
  No `sorry`.
-/
import ArchS12_Bridge
import ArchS7_Final
import ArchS3_Delta
import ArchS2_QTrick

open MeasureTheory Set Complex
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS12

open WeilExplicit Zeta23 ArchS6 ArchS7 ArchS8

/-! ## A. Pieces. -/

theorem re_integral_conj_mul_nonneg (h : ℝ → ℂ) : 0 ≤ (∫ x, conj (h x) * h x).re := by
  have e : (fun x => conj (h x) * h x) = fun x => ((‖h x‖ ^ 2 : ℝ) : ℂ) := by
    funext x; rw [Complex.conj_mul']; push_cast; rfl
  rw [e, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun x => sq_nonneg _

/-- `Re E` for a lift, in terms of `‖h‖²` and CC's K_I form (`prop55_lift` with `Qε = 2ε' χ`). -/
theorem re_Eplus_lift (D : ProlateDataNat) (hε : D.eps1 0 ≠ 0) {h : ℝ → ℂ} (hh : IsWeilTest h)
    {α ℓ : ℝ} (hℓ : ℓ < D.T) (hs : tsupport h ⊆ Icc α (α + ℓ)) :
    (D.Eplus (autocorr fun u => deriv h u - h u / 2)).re
      = -(2 * D.eps1 0 * ((∫ x, conj (h x) * h x).re
          - (∫ x, ∫ y, conj (h x) * h y * (D.chi (y - x) : ℂ)).re)) := by
  rw [D.prop55_lift hh hℓ hs]
  have hε' : (D.eps1 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε
  have hq : ∀ x y, conj (h x) * h y * (D.Qeps |y - x| : ℂ)
      = (2 * D.eps1 0 : ℂ) * (conj (h x) * h y * (D.chi (y - x) : ℂ)) := by
    intro x y
    unfold ProlateData.chi
    push_cast
    field_simp
  simp_rw [hq, integral_const_mul]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.neg_im, mul_zero, zero_mul, sub_zero,
    Complex.mul_im, add_zero, neg_zero]
  ring

/-- Bounds on ε'(1⁺) from S10's certified enclosure. -/
theorem eps1_bounds {D : ProlateDataNat} (hB : ArchS10.CertBasis D) :
    22.99 ≤ D.eps1 0 ∧ D.eps1 0 ≤ 22.997 := by
  have h := abs_le.1 (ArchS10.eps1_enclosure hB)
  have e1 : (22.99 : ℝ) + ArchS10.Data.deltaE ≤ ArchS10.Data.EQ := by
    unfold ArchS10.Data.EQ ArchS10.Data.deltaE; norm_num
  have e2 : (ArchS10.Data.EQ : ℝ) + ArchS10.Data.deltaE ≤ 22.997 := by
    unfold ArchS10.Data.EQ ArchS10.Data.deltaE; norm_num
  constructor <;> linarith [h.1, h.2]

/-! ## B. The core assembly: Sonin trace = archW - 2ε'(‖h‖² - re ⟨h, K_I h⟩). -/

section Core

variable {ι : Type*} (bR : EigenBasis CopR ι) (σ : ℕ ≃ ι)

theorem sonin_hasSum_lift (hB : ArchS10.CertBasis (prolateData bR σ)) {g h : ℝ → ℂ}
    (hg : IsWeilTest g) (hh : IsWeilTest h) (hgh : ∀ u, g u = deriv h u - h u / 2)
    {α ℓ : ℝ} (hℓ : ℓ < Real.log 3) (hs : tsupport h ⊆ Icc α (α + ℓ))
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hg.1.continuous.integrable_of_hasCompactSupport hg.2) (e k))‖ ^ 2)
      (ArchS3.archW g - 2 * (prolateData bR σ).eps1 0 * ((∫ x, conj (h x) * h x).re
          - (∫ x, ∫ y, conj (h x) * h y * ((prolateData bR σ).chi (y - x) : ℂ)).re)) := by
  have H := cc_thm47 bR σ hg e
  have hgl : g = fun u => deriv h u - h u / 2 := funext hgh
  have hE := re_Eplus_lift (prolateData bR σ) (ArchS10.eps1_ne_zero hB) hh hℓ hs
  rw [← hgl] at hE
  rw [hE] at H
  convert H using 1
  ring

end Core

/-! ## C. S12a: the one-condition statement (Y) at |I| = 1/2, by the conceptual route. -/

/-- **S12a, with the Sonin lower bound.**  For a pole-free test `g` supported in `[-L, L]`,
`L ≤ 1/4`, and any Hilbert basis `e` of `L²(ℝ)_ev`, the Sonin trace `s = Σ ‖S ϑ(g) e_k‖²` satisfies
`0 ≤ s` and `s + 1.87 ‖h‖² ≤ Re weilForm(autocorr g)`, with `h = qLift g L` (g = h' - h/2). -/
theorem weil_positivity_one_condition_quarter_sonin {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hL : L ≤ 1 / 4) (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0)
    {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    ∃ s : ℝ, HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hg.1.continuous.integrable_of_hasCompactSupport hg.2) (e k))‖ ^ 2) s ∧ 0 ≤ s ∧
      s + 1.87 * (∫ x, conj (ArchS2.qLift g L x) * ArchS2.qLift g L x).re
        ≤ (weilForm (autocorr g)).re := by
  obtain ⟨ι, bR, σ, hB⟩ := exists_certified_prolate
  set h := ArchS2.qLift g L with hdef
  have hh : IsWeilTest h := ArchS2.isWeilTest_qLift hg hsupp h0
  have hs : tsupport h ⊆ Icc (-L) L := ArchS2.tsupport_qLift hg hsupp h0
  have hgh := ArchS2.qLift_rel hg L
  have hs4 : tsupport h ⊆ Icc (-(1 / 4)) (1 / 4) :=
    hs.trans (Icc_subset_Icc (by linarith) hL)
  have hs' : tsupport h ⊆ Icc (-(1 / 4)) (-(1 / 4) + 1 / 2) := by
    rw [show -(1 / 4 : ℝ) + 1 / 2 = 1 / 4 by norm_num]; exact hs4
  have hl3 : (1 / 2 : ℝ) < Real.log 3 := by
    have := Real.log_two_gt_d9
    have : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  have H := sonin_hasSum_lift bR σ hB hg hh hgh hl3 hs' e
  have hK := form_chi_half hB hh.1.continuous hs4
  have hN := re_integral_conj_mul_nonneg h
  obtain ⟨he1, -⟩ := eps1_bounds hB
  have hL2 : 2 * L ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [ArchS3.re_weilForm_eq_archW hg hsupp hL2 h0]
  refine ⟨_, H, H.nonneg fun _ => sq_nonneg _, ?_⟩
  set ε := (prolateData bR σ).eps1 0
  set N := (∫ x, conj (h x) * h x).re
  set B := (∫ x, ∫ y, conj (h x) * h y * ((prolateData bR σ).chi (y - x) : ℂ)).re
  have h1 : 0.04079 * N ≤ N - B := by linarith
  have h2 : 2 * ε * (0.04079 * N) ≤ 2 * ε * (N - B) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

/-- **S12a.**  The one-condition archimedean Weil positivity (Yoshida's class) on half-width
`L ≤ 1/4`, by Connes-Consani's conceptual route (Sonin trace + prolate kernel K_I, certified
λ_max(K_I) ≤ 0.95921 at |I| = 1/2).  The project's `KWin_Bridge.weil_positivity_prime_free_window`
proves the full window by a certificate; this is the conceptual proof of the |I| = 1/2 case. -/
theorem weil_positivity_one_condition_quarter {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hL : L ≤ 1 / 4) (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0) :
    0 ≤ (weilForm (autocorr g)).re := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ evenL2
  obtain ⟨s, -, hs0, hs⟩ := weil_positivity_one_condition_quarter_sonin hg hL hsupp h0 b
  have := re_integral_conj_mul_nonneg (ArchS2.qLift g L)
  nlinarith

/-! ## D. S12b: CC Theorem 1 and Theorem 6.11 at the full window |I| = log 2. -/

section Full

variable {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hL : 2 * L ≤ Real.log 2)
  (hsupp : tsupport g ⊆ Icc (-L) L) (h0 : paperFT g (I / 2) = 0)

include hg hL hsupp h0 in
/-- The common part: for `D = prolateData bR σ` certified, the Sonin trace `s` and
`archW g = s + 2ε'(‖h‖² - re ⟨h, K_I h⟩)`, with the |I| = log 2 bound on the K_I form. -/
theorem full_window_core {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    ∃ (s ε N B : ℝ), HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hg.1.continuous.integrable_of_hasCompactSupport hg.2) (e k))‖ ^ 2) s ∧
      ArchS3.archW g = s + 2 * ε * (N - B) ∧ 22.99 ≤ ε ∧ ε ≤ 22.997 ∧ 0 ≤ N ∧
      N = (∫ x, conj (ArchS2.qLift g L x) * ArchS2.qLift g L x).re ∧
      B ≤ 0.9995 * N + 0.058 * ‖∫ x, ArchS2.qLift g L x‖ ^ 2 / Real.log 2 := by
  obtain ⟨ι, bR, σ, hB⟩ := exists_certified_prolate
  set h := ArchS2.qLift g L with hdef
  have hh : IsWeilTest h := ArchS2.isWeilTest_qLift hg hsupp h0
  have hs : tsupport h ⊆ Icc (-L) L := ArchS2.tsupport_qLift hg hsupp h0
  have hgh := ArchS2.qLift_rel hg L
  have hsl : tsupport h ⊆ Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) :=
    hs.trans (Icc_subset_Icc (by linarith) (by linarith))
  have hs' : tsupport h ⊆ Icc (-(Real.log 2 / 2)) (-(Real.log 2 / 2) + Real.log 2) := by
    rw [show -(Real.log 2 / 2) + Real.log 2 = Real.log 2 / 2 by ring]; exact hsl
  have hl3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have H := sonin_hasSum_lift bR σ hB hg hh hgh hl3 hs' e
  obtain ⟨he1, he2⟩ := eps1_bounds hB
  refine ⟨_, _, _, _, H, by ring, he1, he2, re_integral_conj_mul_nonneg h, rfl,
    form_chi_log2 hB hh.1.continuous hsl⟩

include hg hL hsupp h0 in
/-- **S12b, CC Theorem 1 (W∞ ≥ SoninTr ≥ 0) in our conventions.**  On CC's two-condition class
(`paperFT g (I/2) = 0` and `paperFT g 0 = 0`, i.e. ∫ h = 0) at the full window `2L ≤ log 2`:
`0 ≤ s` and `s + 0.0229 ‖h‖² ≤ archW g = W∞(g ∗ g*)`, for the Sonin trace `s` in any Hilbert basis. -/
theorem cc_thm1 (hz : paperFT g 0 = 0) {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    ∃ s : ℝ, HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hg.1.continuous.integrable_of_hasCompactSupport hg.2) (e k))‖ ^ 2) s ∧ 0 ≤ s ∧
      s + 0.0229 * (∫ x, conj (ArchS2.qLift g L x) * ArchS2.qLift g L x).re ≤ ArchS3.archW g := by
  obtain ⟨s, ε, N, B, H, hW, he1, -, hN, hNdef, hB⟩ := full_window_core hg hL hsupp h0 e
  have hint : ∫ x, ArchS2.qLift g L x = 0 :=
    (ArchS2.paperFT_zero_lift_iff (ArchS2.isWeilTest_qLift hg hsupp h0) (ArchS2.qLift_rel hg L)).1 hz
  rw [hint, norm_zero] at hB
  refine ⟨s, H, H.nonneg fun _ => sq_nonneg _, ?_⟩
  rw [← hNdef, hW]
  have h1 : 0.0005 * N ≤ N - B := by
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    simp only [this, mul_zero, zero_div, add_zero] at hB
    linarith
  have h2 : 2 * ε * (0.0005 * N) ≤ 2 * ε * (N - B) := mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith

include hg hL hsupp h0 in
/-- **S12b, corollary.**  Archimedean Weil positivity on CC's two-condition class at the full
window, by the conceptual route. -/
theorem weil_positivity_cc_class (hz : paperFT g 0 = 0) : 0 ≤ (weilForm (autocorr g)).re := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ evenL2
  obtain ⟨s, -, hs0, hs⟩ := cc_thm1 hg hL hsupp h0 hz b
  have := re_integral_conj_mul_nonneg (ArchS2.qLift g L)
  rw [ArchS3.re_weilForm_eq_archW hg hsupp hL h0]
  nlinarith

include hg hL hsupp h0 in
/-- **S12b, CC Theorem 6.11 form** (one condition, full window): `archW g ≥ s - 15.4 |ĝ(0)|²` with
`ĝ(0) = paperFT g 0`.  The constant obtained is c = 8·0.058·ε'(1⁺)/log 2 = 4γ/log 2,
γ = 2ε'(1⁺)·0.058 ≈ 2.6676, so c ≈ 15.394 (CC: γ ≈ 2.944, c ≈ 16.99; CC Rem 6.12: 13 < c_best < 17). -/
theorem cc_thm611 {κ : Type*} (e : HilbertBasis κ ℂ evenL2) :
    ∃ s : ℝ, HasSum (fun k ↦ ‖ArchS6.ProlateBasis.soninProj (S := evenPair)
        (theta g (hg.1.continuous.integrable_of_hasCompactSupport hg.2) (e k))‖ ^ 2) s ∧ 0 ≤ s ∧
      s - 15.4 * ‖paperFT g 0‖ ^ 2 ≤ ArchS3.archW g := by
  obtain ⟨s, ε, N, B, H, hW, he1, he2, hN, -, hB⟩ := full_window_core hg hL hsupp h0 e
  have hint : ∫ x, ArchS2.qLift g L x = -2 * paperFT g 0 := by
    have := ArchS2.integral_lift (ArchS2.isWeilTest_qLift hg hsupp h0) (ArchS2.qLift_rel hg L)
    rw [← ArchS2.paperFT_zero] at this
    rw [this]; ring
  have hn : ‖∫ x, ArchS2.qLift g L x‖ ^ 2 = 4 * ‖paperFT g 0‖ ^ 2 := by
    rw [hint, norm_mul, norm_neg]; norm_num; ring
  rw [hn] at hB
  refine ⟨s, H, H.nonneg fun _ => sq_nonneg _, ?_⟩
  rw [hW]
  set G := ‖paperFT g 0‖ ^ 2
  have hG : 0 ≤ G := sq_nonneg _
  have hl2 : 0.6931 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- 2ε'(N - B) ≥ -2ε'·0.058·4G/log 2 ≥ -15.4 G
  have hq : 0.058 * (4 * G) / Real.log 2 ≤ 0.058 * (4 * G) / 0.6931 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hl2.le
  have h1 : -(0.058 * (4 * G) / 0.6931) ≤ N - B := by nlinarith
  have h2 : 2 * ε * (-(0.058 * (4 * G) / 0.6931)) ≤ 2 * ε * (N - B) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : 2 * ε * (0.058 * (4 * G) / 0.6931) ≤ 15.4 * G := by
    have e : 2 * ε * (0.058 * (4 * G) / 0.6931) = (0.464 / 0.6931) * (ε * G) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right he2 hG
    nlinarith
  linarith

end Full

end ArchS12
