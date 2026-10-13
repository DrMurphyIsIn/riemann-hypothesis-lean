/-
  ZhuEnvelope -- Zhu Lemma 3.1 (arXiv:2608.24827 v2, "Crude envelope"), PROVED on the rvm_bridge
  island (2026-09-23).

  STATEMENT (the registry's `WeilWindow.EnvelopeBound`, mirrored VERBATIM below):
    for all t >= 15/4,  Re psi(1/4 + i t/2) - log pi  >=  log (t / (2 pi)) - 1/t,
  psi = Gamma'/Gamma = `Complex.digamma`.  Equivalently Re psi(1/4 + i t/2) >= log(t/2) - 1/t.

  ROUTE.  Zhu proves it from Binet's second formula.  Binet is not in Mathlib or Zeta23, so the
  proof here is assembled from what the island already owns, in two ranges:
    * t >= 25/2: Zeta23's Stirling remainder `StirlingVert.digamma_stirling`
      (|psi(w) - log w + 1/(2w)| <= 3 / (Im w)^2) at w = 1/4 + i t/2, with Re log w >= log(t/2)
      and Re (1/(2w)) = (1/8) / (1/16 + t^2/4) <= 1/(2 t^2); the deficit 25/(2 t^2) <= 1/t exactly
      at t >= 25/2.
    * 15/4 <= t <= 25/2: eleven monotone bands.  Re psi(1/4 + i t/2) is monotone in |t|
      (`RvMBridge30.psiR_mono`, from Zeta23's vertical-line series), so on a band [a, b] the left
      endpoint's rational floor (`RvMBridge30.psiR_ge_rational`: 40 series terms + an integral tail,
      gamma <= 0.58112) is compared against log(b/2) - 1/b, the right endpoint's value of the
      increasing right-hand side; the log is bounded above through exp's Taylor polynomial
      (`Real.sum_le_exp_of_nonneg`).  Band edges were chosen by a script with margin >= 0.002.
  Nothing here is about zeros; it is one inequality for the digamma function.
  No `sorry`.  conjecture1_proved = False.
-/
import E6Bridge30

open MeasureTheory

noncomputable section

namespace RvMBridgeZhu
open RvMBridge11 RvMBridge30

/-! ## A. The registry-facing statement (mirrored verbatim into `WeilWindow.EnvelopeBound`). -/

/-- Zhu Lemma 3.1, CONCRETE: `Re ψ(1/4 + it/2) - log π ≥ log(t/2π) - 1/t` for `t ≥ 15/4`.
    The digamma expression is the one `WeilExplicit.archIntegrand` integrates against. -/
def EnvelopeBound : Prop :=
  ∀ t : ℝ, 15 / 4 ≤ t →
    Real.log (t / (2 * Real.pi)) - 1 / t
      ≤ (Complex.digamma (1 / 4 + ((t : ℂ) / 2) * Complex.I)).re - Real.log Real.pi

/-! ## B. The Stirling range t >= 25/2. -/

lemma psiR_ge_stirling {t : ℝ} (ht : 25 / 2 ≤ t) : Real.log (t / 2) - 1 / t ≤ psiR t := by
  have ht0 : 0 < t := by linarith
  set w : ℂ := 1 / 4 + ((t : ℂ) / 2) * Complex.I with hw
  have hwre : w.re = 1 / 4 := by simp [hw]
  have hwim : w.im = t / 2 := by simp [hw]
  have hpsi : psiR t = (Complex.digamma w).re := rfl
  have hst := Zeta23.StirlingVert.digamma_stirling (w := w) (by rw [hwre]; norm_num)
    (by rw [hwim, abs_of_pos (by linarith)]; linarith)
  rw [hwim] at hst
  -- real part of the remainder
  have hrem : -(3 / (t / 2) ^ 2) ≤ (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re := by
    have h1 := Complex.abs_re_le_norm (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w)
    have h2 := (abs_le.mp (h1.trans hst)).1
    linarith
  -- Re log w >= log (t/2)
  have hlog : Real.log (t / 2) ≤ (Complex.log w).re := by
    rw [Complex.log_re]
    apply Real.log_le_log (by positivity)
    have := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos (by positivity)] at this
    exact this
  -- Re (1/(2w)) = (1/8) / (1/16 + t^2/4)
  have hinv : ((1 / 2 : ℂ) / w).re = (1 / 8) / (1 / 16 + t ^ 2 / 4) := by
    rw [Complex.div_re, Complex.normSq_apply, hwre, hwim]
    simp
    ring
  have hinv_le : (1 / 8) / (1 / 16 + t ^ 2 / 4) ≤ 1 / (2 * t ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hdef : 3 / (t / 2) ^ 2 + 1 / (2 * t ^ 2) ≤ 1 / t := by
    have e : 3 / (t / 2) ^ 2 + 1 / (2 * t ^ 2) = (25 / 2) / t ^ 2 := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have hsplit : (Complex.digamma w).re
      = (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re
        + (Complex.log w).re - ((1 / 2 : ℂ) / w).re := by
    simp only [Complex.add_re, Complex.sub_re]
    ring
  rw [hpsi, hsplit, hinv]
  linarith

/-! ## C. The band mechanism for 15/4 <= t <= 25/2. -/

/-- On a band `[a, b]` the monotone left floor beats the increasing right-hand side at `b`. -/
lemma band_step {a b φ : ℝ} (ha : 0 < a) (hφ : φ ≤ psiR a)
    (hb : Real.log (b / 2) - 1 / b ≤ φ) {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    Real.log (t / 2) - 1 / t ≤ psiR t := by
  have h1 : psiR a ≤ psiR t :=
    psiR_mono ha.le (by rw [abs_of_pos (by linarith)]; exact hat)
  have h2 : Real.log (t / 2) ≤ Real.log (b / 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have h3 : 1 / b ≤ 1 / t := one_div_le_one_div_of_le (by linarith) htb
  linarith

/-- `log x ≤ q` once `x` is below the degree-11 Taylor polynomial of `exp q` (`q ≥ 0`). -/
lemma log_le_of_le_taylor {x q : ℝ} (hx : 0 < x) (hq : 0 ≤ q)
    (h : x ≤ ∑ i ∈ Finset.range 12, q ^ i / (Nat.factorial i : ℝ)) : Real.log x ≤ q := by
  rw [Real.log_le_iff_le_exp hx]
  exact h.trans (Real.sum_le_exp_of_nonneg hq 12)

/-- The right-hand side at the band's right endpoint, bounded by a rational. -/
lemma rhs_le {b q : ℝ} (hb : 0 < b) (hq : 0 ≤ q + 1 / b)
    (h : b / 2 ≤ ∑ i ∈ Finset.range 12, (q + 1 / b) ^ i / (Nat.factorial i : ℝ)) :
    Real.log (b / 2) - 1 / b ≤ q := by
  have := log_le_of_le_taylor (by positivity) hq h
  linarith

/-! ### The eleven left-endpoint floors (N = 40 series terms, tail M = 10^6, gamma <= 0.58112). -/

lemma floor_0 : (1243 / 2000 : ℝ) ≤ psiR (15 / 4) := by
  refine le_trans ?_ (psiR_ge_rational (15 / 4) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_1 : (2067 / 2500 : ℝ) ≤ psiR (23 / 5) := by
  refine le_trans ?_ (psiR_ge_rational (23 / 5) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_2 : (9969 / 10000 : ℝ) ≤ psiR (109 / 20) := by
  refine le_trans ?_ (psiR_ge_rational (109 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_3 : (5711 / 5000 : ℝ) ≤ psiR (63 / 10) := by
  refine le_trans ?_ (psiR_ge_rational (63 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_4 : (12689 / 10000 : ℝ) ≤ psiR (143 / 20) := by
  refine le_trans ?_ (psiR_ge_rational (143 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_5 : (6907 / 5000 : ℝ) ≤ psiR 8 := by
  refine le_trans ?_ (psiR_ge_rational 8 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_6 : (1853 / 1250 : ℝ) ≤ psiR (177 / 20) := by
  refine le_trans ?_ (psiR_ge_rational (177 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_7 : (7871 / 5000 : ℝ) ≤ psiR (97 / 10) := by
  refine le_trans ?_ (psiR_ge_rational (97 / 10) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_8 : (8291 / 5000 : ℝ) ≤ psiR (211 / 20) := by
  refine le_trans ?_ (psiR_ge_rational (211 / 20) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_9 : (4339 / 2500 : ℝ) ≤ psiR (57 / 5) := by
  refine le_trans ?_ (psiR_ge_rational (57 / 5) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

lemma floor_10 : (723 / 400 : ℝ) ≤ psiR (49 / 4) := by
  refine le_trans ?_ (psiR_ge_rational (49 / 4) 40 1000000 eulerMascheroni_le)
  simp only [serF, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-! ### The eleven right-endpoint log bounds. -/

lemma rhs_0 : Real.log ((23 / 5) / 2) - 1 / (23 / 5) ≤ (1243 / 2000 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_1 : Real.log ((109 / 20) / 2) - 1 / (109 / 20) ≤ (2067 / 2500 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_2 : Real.log ((63 / 10) / 2) - 1 / (63 / 10) ≤ (9969 / 10000 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_3 : Real.log ((143 / 20) / 2) - 1 / (143 / 20) ≤ (5711 / 5000 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_4 : Real.log (8 / 2) - 1 / 8 ≤ (12689 / 10000 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_5 : Real.log ((177 / 20) / 2) - 1 / (177 / 20) ≤ (6907 / 5000 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_6 : Real.log ((97 / 10) / 2) - 1 / (97 / 10) ≤ (1853 / 1250 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_7 : Real.log ((211 / 20) / 2) - 1 / (211 / 20) ≤ (7871 / 5000 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_8 : Real.log ((57 / 5) / 2) - 1 / (57 / 5) ≤ (8291 / 5000 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_9 : Real.log ((49 / 4) / 2) - 1 / (49 / 4) ≤ (4339 / 2500 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

lemma rhs_10 : Real.log ((25 / 2) / 2) - 1 / (25 / 2) ≤ (723 / 400 : ℝ) := by
  refine rhs_le (by norm_num) (by norm_num) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-! ## D. Assembly. -/

/-- Zhu Lemma 3.1 in the island's `psiR` vocabulary: `log(t/2) - 1/t ≤ Re ψ(1/4 + it/2)`. -/
theorem psiR_ge_envelope {t : ℝ} (ht : 15 / 4 ≤ t) : Real.log (t / 2) - 1 / t ≤ psiR t := by
  rcases le_or_gt t (23 / 5) with h0 | h0
  · exact band_step (by norm_num) floor_0 rhs_0 ht h0
  rcases le_or_gt t (109 / 20) with h1 | h1
  · exact band_step (by norm_num) floor_1 rhs_1 h0.le h1
  rcases le_or_gt t (63 / 10) with h2 | h2
  · exact band_step (by norm_num) floor_2 rhs_2 h1.le h2
  rcases le_or_gt t (143 / 20) with h3 | h3
  · exact band_step (by norm_num) floor_3 rhs_3 h2.le h3
  rcases le_or_gt t 8 with h4 | h4
  · exact band_step (by norm_num) floor_4 rhs_4 h3.le h4
  rcases le_or_gt t (177 / 20) with h5 | h5
  · exact band_step (by norm_num) floor_5 rhs_5 h4.le h5
  rcases le_or_gt t (97 / 10) with h6 | h6
  · exact band_step (by norm_num) floor_6 rhs_6 h5.le h6
  rcases le_or_gt t (211 / 20) with h7 | h7
  · exact band_step (by norm_num) floor_7 rhs_7 h6.le h7
  rcases le_or_gt t (57 / 5) with h8 | h8
  · exact band_step (by norm_num) floor_8 rhs_8 h7.le h8
  rcases le_or_gt t (49 / 4) with h9 | h9
  · exact band_step (by norm_num) floor_9 rhs_9 h8.le h9
  rcases le_or_gt t (25 / 2) with h10 | h10
  · exact band_step (by norm_num) floor_10 rhs_10 h9.le h10
  exact psiR_ge_stirling h10.le

/-- **Zhu Lemma 3.1, PROVED**: the registry's `EnvelopeBound`. -/
theorem envelopeBound : EnvelopeBound := by
  intro t ht
  have h := psiR_ge_envelope ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) hpi.ne']
  have hpsi : psiR t = (Complex.digamma (1 / 4 + ((t : ℂ) / 2) * Complex.I)).re := rfl
  rw [hlog]
  linarith

end RvMBridgeZhu

end
