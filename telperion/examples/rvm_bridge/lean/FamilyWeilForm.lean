/-
  FamilyWeilForm -- the parametric degree-<= 2 Weil window form (Stage 0 of the quadratic-family
  programme, 2026-09-25; scoping memo FAMILY_THEOREM_SCOPING_2026-09-25.md, section 4 step 1).

  The island's zeta functional (E6Bridge4/5) lives on the FREQUENCY side:
      weilForm f = archSide f - primeSide f,
      archSide f = H_f(0) + H_f(1) - f(0) log pi + (1/2pi) int h_f(r) Re psi(1/4 + i r/2) dr,
      primeSide f = sum' n, Lambda(n)/sqrt n (f(log n) + f(-log n)).
  This file generalises it to the data of a degree-<= 2 L-function with a simple pole at s = 1:
      FormData = (weights c : N -> R, gamma shifts mu in shifts, log-conductor logq),
      archSideF D f = H_f(0) + H_f(1) + f(0) logq - f(0) |shifts| log pi
                      + (1/2pi) int h_f(r) [sum_{mu in shifts} Re psi((1/2 + mu)/2 + i r/2)] dr,
      primeSideF D f = sum' n, c(n)/sqrt n (f(log n) + f(-log n)),
      weilFormF D f = archSideF D f - primeSideF D f.
  The memo's t-side form (2 int F cosh(t/2) + log q F(0) - 2 log pi F(0) + arch_0 + arch_mu
  - 2 sum c(n) n^{-1/2} F(log n)) is the same functional written through the Fourier pair
  h_f <-> f; the identity between the two writings of the archimedean term is NOT proved here
  (it is not needed by Stages 0-2, which work on the frequency side exactly as KWin/KWin2 and
  CF_Arch do).  EXACT RELATION PROVED: with c = Lambda, shifts = [0], logq = 0 the form IS the
  island's zeta weilForm (weilFormF_zeta), and the prime side of an autocorrelation supported in
  the window 2L <= log N is the finite sum over n < N (primeSideF_autocorr_eq_fin).

  Also proved: the split weilFormF D f = weilFormF D|_{logq = 0} f + f(0) logq
  (weilFormF_eq_zero_logq_add) and its real-part form on autocorrelations, where f(0) = ||g||^2
  (RvMBridge31.autocorr_zero), hence monotonicity in logq (re_weilFormF_autocorr_mono_logq).

  DISCLOSURE.  weilFormF is a DEFINITION (the arithmetic side of a would-be explicit formula).
  Only at the zeta data is it tied to anything on the island (weilFormF_zeta, and through it to
  E6Bridge4's explicit formula for zeta); for any other data no identification with a zero sum
  is proved here, and the t-side writing of the archimedean term is not proved.

  Nothing about positivity is proved.  conjecture1_proved = False.
-/
import E6Bridge31

open Zeta23 Complex MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace FamilyWeil
open WeilExplicit

/-! ## A. The data and the form. -/

/-- Data of a degree-<= 2 arithmetic Weil form: prime-power weights `c` (the coefficients of
`-L'/L`, i.e. `c(p^k)` at prime powers, `0` elsewhere), the gamma shifts `mu` of the factors
`Gamma_R(s + mu)`, and the log-conductor `logq`. -/
structure FormData where
  c : ℕ → ℝ
  shifts : List ℝ
  logq : ℝ

/-- The digamma symbol of one factor `Gamma_R(s + mu)` on the critical line:
`Re psi((1/2 + mu)/2 + i r/2) = Re psi((1 + 2 mu)/4 + i r/2)`. -/
def psiShift (μ : ℝ) (r : ℝ) : ℝ :=
  (Complex.digamma ((((1 + 2 * μ) / 4 : ℝ) : ℂ) + ((r : ℂ) / 2) * I)).re

/-- `mu = 0` is the island's `psiR` (E6Bridge11), the zeta weight `Re psi(1/4 + i r/2)`. -/
lemma psiShift_zero (r : ℝ) : psiShift 0 r = RvMBridge11.psiR r := by
  unfold psiShift RvMBridge11.psiR
  congr 3
  push_cast
  ring

/-- `mu = 1` is the `Gamma_R(s+1)` weight `Re psi(3/4 + i r/2)` (Crux3/CF `psiD`). -/
lemma psiShift_one (r : ℝ) :
    psiShift 1 r = (Complex.digamma (3 / 4 + ((r : ℂ) / 2) * I)).re := by
  unfold psiShift
  congr 3
  push_cast
  ring

/-- The archimedean digamma symbol: the sum over the gamma shifts. -/
def symbolArch (D : FormData) (r : ℝ) : ℝ :=
  (D.shifts.map (fun μ => psiShift μ r)).sum

/-- The archimedean side: the two pole terms, the conductor term, the `log pi` terms of the
`|shifts|` factors `Gamma_R`, and the digamma integral. -/
def archSideF (D : FormData) (g : ℝ → ℂ) : ℂ :=
  weilKernel g 0 + weilKernel g 1 + g 0 * (D.logq : ℂ)
    - g 0 * ((D.shifts.length : ℝ) * Real.log Real.pi : ℂ)
    + (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, weilKernel g (1 / 2 + (r : ℂ) * I)
        * ((symbolArch D r : ℝ) : ℂ)

/-- The prime side with weights `c`: `sum' n, c(n)/sqrt n (g(log n) + g(-log n))`
(the same shape as the island's `primeSide` and CF's `primeSideD`). -/
def primeSideF (D : FormData) (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((D.c n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))

/-- The prime side truncated to `n < N`. -/
def primeSideFin (D : FormData) (N : ℕ) (g : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, ((D.c n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))

/-- The parametric Weil form. -/
def weilFormF (D : FormData) (g : ℝ → ℂ) : ℂ := archSideF D g - primeSideF D g

/-! ## B. The sanity anchor: zeta. -/

/-- The zeta data: von Mangoldt weights, the single factor `Gamma_R(s)`, conductor 1. -/
def zetaData : FormData :=
  { c := fun n => ArithmeticFunction.vonMangoldt n, shifts := [0], logq := 0 }

lemma symbolArch_zeta (r : ℝ) :
    symbolArch zetaData r = (Complex.digamma (1 / 4 + ((r : ℂ) / 2) * I)).re := by
  simp only [symbolArch, zetaData, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, psiShift_zero]
  rfl

/-- The parametric form at the zeta data IS the island's zeta functional. -/
theorem weilFormF_zeta (g : ℝ → ℂ) : weilFormF zetaData g = WeilExplicit.weilForm g := by
  unfold weilFormF WeilExplicit.weilForm
  have hprime : primeSideF zetaData g = primeSide g := by
    unfold primeSideF primeSide zetaData
    rfl
  have hint : (∫ r : ℝ, weilKernel g (1 / 2 + (r : ℂ) * I) * ((symbolArch zetaData r : ℝ) : ℂ))
      = ∫ r : ℝ, archIntegrand g r := by
    congr 1
    funext r
    unfold archIntegrand
    rw [symbolArch_zeta]
  rw [hprime]
  congr 1
  unfold archSideF archSide
  rw [hint]
  simp only [zetaData, List.length_cons, List.length_nil, zero_add, Nat.cast_one]
  push_cast
  ring

/-! ## C. The prime side on a window is a finite sum. -/

/-- On the window `2L <= log N` the autocorrelation vanishes at `+-log n` for every `n >= N`. -/
lemma autocorr_pair_eq_zero {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N)
    {n : ℕ} (hn : N ≤ n) :
    autocorr g (Real.log n) = 0 ∧ autocorr g (-Real.log n) = 0 := by
  have hf : Continuous (autocorr g) := (RvMBridge5.isWeilTest_autocorr hg).1.continuous
  have hts := RvMBridge31.tsupport_autocorr_subset hsupp
  have hlog : Real.log N ≤ Real.log n :=
    Real.log_le_log (Nat.cast_pos.mpr hN) (by exact_mod_cast hn)
  exact ⟨RvMBridge31.eq_zero_of_tsupport_subset_Icc_right hf hts (by linarith),
    RvMBridge31.eq_zero_of_tsupport_subset_Icc_left hf hts (by linarith)⟩

/-- On the window `2L <= log N` the prime side of the autocorrelation is the finite sum over
`n < N` (the boundary atom `n = N` at `2L = log N` drops by continuity). -/
theorem primeSideF_autocorr_eq_fin (D : FormData) {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L) {N : ℕ} (hN : 1 ≤ N) (hL : 2 * L ≤ Real.log N) :
    primeSideF D (autocorr g) = primeSideFin D N (autocorr g) := by
  unfold primeSideF primeSideFin
  apply tsum_eq_sum
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  obtain ⟨h1, h2⟩ := autocorr_pair_eq_zero hg hsupp hN hL hn
  rw [h1, h2]
  simp

/-- Two data whose weights agree below `N` have the same prime side on the window. -/
theorem primeSideF_congr_window {D D' : FormData} {N : ℕ} (hc : ∀ n, n < N → D.c n = D'.c n)
    {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ} (hsupp : tsupport g ⊆ Set.Icc (-L) L) (hN : 1 ≤ N)
    (hL : 2 * L ≤ Real.log N) :
    primeSideF D (autocorr g) = primeSideF D' (autocorr g) := by
  unfold primeSideF
  apply tsum_congr
  intro n
  rcases Nat.lt_or_ge n N with hn | hn
  · rw [hc n hn]
  · obtain ⟨h1, h2⟩ := autocorr_pair_eq_zero hg hsupp hN hL hn
    rw [h1, h2]
    simp

/-- The archimedean side depends only on the shifts and the conductor. -/
theorem archSideF_congr {D D' : FormData} (hs : D.shifts = D'.shifts) (hq : D.logq = D'.logq)
    (g : ℝ → ℂ) : archSideF D g = archSideF D' g := by
  unfold archSideF symbolArch
  rw [hs, hq]

/-! ## D. The conductor term splits off: `weilFormF D f = weilFormF D|_{logq=0} f + f(0) logq`. -/

/-- The data with the conductor term replaced. -/
def withLogq (D : FormData) (ℓ : ℝ) : FormData := { D with logq := ℓ }

@[simp] lemma withLogq_c (D : FormData) (ℓ : ℝ) : (withLogq D ℓ).c = D.c := rfl
@[simp] lemma withLogq_shifts (D : FormData) (ℓ : ℝ) : (withLogq D ℓ).shifts = D.shifts := rfl
@[simp] lemma withLogq_logq (D : FormData) (ℓ : ℝ) : (withLogq D ℓ).logq = ℓ := rfl

theorem weilFormF_eq_zero_logq_add (D : FormData) (g : ℝ → ℂ) :
    weilFormF D g = weilFormF (withLogq D 0) g + g 0 * (D.logq : ℂ) := by
  unfold weilFormF archSideF primeSideF symbolArch withLogq
  simp only
  push_cast
  ring

/-- On an autocorrelation the conductor term is `||g||^2 logq` (RvMBridge31.mass). -/
theorem re_weilFormF_autocorr_eq (D : FormData) (g : ℝ → ℂ) :
    (weilFormF D (autocorr g)).re
      = (weilFormF (withLogq D 0) (autocorr g)).re + RvMBridge31.mass g * D.logq := by
  rw [weilFormF_eq_zero_logq_add, Complex.add_re, RvMBridge31.autocorr_zero, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-- MONOTONICITY IN THE CONDUCTOR: same weights and shifts, larger `logq`, larger real part. -/
theorem re_weilFormF_autocorr_mono_logq {D D' : FormData} (hc : D.c = D'.c)
    (hs : D.shifts = D'.shifts) (hq : D'.logq ≤ D.logq) (g : ℝ → ℂ) :
    (weilFormF D' (autocorr g)).re ≤ (weilFormF D (autocorr g)).re := by
  rw [re_weilFormF_autocorr_eq D, re_weilFormF_autocorr_eq D']
  have h0 : withLogq D' 0 = withLogq D 0 := by
    unfold withLogq
    rw [hc, hs]
  rw [h0]
  have := RvMBridge31.mass_nonneg g
  nlinarith

end FamilyWeil
