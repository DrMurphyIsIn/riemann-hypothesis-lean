/-
  SemilocalWeil -- the semilocal (finite-S) Weil form and its window positivity (e9, 2026-10-14).

  For a finite set S of primes and an archimedean shift dc (the delta coefficient at u = 0, measured from the
  explicit-formula value c_inf = psi(1/4) - log pi, so dc = 0 IS the explicit formula):
      weilFormS S dc f = archSide f + dc * f(0) - Sum_{n : minFac n in S} Lambda(n)/sqrt n (f(log n) + f(-log n)).
  Only the prime powers p^k with p in S enter (Lambda vanishes off prime powers, and minFac (p^k) = p).
  `SemilocalPositive S L dc` is pole-free positivity of this form on autocorrelations of tests supported in [-L, L].

  * `weilFormS_zero_eq_of_window`: if S contains every prime p <= e^{2L}, the semilocal form at dc = 0 IS the
    global Weil form on such tests (the autocorrelation lives in [-2L, 2L]; primes beyond e^{2L} never see it).
  * `rh_iff_semilocal_positive`: RH iff for every L, SemilocalPositive (primes <= e^{2L}) L 0.
  * `semilocalPositive_mono_shift`: raising dc preserves positivity (dc * f(0) = dc * ||g||^2).

  This is the formal finite-S target requested by the Riemann session (SEMI-1 data are to be checked against it):
  RH-EQUIVALENT by `rh_iff_semilocal_positive`, and nothing here is progress on RH.  conjecture1_proved = False.
-/
import PFConverseC
import E6Bridge31

open Zeta23 Complex MeasureTheory

noncomputable section

namespace RvMBridgePF
open WeilExplicit

/-- The semilocal prime side: only n whose least prime factor lies in S. -/
def primeSideS (S : Finset ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (if n.minFac ∈ S then ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) else 0)
    * (f (Real.log n) + f (-Real.log n))

/-- The semilocal Weil form with archimedean delta-shift dc (dc = 0: the explicit-formula constant). -/
def weilFormS (S : Finset ℕ) (dc : ℝ) (f : ℝ → ℂ) : ℂ :=
  archSide f + (dc : ℂ) * f 0 - primeSideS S f

/-- Pole-free positivity of the semilocal form on the window [-L, L]. -/
def SemilocalPositive (S : Finset ℕ) (L dc : ℝ) : Prop :=
  ∀ g : ℝ → ℂ, IsWeilTest g → PoleFree g → tsupport g ⊆ Set.Icc (-L) L →
    0 ≤ (weilFormS S dc (autocorr g)).re

/-- The primes p <= e^{2L}. -/
def windowPrimes (L : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (2 * L)⌋₊ + 1)).filter Nat.Prime

lemma mem_windowPrimes {L : ℝ} {p : ℕ} (hp : p.Prime) (hle : (p : ℝ) ≤ Real.exp (2 * L)) :
    p ∈ windowPrimes L := by
  unfold windowPrimes
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (Nat.le_floor hle), hp⟩

/-- On the window, primes beyond e^{2L} do not see the autocorrelation. -/
theorem primeSideS_eq_of_window {S : Finset ℕ} {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L)
    (hS : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp (2 * L) → p ∈ S) :
    primeSideS S (autocorr g) = primeSide (autocorr g) := by
  have hf : Continuous (autocorr g) := (RvMBridge5.isWeilTest_autocorr hg).1.continuous
  have hts := RvMBridge31.tsupport_autocorr_subset hsupp
  unfold primeSideS primeSide
  refine tsum_congr fun n => ?_
  by_cases hmem : n.minFac ∈ S
  · rw [if_pos hmem]
  · rw [if_neg hmem, zero_mul]
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp [hΛ]
    · have hn1 : n ≠ 1 := by rintro rfl; exact hΛ ArithmeticFunction.vonMangoldt_apply_one
      have hn0 : n ≠ 0 := by rintro rfl; exact hΛ (by simp)
      have hmp : n.minFac.Prime := Nat.minFac_prime hn1
      have hgt : Real.exp (2 * L) < (n.minFac : ℝ) := by
        by_contra hle
        exact hmem (hS _ hmp (not_lt.mp hle))
      have hle : (n.minFac : ℝ) ≤ n := by exact_mod_cast Nat.minFac_le (Nat.pos_of_ne_zero hn0)
      have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hlog : 2 * L < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr (hgt.trans_le hle)
      have h1 : autocorr g (Real.log n) = 0 :=
        RvMBridge31.eq_zero_of_tsupport_subset_Icc_right hf hts hlog.le
      have h2 : autocorr g (-Real.log n) = 0 :=
        RvMBridge31.eq_zero_of_tsupport_subset_Icc_left hf hts (by linarith)
      rw [h1, h2]
      simp

/-- At dc = 0 and S containing the window primes, the semilocal form is the global Weil form. -/
theorem weilFormS_zero_eq_of_window {S : Finset ℕ} {g : ℝ → ℂ} (hg : IsWeilTest g) {L : ℝ}
    (hsupp : tsupport g ⊆ Set.Icc (-L) L)
    (hS : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp (2 * L) → p ∈ S) :
    weilFormS S 0 (autocorr g) = weilForm (autocorr g) := by
  unfold weilFormS weilForm
  rw [primeSideS_eq_of_window hg hsupp hS]
  simp

lemma exists_window {g : ℝ → ℂ} (hg : IsWeilTest g) : ∃ L : ℝ, tsupport g ⊆ Set.Icc (-L) L := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hg.2.isCompact.isBounded
  exact ⟨r, by rwa [Real.closedBall_eq_Icc, zero_sub, zero_add] at hr⟩

/-- **RH iff semilocal pole-free positivity on every window, with S = the window primes and dc = 0.** -/
theorem rh_iff_semilocal_positive :
    RiemannHypothesis ↔ ∀ L : ℝ, SemilocalPositive (windowPrimes L) L 0 := by
  constructor
  · intro h L g hg _ hsupp
    rw [weilFormS_zero_eq_of_window hg hsupp fun p hp hle => mem_windowPrimes hp hle]
    exact RvMBridge5.rh_implies_weil_positivity h g hg
  · intro h
    apply weil_positivity_poleFree_implies_rh
    intro g hg hpf
    obtain ⟨L, hL⟩ := exists_window hg
    have := h L g hg hpf hL
    rwa [weilFormS_zero_eq_of_window hg hL fun p hp hle => mem_windowPrimes hp hle] at this

/-- Raising the archimedean delta coefficient preserves semilocal positivity. -/
theorem semilocalPositive_mono_shift {S : Finset ℕ} {L dc dc' : ℝ} (h : SemilocalPositive S L dc)
    (hle : dc ≤ dc') : SemilocalPositive S L dc' := by
  intro g hg hpf hsupp
  have h0 := h g hg hpf hsupp
  have hsplit : weilFormS S dc' (autocorr g)
      = weilFormS S dc (autocorr g) + ((dc' - dc : ℝ) : ℂ) * autocorr g 0 := by
    unfold weilFormS; push_cast; ring
  rw [hsplit, Complex.add_re, RvMBridge31.autocorr_zero, ← Complex.ofReal_mul, Complex.ofReal_re]
  have := RvMBridge31.mass_nonneg g
  nlinarith

/-! ## Hodge-index phrasing on the pole-free span (Riemann session's specification, 2026-10-14).

Classes x = a F₊ + b F₋ + Γ_g with g a pole-free Weil test in the window.  Pairings: F₊·F₋ = 1, F₊² = F₋² = 0,
Γ_g·F± = paperFT g (±i/2) = 0 (pole-free), Γ_g² = -Re weilFormS S dc (g ⋆ g~).  H = F₊ + F₋ (H² = 2 > 0), and
x ∈ H^⊥ iff a + b = 0.  The diagonal Δ is NOT derived: its self-intersection (the delta-mass at u = 1, gates 11/12)
enters only through the INPUT parameter dc.  That is why this Prop is RH-equivalent, not a construction. -/

/-- The self-intersection of x = a F₊ + b F₋ + Γ_g on the pole-free span. -/
def selfIntS (S : Finset ℕ) (dc a b : ℝ) (g : ℝ → ℂ) : ℝ :=
  2 * a * b - (weilFormS S dc (autocorr g)).re

/-- Semilocal Hodge index on the pole-free span: B(x, x) <= 0 for every x ⊥ H = F₊ + F₋. -/
def SemilocalHodgeIndex (S : Finset ℕ) (L dc : ℝ) : Prop :=
  ∀ a b : ℝ, ∀ g : ℝ → ℂ, IsWeilTest g → PoleFree g → tsupport g ⊆ Set.Icc (-L) L →
    a + b = 0 → selfIntS S dc a b g ≤ 0

theorem semilocalHodgeIndex_iff (S : Finset ℕ) (L dc : ℝ) :
    SemilocalHodgeIndex S L dc ↔ SemilocalPositive S L dc := by
  constructor
  · intro h g hg hpf hs
    have := h 0 0 g hg hpf hs (by ring)
    unfold selfIntS at this
    linarith
  · intro h a b g hg hpf hs hab
    have := h g hg hpf hs
    have hb : b = -a := by linarith
    unfold selfIntS
    rw [hb]
    nlinarith [sq_nonneg a]

/-- **RH iff the semilocal Hodge index holds on every window** (S = primes <= e^{2L}, dc = 0). -/
theorem rh_iff_semilocal_hodge_index :
    RiemannHypothesis ↔ ∀ L : ℝ, SemilocalHodgeIndex (windowPrimes L) L 0 := by
  rw [rh_iff_semilocal_positive]
  exact forall_congr' fun L => (semilocalHodgeIndex_iff _ L 0).symm

end RvMBridgePF
