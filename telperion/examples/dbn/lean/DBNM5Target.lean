/-
  DBNM5Target -- Route C milestone M5: the kernel-elaborated TARGET statement of Polymath15
  (arXiv:1904.12438) Theorem 1.3, "effective Riemann-Siegel approximation to H_t(x+iy)", as the
  named Prop `P15Thm13`, with its full vocabulary, plus the consumer step (P15 Corollary 1.4,
  the non-vanishing criterion) proved CONDITIONALLY on that Prop.
  Design: telperion/docs/DESIGN_RH_dbn_effective_Ht_2026-09-23.md.

  `P15Thm13` is NOT proved here.  Proving it is milestone M5 (about 10k-20k lines, of which the
  Riemann-Siegel representation and Arias de Reyna's remainder bounds are shared with the ANDURIL
  Riemann-Siegel route).  The Prop is stated over the island's `DBN.H` (DBNDefs) so a future proof
  plugs in directly.

  Transcription notes (checked against the arXiv LaTeX source of v2, file debruijn.tex):
    * (14) is `f_t = Σ b_n^t / n^{s_*} + γ Σ n^y b_n^t / n^{conj(s_*) + κ}`: the overline on `s_*`
      in the second sum is in the source (line 229) and is lost by PDF text extraction.  Without it
      the second sum has the wrong phase (it must equal `A_{t,N}/B_t` of Corollary 6.4).
    * (71), (72) print `n^{Re s}`; the derivation (Corollary 6.4 divided by `B_t`) and
      Proposition 6.6 (iv), (v) need `n^{Re s_*}`, which is what `eA`, `eB` use.
    * `ε_{t,n}(s₊)`, `ε̃(s₊)` are evaluated at the reflection `(1+y+ix)/2` of `s₊ = (1+y−ix)/2`
      (Corollary 6.4 applies Propositions 6.1 and 6.3 there, via `M_t = M_t^*`, `α = α^*`).  So
      `epsTN` and `epsTilde` take `(σ, T)` with `T = x/2 > 0`.

  conjecture1_proved = False.  Nothing here bears on the Riemann Hypothesis: `P15Thm13` is an
  approximation statement at large height, and the criterion below certifies non-vanishing of H_t
  at a single point, given `P15Thm13`.
-/
import DBNDefs
import DBNM5Alpha

open Complex

namespace DBNM5

noncomputable section

/-- P15 (11): `B_t(x+iy) = M_t((1+y−ix)/2)`. -/
def Bt (t x y : ℝ) : ℂ := Mt t ((1 + (y : ℂ) - (x : ℂ) * I) / 2)

/-- P15 (19): `N = ⌊√(x/(4π) + t/16)⌋`. -/
def NP (t x : ℝ) : ℕ := ⌊Real.sqrt (x / (4 * Real.pi) + t / 16)⌋₊

/-- P15 (15): `b_n^t = exp((t/4) log² n)`. -/
def bnt (t : ℝ) (n : ℕ) : ℝ := Real.exp (t / 4 * Real.log n ^ 2)

/-- P15 (14): `f_t(x+iy) = Σ_{n ≤ N} b_n^t n^{−s_*} + γ Σ_{n ≤ N} n^y b_n^t n^{−(conj(s_*) + κ)}`. -/
def ft (t x y : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 (NP t x), (bnt t n : ℂ) / (n : ℂ) ^ sStar t x y)
  + gammaP t x y * ∑ n ∈ Finset.Icc 1 (NP t x),
      (((n : ℝ) ^ y * bnt t n : ℝ) : ℂ) / (n : ℂ) ^ ((starRingEnd ℂ) (sStar t x y) + kappa t x y)

/-- P15 (44), as a function of `(σ, T)`:
`ε_{t,n}(σ+iT) = exp(((t²/8)|α(σ+iT) − log n|² + t/4 + 1/6)/(T − 3.33)) − 1`. -/
def epsTN (t : ℝ) (n : ℕ) (σ T : ℝ) : ℝ :=
  Real.exp ((t ^ 2 / 8 * ‖alpha ((σ : ℂ) + (T : ℂ) * I) - (Real.log n : ℂ)‖ ^ 2 + t / 4 + 1 / 6)
    / (T - 3.33)) - 1

/-- P15 (68): `T' = x/2 + πt/8`. -/
def Tprime (t x : ℝ) : ℝ := x / 2 + Real.pi * t / 8

/-- P15 (59), as a function of `(σ, T)`, with P15 (49) `a = √(T'/(2π))` and `T' = T + πt/8`:
`ε̃(σ+iT) = (0.397·9^σ/(a − 0.865) + 5/(3(T − 6))) exp(3.49/(T − 4))`. -/
def epsTilde (t σ T : ℝ) : ℝ :=
  (0.397 * (9 : ℝ) ^ σ / (Real.sqrt ((T + Real.pi * t / 8) / (2 * Real.pi)) - 0.865)
      + 5 / (3 * (T - 6))) * Real.exp (3.49 / (T - 4))

/-- P15 (71) (with `Re s_*` for the printed `Re s`): `e_A = |γ| Σ n^y b_n^t n^{−(Re s_* + Re κ)} ε_{t,n}(s₋)`. -/
def eA (t x y : ℝ) : ℝ :=
  ‖gammaP t x y‖ * ∑ n ∈ Finset.Icc 1 (NP t x),
    (n : ℝ) ^ y * bnt t n / (n : ℝ) ^ ((sStar t x y).re + (kappa t x y).re)
      * epsTN t n ((1 - y) / 2) (x / 2)

/-- P15 (72) (with `Re s_*` for the printed `Re s`): `e_B = Σ b_n^t n^{−Re s_*} ε_{t,n}(s₊)`. -/
def eB (t x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (NP t x),
    bnt t n / (n : ℝ) ^ (sStar t x y).re * epsTN t n ((1 + y) / 2) (x / 2)

/-- P15 (74): `e_{C,0} = exp(tπ²/64) |M_0(iT')| / |M_t(s₊)| · (1 + ε̃(s₋) + ε̃(s₊))`. -/
def eC0 (t x y : ℝ) : ℝ :=
  Real.exp (t * Real.pi ^ 2 / 64) * ‖M0 ((Tprime t x : ℂ) * I)‖ / ‖Bt t x y‖
    * (1 + epsTilde t ((1 - y) / 2) (x / 2) + epsTilde t ((1 + y) / 2) (x / 2))

/-- **P15 Theorem 1.3, display (13)**, the M5 target: in the region (5)
(`0 < t ≤ 1/2`, `0 ≤ y ≤ 1`, `x ≥ 200`),
`|H_t(x+iy)/B_t(x+iy) − f_t(x+iy)| ≤ e_A + e_B + e_{C,0}`.  NOT proved on this island. -/
def P15Thm13 : Prop :=
  ∀ t x y : ℝ, 0 < t → t ≤ 1 / 2 → 0 ≤ y → y ≤ 1 → 200 ≤ x →
    ‖DBN.H t ((x : ℂ) + (y : ℂ) * I) / Bt t x y - ft t x y‖ ≤ eA t x y + eB t x y + eC0 t x y

/-- `B_t` never vanishes (it is an exponential). -/
theorem Bt_ne_zero (t x y : ℝ) : Bt t x y ≠ 0 := Complex.exp_ne_zero _

/-- **P15 Corollary 1.4 (criterion for non-vanishing)**, CONDITIONAL on the M5 target `P15Thm13`:
in the region (5), `|f_t(x+iy)| > e_A + e_B + e_{C,0}` forces `H_t(x+iy) ≠ 0`.  This is the step
through which a barrier/canopy certificate (milestone M6) consumes M5. -/
theorem H_ne_zero_of_P15Thm13 (h13 : P15Thm13) {t x y : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hx : 200 ≤ x)
    (hcrit : eA t x y + eB t x y + eC0 t x y < ‖ft t x y‖) :
    DBN.H t ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  intro hH
  have h := h13 t x y ht0 ht hy0 hy1 hx
  rw [hH, zero_div, zero_sub, norm_neg] at h
  linarith

/-! ### The normalization step (layer L13): P15 Corollary 6.5 implies Theorem 1.3 (13)

Corollary 6.5 is the unnormalized "A + B approximation" that the contour analysis produces
(Propositions 6.1 and 6.3 fed into (39)).  Dividing it by `B_t` gives (13).  The identities used
are the conjugation symmetry `alpha = alpha^*` (DBNM5Alpha) and `conj(s_*) + kappa − y =
s₋ + (t/2) alpha(s₋)`: this is where the overline in P15 (14) and the reading `Re s_*` in (71),
(72) are forced. -/

/-- P15 Corollary 6.4: `A_{t,N}(x+iy) = M_t(s₋) Σ b_n^t n^{−(s₋ + (t/2) alpha(s₋))}`. -/
def AtN (t x y : ℝ) : ℂ :=
  Mt t ((1 - (y : ℂ) + (x : ℂ) * I) / 2) * ∑ n ∈ Finset.Icc 1 (NP t x),
    (bnt t n : ℂ) / (n : ℂ) ^ ((1 - (y : ℂ) + (x : ℂ) * I) / 2
      + (t : ℂ) / 2 * alpha ((1 - (y : ℂ) + (x : ℂ) * I) / 2))

/-- P15 Corollary 6.4: `B_{t,N}(x+iy) = M_t(s₊) Σ b_n^t n^{−(s₊ + (t/2) alpha(s₊))}`. -/
def BtN (t x y : ℝ) : ℂ :=
  Mt t ((1 + (y : ℂ) - (x : ℂ) * I) / 2) * ∑ n ∈ Finset.Icc 1 (NP t x),
    (bnt t n : ℂ) / (n : ℂ) ^ ((1 + (y : ℂ) - (x : ℂ) * I) / 2
      + (t : ℂ) / 2 * alpha ((1 + (y : ℂ) - (x : ℂ) * I) / 2))

/-- P15 Corollary 6.4: `E_A = |M_t(s₋)| Σ b_n^t n^{−((1−y)/2 + (t/2) Re alpha(s₋))} ε_{t,n}(s₋)`. -/
def EA (t x y : ℝ) : ℝ :=
  ‖Mt t ((1 - (y : ℂ) + (x : ℂ) * I) / 2)‖ * ∑ n ∈ Finset.Icc 1 (NP t x),
    bnt t n / (n : ℝ) ^ ((1 - y) / 2 + t / 2 * (alpha ((1 - (y : ℂ) + (x : ℂ) * I) / 2)).re)
      * epsTN t n ((1 - y) / 2) (x / 2)

/-- P15 Corollary 6.4: `E_B = |M_t(s₊)| Σ b_n^t n^{−((1+y)/2 + (t/2) Re alpha(s₊))} ε_{t,n}(s₊)`. -/
def EB (t x y : ℝ) : ℝ :=
  ‖Mt t ((1 + (y : ℂ) - (x : ℂ) * I) / 2)‖ * ∑ n ∈ Finset.Icc 1 (NP t x),
    bnt t n / (n : ℝ) ^ ((1 + y) / 2 + t / 2 * (alpha ((1 + (y : ℂ) - (x : ℂ) * I) / 2)).re)
      * epsTN t n ((1 + y) / 2) (x / 2)

/-- P15 Corollary 6.5: `E_{C,0} = exp(tπ²/64) |M_0(iT')| (1 + ε̃(s₋) + ε̃(s₊))`. -/
def EC0 (t x y : ℝ) : ℝ :=
  Real.exp (t * Real.pi ^ 2 / 64) * ‖M0 ((Tprime t x : ℂ) * I)‖
    * (1 + epsTilde t ((1 - y) / 2) (x / 2) + epsTilde t ((1 + y) / 2) (x / 2))

/-- **P15 Corollary 6.5 (A + B approximation)**, unnormalized: in the region (5),
`|H_t(x+iy) − (A_{t,N} + B_{t,N})| ≤ E_A + E_B + E_{C,0}`.  NOT proved on this island; it is what
the analytic layers L4-L12 of the design memo must produce. -/
def P15Cor65 : Prop :=
  ∀ t x y : ℝ, 0 < t → t ≤ 1 / 2 → 0 ≤ y → y ≤ 1 → 200 ≤ x →
    ‖DBN.H t ((x : ℂ) + (y : ℂ) * I) - (AtN t x y + BtN t x y)‖ ≤ EA t x y + EB t x y + EC0 t x y

/-- The exponent identity `conj(s_*) + kappa = s₋ + (t/2) alpha(s₋) + y` (for `x ≠ 0`). -/
theorem conj_sStar_add_kappa (t : ℝ) {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    (starRingEnd ℂ) (sStar t x y) + kappa t x y
      = (1 - (y : ℂ) + (x : ℂ) * I) / 2 + (t : ℂ) / 2 * alpha ((1 - (y : ℂ) + (x : ℂ) * I) / 2)
        + (y : ℂ) := by
  have him : ((1 + (y : ℂ) - (x : ℂ) * I) / 2).im ≠ 0 := by simp [hx]
  have hc : (starRingEnd ℂ) ((1 + (y : ℂ) - (x : ℂ) * I) / 2) = (1 + (y : ℂ) + (x : ℂ) * I) / 2 := by
    simp [map_div₀, map_ofNat]
  have ha := alpha_conj him
  rw [hc] at ha
  unfold sStar kappa
  have e1 : (starRingEnd ℂ) ((1 + (y : ℂ) - (x : ℂ) * I) / 2
        + (t : ℂ) / 2 * alpha ((1 + (y : ℂ) - (x : ℂ) * I) / 2))
      = (1 + (y : ℂ) + (x : ℂ) * I) / 2 + (t : ℂ) / 2 * alpha ((1 + (y : ℂ) + (x : ℂ) * I) / 2) := by
    rw [map_add, map_mul, hc, ha]
    simp [map_div₀, map_ofNat]
  rw [e1]
  ring

/-- `B_t f_t = A_{t,N} + B_{t,N}` (for `x ≠ 0`). -/
theorem Bt_mul_ft (t : ℝ) {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    Bt t x y * ft t x y = AtN t x y + BtN t x y := by
  have hB : Bt t x y ≠ 0 := Bt_ne_zero t x y
  have hterm : ∀ n ∈ Finset.Icc 1 (NP t x),
      (((n : ℝ) ^ y * bnt t n : ℝ) : ℂ) / (n : ℂ) ^ ((starRingEnd ℂ) (sStar t x y) + kappa t x y)
        = (bnt t n : ℂ) / (n : ℂ) ^ ((1 - (y : ℂ) + (x : ℂ) * I) / 2
          + (t : ℂ) / 2 * alpha ((1 - (y : ℂ) + (x : ℂ) * I) / 2)) := by
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (show n ≠ 0 by omega)
    rw [conj_sStar_add_kappa t hx y, cpow_add _ _ hn0, ofReal_mul,
      ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
    have hy0 : (n : ℂ) ^ (y : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; exact fun h ↦ hn0 h.1
    field_simp
  unfold ft
  rw [Finset.sum_congr rfl hterm]
  unfold AtN BtN gammaP
  rw [show Bt t x y = Mt t ((1 + (y : ℂ) - (x : ℂ) * I) / 2) from rfl] at hB ⊢
  unfold sStar
  field_simp
  ring

/-- `E_A / |B_t| = e_A` (for `x ≠ 0`). -/
theorem EA_div_Bt (t : ℝ) {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    EA t x y / ‖Bt t x y‖ = eA t x y := by
  have hB : ‖Bt t x y‖ ≠ 0 := norm_ne_zero_iff.mpr (Bt_ne_zero t x y)
  have hre : (sStar t x y).re + (kappa t x y).re
      = (1 - y) / 2 + t / 2 * (alpha ((1 - (y : ℂ) + (x : ℂ) * I) / 2)).re + y := by
    have h := congrArg Complex.re (conj_sStar_add_kappa t hx y)
    simp only [add_re, conj_re] at h
    rw [h]
    simp only [div_ofNat_re, add_re, sub_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_zero, div_ofNat_im, zero_div, zero_mul]
    ring
  have hterm : ∀ n ∈ Finset.Icc 1 (NP t x),
      (n : ℝ) ^ y * bnt t n / (n : ℝ) ^ ((sStar t x y).re + (kappa t x y).re)
        * epsTN t n ((1 - y) / 2) (x / 2)
      = bnt t n / (n : ℝ) ^ ((1 - y) / 2 + t / 2 * (alpha ((1 - (y : ℂ) + (x : ℂ) * I) / 2)).re)
        * epsTN t n ((1 - y) / 2) (x / 2) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by
      have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (show 0 < n by omega)
    rw [hre, Real.rpow_add hn0]
    have : (n : ℝ) ^ y ≠ 0 := (Real.rpow_pos_of_pos hn0 y).ne'
    field_simp
  unfold eA EA gammaP
  rw [Finset.sum_congr rfl hterm, norm_div]
  rw [show Bt t x y = Mt t ((1 + (y : ℂ) - (x : ℂ) * I) / 2) from rfl] at hB ⊢
  field_simp

/-- `E_B / |B_t| = e_B`. -/
theorem EB_div_Bt (t x y : ℝ) : EB t x y / ‖Bt t x y‖ = eB t x y := by
  have hB : ‖Bt t x y‖ ≠ 0 := norm_ne_zero_iff.mpr (Bt_ne_zero t x y)
  unfold eB EB
  rw [re_sStar]
  rw [show Bt t x y = Mt t ((1 + (y : ℂ) - (x : ℂ) * I) / 2) from rfl] at hB ⊢
  field_simp

/-- `E_{C,0} / |B_t| = e_{C,0}`. -/
theorem EC0_div_Bt (t x y : ℝ) : EC0 t x y / ‖Bt t x y‖ = eC0 t x y := by
  unfold eC0 EC0
  ring

/-- **Layer L13: P15 Corollary 6.5 ⟹ P15 Theorem 1.3 (13).**  The normalization step of P15
section 6.3, proved; the analytic content lives entirely in `P15Cor65`. -/
theorem P15Thm13_of_P15Cor65 (h : P15Cor65) : P15Thm13 := by
  intro t x y ht0 ht hy0 hy1 hx
  have hx0 : x ≠ 0 := by linarith
  have hB : Bt t x y ≠ 0 := Bt_ne_zero t x y
  have hBn : 0 < ‖Bt t x y‖ := norm_pos_iff.mpr hB
  have hc := h t x y ht0 ht hy0 hy1 hx
  have e1 : DBN.H t ((x : ℂ) + (y : ℂ) * I) / Bt t x y - ft t x y
      = (DBN.H t ((x : ℂ) + (y : ℂ) * I) - (AtN t x y + BtN t x y)) / Bt t x y := by
    rw [← Bt_mul_ft t hx0 y]; field_simp
  rw [e1, norm_div, ← EA_div_Bt t hx0 y, ← EB_div_Bt t x y, ← EC0_div_Bt t x y,
    ← add_div, ← add_div]
  exact div_le_div_of_nonneg_right hc hBn.le

end

end DBNM5
