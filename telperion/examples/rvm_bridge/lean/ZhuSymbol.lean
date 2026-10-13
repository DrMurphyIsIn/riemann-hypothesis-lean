/-
  ZhuSymbol -- Zhu eq. (2) (arXiv:2608.24827 v2), the frequency-side symbol representation of
  the Weil form, PROVED on the rvm_bridge island (2026-09-23).

  STATEMENT (the registry's `WeilWindow.SymbolRepresentation L`, mirrored VERBATIM below): for
  every real even smooth compactly supported f with tsupport f ⊆ [-L, L],
      Q(f) := Re weilForm (autocorr f)
            = 2 F(i/2)^2 + (1/2π) ∫ |F(t)|^2 Ψ_L(t) dt,
  with F(z) = ∫ f(u) e^{izu} du (so F(t) = weilKernel f (1/2 + it), F(i/2) = weilKernel f 0) and
  Ψ_L the Weil symbol of eq. (3):
      Ψ_L(t) = Re ψ(1/4 + it/2) - log π - Σ_{log n < 2L} (2Λ(n)/√n) cos(t log n).

  ROUTE.  A rearrangement of the E8 primes-side functional archSide - primeSide (the right-hand
  side of the PROVED node RH_limit_explicit_formula) for g = autocorr f:
    * pole terms: weilKernel g 0 = weilKernel g 1 = |F(i/2)|^2 by Zeta23's transform
      factorisation `paperFT_weilTest` (h_{f*f~}(z) = h_f(z) conj h_f(conj z)) and evenness;
    * archimedean integral: weilKernel g (1/2 + it) = |F(t)|^2 (E6Bridge5);
    * the -g(0) log π term: g(0) = ‖f‖_2^2 = (1/2π) ∫ |F|^2 (Plancherel, as Fourier inversion of
      g at 0, E6Bridge4 `inversion_zero`);
    * prime side: g(log n) = (1/2π) ∫ |F(t)|^2 cos(t log n) dt (Fourier inversion, cosine form,
      Zeta23 `Taper.integral_mul_cos_of_paperFT_eq`), g even, and g(log n) = 0 once log n ≥ 2L
      because supp g ⊆ [-2L, 2L] (the equality case is a null set); the comb is a FINITE sum
      (n < e^{2L}), so it passes through the integral.
  Nothing about zeros is used or claimed.  No `sorry`.  conjecture1_proved = False.
-/
import E6Bridge5
import Zeta23.Taper.Fourier

open MeasureTheory Zeta23
open scoped ComplexConjugate

/-! ## A. The WeilForm vocabulary, mirrored VERBATIM from
telperion/examples/weil_form_enclosure/lean/WeilFormDefs.lean (= missions/rh RHDefs.lean, namespace
WeilForm).  `WeilForm.autocorr` is definitionally `WeilExplicit.autocorr` (E6Bridge5). -/

namespace WeilForm
open WeilExplicit

/-- The Weil pairing of a test function: the E8 right-hand side `archSide f - primeSide f`,
    which `RH_limit_explicit_formula` identifies with the sum over the zeros
    `Σ_ρ zeroMult ρ · weilKernel f ρ`.  Evaluating THIS is what the `weil_form_enclosure`
    emitter's Arb backend does; the kernel only ever sees an enclosure of it as a hypothesis. -/
noncomputable def weilForm (f : ℝ → ℂ) : ℂ :=
  archSide f - primeSide f

/-- The cross-correlation `f_{ij}(x) = ∫ g_i(t) conj (g_j (t - x)) dt`.  Its diagonal
    `crossCorr g g` is the autocorrelation `g ⋆ g̃` on which Weil positivity is stated; the
    off-diagonal entries are the Weil-Gram matrix's off-diagonal entries. -/
noncomputable def crossCorr (gi gj : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ t : ℝ, gi t * (starRingEnd ℂ) (gj (t - x))

/-- The autocorrelation, the diagonal of `crossCorr`. -/
noncomputable abbrev autocorr (g : ℝ → ℂ) : ℝ → ℂ := crossCorr g g

end WeilForm

/-! ## B. The registry-facing definitions (mirrored verbatim into RHDefs `WeilWindow`). -/

namespace WeilWindow
open MeasureTheory Complex WeilExplicit WeilForm

/-- Zhu eq. (3), the Weil symbol `Ψ_L(t) = Re ψ(1/4 + it/2) - log π - Σ_{log n < 2L} (2Λ(n)/√n)
    cos(t log n)`.  The comb is a FINITE sum (`n < e^{2L}`) with total mass `combMass L`. -/
noncomputable def weilSymbol (L : ℝ) (t : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + ((t : ℂ) / 2) * Complex.I)).re - Real.log Real.pi
    - ∑' n : ℕ, if Real.log n < 2 * L then
        2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0

/-- Zhu eq. (2), CONCRETE: for real even smooth compactly supported `f` supported in `[-L, L]`,
    `Q(f) = 2 F(i/2)² + (1/2π) ∫ |F(t)|² Ψ_L(t) dt` with `F(t) = weilKernel f (1/2 + it)` and
    `F(i/2) = weilKernel f 0`.  A rearrangement of the PROVED `RH_limit_explicit_formula`'s
    primes-side functional. -/
def SymbolRepresentation (L : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    (WeilForm.weilForm (WeilForm.autocorr f)).re
      = 2 * ‖WeilExplicit.weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖WeilExplicit.weilKernel f (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 * weilSymbol L t

/-- Zhu eq. (2) in the ODD sector (Lemma 6.1): for real ODD smooth compactly supported `f`
    supported in `[-L, L]`, `Q(f) = -2 F(i/2)² + (1/2π) ∫ |F(t)|² Ψ_L(t) dt`; the pole term
    changes sign, the multiplier term is parity-blind. -/
def SymbolRepresentationOdd (L : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, WeilExplicit.IsWeilTest f → (∀ x, (f x).im = 0) → (∀ x, f (-x) = -f x) →
    tsupport f ⊆ Set.Icc (-L) L →
    (WeilForm.weilForm (WeilForm.autocorr f)).re
      = -2 * ‖WeilExplicit.weilKernel f 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖WeilExplicit.weilKernel f (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 * weilSymbol L t

end WeilWindow

/-! ## C. The proof. -/

noncomputable section

namespace RvMBridgeZhu
open WeilExplicit RvMBridge4 RvMBridge5

lemma weilForm_autocorr_eq (f : ℝ → ℂ) :
    WeilForm.weilForm (WeilForm.autocorr f) = WeilExplicit.weilForm (WeilExplicit.autocorr f) := rfl

/-- The autocorrelation of a real function is real: its values are `∫ v x * v (x - y)`. -/
lemma autocorr_ofReal_eq (v : ℝ → ℝ) :
    WeilExplicit.autocorr (fun u => (v u : ℂ)) = fun y => ((∫ x : ℝ, v x * v (x - y) : ℝ) : ℂ) := by
  funext y
  unfold WeilExplicit.autocorr
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [Complex.conj_ofReal]
  push_cast
  ring

/-- The autocorrelation of a real function of definite parity (`v(-u) = ε v(u)`, `ε² = 1`) is
even. -/
lemma autocorr_neg_of_parity {v : ℝ → ℝ} {ε : ℝ} (hε : ε * ε = 1) (hpar : ∀ u, v (-u) = ε * v u)
    (y : ℝ) :
    WeilExplicit.autocorr (fun u => (v u : ℂ)) (-y) = WeilExplicit.autocorr (fun u => (v u : ℂ)) y := by
  have hεC : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
  unfold WeilExplicit.autocorr
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1
  funext x
  simp only
  rw [hpar x, sub_neg_eq_add, show -x - y = -(x + y) by ring, hpar (x + y), Complex.conj_ofReal,
    Complex.conj_ofReal]
  push_cast
  linear_combination (-((v x : ℂ) * (v (x + y) : ℂ))) * hεC

/-- The transform of a real function of definite parity: `h_v(-z) = ε h_v(z)`. -/
lemma paperFT_neg_of_parity {v : ℝ → ℝ} {ε : ℝ} (hε : ε * ε = 1) (hpar : ∀ u, v (-u) = ε * v u)
    (z : ℂ) :
    paperFT (fun u => (v u : ℂ)) (-z) = (ε : ℂ) * paperFT (fun u => (v u : ℂ)) z := by
  have hεC : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
  unfold paperFT
  rw [← integral_const_mul]
  conv_rhs => rw [← integral_neg_eq_self]
  congr 1
  funext u
  simp only
  rw [hpar u]
  push_cast
  rw [show Complex.I * z * -(u : ℂ) = Complex.I * -z * u by ring]
  linear_combination (-((v u : ℂ) * Complex.exp (Complex.I * -z * u))) * hεC

/-- Support: `f` supported in `[-L, L]` makes `autocorr f` vanish for `|y| ≥ 2L` (the boundary
case is a single-point null set). -/
lemma autocorr_eq_zero_of_two_mul_le {v : ℝ → ℝ} {L : ℝ}
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Set.Icc (-L) L) {y : ℝ} (hy : 2 * L ≤ |y|) :
    WeilExplicit.autocorr (fun u => (v u : ℂ)) y = 0 := by
  have hv : ∀ x, v x ≠ 0 → |x| ≤ L := by
    intro x hx
    have hmem : x ∈ tsupport (fun u => (v u : ℂ)) :=
      subset_tsupport _ (by simpa [Function.mem_support] using hx)
    have := hsupp hmem
    exact abs_le.mpr ⟨this.1, this.2⟩
  unfold WeilExplicit.autocorr
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) ((Set.toFinite ({L, -L} : Set ℝ)).countable.measure_zero _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, Complex.conj_ofReal] at hx
  have hx' : v x ≠ 0 ∧ v (x - y) ≠ 0 := by
    refine ⟨fun h => hx ?_, fun h => hx ?_⟩
    · simp [h]
    · simp [h]
  have h1 := abs_le.mp (hv _ hx'.1)
  have h2 := abs_le.mp (hv _ hx'.2)
  rcases le_abs.mp hy with h | h
  · have : x = L := le_antisymm h1.2 (by linarith [h2.1])
    simp [this]
  · have : x = -L := le_antisymm (by linarith [h2.2]) h1.1
    simp [this]

/-- The main computation, for `f = ofReal ∘ v` with `v(-u) = ε v(u)`, `ε² = 1` (`ε = 1` even,
`ε = -1` odd): `Q(f) = 2 ε |F(i/2)|² + (1/2π) ∫ |F|² Ψ_L`. -/
theorem symbol_representation_ofReal {v : ℝ → ℝ} {L ε : ℝ} (hε : ε * ε = 1)
    (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = ε * v u)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Set.Icc (-L) L) :
    (WeilForm.weilForm (WeilForm.autocorr (fun u => (v u : ℂ)))).re
      = 2 * ε * ‖WeilExplicit.weilKernel (fun u => (v u : ℂ)) 0‖ ^ 2
        + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, ‖WeilExplicit.weilKernel (fun u => (v u : ℂ)) (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2
            * WeilWindow.weilSymbol L t := by
  set fC : ℝ → ℂ := fun u => (v u : ℂ) with hfC
  set g : ℝ → ℂ := WeilExplicit.autocorr fC with hgdef
  have hg : IsWeilTest g := isWeilTest_autocorr hf
  have hcont : Continuous fC := hf.1.continuous
  have hcs : HasCompactSupport fC := hf.2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the transform on the line and the symbol weight
  set F : ℝ → ℝ := fun r => ‖weilKernel fC (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2 with hF
  set psi : ℝ → ℝ := fun r => (Complex.digamma (1 / 4 + ((r : ℂ) / 2) * Complex.I)).re with hpsi
  have hline : ∀ r : ℝ, paperFT g r = (F r : ℂ) := by
    intro r
    rw [← weilKernel_line, hgdef, weilKernel_autocorr_line hf, hF]
    simp only
    rw [weilKernel_line]
    push_cast
    ring
  /- pole terms -/
  have hcI : (starRingEnd ℂ) (Complex.I / 2) = -(Complex.I / 2) := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hcI' : (starRingEnd ℂ) (-Complex.I / 2) = Complex.I / 2 := by
    simp [Complex.conj_I, map_ofNat, neg_div]
  have hpole0 : weilKernel g 0 = ((ε * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_zero, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hcont hcont hcs hcs, hcI,
      hfC, paperFT_neg_of_parity hε hev, map_mul, Complex.conj_ofReal, mul_left_comm,
      Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  have hpole1 : weilKernel g 1 = ((ε * ‖weilKernel fC 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [weilKernel_one, hgdef, autocorr_eq_weilTest, EF.paperFT_weilTest hcont hcont hcs hcs, hcI',
      hfC, neg_div, paperFT_neg_of_parity hε hev, mul_assoc, Complex.mul_conj', weilKernel_zero]
    push_cast
    ring
  /- g(0) = ‖f‖² and Plancherel -/
  have hg0 : g 0 = ((∫ x : ℝ, ‖fC x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hgdef]
    unfold WeilExplicit.autocorr
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [sub_zero, Complex.mul_conj']
    push_cast
    ring
  have hFint : Integrable F := by
    have := (integrable_paperFT hg).re
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp [hline r]
  have hplan : (∫ x : ℝ, ‖fC x‖ ^ 2) = (1 / (2 * Real.pi)) * ∫ r, F r := by
    have h := inversion_zero hg
    rw [hg0] at h
    have h2 : ∫ r : ℝ, paperFT g r = ((∫ r, F r : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext r
      exact hline r
    rw [h2] at h
    have h3 : ((1 / (2 * Real.pi) * ∫ r, F r : ℝ) : ℂ) = ((∫ x : ℝ, ‖fC x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact h
    exact (Complex.ofReal_inj.mp h3).symm
  /- the archimedean integral -/
  have harch_pt : ∀ r : ℝ, archIntegrand g r = ((F r * psi r : ℝ) : ℂ) := by
    intro r
    unfold archIntegrand
    rw [hgdef, weilKernel_autocorr_line hf, hF, hpsi]
    simp only
    rw [weilKernel_line]
    push_cast
    ring
  have harch : ∫ r : ℝ, archIntegrand g r = ((∫ r, F r * psi r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    exact harch_pt r
  have hFpsi : Integrable (fun r => F r * psi r) := by
    have := (integrable_archIntegrand hg).re
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp [harch_pt r]
  /- the prime side -/
  set A : ℝ → ℝ := fun y => (g y).re with hA
  have hgA : g = fun y => (A y : ℂ) := by
    funext y
    rw [hA]
    simp only
    rw [hgdef, autocorr_ofReal_eq]
    simp
  have hAc : Continuous A := Complex.continuous_re.comp hg.1.continuous
  have hAi : Integrable A := by
    exact (hg.1.continuous.integrable_of_hasCompactSupport (μ := volume) hg.2).re
  have hFT : ∀ r : ℝ, paperFT (fun u => (A u : ℂ)) r = (F r : ℂ) := by
    intro r
    rw [← hgA]
    exact hline r
  have hcosint : ∀ n : ℕ, ∫ r, F r * Real.cos (r * Real.log n) = 2 * Real.pi * A (Real.log n) :=
    fun n => Taper.integral_mul_cos_of_paperFT_eq hAc hAi hFint hFT (Real.log n)
  have hgeven : ∀ y, g (-y) = g y := fun y => by
    rw [hgdef]
    exact autocorr_neg_of_parity hε hev y
  have hgzero : ∀ y, 2 * L ≤ |y| → g y = 0 := fun y hy => by
    rw [hgdef]
    exact autocorr_eq_zero_of_two_mul_le hsupp hy
  -- the real prime term
  set term : ℕ → ℝ := fun n => if Real.log n < 2 * L then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * ∫ r, F r * Real.cos (r * Real.log n)
    else 0 with hterm
  have hprime_pt : ∀ n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))
        = (((1 / (2 * Real.pi)) * term n : ℝ) : ℂ) := by
    intro n
    rw [hterm]
    simp only
    split_ifs with hn
    · rw [hgeven, hcosint n]
      have hgn : g (Real.log n) = (A (Real.log n) : ℂ) := by rw [hgA]
      rw [hgn]
      push_cast
      field_simp
      ring
    · have h1 : g (Real.log n) = 0 := hgzero _ ((not_lt.mp hn).trans (le_abs_self _))
      have h2 : g (-Real.log n) = 0 := hgzero _ (by rw [abs_neg]; exact (not_lt.mp hn).trans (le_abs_self _))
      rw [h1, h2]
      simp
  -- the comb is finite
  set N0 : ℕ := ⌈Real.exp (2 * L)⌉₊ + 1 with hN0
  have hbig : ∀ n : ℕ, n ∉ Finset.range N0 → ¬ Real.log n < 2 * L := by
    intro n hn hlt
    have hn' : N0 ≤ n := by simpa [Finset.mem_range] using hn
    have h1 : Real.exp (2 * L) < (n : ℝ) := by
      have := Nat.le_ceil (Real.exp (2 * L))
      have h2 : ((⌈Real.exp (2 * L)⌉₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have h3 : 2 * L < Real.log n := by
      rw [← Real.log_exp (2 * L)]
      exact Real.log_lt_log (Real.exp_pos _) h1
    linarith
  have hprime : primeSide g = (((1 / (2 * Real.pi)) * ∑ n ∈ Finset.range N0, term n : ℝ) : ℂ) := by
    unfold primeSide
    have hvan : ∀ n ∉ Finset.range N0, term n = 0 := fun n hn => by
      rw [hterm]; simp only; rw [if_neg (hbig n hn)]
    rw [tsum_congr hprime_pt, ← Complex.ofReal_tsum, tsum_mul_left,
      tsum_eq_sum (s := Finset.range N0) hvan]
  /- the symbol as a finite sum, and the interchange -/
  have hsym : ∀ t : ℝ, WeilWindow.weilSymbol L t = psi t - Real.log Real.pi
      - ∑ n ∈ Finset.range N0, (if Real.log n < 2 * L then
          2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0) := by
    intro t
    unfold WeilWindow.weilSymbol
    rw [tsum_eq_sum (s := Finset.range N0) (fun n hn => by rw [if_neg (hbig n hn)])]
  have hcosI : ∀ n : ℕ, Integrable (fun r => F r * Real.cos (r * Real.log n)) := by
    intro n
    have h := hFint.bdd_mul (c := 1)
      (by fun_prop : Continuous fun r : ℝ => Real.cos (r * Real.log n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    exact h.congr (Filter.Eventually.of_forall fun r => mul_comm _ _)
  have htermI : ∀ n ∈ Finset.range N0, Integrable (fun r => F r * (if Real.log n < 2 * L then
      2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (r * Real.log n) else 0)) := by
    intro n _
    split_ifs with hn
    · have := (hcosI n).const_mul (2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n)
      exact this.congr (Filter.Eventually.of_forall fun r => by simp only; ring)
    · simp
  have hint : ∫ t : ℝ, F t * WeilWindow.weilSymbol L t
      = (∫ r, F r * psi r) - Real.log Real.pi * (∫ r, F r) - ∑ n ∈ Finset.range N0, term n := by
    have e : (fun t : ℝ => F t * WeilWindow.weilSymbol L t)
        = fun t => (F t * psi t - F t * Real.log Real.pi)
          - ∑ n ∈ Finset.range N0, F t * (if Real.log n < 2 * L then
              2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0) := by
      funext t
      rw [hsym t, ← Finset.mul_sum]
      ring
    have hI1 : Integrable (fun t => F t * psi t - F t * Real.log Real.pi) :=
      hFpsi.sub (hFint.mul_const _)
    have hI2 : Integrable (fun t => F t * Real.log Real.pi) := hFint.mul_const _
    rw [e, integral_sub hI1 (integrable_finsetSum _ htermI),
      integral_sub hFpsi hI2, integral_mul_const, integral_finsetSum _ htermI]
    have hterm_eq : ∀ n ∈ Finset.range N0,
        (∫ t, F t * (if Real.log n < 2 * L then
          2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * Real.cos (t * Real.log n) else 0))
          = term n := by
      intro n _
      rw [hterm]
      simp only
      split_ifs with hn
      · rw [← integral_const_mul]
        congr 1
        funext t
        ring
      · simp
    rw [Finset.sum_congr rfl hterm_eq]
    ring
  /- assembly -/
  have hcomplex : archSide g - primeSide g
      = ((2 * ε * ‖weilKernel fC 0‖ ^ 2 + (1 / (2 * Real.pi)) *
          ∫ t : ℝ, F t * WeilWindow.weilSymbol L t : ℝ) : ℂ) := by
    unfold archSide
    rw [hpole0, hpole1, hg0, harch, hprime, hint, hplan]
    push_cast
    ring
  rw [weilForm_autocorr_eq, WeilExplicit.weilForm, ← hgdef, hcomplex, Complex.ofReal_re]

/-- **Zhu eq. (2), PROVED**: the registry's `SymbolRepresentation L`, for every `L`. -/
theorem symbolRepresentation (L : ℝ) : WeilWindow.SymbolRepresentation L := by
  intro f hf hreal hev hsupp
  obtain ⟨v, rfl⟩ : ∃ v : ℝ → ℝ, f = fun u => (v u : ℂ) :=
    ⟨fun u => (f u).re, funext fun u => Complex.ext (by simp) (by simp [hreal u])⟩
  have hev' : ∀ u, v (-u) = 1 * v u := fun u => by
    have h : ((v (-u) : ℝ) : ℂ) = (v u : ℝ) := hev u
    rw [one_mul]
    exact_mod_cast h
  have := symbol_representation_ofReal (ε := 1) (by norm_num) hf hev' hsupp
  rw [this]
  ring

/-- **Zhu eq. (2), ODD sector (Lemma 6.1), PROVED**: the registry's `SymbolRepresentationOdd L`. -/
theorem symbolRepresentationOdd (L : ℝ) : WeilWindow.SymbolRepresentationOdd L := by
  intro f hf hreal hodd hsupp
  obtain ⟨v, rfl⟩ : ∃ v : ℝ → ℝ, f = fun u => (v u : ℂ) :=
    ⟨fun u => (f u).re, funext fun u => Complex.ext (by simp) (by simp [hreal u])⟩
  have hodd' : ∀ u, v (-u) = -1 * v u := fun u => by
    have h : ((v (-u) : ℝ) : ℂ) = -(v u : ℝ) := hodd u
    rw [neg_one_mul]
    exact_mod_cast h
  have := symbol_representation_ofReal (ε := -1) (by norm_num) hf hodd' hsupp
  rw [this]
  ring

end RvMBridgeZhu

end
