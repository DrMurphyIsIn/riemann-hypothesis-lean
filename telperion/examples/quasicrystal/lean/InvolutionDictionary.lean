/-
  InvolutionDictionary.lean -- PROGRAM MIRRORMERE (reverse-Dyson) QC-1, Wave-2
  handoff W2a: the involution dictionary.

  Makes the slogan "functional equation ⟺ self-inversive symmetry" a kernel
  theorem, in the finite (polynomial / exponential-sum) model.

  TWO ANTI-HOLOMORPHIC INVOLUTIONS AND THE MAP THAT INTERTWINES THEM.

    * σ_circ : z ↦ 1 / conj z    -- fixed locus the unit circle |z| = 1.
      Self-inversive polynomials are exactly those whose (nonzero) root multiset
      respects σ_circ.
    * σ_line : x ↦ conj x        -- fixed locus the real line ℝ.
      "Functional-equation" objects (Hardy-Z-style REAL structure) are exactly
      those respecting σ_line.
    * z = e^{iωx}  (ω > 0 real)  INTERTWINES the two: it sends σ_line to σ_circ.

  DELIVERABLES.
    1. `intertwiner` : e^{iω·conj x} = (conj (e^{iωx}))⁻¹, the clean identity that
       transports σ_line to σ_circ; plus `fixed_locus_correspondence`, the
       re-export of `RationalFreqReduction.im_zero_iff_norm_one` (Im x = 0 ⟺
       |e^{iωx}| = 1 : fixed locus of σ_line ⟷ fixed locus of σ_circ).
    2. `selfInversive_zeros_symmetric` : a self-inversive `p` has its nonzero root
       *set* invariant under z ↦ 1/conj z (set-level; see doc-note on multiplicity).
    3. THE HEADLINER `selfInversive_iff_hardyZ_real` : for `p` self-inversive with
       phase `phase` and `p(0) ≠ 0`, the normalized exponential sum
         Z(x) := u · e^{-i n ω x / 2} · p(e^{iωx})          (n = natDegree p)
       with the unimodular constant `u` a fixed square root of `conj phase`, is
       REAL on ℝ.  This is the finite model of `LambdaLineReal.completedZeta_im_eq_zero`
       (Λ real on the critical line): the functional equation AS the reality of the
       completed function on the symmetry locus.
    4. `twoFreq_dictionary` : the binomial instance `c₁ + c₂ z^m` is self-inversive
       ⟺ |c₁| = |c₂|, tying `TwoFreqRigidity`'s equal-modulus hypothesis to the
       dictionary; corollary `selfInversive_binomial_realRooted` : the associated
       exponential sum is then real-rooted (reverse-Dyson in miniature).
    5. `fixed_locus_dichotomy` : each nonzero root of a self-inversive `p` is either
       on |z| = 1 or paired with its reflection 1/conj z (finite model of
       "on-line or in conjugate quartets").

  conjecture1_proved = False.  Every claim here is finite/unconditional; NONE of
  this decides RH or claims Lee-Yang membership is forced by spectral positivity.
-/
import LeeYangCore
import RationalFreqReduction
import TwoFreqRigidity
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp

open Polynomial Complex

namespace Quasicrystal

noncomputable section

/-! ## 1. The intertwiner and the fixed-locus correspondence -/

/-- **Intertwiner.**  For real `ω` and complex `x`, the exponential map `z = e^{iωx}`
carries the anti-holomorphic involution `σ_line : x ↦ conj x` (fixed locus ℝ) to
`σ_circ : z ↦ 1 / conj z` (fixed locus |z| = 1):

  `e^{iω·conj x} = (conj (e^{iωx}))⁻¹`.

Because `conj (e^{iωx}) = e^{-iω·conj x}`, its inverse is `e^{iω·conj x}` -- a clean
unconditional identity (needs `ω` real; no positivity, no `x` constraint). -/
theorem intertwiner (ω : ℝ) (x : ℂ) :
    Complex.exp ((ω : ℂ) * (starRingEnd ℂ) x * Complex.I)
      = ((starRingEnd ℂ) (Complex.exp ((ω : ℂ) * x * Complex.I)))⁻¹ := by
  rw [← Complex.exp_conj]
  rw [← Complex.exp_neg]
  congr 1
  -- conj (ω x I) = ω (conj x) (conj I) = -ω (conj x) I, negated gives ω (conj x) I
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **Fixed-locus correspondence.**  For `ω ≠ 0`, `x` lies on the fixed locus of
`σ_line` (the real line, `Im x = 0`) iff its image `z = e^{iωx}` lies on the fixed
locus of `σ_circ` (the unit circle, `|z| = 1`).  This is `im_zero_iff_norm_one`
re-exported into the dictionary's language. -/
theorem fixed_locus_correspondence (ω : ℝ) (x : ℂ) (hω : ω ≠ 0) :
    x.im = 0 ↔ ‖Complex.exp ((ω : ℂ) * x * Complex.I)‖ = 1 :=
  im_zero_iff_norm_one ω x hω

/-! ## 2. Self-inversive root symmetry -/

/-- **Self-inversive zeros are `σ_circ`-symmetric (set level).**  If `p` is
self-inversive and `z ≠ 0` is a root of `p`, then `1 / conj z` is also a root of `p`.
So the nonzero root SET of `p` is invariant under `σ_circ : z ↦ 1 / conj z`.

Doc-note (multiplicity): this is the set-level statement, which is the honest
content of `IsSelfInversive` as phrased (a pointwise functional identity).  The
multiset/with-multiplicity refinement would require differentiating the identity or
a coefficient-palindrome formulation; not claimed here. -/
theorem selfInversive_zeros_symmetric {p : ℂ[X]} (hp : IsSelfInversive p)
    {z : ℂ} (hz : z ≠ 0) (hroot : p.eval z = 0) :
    p.eval (1 / (starRingEnd ℂ) z) = 0 := by
  obtain ⟨phase, _hphase, hid⟩ := hp
  have h := hid z hz
  rw [hroot, mul_zero] at h
  -- h : z ^ natDegree p * conj (p.eval (1 / conj z)) = 0
  have hzpow : z ^ p.natDegree ≠ 0 := pow_ne_zero _ hz
  have hconj : (starRingEnd ℂ) (p.eval (1 / (starRingEnd ℂ) z)) = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hzpow
    · exact h1
  -- conj w = 0 ⇒ w = 0
  have := congrArg (starRingEnd ℂ) hconj
  simpa using this

/-! ## 3. THE HEADLINER: functional equation ⟺ reality on the symmetry locus -/

/-- The normalized exponential sum ("finite Hardy-Z"):
`Z(x) := u · e^{-i n ω x / 2} · p(e^{iωx})`, where `n = natDegree p` and `u : ℂ` is a
fixed unimodular normalizing constant.  Evaluated on real `x` (returning ℂ). -/
def hardyZ (p : ℂ[X]) (u : ℂ) (ω x : ℝ) : ℂ :=
  u * Complex.exp (-(((p.natDegree : ℝ) * ω * x / 2 : ℝ) : ℂ) * Complex.I)
    * p.eval (Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I))

/-- On the unit circle, the involution `σ_circ : z ↦ 1 / conj z` is the identity:
for `z = e^{iωx}` with `x` real, `1 / conj z = z`.  (The self-inversive functional
identity, evaluated at a circle point, collapses `p(1/conj z)` to `p(z)`.) -/
theorem inv_conj_exp_real (ω : ℝ) (x : ℝ) :
    1 / (starRingEnd ℂ) (Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I))
      = Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) := by
  set z : ℂ := Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) with hz
  have hznorm : ‖z‖ = 1 := by
    rw [hz]; exact_mod_cast norm_exp_arg ω x
  have hmul : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hznorm]; norm_num
  have hzne : (starRingEnd ℂ) z ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact one_ne_zero hmul.symm
  rw [div_eq_iff hzne]
  linear_combination -hmul

/-- **Self-inversive reality identity on the circle.**  If `p` satisfies the
self-inversive functional identity with unimodular phase `phase`, then at a circle
point `z = e^{iωx}` (x real) the identity collapses (via `1/conj z = z`) to
  `zⁿ · conj (p z) = phase · p z`,   n = natDegree p, zⁿ = e^{i n ω x}. -/
theorem selfInversive_circle_identity {p : ℂ[X]} {phase : ℂ}
    (hid : ∀ z : ℂ, z ≠ 0 →
      z ^ p.natDegree * (starRingEnd ℂ) (p.eval (1 / (starRingEnd ℂ) z))
        = phase * p.eval z)
    (ω : ℝ) (x : ℝ) :
    (Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) ^ p.natDegree
        * (starRingEnd ℂ) (p.eval (Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)))
      = phase * p.eval (Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I)) := by
  set z : ℂ := Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) with hz
  have hzne : z ≠ 0 := by rw [hz]; exact Complex.exp_ne_zero _
  have h := hid z hzne
  rwa [inv_conj_exp_real ω x] at h

/-- **THE HEADLINER: functional equation ⟺ reality on the symmetry locus.**

For `p` satisfying the self-inversive functional identity with unimodular phase
`phase`, and a normalizing constant `u` that is a unimodular square root of `phase`
(`‖u‖ = 1`, `u ^ 2 = phase`), the normalized exponential sum
  `Z(x) = u · e^{-i n ω x / 2} · p(e^{iωx})`,   n = natDegree p,
is REAL on the real line: `(hardyZ p u ω x).im = 0` for every real `x`.

This is the finite model of `LambdaLineReal.completedZeta_im_eq_zero` (the completed
zeta `Λ` is real on the critical line `Re s = 1/2`).  There, conjugation composed
with the functional equation `Λ(1-s) = Λ(s)` fixes `Λ` on the symmetry locus; here,
conjugation composed with the self-inversive identity `zⁿ conj(p z) = phase · p z`
fixes `Z` on the circle's preimage.  The half-degree phase `e^{-inωx/2}` and the
square-root normalization `u² = phase` are the finite analogues of the archimedean
`π^{-s/2}Γ(s/2)` completion factor that symmetrizes `s ↦ 1 - s`. -/
theorem selfInversive_iff_hardyZ_real {p : ℂ[X]} {phase u : ℂ}
    (hid : ∀ z : ℂ, z ≠ 0 →
      z ^ p.natDegree * (starRingEnd ℂ) (p.eval (1 / (starRingEnd ℂ) z))
        = phase * p.eval z)
    (hu_norm : ‖u‖ = 1) (hu_sq : u ^ 2 = phase) (ω : ℝ) (x : ℝ) :
    (hardyZ p u ω x).im = 0 := by
  set z : ℂ := Complex.exp ((ω : ℂ) * (x : ℂ) * Complex.I) with hz
  set E : ℂ := Complex.exp (-(((p.natDegree : ℝ) * ω * x / 2 : ℝ) : ℂ) * Complex.I)
    with hE
  -- conj E = E⁻¹, and E ≠ 0
  have hEne : E ≠ 0 := by rw [hE]; exact Complex.exp_ne_zero _
  have hconjE : (starRingEnd ℂ) E = E⁻¹ := by
    rw [hE, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    ring
  -- z ^ n = E⁻² :  z^n = exp(n ω x I),  E⁻² = exp(n ω x I)
  have hzpow : z ^ p.natDegree = (E⁻¹) ^ 2 := by
    rw [hz, hE, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- circle identity gives conj (p z) in terms of p z
  have hci := selfInversive_circle_identity hid ω x
  rw [← hz] at hci
  -- conj u * phase = u  (from |u| = 1 and u² = phase)
  have huu : (starRingEnd ℂ) u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu_norm]; norm_num
  have hconjphase : (starRingEnd ℂ) u * phase = u := by
    rw [← hu_sq]; linear_combination u * huu
  -- Now show conj Z = Z, then conclude im = 0.
  have hZeq : (starRingEnd ℂ) (hardyZ p u ω x) = hardyZ p u ω x := by
    unfold hardyZ
    rw [← hz, ← hE]
    rw [map_mul, map_mul, hconjE]
    -- goal: conj u * E⁻¹ * conj (p z) = u * E * p z
    -- from hci: z^n * conj(p z) = phase * p z, and z^n = E⁻², so conj(p z) = phase * p z * E²
    have hconjpz : (starRingEnd ℂ) (p.eval z) = phase * p.eval z * E ^ 2 := by
      have hEsq : (E⁻¹) ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hEne)
      rw [hzpow] at hci
      have : (starRingEnd ℂ) (p.eval z) = phase * p.eval z / (E⁻¹) ^ 2 := by
        rw [eq_div_iff hEsq]; linear_combination hci
      rw [this]
      field_simp
    rw [hconjpz]
    -- goal: conj u * E⁻¹ * (phase * p z * E²) = u * E * p z
    have hErw : E⁻¹ * E ^ 2 = E := by field_simp
    calc (starRingEnd ℂ) u * E⁻¹ * (phase * p.eval z * E ^ 2)
        = ((starRingEnd ℂ) u * phase) * (E⁻¹ * E ^ 2) * p.eval z := by ring
      _ = u * E * p.eval z := by rw [hconjphase, hErw]
  exact Complex.conj_eq_iff_im.mp hZeq

/-! ## 4. The two-frequency dictionary: equal modulus IS the FE condition -/

/-- The binomial polynomial `p(z) = c₁ + c₂ z^m` -- the polynomial attached to the
two-frequency exponential sum by the substitution `z = e^{iωx}`. -/
def binomialPoly (c₁ c₂ : ℂ) (m : ℕ) : ℂ[X] :=
  Polynomial.C c₁ + Polynomial.C c₂ * X ^ m

@[simp] theorem binomialPoly_eval (c₁ c₂ z : ℂ) (m : ℕ) :
    (binomialPoly c₁ c₂ m).eval z = c₁ + c₂ * z ^ m := by
  unfold binomialPoly; simp

theorem binomialPoly_natDegree (c₁ c₂ : ℂ) (m : ℕ) (hm : 0 < m) (hc₂ : c₂ ≠ 0) :
    (binomialPoly c₁ c₂ m).natDegree = m := by
  unfold binomialPoly
  compute_degree!
  rw [if_neg (by omega)]; simpa using hc₂

/-- **The two-frequency dictionary.**  For `m ≥ 1` and nonzero coefficients, the
binomial `c₁ + c₂ z^m` is self-inversive IFF `|c₁| = |c₂|`.  This is the polynomial
face of `TwoFreqRigidity`: Theorem A's equal-modulus rigidity condition `|c₁| = |c₂|`
IS exactly the functional-equation (self-inversive) condition.  The forward direction
reads the equal modulus off the coefficient-matching `conj c₂ = phase · c₁`,
`conj c₁ = phase · c₂` with `|phase| = 1`; the reverse exhibits the explicit phase
`phase = conj c₂ / c₁`. -/
theorem twoFreq_dictionary (c₁ c₂ : ℂ) (m : ℕ) (hm : 0 < m)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) :
    IsSelfInversive (binomialPoly c₁ c₂ m) ↔ ‖c₁‖ = ‖c₂‖ := by
  have hdeg : (binomialPoly c₁ c₂ m).natDegree = m := binomialPoly_natDegree c₁ c₂ m hm hc₂
  constructor
  · -- self-inversive ⇒ equal modulus
    rintro ⟨phase, hphase, hid⟩
    -- The pointwise identity, simplified, is
    --   conj c₁ · zᵐ + conj c₂ = phase c₁ + phase c₂ · zᵐ   (for all z ≠ 0).
    have hpt : ∀ z : ℂ, z ≠ 0 →
        (starRingEnd ℂ) c₁ * z ^ m + (starRingEnd ℂ) c₂
          = phase * c₁ + phase * c₂ * z ^ m := by
      intro z hzne
      have h := hid z hzne
      rw [hdeg] at h
      -- evaluate p(1/conj z)
      have hcz : (starRingEnd ℂ) z ≠ 0 := by simpa using hzne
      rw [binomialPoly_eval, binomialPoly_eval] at h
      -- p(1/conj z) = c₁ + c₂ (1/conj z)^m ; conj of it = conj c₁ + conj c₂ (1/z)^m
      rw [show (1 / (starRingEnd ℂ) z) ^ m = 1 / ((starRingEnd ℂ) z) ^ m by
            rw [div_pow, one_pow]] at h
      rw [map_add, map_mul, map_div₀, map_one, map_pow, Complex.conj_conj] at h
      -- h : zᵐ * (conj c₁ + conj c₂ * (1 / zᵐ)) = phase * (c₁ + c₂ * zᵐ)
      have hzm : z ^ m ≠ 0 := pow_ne_zero _ hzne
      field_simp at h ⊢
      linear_combination h
    -- pin coefficients via z = 1 and z = 2
    have h1 := hpt 1 one_ne_zero
    have h2 := hpt 2 two_ne_zero
    simp only [one_pow, mul_one] at h1
    have h2m : (2 : ℂ) ^ m ≠ 1 := by
      intro hcon
      have hnorm : ‖(2 : ℂ) ^ m‖ = 1 := by rw [hcon, norm_one]
      rw [norm_pow, Complex.norm_ofNat] at hnorm
      have hge : (1 : ℝ) < 2 ^ m := by
        calc (1 : ℝ) < 2 := by norm_num
          _ = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ m := by apply pow_le_pow_right₀ (by norm_num) hm
      linarith
    -- from h1, h2 : conj c₁ = phase c₂  and  conj c₂ = phase c₁
    have hcoeff1 : (starRingEnd ℂ) c₁ = phase * c₂ := by
      have hsub : ((starRingEnd ℂ) c₁ - phase * c₂) * ((2:ℂ)^m - 1) = 0 := by
        linear_combination h2 - h1
      rcases mul_eq_zero.mp hsub with h | h
      · exact sub_eq_zero.mp h
      · exact absurd (sub_eq_zero.mp h) h2m
    have hcoeff2 : (starRingEnd ℂ) c₂ = phase * c₁ := by
      linear_combination h1 - hcoeff1
    -- take norms:  |c₁| = |phase||c₂| = |c₂|,  and |c₂| = |c₁|
    have hn1 := congrArg (‖·‖) hcoeff1
    rw [Complex.norm_conj, norm_mul, hphase, one_mul] at hn1
    exact hn1
  · -- equal modulus ⇒ self-inversive, phase = conj c₂ / c₁
    intro hEq
    refine ⟨(starRingEnd ℂ) c₂ / c₁, ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, hEq, div_self]
      rwa [ne_eq, norm_eq_zero]
    · intro z hzne
      rw [hdeg]
      have hcz : (starRingEnd ℂ) z ≠ 0 := by simpa using hzne
      have hzm : z ^ m ≠ 0 := pow_ne_zero _ hzne
      rw [binomialPoly_eval, binomialPoly_eval,
        show (1 / (starRingEnd ℂ) z) ^ m = 1 / ((starRingEnd ℂ) z) ^ m by
          rw [div_pow, one_pow],
        map_add, map_mul, map_div₀, map_one, map_pow, Complex.conj_conj]
      -- goal: zᵐ (conj c₁ + conj c₂ (1/zᵐ)) = (conj c₂ / c₁)(c₁ + c₂ zᵐ)
      -- need conj c₁ · c₁ = conj c₂ · c₂ (equal modulus), i.e. |c₁|²=|c₂|²
      have hmod : (starRingEnd ℂ) c₁ * c₁ = (starRingEnd ℂ) c₂ * c₂ := by
        rw [mul_comm ((starRingEnd ℂ) c₁), mul_comm ((starRingEnd ℂ) c₂),
          Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq, hEq]
      field_simp
      linear_combination z ^ m * hmod

/-- **Corollary (reverse-Dyson in miniature).**  A self-inversive binomial
`c₁ + c₂ z^m` (equivalently `|c₁| = |c₂|`) makes the associated two-frequency
exponential sum `F(x) = c₁ e^{iλ₁x} + c₂ e^{i(λ₁+mω)x}` real-rooted.  FE symmetry
(self-inversivity) ⇒ reality of the support.  Composes `twoFreq_dictionary` with
`TwoFreqRigidity.twoFreq_realRooted_iff` at frequencies `λ₁` and `λ₁ + m·ω`. -/
theorem selfInversive_binomial_realRooted (c₁ c₂ : ℂ) (m : ℕ) (ω lam₁ : ℝ)
    (hm : 0 < m) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hω : ω ≠ 0)
    (hself : IsSelfInversive (binomialPoly c₁ c₂ m)) :
    ∀ x : ℂ, twoFreq c₁ c₂ lam₁ (lam₁ + m * ω) x = 0 → x.im = 0 := by
  have hEq : ‖c₁‖ = ‖c₂‖ := (twoFreq_dictionary c₁ c₂ m hm hc₁ hc₂).mp hself
  have hlam : lam₁ ≠ lam₁ + m * ω := by
    intro h
    have : (m : ℝ) * ω = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (by exact_mod_cast h1 : m = 0) (by omega)
    · exact hω h1
  exact (twoFreq_realRooted_iff c₁ c₂ lam₁ (lam₁ + m * ω) hc₁ hc₂ hlam).mpr hEq

/-! ## 5. The fixed-locus dichotomy: on the circle, or in reflected pairs -/

/-- **Fixed-locus dichotomy.**  Every nonzero root `z` of a self-inversive `p` is
either ON the unit circle (`|z| = 1`, the fixed locus of `σ_circ`) OR its reflection
`1 / conj z` is a DISTINCT root of `p` -- i.e. off-circle roots occur in reflected
pairs `{z, 1/conj z}`.  This is the finite model of "zeros on the critical line, or in
conjugate quartets": at the polynomial level the involution `σ_circ` either fixes a
root or exchanges it with a genuinely different partner root. -/
theorem fixed_locus_dichotomy {p : ℂ[X]} (hp : IsSelfInversive p)
    {z : ℂ} (hz : z ≠ 0) (hroot : p.eval z = 0) :
    ‖z‖ = 1 ∨ (p.eval (1 / (starRingEnd ℂ) z) = 0 ∧ 1 / (starRingEnd ℂ) z ≠ z) := by
  by_cases hcirc : ‖z‖ = 1
  · exact Or.inl hcirc
  · refine Or.inr ⟨selfInversive_zeros_symmetric hp hz hroot, ?_⟩
    -- if 1/conj z = z then z conj z = 1, so ‖z‖ = 1, contradiction
    intro hfix
    apply hcirc
    have hcz : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
    have hmul : z * (starRingEnd ℂ) z = 1 := by
      have h := hfix
      field_simp at h
      -- h : 1 = conj z * z
      linear_combination -h
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hmul
    have hsq : ‖z‖ ^ 2 = 1 := by exact_mod_cast hmul
    nlinarith [norm_nonneg z, hsq]

end

end Quasicrystal
