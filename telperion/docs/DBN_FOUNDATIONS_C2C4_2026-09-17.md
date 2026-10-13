# Route C foundations: de Bruijn–Newman C2 → C3 → C4 (first cut, 2026-09-17)

**Status line: `conjecture1_proved = False`.** Nothing in this document, in the new
`telperion/examples/dbn` island, or in the three new registry nodes proves the Riemann
Hypothesis, proves the de Bruijn theorem, or bounds the de Bruijn–Newman constant Λ. This is the
first honest cut of milestone C2 ("DBNDefs") from
`telperion/docs/RH_ROUTES_ROADMAP_2026-09-16.md` §4, plus the C3/C4 *statements* registered as
DRAFT nodes so the campaign graph has somewhere to hang the next months of work.

Branch `feat/dbn-foundations`. New island: `telperion/examples/dbn/lean/` (`DBNDefs.lean`,
`AxiomGuardDBN.lean`). Same toolchain (`leanprover/lean4:v4.34.0-rc1`) and Mathlib pin
(`de5ce8a9`, through the pinned `LiCriterion` dependency @ `35df682f`) as the `li_positivity`
island, so `LiCriterion.riemannXi` is the shared ξ vocabulary. CI job `dbn-compiles` in
`.github/workflows/telperion-lean-e2e.yml` (build + no-`sorry` scan + axiom guard).

## 1. Conventions chosen (and where they come from)

We follow the Polymath15 / Rodgers–Tao normalization exactly:

```
Φ(u)   := ∑_{n ≥ 1} (2π² n⁴ e^{9u} − 3π n² e^{5u}) · exp(−π n² e^{4u})          (u ∈ ℝ)
H_t(z) := ∫_0^∞ e^{t u²} Φ(u) cos(z u) du                                          (t ∈ ℝ, z ∈ ℂ)
```

- Polymath15, *Effective approximation of heat flow evolution of the Riemann ξ function, and a
  new upper bound for the de Bruijn–Newman constant*, arXiv:1904.12438, §1 eqs. (1)–(3).
- B. Rodgers, T. Tao, *The de Bruijn–Newman constant is non-negative*, Forum Math. Pi 8 (2020)
  e6 (**not** Annals — the corpus miscitation flagged in the roadmap), §1.
- N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Math. J. 17 (1950) 197–226
  (the t ≥ 1/2 real-zeros theorem; his Φ is the same kernel up to the u ↦ u/… rescaling that
  Polymath15 absorbs into the definition above).
- C. M. Newman, *Fourier transforms with only real zeros*, Proc. AMS 61 (1976) 245–251
  (Λ ≥ −∞ well-defined, conjecture Λ ≥ 0).
- H. Ki, Y.-O. Kim, J. Lee, *On the de Bruijn–Newman constant*, Adv. Math. 222 (2009) 281–306
  (Λ < 1/2, strict; the unconditional baseline any certified bound must beat).
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §10.1 (the classical
  Fourier representation of Ξ that the representation theorem below is a change of variables of).

Lean-side choices (all in `DBNDefs.lean`, namespace `DBN`):

| object | Lean | remark |
|---|---|---|
| Φ | `Φ (u : ℝ) : ℝ := ∑' n : ℕ+, …` | indexed by `ℕ+` as in the brief; `Real.pi`/`Real.exp` spelled out so the definition is verbatim-copyable into `missions/rh/lean/Statements/RHDefs.lean` |
| theta moments | `thetaMoment k u := ∑' n : ℤ, (n²)^k exp(−π n² e^{4u})` | the working object for the functional equation; `thetaMoment 0 u = jacobiTheta₂ 0 (i e^{4u})` |
| integrand | `HIntegrand t z u := ↑(e^{t u²}) * ↑(Φ u) * cos(z u)` | ℂ-valued |
| H_t | `H t z := ∫ u in Set.Ioi 0, HIntegrand t z u` | Bochner integral over (0, ∞); the *even-extension* form ½∫_ℝ is not used |
| ξ | `LiCriterion.riemannXi s = (1/2) s (s−1) Λ₀(s) + 1/2` | upstream pin; bridged to Mathlib's `completedRiemannZeta` (below) |

## 2. The normalization constant: H₀(z) = (1/8) · ξ(1/2 + iz/2)

Derivation (paper, then a 30-digit numerical check; **not yet a Lean theorem**).

Write ψ(x) = ∑_{n ≥ 1} e^{−π n² x} and x = e^{4u}. Since ψ'(x) = −π ∑ n² e^{−πn²x} and
ψ''(x) = π² ∑ n⁴ e^{−πn²x},

```
Φ(u) = 2 x^{9/4} ψ''(x) + 3 x^{5/4} ψ'(x) = 2 x^{3/4} · d/dx [ x^{3/2} ψ'(x) ]      (x = e^{4u}).
```

Titchmarsh (10.1) gives, for Ξ(t) := ξ(1/2 + it),

```
Ξ(t) = 4 ∫_1^∞ d/dx[ x^{3/2} ψ'(x) ] · x^{−1/4} cos(½ t log x) dx .
```

Substituting x = e^{4u}, dx = 4 e^{4u} du, log x = 4u, x^{−1/4} = e^{−u}:

```
Ξ(t) = 16 ∫_0^∞ e^{3u} d/dx[x^{3/2}ψ'(x)]|_{x=e^{4u}} cos(2tu) du = 8 ∫_0^∞ Φ(u) cos(2tu) du = 8 H_0(2t),
```

i.e. **H₀(z) = (1/8) Ξ(z/2) = (1/8) ξ(1/2 + iz/2)** with ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s).
This is precisely Polymath15 eq. (3) and Rodgers–Tao §1. Numerical confirmation (mpmath, 30
digits, `∫_0^∞` split at 1, 2, 4):

| z | H₀(z) by quadrature | ξ(1/2 + iz/2)/8 | ratio |
|---|---|---|---|
| 0 | 0.0621400972735392637390967174607 | 0.0621400972735392637390967174607 | 1.0 |
| 1 | 0.061782123488759537547571102295 | same | 1.0 |
| 3 | 0.0589866171381479671344708094699 | same | 1.0 |
| 0.5 + 0.7i | 0.0622258244774459532843… − 0.000251579340958721704… i | same | 1.0 |

(Φ(±0.1), Φ(±0.3), Φ(±0.2) also agree to 30 digits — the evenness theorem below is the
formal version.)

Which ξ? Mathlib's `completedRiemannZeta s = Λ(s) = π^{−s/2}Γ(s/2)ζ(s)` and
`completedRiemannZeta₀ s = Λ(s) + 1/s + 1/(1−s)` (entire). The upstream
`LiCriterion.riemannXi s := ½ s(s−1) Λ₀(s) + ½`; since ½ s(s−1)(1/s + 1/(1−s)) = −½, this equals
½ s(s−1) Λ(s) for s ∉ {0, 1} — the textbook ξ. The island proves this bridge
(`riemannXi_eq_completedRiemannZeta`), so the registry statement is in the pinned vocabulary and
the constant 1/8 is the one that makes it true.

## 3. What is PROVED (island `DBNDefs.lean`; every line `[propext, Classical.choice, Quot.sound]`)

`AxiomGuardDBN.lean` prints 31 axiom lines; all are exactly `[propext, Classical.choice,
Quot.sound]`, no `sorryAx` anywhere. No `sorry` in any committed island file (CI scans).

**Theta moments and the functional equation**
- `summable_thetaTerm`, `summable_thetaMoment` — the ℤ-indexed moment series converge for every
  u (from Mathlib's `summable_pow_mul_jacobiTheta₂_term_bound`).
- `hasDerivAt_thetaMoment` — `(thetaMoment k)' = −4π e^{4u} · thetaMoment (k+1)`, termwise
  (via `hasDerivAt_tsum_of_isPreconnected` on the bounded interval (u−1, u+1)).
- `continuous_thetaMoment`.
- `ofReal_thetaMoment_zero` — `thetaMoment 0 u = jacobiTheta₂ 0 (i e^{4u})`.
- `thetaMoment_zero_fe` — **the theta functional equation** in the u-variable,
  `θ₀(u) = e^{−2u} θ₀(−u)`, from Mathlib's `jacobiTheta₂_functional_equation` at z = 0,
  τ = i e^{4u} (the cpow `(e^{4u})^{1/2} = e^{2u}` and `−1/(i x) = i/x` are the only algebra).
- `thetaMoment_fe_deriv1`, `thetaMoment_fe_deriv2` — the FE differentiated once and twice
  (`HasDerivAt.unique` on both sides).

**Φ**
- `summable_thetaTerm_pnat`, `summable_Φ_term` — **the Φ series is summable for every u**.
- `thetaMoment_eq_two_mul_pnat`, `Φ_eq` — `Φ(u) = π² e^{9u} θ₂(u) − (3/2) π e^{5u} θ₁(u)`.
- `Φ_neg : Φ (−u) = Φ u`, `Φ_even : Function.Even Φ` — **Φ is even, as a theorem** (the
  linear combination (−e^u/16)·FE'' − (e^u/8)·FE' of the differentiated functional equation).
  This is the identity de Bruijn/Newman/Polymath15 all *assume* when they extend H_t to ℝ.
- `continuous_Φ`.

**Decay and integrability**
- `abs_Φ_le` — for u ≥ 0, `|Φ(u)| ≤ ΦBoundConst · e^{9u} · exp(−(π/2) e^{4u})` with the explicit
  constant `ΦBoundConst = ∑_{n ≥ 1} (2π²n⁴ + 3πn²) e^{−πn²/2}` (`ΦBoundConst_nonneg`,
  `summable_ΦBoundConst_term`).
- `integrableOn_exp_quad_mul_exp_neg_exp` — `exp(a u² + b u) · exp(−(π/2) e^{4u})` is integrable
  on (0, ∞) for **every** a, b ∈ ℝ (double exponential beats any Gaussian; via
  `integrable_of_isBigO_exp_neg` and a `Tendsto … atBot` factorization).
- `norm_cos_le_exp_norm`, `norm_sin_le_exp_norm` — `‖cos w‖, ‖sin w‖ ≤ e^{‖w‖}`.
- `continuous_HIntegrand`, `integrableOn_HIntegrand` — **the H_t integrand is integrable on
  (0, ∞) for every t ∈ ℝ and z ∈ ℂ** (so `H t z` is a genuine integral, not a junk value,
  for all t — including t < 0 and t > 1/2).

**H_t**
- `H_neg : H t (−z) = H t z`.
- `H_ofReal`, `H_ofReal_im : (H t x).im = 0` for real x — **H_t is real on the real axis**.
- `hasDerivAt_HIntegrand`, `continuous_HIntegrand'`, `hasDerivAt_H` — differentiation under the
  integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominated on the unit ball
  by the majorant above with b = 11 + ‖z₀‖), derivative `∫_0^∞ e^{tu²} Φ(u) (−u sin(z₀u)) du`.
- `differentiable_H : Differentiable ℂ (H t)` — **H_t is entire for every t**.

**ξ bridge**
- `riemannXi_eq_completedRiemannZeta` — `LiCriterion.riemannXi s = ½ s (s−1) completedRiemannZeta s`
  for s ≠ 0, 1.

## 4. What is STATED ONLY (registry, campaign `rh`, all DRAFT, all `:= by sorry` in the
statement files by design — statements, not proofs)

Registered with the mission CLI (never by hand); `mission verify rh` → `OK`;
`missions/rh/lean` still `lake build`s. `RHDefs.lean` gained a `DBN` block (verbatim extracts
of `thetaMoment`, `Φ`, `HIntegrand`, `H` by line range; `build_rhdefs.py` regenerates it).

| node | kind | deps | statement |
|---|---|---|---|
| `RH.dbn_H0_eq_xi` (C2 headline) | lemma | — | `∀ z, DBN.H 0 z = (1/8) * LiCriterion.riemannXi (1/2 + I*z/2)` |
| `RH.dbn_debruijn_real_zeros` (C3) | milestone | C2 | `∀ t, 1/2 ≤ t → ∀ z, DBN.H t z = 0 → z.im = 0` |
| `RH.dbn_rh_iff_H0_real_zeros` (C4) | milestone | C2 | `(∀ ρ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1/2) ↔ ∀ z, DBN.H 0 z = 0 → z.im = 0` |

The RH side of C4 is phrased in the AND_ladder grammar ("every zero of ζ in the open critical
strip has real part 1/2"), *not* Mathlib's `RiemannHypothesis` (which quantifies over all zeros
and excludes the trivial ones and s = 1 by hypotheses); the two are classically equivalent but
that equivalence is itself a small theorem, so the ladder grammar was kept for uniformity with
`RH_li_ladder_reduction` and friends.

`mission audit` was **not** run (blind read-back is a separate session).

## 5. Why Λ is NOT defined yet (the sInf trap)

The de Bruijn–Newman constant is "Λ := inf { t : all zeros of H_t are real }" — but in Lean an
`sInf` over ℝ of an *empty* set is junk (0), and of a set that is not an up-set is meaningless
as "the threshold". Defining `Λ` today would produce a term whose every stated property
(Λ ≤ 1/2, Λ ≥ 0, RH ⟺ Λ ≤ 0) silently depends on facts not yet proved:

1. the set S := { t | ∀ z, H_t z = 0 → z.im = 0 } is **non-empty** — that is de Bruijn's t ≥ 1/2
   theorem (C3), and
2. S is an **up-set** (t ∈ S, t' ≥ t ⟹ t' ∈ S) — the heat-flow monotonicity (also de Bruijn
   1950), which is what makes `sInf S` the threshold rather than an arbitrary accumulation
   point, and
3. S is **bounded below** — Newman 1976 (Λ > −∞), without which the sInf is again junk (0) and
   "Λ ≥ 0" would be a definitional accident, not Rodgers–Tao.

The roadmap's discipline is therefore kept: Λ appears nowhere in the island or the registry.
When C3 lands, Λ should be introduced *together with* the three lemmas above, and the C4 node
re-expressed as `RH ↔ Λ ≤ 0` only then.

## 6. Honest next steps

**C2 remainder — the representation theorem `RH.dbn_H0_eq_xi`.** Not attempted in Lean this
session (roadmap: months). Shape of the proof, in Mathlib vocabulary:
1. Mathlib's `completedRiemannZeta₀` is `completedHurwitzZetaEven₀ 0`, built from the
   `hurwitzEvenFEPair 0` weak-FE pair; its `Λ₀` is the *symmetrized* Mellin transform
   `∫_1^∞ (θ(x) − 1) (x^{s/2} + x^{(1−s)/2}) dx/x`-type expression (`WeakFEPair.Λ₀`,
   `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`). The first job is a clean lemma
   `completedRiemannZeta₀_eq_integral : Λ₀(s) = ∫_1^∞ ψ(x)(x^{s/2−1} + x^{−s/2−1/2}) dx + …`
   with the boundary constants made explicit — this is where the `+ 1/2` of `riemannXi` comes
   from.
2. Two integrations by parts on (1, ∞) (`intervalIntegral.integral_mul_deriv_eq_deriv_mul` /
   `integral_Ioi_of_hasDerivAt_of_tendsto` with the boundary terms killed by the decay bounds
   already proved here: `abs_Φ_le` is the u-side of the same estimate), producing
   ξ(1/2 + it) = 4 ∫_1^∞ (x^{3/2}ψ')' x^{−1/4} cos(½ t log x) dx.
3. The substitution x = e^{4u} (`integral_comp_exp`-style change of variables on Ioi) and the
   identification with `Φ` via `Φ_eq` and `hasDerivAt_thetaMoment` — the theta-moment layer was
   built so that step 3 is algebra, not analysis.
The dominated-convergence justifications the roadmap warns about are exactly the two IBP steps.

**C3 — de Bruijn 1950 (t ≥ 1/2 ⟹ real zeros).** The classical route is: (a) Φ has the
Pólya-type representation making H_t, for t ≥ 1/2, a limit of polynomials in the Laguerre–Pólya
class (de Bruijn 1950 works with the factorization of e^{tu²}Φ(u) into factors whose Fourier
transforms have only real zeros; Ki–Kim–Lee 2009 has the cleanest modern statement); (b)
the heat-flow monotonicity lemma (real zeros at t₀ ⟹ real zeros for all t ≥ t₀) which is the
same Laguerre–Pólya closure argument. Neither Laguerre–Pólya class nor "Fourier transforms with
only real zeros" exist in Mathlib; the first months of C3 are that infrastructure. What THIS
session contributes to C3: `differentiable_H` (H_t entire, all t), `H_ofReal_im` (real on ℝ),
`H_neg` (even) and the uniform integrability lemma — the hypotheses every version of the
argument starts from.

**C4 — RH ⟺ real zeros of H₀.** Given C2 this is the change of variables s = 1/2 + iz/2 on the
zero sets plus the fact that ξ's zeros are exactly ζ's nontrivial zeros (Mathlib has
`riemannZeta_eq_zero_iff`-type facts and `completedRiemannZeta` zero-set lemmas; the
`li_positivity` island's `XiLineZeros`/`ZetaZeroConfinement` already do the ξ ↔ ζ zero bridge on
the v4.34 pin and should be reused, not re-proved). C4 is "authorable now" and is authored now
(as a statement); its proof is blocked only on C2.

**Engineering.** If a C6-style verified evaluator is ever wanted, `abs_Φ_le` with its explicit
constant is the tail bound it needs; `ΦBoundConst` itself is a sum the enclosure engine can bound
rigorously (it is a `li_coeff`-class object: ∑ polynomial × e^{−πn²/2}).

## 7. Files

- `telperion/examples/dbn/lean/{lakefile.toml, lean-toolchain, lake-manifest.json, DBNDefs.lean, AxiomGuardDBN.lean}`
- `telperion/missions/rh/nodes/RH_dbn_{H0_eq_xi,debruijn_real_zeros,rh_iff_H0_real_zeros}.toml`
- `telperion/missions/rh/lean/Statements/RH_dbn_*.lean`, `Statements.lean` (imports),
  `Statements/RHDefs.lean` (DBN block), `build_rhdefs.py` (extractor for that block)
- `.github/workflows/telperion-lean-e2e.yml` (`dbn-compiles`)
- `telperion.toml`: no entry — the island is hand-authored Lean with no `generate.py`, and the
  regen-diff net enumerates `examples/*/generate.py` only (checked: `cli.py` verify).
