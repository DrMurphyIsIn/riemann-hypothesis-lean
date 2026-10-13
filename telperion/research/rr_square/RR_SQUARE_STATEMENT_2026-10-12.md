# Conjecture RR-square, made precise and kernel-checked

Date 2026-10-12. Session e9, at the user's request ("Find it. The sharp missing statement."). The design follows the
geometry session's four suggestions, which the user endorsed. Builds on the unpublished research notes `g6_transport.md` §3-4
(Conjecture RR-□) and `g6_ff_dictionary.md`. Lean: telperion/examples/weil_form_enclosure/lean/RRSquare*.lean (originally a scratch island; Lean v4.32.0,
Mathlib v4.32.0, the same pin as Arda's weil_form_enclosure island). Pushed to Arda on the user's instruction.
AI work, not reviewed. conjecture1_proved = False. Nothing here is progress on RH.

## The statement

For one window L, take:
- `V`, the real span of Frobenius-graph classes, i.e. the window's test functions;
- `B`, Weil's pairing on `V`, with the sign of the dictionary (B = -(1/ℓ) × Weil form);
- `f = f₁ + f₂`, the degree class (pole terms).

**Conjecture RR-□ (sharp form).** There is a square `X` constructed without reference to the zeros of ζ. It carries
divisors `Div ⊇ V`, principal divisors `Prin`, effective divisors, and real-valued (type II) section dimensions
`h0, h1 ≥ 0`, such that:

1. **(deg)** a linear degree `deg : Div → ℝ` that vanishes on `Prin` and restricts to `B(·, f)` on `V`;
2. **(eff)** if `h0 X > 0`, then `X ≡ E mod Prin` with `E` effective, and either `deg E > 0` or `E ∈ Prin`;
3. **(compat)** principal divisors lying in `V` are numerically trivial: `B v v = 0`;
4. **(RR)** for every v in V and n ≥ 1: h0(nv) - h1(nv) + h0(K - nv) = ½ n² B(v,v) - ½ n a(v) + χ, with Serre duality
   h2 = h0(K - ·) substituted in;
5. **(bound)** degree bounds dimension: `h0 X ≤ β(deg X)` for some function `β`.

Lean: `RRSquare.RRAxiomsBounded B f ι` in `RRSquare.lean`. Items 1-4 are the dimension-level content of g6_transport
§4 (a)-(d). **Item 5 is new.**

## Kernel-checked results (all depend on [propext, Classical.choice, Quot.sound] only; AxiomGuardRRSquare.lean)

| theorem | content |
|---|---|
| `hodge_index` | 1-5 imply `B v v ≤ 0` whenever `B v f = 0`. This is Grothendieck's argument: n → ∞ at a fixed window. |
| `countermodel` | 1-4 **without 5** have a model on ℝ³ (a hyperbolic plane plus a positive direction) that violates the Hodge index. |
| `collapse` | with `Div = V`, 1-5 are satisfiable **iff** the Hodge index holds (Lemma B in kernel form). |
| `G2F5_hodge`, `G2F5_model` | for y² = x⁵ + x³ + 3x + 2 over F₅, the Hodge index holds on span{f₁, f₂, Γ₀..Γ₄} by an exact sum-of-squares certificate, so the axioms are satisfiable |
| `FK3_hodge`, `FK3_model`, `FK3_graphs_meet_negatively` | the on-circle fake (q = 2, N₁ = -1) also passes the Hodge index and has a model, yet Γ₀·Γ₁ = -1 < 0 |
| `FK2_hodge_fails`, `FK2_no_model` | the off-circle fake (q = 3): an explicit rational vector violates the Hodge index, so no model exists |
| `weil_positive_of_rr` | RR-□ on a window gives `0 ≤ Re weilForm (autocorr g)` for every pole-free test `g` in it, using Arda's own `WeilExplicit` / `WeilForm` definitions (verbatim copy, sha256 55e342c4…) |

## What this sharpens

1. **The degree bound (or a no-zero-divisor axiom) is load-bearing, and g6_transport's derivation skipped it.** From
   RR, h0(nv) + h0(K - nv) grows like n². The memo concludes that ±nv is effective. But the growth can sit entirely in
   h0(K - nv). That divisor has the fixed degree deg K, so (eff) is satisfied with no contradiction. `countermodel` does
   exactly this. Two classical fixes:
   - (5) itself: on C × C, h0 is bounded by a function of the degree against an ample class;
   - "no zero divisors": if h0(A) > 0 then h0(B) ≤ h0(A + B).

   Either closes the argument. The second is what g6's (a) clause H⁰(D)·H⁰(D') ⊂ H⁰(D + D') would need, plus
   injectivity. Inclusion alone allows zero multiplication.
   **This is a real tension for type II dimensions.** Hilbert modules over a II₁ factor have zero divisors in
   abundance, so the domain property is not automatic in the real-dimension (Connes-Consani, Murray-von Neumann) setting
   the programme expects to need. A candidate square must supply (5) or the domain property explicitly.

2. **No bare existence statement can be the target.** By `collapse`, "there exist Div, Prin and dimensions satisfying
   1-5" is equivalent to the Hodge index already on `Div = V`, i.e. to Weil's criterion. So the missing statement is not
   a Prop of the form ∃-structure. It is a **construction**: a specific square, defined without the zeros, for which
   1-5 are then proved. The non-formal clause "constructed without reference to the zeros" carries all of the content,
   and it cannot be typed as an existence statement.

3. **Effectivity of the graphs is invisible to the axioms.** FK3 has an on-circle spectrum but N₁ < 0, so its "graphs"
   meet negatively. It still satisfies 1-5, through the collapse model. The Euler product, where ζ and DH part ways
   (g6_transport fact 2), enters only through the *construction*, not through the axioms. If wanted, "graphs are
   effective and distinct effective prime divisors meet ≥ 0" would have to be added as axiom 6. FK3 violates it
   decidably.

4. **The sign has a single source.** In `hodge_index` the only inequality used, apart from (bound), is h1 ≥ 0. Every
   other step is an identity or a degree computation. This matches ffdict's finding that the sign is ampleness of
   f₁ + f₂ carried through Riemann-Roch.

## The sharp missing statement, in one sentence

Construct, without the zeros, a square whose section spaces have real dimensions satisfying a Riemann-Roch index
identity with leading term Weil's form, an effectivity/degree axiom, and a degree bound (or no zero divisors). Then
Weil positivity follows, by `weil_positive_of_rr`. The degree bound is the clause that existing type II frameworks do
not provide for free.

## Next step (2026-10-12): axiom 5 in Connes-Consani's characteristic-one framework

Cleared with the geometry session (no overlap). Source: Connes-Consani, "Geometry of the scaling site",
arXiv:1603.03191, §5, read from the PDF text: definitions (25)-(28), Prop. 5.15, Lemma 5.13, Thm 5.17.

**New in Lean: `hodge_index_of_domain` (13 theorems now, all [propext, Classical.choice, Quot.sound]).**
"No zero divisors" (`h0 X > 0 ⇒ h0 Y ≤ h0 (X + Y)`) on its own, without any degree bound, gives the Hodge index.
- If h0(K - nv) > 0, then h0(K + nv) ≤ h0(2K) is bounded. RR at -v then forces sections of -nv, which have degree 0,
  so -nv is principal and hence null.
- Otherwise RR at v forces sections of nv, with the same conclusion.
So the clause "degree bound OR no zero divisors" is now kernel-checked in both forms.

**On the periodic orbit C_p, all three behaviours hold.** H0(D) = {f in K(C_p) : D + (f) ≥ 0}, with sections
R_max-valued, convex, piecewise affine functions, and Dim_R = lim p^{-n} dim_top H0(D)^{p^n}.
1. **Vanishing in negative degree:** H0(D) = 0 for deg D < 0 (Lemma 5.13(i), PROVED by CC). This was the geometry
   session's suggested first filter, and C_p passes it.
2. **Degree bound:** Dim_R H0(D) = deg D for deg D ≥ 0 (Thm 5.17(i), PROVED by CC), so h0 ≤ max(deg, 0).
3. **No zero divisors (PROVED here, elementary; one standard input cited from memory).** The product of sections is
   pointwise addition of functions, with f in H0(A) and g in H0(B) giving f + g in H0(A + B), because (f + g) =
   (f) + (g). For a fixed section g of A, the map ξ ↦ ξ + g:
   - is R_max-linear, since + distributes over ∨;
   - is injective, and an isometry for CC's metric d(f, g) = max |f - g| on [1, p];
   - maps the filtration level H0(B)^{p^n} into H0(A+B)^{p^n} once ‖g‖_p ≤ p^n, by Prop. 5.15(ii).
   Covering dimension is monotone on subspaces of separable metric spaces (the subset theorem, Engelking; from
   memory). So dim_top H0(B)^{p^n} ≤ dim_top H0(A+B)^{p^n} for large n, and Dim_R H0(B) ≤ Dim_R H0(A+B).

**Correction to the recorded "type II tension".** CC's Dim_R is a normalised Lebesgue covering dimension of filtered
R_max-modules of functions, not a von Neumann trace. Their sections live in a semifield K(C_p) whose multiplication is
addition of real functions, which is cancellative. So zero divisors cannot occur. The tension applies to
Hilbert-module (II_1) realisations, not to CC's characteristic-one realisation. The F1 survey's description of Dim_R as
"Murray-von Neumann-style" is right about the normalisation but wrong about where zero divisors could come from.

**General form (PROVED at the level of the argument above).** For any characteristic-one construction whose sections
are R_max-valued functions, with multiplication = pointwise sum, and whose Dim is a normalised topological dimension of
sup-metric filtered modules with a filtration subadditive under sums, the no-zero-divisor axiom holds automatically.
This includes a square of the scaling site, if one were built that way. So axiom 5 comes free in this framework. The
degree bound on a square would NOT be automatic, but by `hodge_index_of_domain` it is not needed.

**The sharp statement, narrowed.** In characteristic one the open content of RR-□ is:
- (i) a square whose sections are R_max-valued functions;
- (ii) a Riemann-Roch index identity with Serre duality, whose leading n² term is Weil's form;
- (iii) effectivity with positive degree on the graph cone (where the Euler product enters);
- (iv) principal divisors in the graph span are numerically null.

The sign then comes from h1 ≥ 0 plus the automatic domain property. CC's curve-level theorem supplies the shape of
(ii) on C_p only, and the square is not constructed.
