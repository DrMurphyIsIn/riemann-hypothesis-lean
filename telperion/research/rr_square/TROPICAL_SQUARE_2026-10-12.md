# Tropical surfaces as the square: what is proved, and the local-to-global template

Date 2026-10-12. Session e9, cleared with the geometry session. Sources read from PDF text in this folder:
- Cartwright, "Combinatorial tropical surfaces", arXiv:1506.02023;
- Cartwright, "Tropical complexes", arXiv:1308.3813;
- Cartwright, "A specialization inequality for tropical complexes", arXiv:1511.00650;
- Sumi, "Tropical theta functions and Riemann-Roch inequality for tropical abelian surfaces", arXiv:1809.10987
  (Math. Z. 2021);
- Engelking, *Dimension Theory* (1978).

AI work, not reviewed. conjecture1_proved = False. Nothing here is progress on RH.

## 0. Engelking pinned (closes the open citation in the char-one step)

Engelking, *Dimension Theory* (1978):
- Thm 1.1.2 (subspace theorem): ind M ≤ ind X for every subspace M of a regular space X;
- Thm 1.7.7 (coincidence theorem): ind X = Ind X = dim X for every separable metric space X.

The section spaces H0(D)^ρ are subspaces of C([1, p]) with the sup metric, which is separable metric. So
dim_top H0(B)^ρ ≤ dim_top H0(A+B)^ρ under the isometric embedding ξ ↦ ξ + g. The no-zero-divisor property on C_p is
now fully cited.

## 1. What tropical geometry actually proves in dimension 2

- **Tropical Hodge index: PROVED, with no Riemann-Roch** (Cartwright 1506.02023, Thm 1.1). For a 2-dimensional tropical
  complex Δ that is locally connected through codimension 1 (every vertex link is connected), the intersection pairing
  on NS(Δ) ⊗ Q is nondegenerate with at most one positive eigenvalue.
- **Riemann-Roch for tropical surfaces: CONJECTURED** (Cartwright 1511.00650, Conj. 3.6):
  h0(D) + h0(K - D) ≥ ½ D·(D - K) + χ(Δ), with Serre duality assumed in place of h2. It is verified in examples.
- **Proved cases of that inequality:**
  - tropical abelian surfaces (Sumi, Cor. 48): h0(D) + h0(-D) ≥ ½ D². Here h0 is the dimension of a convex
    polyhedron (Thm 44), the same topological dimension that Connes-Consani's Dim_R normalises;
  - smooth tropical toric surfaces (arXiv:2105.12216, abstract only, not read).
- **Resolving Connes's remark** ("tropical RR is curve-only, no Serre duality for j ≠ 0", per the F1 survey). That is
  still right for a general Riemann-Roch *theorem*, but out of date in two ways: an RR *inequality* is proved for
  abelian and toric tropical surfaces, and the *Hodge index* is proved for all locally connected tropical surfaces
  without any Riemann-Roch.

## 2. The mechanism of Cartwright's Hodge index: an exact local-to-global template

Proof of Lemma 4.5 / Thm 1.1, read line by line:
- M_Δ = ⊕_v M_v is block diagonal over the vertices. Each local block, the intersection form of the vertex star, has
  **exactly one positive eigenvalue**.
- The global pairing is the restriction of M_Δ to global Cartier divisors.
- The n vertex hat functions φ_i are principal. They satisfy exactly **one** relation, Σ φ_i = 1, because connectedness
  makes linear functions constant. They and their duals give n - 1 hyperbolic pairs.
- So the positive directions number at most n - (n - 1) = 1.
- Integrality is used only to clear denominators. The signature count is real linear algebra.

Adelic dictionary (CONJECTURED as a template; SPECULATIVE as to existence):

| Cartwright | arithmetic analogue |
|---|---|
| vertex v, star form M_v with exactly one positive direction | place v, a finite-dimensional local space carrying the local Weil term with exactly one positive direction |
| hat functions φ_v (principal), one relation Σ φ_v = 1 | local functions log\|·\|_v; the product formula Σ_v log\|x\|_v = 0 is the single relation |
| ≤ 1 positive direction globally | Weil positivity on the primitive part (Lemma A) |

**This would bypass Riemann-Roch entirely.** The sign is a local count (one positive direction per place) minus a
global count of principal relations, with the product formula as the only relation.

## 3. First test of the template: the naive local terms FAIL (PROVED, elementary; checked numerically)

The local prime term of Weil's form, -W_p, is a convolution form whose symbol on the circle θ = t log p is
-2 log p · Re[z/(1 - z)], with z = p^{-1/2} e^{iθ}. Its sign is that of 1/p - p^{-1/2} cos θ, which is positive exactly
when cos θ < p^{-1/2}. That is a set of positive measure, 1 - arccos(p^{-1/2})/π of the circle:

| p | 2 | 3 | 5 | 7 | 101 |
|---|---|---|---|---|---|
| positive fraction | 0.7500 | 0.6959 | 0.6476 | 0.6234 | 0.5317 |

So on window test functions the local p-term has a number of positive directions that grows linearly with the window,
not one. The archimedean term likewise has symbol ~ log|t|, positive at high frequency. The explicit formula's own
place-by-place split is therefore NOT a Cartwright decomposition. Applying the template would need different local
spaces: finite-dimensional "vertex stars" at each place, on which the local term has exactly one positive direction.
Those would have to come from a geometry (the scaling site's local structure at v), not be read off the explicit
formula.

## 4. Obstructions specific to zeta

1. **Finiteness.** Cartwright's NS is that of a finite Δ-complex and has finite rank. Zeta's window form has rank
   growing with the window: degree and genus grow together (g5). So one needs a tower Δ_L with compatible pairings, or
   an infinite complex. The proof's count n - (n - 1) involves infinitely many places, and for a direct limit it would
   need care.
2. **Integrality.** Tropical complexes carry integer structure constants. CC's C_p has slopes in the dense group
   H_p ⊂ Q and real local terms (log p, 1/|1 - u|_p). The signature argument is real linear algebra, so this is
   probably not fatal, but the framework would have to be generalised.
3. **Circularity** (`collapse` / Lemma B). Assigning Weil's form as an intersection form is equivalent to the
   signature condition. The local stars and their forms must come from the scaling site's own geometry.

## 5. Verdict

A tropical square need not supply Riemann-Roch. Cartwright's local-to-global count gives the Hodge index from
one-positive-direction local forms plus one principal relation, and the product formula is the natural candidate for
that relation. The naive local Weil terms have infinitely many positive directions, though, so the template needs
local spaces that do not yet exist. The narrowed missing statement has an alternative form, **TROP-□**:

> Local finite-dimensional spaces at each place, built from the scaling site, on which the local term of Weil's form
> has exactly one positive direction, glued by principal divisors whose only relation is the product formula.

Neither RR-□ nor TROP-□ is known.

## Correction to §3: sign conventions (2026-10-12, prompted by the geometry session)

Cartwright counts positive directions of the intersection form. In our dictionary that is B = -(Weil form), so the
local forms to test are B_p = +W_p and B_∞ = -(archimedean term). §3 computed -W_p, the wrong orientation. In the right
convention:

- **B_p = +W_p** is positive where cos θ > p^{-1/2}, a fraction arccos(p^{-1/2})/π of the circle: 0.2500, 0.3041,
  0.3524, 0.3766, 0.4683 at p = 2, 3, 5, 7, 101. The symbol is periodic in t, so there are still **infinitely many**
  positive directions, even on a single window. The conclusion at p is unchanged; only the fractions change.
- **B_∞** is positive where Re ψ(1/4 + ir/2) < log π, i.e. on the **bounded** band |r| < r0, with r0 = 6.289836
  (mpmath root). On a window of length L this gives about 2 L r0/π positive directions: **finite but growing with L**.
  This matches the geometry session's archimedean negative-index count, and it is g5's "degree" count.

So the archimedean place is qualitatively closest to a Cartwright star, with finitely many positive directions per
window and a positive transverse jump weight plus one diagonal constant (gate 3). Still, no place has exactly one
positive direction. The template needs local spaces on which the count drops to one. The prime places are worse than
infinity, because their symbols are periodic.
