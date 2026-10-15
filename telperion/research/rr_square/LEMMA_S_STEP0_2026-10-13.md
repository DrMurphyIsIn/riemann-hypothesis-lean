# Lemma S, step 0: the single-orbit square hinges on the cone-point excess (e9, 2026-10-13)

Approved by the author (Lemma S assigned to e9; the geometry session concurs). Inputs: the gate-8 note `g8_cc_square.md` (unpublished) §4
(statement) and §2(e) (counterexample). Script: `s0_mixed_area.py`. AI work, not reviewed. conjecture1_proved = False.

## Result

1. **The §2(e) violation rests on one assumption (COMPUTED, exact arithmetic).** On X_p = (R*_+)^2/(p^Z)^2 the graph
   Γ_μ is the image of the ray λ2 = μ λ1. All rays pass through the cone point (the origin), which X_p excludes, so
   graphs are disjoint as sets. g8 took Γ_μ·Γ_ν = 0. A section-growth (Newton-polygon) pairing instead sees the mixed
   area of the jump vectors, ξ0 ↔ (1,0), ξ1 ↔ (0,1), Γ_μ ↔ (μ,-1). That gives:
   - Γ_μ·ξ0 = 1 and Γ_μ·ξ1 = μ, which are CC's real degrees exactly;
   - Γ_μ·Γ_ν = |μ - ν| ≠ 0, which is the excess intersection at the cone point.

   | pairing | signature on span{ξ0, ξ1, Γ_μ (5 values)} | g8's v = P1 - (5/6)P_{3/2} |
   |---|---|---|
   | disjoint (g8 §2(e)) | (2, 2): Hodge index violated | B(v,f) = 0, B(v,v) = +1/12 |
   | mixed area (cone-point excess) | (1, 6): Hodge index holds | B(v,f) = 0, B(v,v) = -3/4 |

   Over 2000 random families of jump vectors in a half-plane, the mixed-area Gram always has exactly one positive
   direction. That is Minkowski's inequality, i.e. the 2-dimensional Alexandrov-Fenchel, which is PROVED.

2. **So Lemma S reduces to one question (CONJECTURED framing; the dichotomy is PROVED).** Does Dim_R-growth of
   H0(nD) on X_p record the cone-point excess?
   - If yes, then q = mixed area. It is Lorentzian, so the Hodge index and the RR-square conclusion hold on the single
     orbit, and the result is blind to ζ: pure lattice geometry.
   - If no, then q is the disjoint pairing and has two positive directions. By `hodge_index_of_domain` (domain
     automatic in char one) no RR index identity with h1 ≥ 0 can hold, so CC's Dim_R would not extend to 2 dimensions
     with RR.
   The geometry session put "the Δ_B-excess term" AFTER Lemma S. Step 0 shows it is INSIDE Lemma S: the cone point is
   where every graph meets every other graph.

3. **Making it computable (method, CONJECTURED to be the right reduction).**
   - On the universal cover (R*_+)^2, a Cartier divisor supported on graph classes has a global local-finite equation
     d̃. The lifts of Γ_μ are the rays λ2 = μ p^k λ1 (k ∈ Z), which accumulate toward the two axes, not at interior
     points. Choosing the "zero side" of each ray consistently in k makes the sum locally finite.
   - Then H0(nD) ≅ {convex PL F on the cover, with integral gradients after the p^m twist, and F∘γ = F + n A_γ for
     γ ∈ (p^Z)^2}, where A_γ = d̃∘γ - d̃ is affine.
   - This is the tropical theta-function setting of Sumi (Thm 39: such spaces are convex polyhedra), with dilations in
     place of translations. dim_top is the number of orbits of gradient lattice points in an invariant convex region
     under the affine expanding maps g ↦ (p g1, g2) - n∇A_{(p,1)} and g ↦ (g1, p g2) - n∇A_{(1,p)}.
   - Lemma S part (1) is then a 2-dimensional lattice-orbit count. Its n^2 coefficient decides between the two rows
     above. That computation is NOT done here.

4. **The fibre span alone (CONJECTURED).** For D = aξ0 + bξ1 the theta functions are box products (CC Thm 5.12 on each
   factor), and the expected growth is Dim_R H0(nD) ~ n^2 ab, i.e. q = 2ab, the hyperbolic plane. Both pairings agree
   there; graphs are what separate them.
