# Lemma S, step 1: graphs carry no Cartier divisor on the single-orbit square (e9, 2026-10-13)

User: "Proceed". Follows step 0 (`LEMMA_S_STEP0_2026-10-13.md`). Check script: `s1_no_graph_divisors.py`. AI work, not
reviewed. conjecture1_proved = False.

## Proposition (PROVED, elementary; numerical check in s1)

Give X_p = (R*_+)^2/(p^Z × p^Z) the CC-style structure: local sections are continuous functions, piecewise affine in
(λ1, λ2), invariant under γ1 = (p,1) and γ2 = (1,p), with Cartier divisors = K^×/O^× (local PL equations modulo affine
functions). Let D be a Cartier divisor whose support lies in a union of fibres (λ1 = c, λ2 = c) and graphs
Γ_μ = image of the ray λ2 = μ λ1. **Then every graph coefficient of D is zero.** On span{ξ0, ξ1, Γ_r}, only fibre
combinations are Cartier.

**Proof.**
1. *Locally constant jump.* Along a crease segment, local equations on overlapping neighbourhoods differ by affine
   functions, so the gradient jump J across the crease is constant until another crease meets it.
2. *Fibre crossings do not change it.* At a crossing of the ray (direction (1, μ)) with a fibre, continuity around the
   vertex gives Σ (jumps) = 0. A vertical fibre's jump is a multiple of (1, 0) and a horizontal fibre's of (0, 1).
   Neither has a component that can absorb a change along the ray normal (μ, -1), so the ray jump is the same on both
   sides (s1 (b): equal in every independent solution). Graphs Γ_μ, Γ_ν with μ/ν ∉ p^Z do not meet in X_p at all.
3. *Monodromy.* The diagonal δ = γ1γ2 maps the ray to itself, so the segment from λ to pλ closes into a loop on X_p.
   Pulled back along δ, the local equation max(0, <J,x>) becomes max(0, <J,x/p>) = max(0, <J,x>)/p, i.e. jump J/p
   (s1 (a)). Steps 1-2 make the jump constant around the loop, so J = J/p and J = 0. ∎

## Consequences for Lemma S

1. **As posed on span{ξ0, ξ1, Γ_r}, Lemma S is ill-posed.** H0(nD) is defined only for fibre combinations, where
   q(aξ0 + bξ1) = 2ab (the hyperbolic plane; Hodge holds trivially; ζ-blind). g8 §2(e)'s real-degree Gram AND step 0's
   mixed-area Gram are both pairings on classes that are not Cartier divisors on X_p.
2. **Graphs become divisors only in two ways, and both put the cone point at the centre.**
   - On the cylinder Y_p = (R*_+)^2 / ⟨γ1 γ2^{-1}⟩, the diagonal loop is unwound and Γ_μ is Cartier with constant
     coefficient. But Y_p is non-compact exactly in the scaling direction δ, with ends at |λ| → 0 (the cone point) and
     |λ| → ∞. Graphs are disjoint in Y_p, and their only "intersection" is at the cone-point end. So a pairing on
     graph classes needs a compactification of Y_p at that end: the cone-point excess of step 0 is a boundary term at
     the end of the scaling flow, i.e. Δ_B.
   - On X_p with Frobenius-twisted divisors: allow gluing modulo the char-one Frobenius f ~ p^n f (CC Lemma 5.18(ii)),
     so that the factor 1/p around the loop is absorbed. Sections are then twisted-equivariant (degree -1 under δ),
     which is the 2-dimensional form of CC's "real degrees in λH_p". This is not defined in CC's papers.
3. **Restated dichotomy.** Step 0 asked whether Dim_R growth records the cone-point excess. Step 1 shows the question
   cannot even be posed on compact X_p: graphs exist only after unwinding or twisting the scaling direction, and their
   pairing is then decided entirely at the cone-point end. This matches g8 §2(b) ("all Ψ(λ) contain Δ_B") and
   Riemann's Route J (the excess appears as exactly the G_m/pole part).
4. **For the construction agents.** Any char-one square in which graph classes are Cartier must either be non-compact
   along the scaling flow with an end at the archimedean locus, or carry Frobenius-twisted divisors. SCALE-1's
   property (1), a multiplier e^t on a connected scaling family, is exactly this monodromy: e^t = p per loop here.

## Status of Lemma S

- **Done:** step 0 (the dichotomy) and step 1 (graphs are not Cartier on compact X_p; the fibre plane is hyperbolic).
- **Next (not done):** step 2 is the section count on the Frobenius-twisted (or compactified-cylinder) model. That is
  where a graph pairing, if any, is defined; on a single orbit it is expected to be ζ-blind (Route J).

## Lean (2026-10-13)

The abstract core is kernel-checked in `telperion/examples/weil_form_enclosure/lean/LemmaSCore.lean`:
`ray_jump_preserved_vertical` / `_horizontal` (balancing at fibre crossings), `jump_zero_of_monodromy`, and
`graph_coefficient_zero` (loop). All [propext, Classical.choice, Quot.sound]; printed by `AxiomGuardRRSquare`.
