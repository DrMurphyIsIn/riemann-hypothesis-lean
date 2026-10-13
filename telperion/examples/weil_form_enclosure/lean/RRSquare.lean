import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Conjecture RR-square, made precise (abstract Grothendieck argument)

For one window: `V` is the graph span with Weil's pairing `B`; `f = f₁ + f₂` gives the degree; `Div ⊇ V` (via `ι`) are
divisors on a hypothetical square, `Prin` its principal divisors, `h0`, `h1` real-valued (type II) section dimensions.

* `RRAxioms` (no degree bound) is the dimension-level content of the unpublished note `g6_transport.md` §4, (a)-(d),
  with Serre duality built into the index identity.
* `RRAxiomsBounded` adds `h0 X ≤ β (deg X)` ("degree bounds dimension"; true on `C × C` for an ample degree).

Results:
* `hodge_index` : `RRAxiomsBounded` ⇒ `B v v ≤ 0` whenever `B v f = 0` (the Hodge index; on the graph span this is
  Weil's criterion, g6_transport Lemma A).
* `countermodel` : there is an `RRAxioms` model (genuine hyperbolic plane plus one positive direction) violating the Hodge
  index, so the degree bound (or an equivalent no-zero-divisor axiom) cannot be dropped.

Nothing here is progress on RH. conjecture1_proved = False.
-/

namespace RRSquare

variable {V Div : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Div] [Module ℝ Div]

/-- Dimension-level axioms (a)-(d) of Conjecture RR-square for one window. -/
structure RRAxioms (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div) where
  deg : Div →ₗ[ℝ] ℝ
  deg_ι : ∀ v, deg (ι v) = B v f
  Prin : Submodule ℝ Div
  deg_prin : ∀ X ∈ Prin, deg X = 0
  Eff : Div → Prop
  h0 : Div → ℝ
  h1 : Div → ℝ
  h0_nonneg : ∀ X, 0 ≤ h0 X
  h1_nonneg : ∀ X, 0 ≤ h1 X
  K : Div
  a : V → ℝ
  χ : ℝ
  /-- Riemann-Roch index identity, with `h2 (nD) = h0 (K - nD)` (Serre duality) substituted. -/
  rr : ∀ (v : V) (n : ℕ), h0 (ι ((n : ℝ) • v)) - h1 (ι ((n : ℝ) • v)) + h0 (K - ι ((n : ℝ) • v))
      = (1 / 2) * (n : ℝ) ^ 2 * B v v - (1 / 2) * (n : ℝ) * a v + χ
  /-- Effectivity (Connes's facts 1-2): sections give an effective representative of positive degree, or a principal one. -/
  eff : ∀ X, 0 < h0 X → ∃ E, Eff E ∧ X - E ∈ Prin ∧ (0 < deg E ∨ E ∈ Prin)
  /-- Compatibility: principal divisors in the graph span are numerically trivial. -/
  compat : ∀ v, ι v ∈ Prin → B v v = 0

/-- Axioms plus "degree bounds dimension". -/
structure RRAxiomsBounded (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div)
    extends RRAxioms B f ι where
  β : ℝ → ℝ
  bound : ∀ X, h0 X ≤ β (deg X)

/-- The Hodge index from the bounded axioms (Grothendieck's argument). -/
theorem hodge_index {B : LinearMap.BilinForm ℝ V} {f : V} {ι : V →ₗ[ℝ] Div}
    (A : RRAxiomsBounded B f ι) (v : V) (hv : B v f = 0) : B v v ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set c := B v v
  set M := A.β (A.deg A.K)
  set a0 := A.a v
  -- choose n ≥ 1 with n c ≥ |a0| + 2(|χ| + |M|) + 2
  obtain ⟨n, hn⟩ := exists_nat_ge ((|a0| + 2 * (|A.χ| + |M|) + 2) / c)
  set m : ℕ := n + 1
  have hm1 : (1 : ℝ) ≤ m := by simp [m]
  have hmc : |a0| + 2 * (|A.χ| + |M|) + 2 ≤ (m : ℝ) * c := by
    have h1 : (|a0| + 2 * (|A.χ| + |M|) + 2) ≤ (n : ℝ) * c := by
      rwa [div_le_iff₀ hpos] at hn
    have : (n : ℝ) * c ≤ (m : ℝ) * c := by
      apply mul_le_mul_of_nonneg_right _ hpos.le; simp [m]
    linarith
  -- degree of K - m v is deg K
  have hdegK : A.deg (A.K - ι ((m : ℝ) • v)) = A.deg A.K := by
    rw [map_sub, A.deg_ι, LinearMap.BilinForm.smul_left, hv]; ring
  have hKb : A.h0 (A.K - ι ((m : ℝ) • v)) ≤ M := by
    have := A.bound (A.K - ι ((m : ℝ) • v)); rwa [hdegK] at this
  have hrr := A.rr v m
  have hh1 := A.h1_nonneg (ι ((m : ℝ) • v))
  -- lower bound: h0 (m v) > 0
  have key : (1 / 2) * (m : ℝ) ^ 2 * c - (1 / 2) * (m : ℝ) * a0 + A.χ - M ≥ 1 := by
    have ha : -(1 / 2) * (m : ℝ) * a0 ≥ -(1 / 2) * (m : ℝ) * |a0| := by
      have h1 : (m : ℝ) * a0 ≤ (m : ℝ) * |a0| :=
        mul_le_mul_of_nonneg_left (le_abs_self a0) (by positivity)
      linarith
    have hχ : A.χ ≥ -|A.χ| := neg_abs_le _
    have hM : -M ≥ -|M| := by linarith [le_abs_self M]
    have hsq : (1 / 2) * (m : ℝ) ^ 2 * c = (1 / 2) * (m : ℝ) * ((m : ℝ) * c) := by ring
    have : (1 / 2) * (m : ℝ) * ((m : ℝ) * c)
        ≥ (1 / 2) * (m : ℝ) * (|a0| + 2 * (|A.χ| + |M|) + 2) := by
      apply mul_le_mul_of_nonneg_left hmc; positivity
    nlinarith [abs_nonneg A.χ, abs_nonneg M, abs_nonneg a0]
  have hpos0 : 0 < A.h0 (ι ((m : ℝ) • v)) := by linarith
  obtain ⟨E, -, hXE, hE⟩ := A.eff _ hpos0
  have hdegX : A.deg (ι ((m : ℝ) • v)) = 0 := by
    rw [A.deg_ι, LinearMap.BilinForm.smul_left, hv, mul_zero]
  have hdegE : A.deg E = 0 := by
    have h := A.deg_prin _ hXE
    rw [map_sub, hdegX] at h; linarith
  have hEP : E ∈ A.Prin := by
    rcases hE with h | h
    · exact absurd h (by rw [hdegE]; exact lt_irrefl 0)
    · exact h
  have hXP : ι ((m : ℝ) • v) ∈ A.Prin := by
    have := A.Prin.add_mem hXE hEP; simpa using this
  have h0B := A.compat _ hXP
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at h0B
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have : c = 0 := by
    have : (m : ℝ) * ((m : ℝ) * c) = 0 := h0B
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hm0
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hm0
      · exact h'
  linarith



/-! ## The domain alternative: no zero divisors also suffices

"No zero divisors": a nonzero section `s ∈ H⁰(A)` embeds `H⁰(B)` into `H⁰(A + B)`, so `h0 B ≤ h0 (A + B)`. This holds
automatically in Connes-Consani's characteristic-one setting, where multiplication of sections is addition of
`ℝ_max`-valued functions (an isometric embedding for the sup metric) and `Dim_ℝ` is a normalised topological dimension. -/

/-- Axioms plus "no zero divisors". -/
structure RRAxiomsDomain (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div)
    extends RRAxioms B f ι where
  domain : ∀ X Y, 0 < h0 X → h0 Y ≤ h0 (X + Y)

/-- If `ι (n • v)` has sections and `B v f = 0`, then `B v v = 0` (effectivity + compatibility). -/
lemma sections_force_null {B : LinearMap.BilinForm ℝ V} {f : V} {ι : V →ₗ[ℝ] Div}
    (A : RRAxioms B f ι) (v : V) (hv : B v f = 0) (m : ℕ) (hm : 1 ≤ m)
    (hpos0 : 0 < A.h0 (ι ((m : ℝ) • v))) : B v v = 0 := by
  obtain ⟨E, -, hXE, hE⟩ := A.eff _ hpos0
  have hdegX : A.deg (ι ((m : ℝ) • v)) = 0 := by
    rw [A.deg_ι, LinearMap.BilinForm.smul_left, hv, mul_zero]
  have hdegE : A.deg E = 0 := by
    have h := A.deg_prin _ hXE
    rw [map_sub, hdegX] at h; linarith
  have hEP : E ∈ A.Prin := by
    rcases hE with h | h
    · exact absurd h (by rw [hdegE]; exact lt_irrefl 0)
    · exact h
  have hXP : ι ((m : ℝ) • v) ∈ A.Prin := by
    have := A.Prin.add_mem hXE hEP; simpa using this
  have h0B := A.compat _ hXP
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at h0B
  have hm0 : (m : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ m := by exact_mod_cast hm
                               linarith
  have : (m : ℝ) * ((m : ℝ) * B v v) = 0 := h0B
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hm0
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hm0
    · exact h'

/-- Large `n` makes both Riemann-Roch right-hand sides beat any fixed constant. -/
lemma rr_rhs_large (c a1 a2 χ M : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, 1 ≤ m ∧ (1 / 2) * (m : ℝ) ^ 2 * c - (1 / 2) * (m : ℝ) * a1 + χ - M ≥ 1 ∧
      (1 / 2) * (m : ℝ) ^ 2 * c - (1 / 2) * (m : ℝ) * a2 + χ - M ≥ 1 := by
  set a := |a1| + |a2|
  obtain ⟨n, hn⟩ := exists_nat_ge ((a + 2 * (|χ| + |M|) + 2) / c)
  have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by simp
  have hmc : a + 2 * (|χ| + |M|) + 2 ≤ ((n + 1 : ℕ) : ℝ) * c := by
    have h1 : (a + 2 * (|χ| + |M|) + 2) ≤ (n : ℝ) * c := by rwa [div_le_iff₀ hc] at hn
    have : (n : ℝ) * c ≤ ((n + 1 : ℕ) : ℝ) * c := by
      apply mul_le_mul_of_nonneg_right _ hc.le; simp
    linarith
  have hbig : (1 / 2) * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * c)
      ≥ (1 / 2) * ((n + 1 : ℕ) : ℝ) * (a + 2 * (|χ| + |M|) + 2) := by
    apply mul_le_mul_of_nonneg_left hmc; positivity
  have ha1 : a1 ≤ a := by have := le_abs_self a1; have := abs_nonneg a2; simp only [a]; linarith
  have ha2 : a2 ≤ a := by have := le_abs_self a2; have := abs_nonneg a1; simp only [a]; linarith
  have hχ := neg_abs_le χ
  have hM := le_abs_self M
  set N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hsq : (1 / 2) * N ^ 2 * c = (1 / 2) * N * (N * c) := by ring
  have hprod : 0 ≤ (N - 1) * (|χ| + |M|) :=
    mul_nonneg (by linarith) (by positivity)
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · have h3 : N * a1 ≤ N * a := mul_le_mul_of_nonneg_left ha1 (by positivity)
    have : (1 / 2) * N ^ 2 * c - (1 / 2) * N * a1 + χ - M ≥ 1 := by
      rw [hsq]; nlinarith
    exact this
  · have h3 : N * a2 ≤ N * a := mul_le_mul_of_nonneg_left ha2 (by positivity)
    have : (1 / 2) * N ^ 2 * c - (1 / 2) * N * a2 + χ - M ≥ 1 := by
      rw [hsq]; nlinarith
    exact this

/-- The Hodge index from the domain axioms (no degree bound needed). -/
theorem hodge_index_of_domain {B : LinearMap.BilinForm ℝ V} {f : V} {ι : V →ₗ[ℝ] Div}
    (A : RRAxiomsDomain B f ι) (v : V) (hv : B v f = 0) : B v v ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set c := B v v
  set M := A.h0 (A.K + A.K)
  have hM0 : 0 ≤ M := A.h0_nonneg _
  obtain ⟨m, hm, hb1, hb2⟩ := rr_rhs_large c (A.a v) (A.a (-v)) A.χ M hpos
  have hvneg : B (-v) f = 0 := by simp [hv]
  have hcneg : B (-v) (-v) = c := by simp [c]
  have hrr := A.rr v m
  have hrr' := A.rr (-v) m
  have hh1 := A.h1_nonneg (ι ((m : ℝ) • v))
  have hh1' := A.h1_nonneg (ι ((m : ℝ) • (-v)))
  have hKeq : A.K - ι ((m : ℝ) • (-v)) = A.K + ι ((m : ℝ) • v) := by
    simp [smul_neg, map_neg, sub_neg_eq_add]
  rw [hKeq, hcneg] at hrr'
  by_cases hK : 0 < A.h0 (A.K - ι ((m : ℝ) • v))
  · have hdom := A.domain _ (A.K + ι ((m : ℝ) • v)) hK
    have hsum : A.K - ι ((m : ℝ) • v) + (A.K + ι ((m : ℝ) • v)) = A.K + A.K := by abel
    rw [hsum] at hdom
    have hp : 0 < A.h0 (ι ((m : ℝ) • (-v))) := by linarith
    have := sections_force_null A.toRRAxioms (-v) hvneg m hm hp
    rw [hcneg] at this; linarith
  · push Not at hK
    have hp : 0 < A.h0 (ι ((m : ℝ) • v)) := by linarith
    exact absurd (sections_force_null A.toRRAxioms v hv m hm hp) (ne_of_gt hpos)

/-! ## Collapse: with `Div = V` the bounded axioms are exactly the Hodge index

This is Lemma B of `g6_transport.md` §3 in kernel form. A bare existence statement "some structure satisfies the axioms"
is therefore circular. The content of Conjecture RR-square must be a *construction* (a square built without reference
to the zeros, with `Div ⊋ V` and principal divisors), not an existence Prop. -/

theorem cauchy_schwarz_of_hodge {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) {f : V} (hf : 0 < B f f)
    (hodge : ∀ v, B v f = 0 → B v v ≤ 0) (X : V) : B f f * B X X ≤ (B X f) ^ 2 := by
  set t := B X f / B f f
  set Y := X - t • f
  have hYf : B Y f = 0 := by
    simp only [Y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, t]
    field_simp; ring
  have hfY : B f Y = 0 := by rw [← hB.eq]; simpa using hYf
  have hYY := hodge Y hYf
  have hX : X = Y + t • f := by simp [Y]
  have hXX : B X X = B Y Y + t ^ 2 * B f f := by
    rw [hX]; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hYf, hfY]; ring
  have : B f f * B X X ≤ B f f * (t ^ 2 * B f f) := by
    rw [hXX]; nlinarith
  calc B f f * B X X ≤ B f f * (t ^ 2 * B f f) := this
    _ = (B X f) ^ 2 := by simp only [t]; field_simp

open Classical in
/-- Under the Hodge index, a model of the bounded axioms with `Div = V`, `Prin = ⊥`. -/
noncomputable def trivialModel {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) {f : V} (hf : 0 < B f f)
    (hodge : ∀ v, B v f = 0 → B v v ≤ 0) : RRAxiomsBounded B f (LinearMap.id : V →ₗ[ℝ] V) :=
  let h0 : V → ℝ := fun X => if 0 < B X f then (B X f) ^ 2 / (2 * B f f) + 1 else if X = 0 then 1 else 0
  have h0nn : ∀ X, 0 ≤ h0 X := by intro X; simp only [h0]; split_ifs <;> positivity
  have cs := cauchy_schwarz_of_hodge hB hf hodge
  have key : ∀ X : V, (1 / 2) * B X X ≤ h0 X + h0 (-X) := by
    intro X
    rcases lt_trichotomy (B X f) 0 with h | h | h
    · have hn : 0 < B (-X) f := by simp; linarith
      have hsq : (B (-X) f) ^ 2 = (B X f) ^ 2 := by simp
      have hm : h0 (-X) = (B X f) ^ 2 / (2 * B f f) + 1 := by
        simp only [h0, if_pos hn, hsq]
      have := cs X
      have h2 : (1 / 2) * B X X ≤ (B X f) ^ 2 / (2 * B f f) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith [h0nn X]
    · have := hodge X h; linarith [h0nn X, h0nn (-X)]
    · have : h0 X = (B X f) ^ 2 / (2 * B f f) + 1 := by simp only [h0, if_pos h]
      have := cs X
      have h2 : (1 / 2) * B X X ≤ (B X f) ^ 2 / (2 * B f f) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith [h0nn (-X)]
  { deg := B.flip f
    deg_ι := by intro v; simp
    Prin := ⊥
    deg_prin := by intro X hX; simp at hX; simp [hX]
    Eff := fun X => 0 < B X f ∨ X = 0
    h0 := h0
    h1 := fun X => h0 X + h0 (-X) - (1 / 2) * B X X
    h0_nonneg := h0nn
    h1_nonneg := by intro X; have := key X; linarith
    K := 0
    a := fun _ => 0
    χ := 0
    rr := by
      intro v n
      simp only [LinearMap.id_apply, zero_sub, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    eff := by
      intro X hX
      refine ⟨X, ?_, by simp, ?_⟩ <;> simp only [h0] at hX <;> split_ifs at hX with h1 h2
      · exact Or.inl h1
      · exact Or.inr h2
      · exact absurd hX (lt_irrefl 0)
      · left; simpa using h1
      · right; simp [h2]
      · exact absurd hX (lt_irrefl 0)
    compat := by intro v hv; simp at hv; simp [hv]
    β := fun d => if 0 < d then d ^ 2 / (2 * B f f) + 1 else 1
    bound := by
      intro X
      show h0 X ≤ (if 0 < B X f then (B X f) ^ 2 / (2 * B f f) + 1 else 1)
      by_cases h : 0 < B X f
      · simp only [h0, if_pos h, le_refl]
      · simp only [h0, if_neg h]
        split_ifs <;> norm_num }

/-- **Collapse.** With `Div = V`, the bounded RR axioms are satisfiable iff the Hodge index holds. -/
theorem collapse {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) {f : V} (hf : 0 < B f f) :
    Nonempty (RRAxiomsBounded B f (LinearMap.id : V →ₗ[ℝ] V)) ↔ ∀ v, B v f = 0 → B v v ≤ 0 :=
  ⟨fun ⟨A⟩ => hodge_index A, fun h => ⟨trivialModel hB hf h⟩⟩

/-! ## Countermodel: without the degree bound the axioms do not imply the Hodge index -/

/-- `B(x, y) = x₀ y₁ + x₁ y₀ + x₂ y₂` on `ℝ³`: a hyperbolic plane plus one positive direction. -/
def Bc : LinearMap.BilinForm ℝ (Fin 3 → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => x 0 * y 1 + x 1 * y 0 + x 2 * y 2)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)

/-- `f = f₁ + f₂`. -/
def fc : Fin 3 → ℝ := ![1, 1, 0]

/-- Divisors `ℝ³ × ℝ`, graph span as the first factor. -/
abbrev DivC := (Fin 3 → ℝ) × ℝ

def ιc : (Fin 3 → ℝ) →ₗ[ℝ] DivC := LinearMap.inl ℝ _ _

def degc : DivC →ₗ[ℝ] ℝ where
  toFun X := X.1 0 + X.1 1 + X.2
  map_add' X Y := by simp; ring
  map_smul' r X := by simp; ring

lemma degc_apply (X : DivC) : degc X = X.1 0 + X.1 1 + X.2 := rfl

open Classical in
noncomputable def h0c (X : DivC) : ℝ :=
  if 0 < degc X then |Bc X.1 X.1| / 2 + 1 else if X = 0 then 1 else 0

lemma h0c_nonneg (X : DivC) : 0 ≤ h0c X := by
  unfold h0c; split_ifs <;> positivity

def Kc : DivC := (0, 1)

open Classical in
noncomputable def h1c (X : DivC) : ℝ :=
  if X.2 = 0 then h0c X + h0c (Kc - X) - (1 / 2) * Bc X.1 X.1 else 0

lemma Bc_neg (w : Fin 3 → ℝ) : Bc (-w) (-w) = Bc w w := by simp

lemma h1c_nonneg (X : DivC) : 0 ≤ h1c X := by
  unfold h1c
  split_ifs with h2
  · by_cases hd : 0 < degc X
    · have : h0c X = |Bc X.1 X.1| / 2 + 1 := by
        unfold h0c; rw [if_pos hd]
      have := h0c_nonneg (Kc - X)
      have := le_abs_self (Bc X.1 X.1)
      linarith
    · have hd' : 0 < degc (Kc - X) := by
        rw [map_sub]; simp only [degc_apply, Kc, h2] at *; push Not at hd
        simp; linarith
      have hK : h0c (Kc - X) = |Bc (Kc - X).1 (Kc - X).1| / 2 + 1 := by
        unfold h0c; rw [if_pos hd']
      have h1 : (Kc - X).1 = -X.1 := by simp [Kc]
      rw [h1, Bc_neg] at hK
      have := h0c_nonneg X
      have := le_abs_self (Bc X.1 X.1)
      linarith
  · exact le_refl 0

open Classical in
/-- The countermodel satisfies the dimension-level axioms. -/
noncomputable def counterAxioms : RRAxioms Bc fc ιc where
  deg := degc
  deg_ι := by intro v; simp [degc_apply, ιc, Bc, fc]
  Prin := ⊥
  deg_prin := by intro X hX; simp at hX; simp [hX]
  Eff := fun X => 0 < degc X ∨ X = 0
  h0 := h0c
  h1 := h1c
  h0_nonneg := h0c_nonneg
  h1_nonneg := h1c_nonneg
  K := Kc
  a := fun _ => 0
  χ := 0
  rr := by
    intro v n
    have : (ιc ((n : ℝ) • v)).2 = 0 := by simp [ιc]
    simp only [h1c, this, if_true]
    have h1 : (ιc ((n : ℝ) • v)).1 = (n : ℝ) • v := by simp [ιc]
    rw [h1, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    ring
  eff := by
    intro X hX
    refine ⟨X, ?_, by simp, ?_⟩
    · unfold h0c at hX
      split_ifs at hX with h1 h2
      · exact Or.inl h1
      · exact Or.inr h2
      · exact absurd hX (lt_irrefl 0)
    · unfold h0c at hX
      split_ifs at hX with h1 h2
      · exact Or.inl h1
      · right; simp [h2]
      · exact absurd hX (lt_irrefl 0)
  compat := by
    intro v hv
    simp [ιc] at hv
    simp [hv]

/-- The countermodel violates the Hodge index: `e₃ ⊥ f` but `B e₃ e₃ = 1 > 0`. -/
theorem countermodel :
    ∃ (A : RRAxioms Bc fc ιc) (v : Fin 3 → ℝ), A.deg (ιc v) = 0 ∧ Bc v fc = 0 ∧ 0 < Bc v v :=
  ⟨counterAxioms, ![0, 0, 1], by simp [counterAxioms, degc_apply, ιc], by simp [Bc, fc], by simp [Bc]⟩

end RRSquare
