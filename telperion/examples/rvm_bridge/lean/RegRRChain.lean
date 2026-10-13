import PFConverseC

/-!
# Registry-shape statements of the RR-square conditional chain (e9, 2026-10-13)

Five root-namespace theorems whose statements are the registry statements VERBATIM (fully qualified, every axiom spelled
out as an explicit hypothesis so the read-back can see each one), proved from `PFConverseC` (and the `collapse` port below):
* `rr_square_hodge_index`          : RR axioms + degree bound  => Hodge index (RvMBridgePF.RRSquare.hodge_index);
* `rr_square_hodge_index_domain`   : RR axioms + no zero divisors => Hodge index (hodge_index_of_domain);
* `rr_square_collapse`             : with Div = V the bounded axioms are satisfiable IFF the Hodge index holds, so a bare
                                     existence statement is circular: the content must be a construction;
* `polefree_weil_converse`         : Weil positivity on pole-free tests => Mathlib's RiemannHypothesis;
* `rr_windows_imply_rh`            : RR-square windows covering every pole-free test => RiemannHypothesis.
A CONDITIONAL REDUCTION, not progress on RH: by `rr_square_collapse` such windows exist trivially under RH.
conjecture1_proved = False.
-/

open Classical

namespace RvMBridgePF.RRSquare

variable {V Div : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup Div] [Module ℝ Div]

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


end RvMBridgePF.RRSquare

open RvMBridgePF RvMBridgePF.RRSquare

/-- Registry shape of `MM_rr_square_hodge_index`. -/
theorem rr_square_hodge_index {V Div : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup Div] [Module ℝ Div]
    (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div) (deg : Div →ₗ[ℝ] ℝ)
    (hdeg : ∀ v, deg (ι v) = B v f) (Prin : Submodule ℝ Div) (hprin : ∀ X ∈ Prin, deg X = 0)
    (h0 h1 : Div → ℝ) (h0nn : ∀ X, 0 ≤ h0 X) (h1nn : ∀ X, 0 ≤ h1 X) (K : Div) (a : V → ℝ) (χ : ℝ)
    (rr : ∀ (v : V) (n : ℕ), h0 (ι ((n : ℝ) • v)) - h1 (ι ((n : ℝ) • v)) + h0 (K - ι ((n : ℝ) • v))
      = (1 / 2) * (n : ℝ) ^ 2 * B v v - (1 / 2) * (n : ℝ) * a v + χ)
    (eff : ∀ X, 0 < h0 X → ∃ E, X - E ∈ Prin ∧ (0 < deg E ∨ E ∈ Prin))
    (compat : ∀ v, ι v ∈ Prin → B v v = 0)
    (β : ℝ → ℝ) (bound : ∀ X, h0 X ≤ β (deg X)) (v : V) (hv : B v f = 0) : B v v ≤ 0 :=
  RvMBridgePF.RRSquare.hodge_index
    { deg := deg, deg_ι := hdeg, Prin := Prin, deg_prin := hprin, Eff := fun _ => True, h0 := h0, h1 := h1,
      h0_nonneg := h0nn, h1_nonneg := h1nn, K := K, a := a, χ := χ, rr := rr,
      eff := fun X hX => (eff X hX).elim fun E hE => ⟨E, trivial, hE⟩, compat := compat,
      β := β, bound := bound } v hv

/-- Registry shape of `MM_rr_square_hodge_index_domain`. -/
theorem rr_square_hodge_index_domain {V Div : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup Div] [Module ℝ Div]
    (B : LinearMap.BilinForm ℝ V) (f : V) (ι : V →ₗ[ℝ] Div) (deg : Div →ₗ[ℝ] ℝ)
    (hdeg : ∀ v, deg (ι v) = B v f) (Prin : Submodule ℝ Div) (hprin : ∀ X ∈ Prin, deg X = 0)
    (h0 h1 : Div → ℝ) (h0nn : ∀ X, 0 ≤ h0 X) (h1nn : ∀ X, 0 ≤ h1 X) (K : Div) (a : V → ℝ) (χ : ℝ)
    (rr : ∀ (v : V) (n : ℕ), h0 (ι ((n : ℝ) • v)) - h1 (ι ((n : ℝ) • v)) + h0 (K - ι ((n : ℝ) • v))
      = (1 / 2) * (n : ℝ) ^ 2 * B v v - (1 / 2) * (n : ℝ) * a v + χ)
    (eff : ∀ X, 0 < h0 X → ∃ E, X - E ∈ Prin ∧ (0 < deg E ∨ E ∈ Prin))
    (compat : ∀ v, ι v ∈ Prin → B v v = 0)
    (domain : ∀ X Y, 0 < h0 X → h0 Y ≤ h0 (X + Y)) (v : V) (hv : B v f = 0) : B v v ≤ 0 :=
  RvMBridgePF.RRSquare.hodge_index_of_domain
    { deg := deg, deg_ι := hdeg, Prin := Prin, deg_prin := hprin, Eff := fun _ => True, h0 := h0, h1 := h1,
      h0_nonneg := h0nn, h1_nonneg := h1nn, K := K, a := a, χ := χ, rr := rr,
      eff := fun X hX => (eff X hX).elim fun E hE => ⟨E, trivial, hE⟩, compat := compat,
      domain := domain } v hv

/-- Registry shape of `MM_rr_square_collapse`. -/
theorem rr_square_collapse {V : Type} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V)
    (hB : ∀ x y, B x y = B y x) (f : V) (hf : 0 < B f f) :
    (∃ (deg : V →ₗ[ℝ] ℝ) (Prin : Submodule ℝ V) (h0 h1 : V → ℝ) (K : V) (a : V → ℝ) (χ : ℝ) (β : ℝ → ℝ),
      (∀ v, deg v = B v f) ∧ (∀ X ∈ Prin, deg X = 0) ∧ (∀ X, 0 ≤ h0 X) ∧ (∀ X, 0 ≤ h1 X) ∧
      (∀ (v : V) (n : ℕ), h0 ((n : ℝ) • v) - h1 ((n : ℝ) • v) + h0 (K - (n : ℝ) • v)
        = (1 / 2) * (n : ℝ) ^ 2 * B v v - (1 / 2) * (n : ℝ) * a v + χ) ∧
      (∀ X, 0 < h0 X → ∃ E, X - E ∈ Prin ∧ (0 < deg E ∨ E ∈ Prin)) ∧
      (∀ v, v ∈ Prin → B v v = 0) ∧ (∀ X, h0 X ≤ β (deg X))) ↔
    ∀ v, B v f = 0 → B v v ≤ 0 := by
  constructor
  · rintro ⟨deg, Prin, h0, h1, K, a, χ, β, hd, hp, h0n, h1n, hrr, he, hc, hb⟩ v hv
    exact rr_square_hodge_index B f LinearMap.id deg (fun v => by simpa using hd v) Prin hp h0 h1 h0n h1n K a χ
      (fun v n => by simpa using hrr v n) he (fun v hv => hc v (by simpa using hv)) β hb v hv
  · intro h
    have hS : B.IsSymm := ⟨fun x y => by simpa using hB x y⟩
    obtain ⟨A⟩ := (RvMBridgePF.RRSquare.collapse hS hf).2 h
    refine ⟨A.deg, A.Prin, A.h0, A.h1, A.K, A.a, A.χ, A.β, fun v => by simpa using A.deg_ι v, A.deg_prin,
      A.h0_nonneg, A.h1_nonneg, fun v n => by simpa using A.rr v n, fun X hX => ?_,
      fun v hv => A.compat v (by simpa using hv), A.bound⟩
    obtain ⟨E, -, hE⟩ := A.eff X hX
    exact ⟨E, hE⟩

/-- Registry shape of `MM_polefree_weil_converse`. -/
theorem polefree_weil_converse
    (hpos : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → Zeta23.paperFT g (Complex.I / 2) = 0 →
      Zeta23.paperFT g (-Complex.I / 2) = 0 → 0 ≤ (WeilExplicit.weilForm (WeilExplicit.autocorr g)).re) :
    RiemannHypothesis :=
  RvMBridgePF.weil_positivity_poleFree_implies_rh fun g hg hpf => hpos g hg hpf.1 hpf.2

/-- Registry shape of `MM_rr_windows_imply_rh`. -/
theorem rr_windows_imply_rh {ι' : Type} (V Div : ι' → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, AddCommGroup (Div i)] [∀ i, Module ℝ (Div i)]
    (B : ∀ i, LinearMap.BilinForm ℝ (V i)) (f : ∀ i, V i) (ι : ∀ i, V i →ₗ[ℝ] Div i)
    (deg : ∀ i, Div i →ₗ[ℝ] ℝ) (hdeg : ∀ i v, deg i (ι i v) = B i v (f i))
    (Prin : ∀ i, Submodule ℝ (Div i)) (hprin : ∀ i, ∀ X ∈ Prin i, deg i X = 0)
    (h0 h1 : ∀ i, Div i → ℝ) (h0nn : ∀ i X, 0 ≤ h0 i X) (h1nn : ∀ i X, 0 ≤ h1 i X)
    (K : ∀ i, Div i) (a : ∀ i, V i → ℝ) (χ : ι' → ℝ)
    (rr : ∀ i (v : V i) (n : ℕ), h0 i (ι i ((n : ℝ) • v)) - h1 i (ι i ((n : ℝ) • v)) + h0 i (K i - ι i ((n : ℝ) • v))
      = (1 / 2) * (n : ℝ) ^ 2 * B i v v - (1 / 2) * (n : ℝ) * a i v + χ i)
    (eff : ∀ i X, 0 < h0 i X → ∃ E, X - E ∈ Prin i ∧ (0 < deg i E ∨ E ∈ Prin i))
    (compat : ∀ i v, ι i v ∈ Prin i → B i v v = 0)
    (clause : ∀ i, (∃ β : ℝ → ℝ, ∀ X, h0 i X ≤ β (deg i X)) ∨ (∀ X Y, 0 < h0 i X → h0 i Y ≤ h0 i (X + Y)))
    (τ : ∀ i, V i → ℝ → ℂ) (c : ι' → ℝ) (hc : ∀ i, 0 < c i)
    (hdiag : ∀ i v, B i v v = -(c i * (WeilExplicit.weilForm (WeilExplicit.autocorr (τ i v))).re))
    (hpole : ∀ i v, Zeta23.paperFT (τ i v) (Complex.I / 2) = 0 → Zeta23.paperFT (τ i v) (-Complex.I / 2) = 0 →
      B i v (f i) = 0)
    (hcover : ∀ g : ℝ → ℂ, WeilExplicit.IsWeilTest g → Zeta23.paperFT g (Complex.I / 2) = 0 →
      Zeta23.paperFT g (-Complex.I / 2) = 0 → ∃ i, ∃ v : V i, τ i v = g) :
    RiemannHypothesis := by
  let base : ∀ i, RRAxioms (B i) (f i) (ι i) := fun i =>
    { deg := deg i, deg_ι := hdeg i, Prin := Prin i, deg_prin := hprin i, Eff := fun _ => True, h0 := h0 i,
      h1 := h1 i, h0_nonneg := h0nn i, h1_nonneg := h1nn i, K := K i, a := a i, χ := χ i, rr := rr i,
      eff := fun X hX => (eff i X hX).elim fun E hE => ⟨E, trivial, hE⟩, compat := compat i }
  let W : ι' → RRWindow := fun i =>
    { V := V i, Div := Div i, B := B i, f := f i, ι := ι i,
      ax := if hcl : ∃ β : ℝ → ℝ, ∀ X, h0 i X ≤ β (deg i X) then
          Sum.inl { base i with β := hcl.choose, bound := hcl.choose_spec }
        else Sum.inr { base i with domain := (clause i).resolve_left hcl },
      τ := τ i, c := c i, hc := hc i, hdiag := hdiag i, hpole := fun v hv => hpole i v hv.1 hv.2 }
  exact rh_of_rr_windows W fun g hg hpf => hcover g hg hpf.1 hpf.2
