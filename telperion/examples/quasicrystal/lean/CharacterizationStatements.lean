/-
  CharacterizationStatements.lean -- PROGRAM MIRRORMERE (reverse-Dyson) QC-1,
  increment (iii).

  The 1-D Fourier-quasicrystal characterization, carried as NAMED Prop-STATEMENTS
  from the literature (qc-lit deliverable A1, `telperion/docs/QC_LITERATURE.md`).

  IMPORTANT DISCIPLINE.  Everything here is a `def ... : Prop` -- a STATEMENT, not
  a theorem.  Nothing in this file is proved, and NOTHING here is `#print axioms`
  guarded as a QC-1 kernel result.  These are the external, published statements
  (Kurasov-Sarnak; Olevskii-Ulanovskii; Alon-Cohen-Vinzant Cor 1.4; Lev-Olevskii
  rigidity; Alon-Kummer-Kurasov-Vinzant Thm 2.9) written in Lean so the island
  records precisely WHAT the classification says and WHERE zeta sits relative to
  it.  They are deliberately parameterized over abstract predicates (`IsFQ`,
  `IsCrystalline`, `IsLeeYangMulti`, ...) rather than committing to a single
  measure-theoretic encoding: the honest content is the LOGICAL SHAPE of each
  statement and its hypothesis list, which is what the boundary lemmas
  (increment iv) contradict for zeta.

  conjecture1_proved = False.  These are reports of others' theorems + open
  program conjectures; NONE is claimed as proved here, and this is NOT a proof
  of RH.
-/
import BoundaryLemmas

namespace Quasicrystal.CharacterizationStatements

/-! ## Abstract vocabulary

We parameterize over opaque predicates standing for the measure-theoretic notions.
A future increment may instantiate these against a concrete Mathlib measure
encoding; for now they carry the logical structure of the literature statements. -/

/- Placeholder type of the objects (measures / point configurations on ℝ). -/
variable {Meas : Type*}

/- `IsCrystalline μ`: `μ` is a discrete (locally finite, atomic) tempered measure
whose distributional Fourier transform is also a discrete measure (Meyer §1.5). -/
variable (IsCrystalline : Meas → Prop)

/- `IsFourierQuasicrystal μ`: a crystalline measure with BOTH `|μ|` and `|μ̂|`
tempered (Alon-Cohen-Vinzant def; the strictly stronger "FQ" grade, §1.3, §1.6). -/
variable (IsFourierQuasicrystal : Meas → Prop)

/- `IsNValuedFQ μ`: a Fourier quasicrystal whose atoms carry masses in ℕ -- the
counting measure of a multiset (ACV §1.3). -/
variable (IsNValuedFQ : Meas → Prop)

/- `IsLeeYangCountingMeasure μ`: `μ = μ_{p,ℓ}` for some multivariate Lee-Yang
polynomial `p` and positive ℚ-linearly-independent frequency vector `ℓ`, i.e. the
counting measure of the real zeros of `x ↦ p(e^{i x ℓ})` (Kurasov-Sarnak §1.1). -/
variable (IsLeeYangCountingMeasure : Meas → Prop)

/- `SupportUniformlyDiscrete μ` / `SpectrumUniformlyDiscrete μ`: the two
uniform-discreteness hypotheses that the Lev-Olevskii rigidity theorem needs on
BOTH sides (§1.2). -/
variable (SupportUniformlyDiscrete SpectrumUniformlyDiscrete : Meas → Prop)

/- `IsPeriodicCombination μ`: `μ` is essentially a finite combination of Dirac
combs of lattices (the rigidity conclusion, §1.2). -/
variable (IsPeriodicCombination : Meas → Prop)

/- `IsStealthyHyperuniform μ`: the structural rigidity conclusion of
Alon-Kummer-Kurasov-Vinzant Thm 2.9 (§1.4). -/
variable (IsStealthyHyperuniform : Meas → Prop)

/- Vocabulary for ACV Theorem 1.1 (§1.3), stated over an opaque type `ExpPoly` of
exponential polynomials `f(x) = Σ_j c_j e^{λ_j x}` on ℝ. `IsRealRooted f`: all
(complex) zeros of `f` are real. `IsLeeYangRestriction f`: there exist a
multivariate Lee-Yang polynomial `p` and positive ℚ-linearly-independent
frequencies `ℓ` with `f(x) = e^{λ₀ x} · p(exp(i x ℓ))`. -/
variable {ExpPoly : Type*}
variable (IsRealRooted IsLeeYangRestriction : ExpPoly → Prop)

/-! ## The named statements (literature; NOT proved here) -/

/- **Kurasov-Sarnak (§1.1), forward direction.**  Every Lee-Yang counting measure
is an ℕ-valued Fourier quasicrystal.  [J. Math. Phys. 61 (2020) 083501] -/
def KurasovSarnak_forward : Prop :=
  ∀ μ : Meas, IsLeeYangCountingMeasure μ → IsNValuedFQ μ

/-- **Alon-Cohen-Vinzant Theorem 1.1 (§1.3).**  Every real-rooted exponential
polynomial is the restriction of a Lee-Yang polynomial: if `f(x) = Σ_j c_j e^{λ_j x}`
is real rooted, then there are a Lee-Yang polynomial `p` and positive ℚ-linearly
independent frequencies `ℓ` with `f(x) = e^{λ₀ x} p(exp(i x ℓ))`.
[J. Funct. Anal. (2024), arXiv 2303.03201]  This is the structural lemma that, with
O-U, closes the loop to Cor 1.4; it is the polynomial-level form of the increment-(i)
bridge (`expPoly`). -/
def ACV_thm11_realrooted_is_leeyang_restriction : Prop :=
  ∀ f : ExpPoly, IsRealRooted f → IsLeeYangRestriction f

/-- **Olevskii-Ulanovskii (§1.2), converse (1-D).**  Literature statement is a
two-way equivalence: a discrete unit-mass measure is a Fourier quasicrystal IFF its
support is the real zero set of a real-rooted exponential polynomial with imaginary
frequencies.  [C. R. Math. Acad. Sci. Paris 358 (2020) 1207-1211]  We record here the
direction consumed by the classification loop (ℕ-valued FQ ⇒ Lee-Yang counting); the
reverse inclusion is `KurasovSarnak_forward`. -/
def OlevskiiUlanovskii_converse : Prop :=
  ∀ μ : Meas, IsNValuedFQ μ → IsLeeYangCountingMeasure μ

/-- **Alon-Cohen-Vinzant Corollary 1.4 (§1.3) -- THE 1-D CHARACTERIZATION.**
A measure `μ` on ℝ is an ℕ-valued Fourier quasicrystal IF AND ONLY IF
`μ = μ_{p,ℓ}` for some Lee-Yang polynomial `p` and positive frequencies `ℓ`.
[J. Funct. Anal. (2024), arXiv 2303.03201]  This is the Pillar-2 anchor: the
classification of the well-behaved 1-D objects is COMPLETE. -/
def ACV_characterization : Prop :=
  ∀ μ : Meas, IsNValuedFQ μ ↔ IsLeeYangCountingMeasure μ

/-- INTERNAL bookkeeping observation (NOT a literature statement): Cor 1.4's iff is
the conjunction of its two directions -- the KS forward inclusion and the O-U/ACV
converse.  Recorded only to make the loop structure explicit; it bakes in no
zeta-side primitive and asserts nothing beyond propositional shape. -/
def characterization_is_two_inclusions : Prop :=
  (KurasovSarnak_forward IsNValuedFQ IsLeeYangCountingMeasure ∧
    OlevskiiUlanovskii_converse IsNValuedFQ IsLeeYangCountingMeasure)
  ↔ ACV_characterization IsNValuedFQ IsLeeYangCountingMeasure

/-- **Class inclusions (§1.3, §1.6, Favorov §1.6).**  ℕ-valued FQ ⊆ FQ ⊆
crystalline, both inclusions STRICT (Favorov: a crystalline measure that is not an
FQ exists; the strictness is the `|μ̂|`-temperedness discriminator). -/
def class_tower : Prop :=
  (∀ μ : Meas, IsNValuedFQ μ → IsFourierQuasicrystal μ) ∧
  (∀ μ : Meas, IsFourierQuasicrystal μ → IsCrystalline μ)

/-- **Lev-Olevskii rigidity (§1.2).**  If BOTH the support and the spectrum of `μ`
are uniformly discrete, then `μ` is (essentially) a finite combination of lattice
Dirac combs -- i.e. periodic.  [Invent. Math. 200 (2015) 585-606]  The two
uniform-discreteness hypotheses are load-bearing; zeta fails BOTH (increment iv). -/
def LevOlevskii_rigidity : Prop :=
  ∀ μ : Meas,
    SupportUniformlyDiscrete μ → SpectrumUniformlyDiscrete μ → IsPeriodicCombination μ

/-- **Alon-Kummer-Kurasov-Vinzant Thm 2.9 (§1.4).**  Every Fourier quasicrystal
support is stealthy hyperuniform.  [Invent. Math. 239 (2025) 321-376]  Recorded as
a rigidity property the zeta comb should be shown to lack (or satisfy only
conditionally). -/
def AKKV_stealthy : Prop :=
  ∀ μ : Meas, IsFourierQuasicrystal μ → IsStealthyHyperuniform μ

/-! ## Where zeta sits (the program conjectures -- OPEN, honestly labeled)

These are NOT theorems.  They state the reverse-Dyson TARGET equivalences whose
truth is governed by RH.  `conjecture1_proved = False`: each is an open program
conjecture, recorded so the falsification matrix (A2/zoo) and the wedge (B3) have
precise objects to attack. -/

/- Abstract zeta object and RH placeholder for the program-conjecture statements. -/
variable (ZetaComb : Meas) (RiemannHypothesis : Prop)

/-- **PROGRAM CONJECTURE (Favorov discriminator, §1.6/§2 table).**  The zeta comb
is a Fourier quasicrystal (equivalently: its absolute dual comb is tempered) IF AND
ONLY IF RH.  OPEN.  This is the target equivalence the whole program aims to make
precise; it is stated, never asserted. -/
def zeta_FQ_iff_RH : Prop :=
  IsFourierQuasicrystal ZetaComb ↔ RiemannHypothesis

/-- **PROGRAM CONJECTURE (Dyson lineage, §1.7).**  Under RH the zeta zeros form a
crystalline measure with prime-log spectrum.  OPEN (Weil measure is not crystalline
in the strict sense without regularization -- the honest §1.7 caveat). -/
def zeta_crystalline_under_RH : Prop :=
  RiemannHypothesis → IsCrystalline ZetaComb

end Quasicrystal.CharacterizationStatements
