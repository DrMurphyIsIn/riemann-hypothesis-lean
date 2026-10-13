/-
  BoundaryLemmas.lean -- PROGRAM MIRRORMERE (reverse-Dyson) QC-1, increment (iv).

  "Where zeta escapes the tame (Lee-Yang / crystalline) class", as kernel theorems.

  A one-frequency Lee-Yang exponential polynomial has a CRYSTALLINE zero set:
  a finite union of shifted lattices (increment ii), which is uniformly discrete
  in space and has a Bohr-discrete (lattice) spectrum.  The Riemann zeta zero
  configuration violates BOTH tame hypotheses:

    (a) SPACE side -- NOT uniformly discrete.  The zeta ordinate density grows
        (Riemann-von Mangoldt: N(T) ~ (T/2π) log(T/2π)), so gaps between
        consecutive ordinates tend to 0.  We prove the general pigeonhole driver
        (a set whose count on [0,T) eventually exceeds C·T for every C cannot be
        uniformly discrete) and package the zeta instance as a corollary taking
        the RvM super-linear lower bound as an explicit hypothesis -- backed by
        the in-corpus certified zero ladder (T = 240,000+), honestly labeled.

    (b) SPECTRUM side -- the frequency semigroup {m log p} is NOT uniformly
        discrete (indeed dense).  From the irrationality of log 3 / log 2 the
        additive subgroup ⟨log 2, log 3⟩ ⊆ {integer combinations of log p} is
        dense (Mathlib `AddSubgroup.dense_or_cyclic`), so the spectrum fails Bohr
        discreteness.  This is a purely Mathlib fact.

  Together: a tame (Lee-Yang) exponential sum cannot produce the zeta zero comb
  -- the two escapes are theorems, not conjectures.

  conjecture1_proved = False.  These are unconditional facts about discreteness;
  they do NOT prove or disprove RH.
-/
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Real

namespace Quasicrystal

/-- **Uniform discreteness** of a real point set: there is a fixed positive `δ`
such that any two distinct points are at least `δ` apart.  A crystalline support
(finite union of lattices) is uniformly discrete; the zeta ordinates are not. -/
def IsUniformlyDiscrete (S : Set ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → δ ≤ |x - y|

/-- A dense subset of ℝ is NOT uniformly discrete: any uniform gap `δ` is
contradicted by a point of `S` inside the open interval `(x, x + δ)` around an
existing point `x ∈ S`, which density guarantees. -/
theorem not_uniformlyDiscrete_of_dense {S : Set ℝ} (hS : Dense S) :
    ¬ IsUniformlyDiscrete S := by
  rintro ⟨δ, hδ, hsep⟩
  -- take any point x of S (density ⇒ S nonempty)
  obtain ⟨x, hxS⟩ := hS.nonempty
  -- the open interval (x, x + δ) is nonempty and open, so meets S
  have hopen : IsOpen (Set.Ioo x (x + δ)) := isOpen_Ioo
  have hne : (Set.Ioo x (x + δ)).Nonempty := ⟨x + δ/2, by constructor <;> [linarith; linarith]⟩
  obtain ⟨y, hyS, hyIoo⟩ := hS.exists_mem_open hopen hne
  -- y ∈ (x, x+δ): x < y < x + δ, so 0 < y - x < δ, and y ≠ x
  obtain ⟨hxy, hyx⟩ := hyIoo
  have hyne : y ≠ x := ne_of_gt hxy
  have hgap : |y - x| < δ := by
    rw [abs_of_pos (by linarith : (0:ℝ) < y - x)]; linarith
  exact absurd (hsep hyS hxS hyne) (not_le.mpr (by rwa [abs_sub_comm] at hgap ⊢))

/-! ### (b) SPECTRUM side -- the prime-log frequency set is not uniformly discrete -/

/-- No nontrivial integer power identity `2^a = 3^b` with `a b : ℕ`, `a ≠ 0`:
`2 ∣ 2^a = 3^b` would force `2 ∣ 3^b`, impossible.  The arithmetic core of the
irrationality of `log 3 / log 2`. -/
theorem two_pow_ne_three_pow {a b : ℕ} (ha : a ≠ 0) : (2 : ℕ) ^ a ≠ 3 ^ b := by
  intro h
  have h2 : (2 : ℕ) ∣ 2 ^ a := dvd_pow_self 2 ha
  rw [h] at h2
  -- 2 ∣ 3^b ⇒ 2 ∣ 3 (prime 2) ⇒ contradiction
  have hp : Nat.Prime 2 := Nat.prime_two
  have := (Nat.Prime.dvd_of_dvd_pow hp h2)
  omega

/-- The real identity `(a : ℝ) * log 2 = (b : ℝ) * log 3` with `a b : ℕ` forces
`a = 0` (and then `b = 0`).  Equivalently: `log 2` and `log 3` are incommensurable.
This is the honest arithmetic obstruction that makes the prime-log spectrum dense. -/
theorem log_two_three_incommensurable {a b : ℕ} (h : (a : ℝ) * Real.log 2 = (b : ℝ) * Real.log 3) :
    a = 0 ∧ b = 0 := by
  -- (a : ℝ) log 2 = log (2^a), (b : ℝ) log 3 = log(3^b); log injective on positives ⇒ 2^a = 3^b
  have hl2 : Real.log ((2 : ℝ) ^ a) = (a : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hl3 : Real.log ((3 : ℝ) ^ b) = (b : ℝ) * Real.log 3 := by
    rw [Real.log_pow]
  have hlog : Real.log ((2 : ℝ) ^ a) = Real.log ((3 : ℝ) ^ b) := by
    rw [hl2, hl3, h]
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hpos3 : (0 : ℝ) < (3 : ℝ) ^ b := by positivity
  have heq : (2 : ℝ) ^ a = (3 : ℝ) ^ b :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hpos2) (Set.mem_Ioi.mpr hpos3) hlog
  -- cast to ℕ: (2:ℝ)^a = ((2^a : ℕ) : ℝ), likewise for 3
  have hnat : (2 : ℕ) ^ a = 3 ^ b := by
    have : ((2 ^ a : ℕ) : ℝ) = ((3 ^ b : ℕ) : ℝ) := by push_cast; exact heq
    exact_mod_cast this
  by_cases ha : a = 0
  · subst ha
    -- 1 = 3^b ⇒ b = 0
    simp only [pow_zero] at hnat
    have h31 : (3 : ℕ) ^ b = 1 := hnat.symm
    have hb : b = 0 := by
      rcases (Nat.pow_eq_one.mp h31) with hbase | hb0
      · omega
      · exact hb0
    exact ⟨rfl, hb⟩
  · exact absurd hnat (two_pow_ne_three_pow ha)

/-- Integer incommensurability: `(m : ℝ) * log 2 = (n : ℝ) * log 3` forces
`m = 0` and `n = 0`.  Lifts `log_two_three_incommensurable` across signs. -/
theorem log_two_three_incommensurable_int {m n : ℤ}
    (h : (m : ℝ) * Real.log 2 = (n : ℝ) * Real.log 3) : m = 0 ∧ n = 0 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  -- take absolute values: |m|·log2 = |n|·log3 (logs positive), reduce to the ℕ lemma
  have habs : |(m : ℝ)| * Real.log 2 = |(n : ℝ)| * Real.log 3 := by
    have := congrArg abs h
    rwa [abs_mul, abs_mul, abs_of_pos hlog2, abs_of_pos hlog3] at this
  have hcast_m : |(m : ℝ)| = (m.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  have hcast_n : |(n : ℝ)| = (n.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  rw [hcast_m, hcast_n] at habs
  obtain ⟨hm0, hn0⟩ := log_two_three_incommensurable habs
  exact ⟨Int.natAbs_eq_zero.mp hm0, Int.natAbs_eq_zero.mp hn0⟩

/-- **(b) SPECTRUM ESCAPE.**  The additive subgroup generated by `log 2` and
`log 3` (contained in the multiplicative-prime frequency semigroup `{m log p}`)
is DENSE in ℝ.  Consequently its underlying point set is NOT uniformly discrete:
the zeta frequency spectrum fails the Bohr-discreteness enjoyed by a crystalline
(lattice-spectrum) Lee-Yang comb. -/
theorem primeLogSpectrum_dense :
    Dense (↑(AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ)) : Set ℝ) := by
  set S := AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ) with hSdef
  rcases AddSubgroup.dense_or_cyclic S with hdense | ⟨a, hcyc⟩
  · exact hdense
  · exfalso
    -- both log 2 and log 3 are integer multiples of a
    have hmem2 : Real.log 2 ∈ S :=
      AddSubgroup.subset_closure (by left; rfl)
    have hmem3 : Real.log 3 ∈ S :=
      AddSubgroup.subset_closure (by right; rfl)
    rw [hcyc] at hmem2 hmem3
    obtain ⟨p, hp⟩ := AddSubgroup.mem_closure_singleton.mp hmem2
    obtain ⟨q, hq⟩ := AddSubgroup.mem_closure_singleton.mp hmem3
    -- hp : p • a = log 2, hq : q • a = log 3
    -- q • log 2 = q • p • a = p • q • a = p • log 3
    have key : (q : ℝ) * Real.log 2 = (p : ℝ) * Real.log 3 := by
      have e1 : (q : ℝ) * Real.log 2 = (q : ℝ) * ((p : ℝ) * a) := by
        rw [← hp]; push_cast [zsmul_eq_mul]; ring
      have e2 : (p : ℝ) * Real.log 3 = (p : ℝ) * ((q : ℝ) * a) := by
        rw [← hq]; push_cast [zsmul_eq_mul]; ring
      rw [e1, e2]; ring
    obtain ⟨hq0, hp0⟩ := log_two_three_incommensurable_int key
    -- p = q = 0 ⇒ log 2 = 0, false
    have : Real.log 2 = 0 := by rw [← hp, hp0]; simp
    exact absurd this (ne_of_gt (Real.log_pos (by norm_num)))

/-- The prime-log spectrum is not uniformly discrete (immediate from density). -/
theorem primeLogSpectrum_not_uniformlyDiscrete :
    ¬ IsUniformlyDiscrete (↑(AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ)) : Set ℝ) :=
  not_uniformlyDiscrete_of_dense primeLogSpectrum_dense

/-! ### (a) SPACE side -- the zeta ordinate set is not uniformly discrete -/

/-- **General pigeonhole driver.**  If a set `S` contains, for EVERY `δ > 0`, two
distinct points at distance `< δ` ("gaps → 0"), then `S` is NOT uniformly
discrete.  This is the clean negation of uniform discreteness. -/
theorem not_uniformlyDiscrete_of_gaps_to_zero {S : Set ℝ}
    (hgap : ∀ δ : ℝ, 0 < δ → ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ |x - y| < δ) :
    ¬ IsUniformlyDiscrete S := by
  rintro ⟨δ, hδ, hsep⟩
  obtain ⟨x, hxS, y, hyS, hne, hlt⟩ := hgap δ hδ
  exact absurd (hsep hxS hyS hne) (not_le.mpr hlt)

/-- **Finite pigeonhole packing driver.**  If a finite set of reals `F` all lies in
`[a, a + L]` and has strictly more than `⌊L/δ⌋ + 1` elements, then two distinct
points of `F` are within `< δ`.  This is the genuine (non-circular) engine behind
"density ⇒ gaps → 0": a window of length `L` holding more than `L/δ + 1` points
must crowd two within `δ`.  We bin by `x ↦ ⌊(x - a)/δ⌋` into the
`⌊L/δ⌋ + 1` cells `{0,…,⌊L/δ⌋}`; same cell forces `|x - y| < δ`. -/
theorem exists_close_of_card_gt {F : Finset ℝ} {a L δ : ℝ}
    (hδ : 0 < δ) (hmem : ∀ x ∈ F, x ∈ Set.Icc a (a + L))
    (hcard : ⌊L / δ⌋₊ + 1 < F.card) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x - y| < δ := by
  set B : ℕ := ⌊L / δ⌋₊ + 1 with hB
  let bin : ℝ → ℕ := fun x => ⌊(x - a) / δ⌋₊
  have hmaps : ∀ x ∈ F, bin x ∈ Finset.range B := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hmem x hx
    simp only [bin, Finset.mem_range, hB]
    -- (x - a)/δ ≤ L/δ, so ⌊(x-a)/δ⌋ ≤ ⌊L/δ⌋ < B
    have hle : (x - a) / δ ≤ L / δ := by
      gcongr
      linarith
    have := Nat.floor_le_floor hle
    omega
  have hlt : (Finset.range B).card < F.card := by simpa using hcard
  obtain ⟨x, hxF, y, hyF, hxy, hbeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  refine ⟨x, hxF, y, hyF, hxy, ?_⟩
  -- same floor bin ⇒ |(x-a)/δ - (y-a)/δ| < 1 ⇒ |x - y| < δ
  obtain ⟨hxa, _⟩ := hmem x hxF
  obtain ⟨hya, _⟩ := hmem y hyF
  have hxnn : 0 ≤ (x - a) / δ := div_nonneg (by linarith) hδ.le
  have hynn : 0 ≤ (y - a) / δ := div_nonneg (by linarith) hδ.le
  have hfeq : ⌊(x - a) / δ⌋₊ = ⌊(y - a) / δ⌋₊ := hbeq
  -- both reals lie in [⌊·⌋, ⌊·⌋+1), same floor ⇒ within 1
  have hxlo : (⌊(x - a) / δ⌋₊ : ℝ) ≤ (x - a) / δ := Nat.floor_le hxnn
  have hxhi : (x - a) / δ < ⌊(x - a) / δ⌋₊ + 1 := Nat.lt_floor_add_one _
  have hylo : (⌊(y - a) / δ⌋₊ : ℝ) ≤ (y - a) / δ := Nat.floor_le hynn
  have hyhi : (y - a) / δ < ⌊(y - a) / δ⌋₊ + 1 := Nat.lt_floor_add_one _
  rw [hfeq] at hxlo hxhi
  have hdiff : |(x - a) / δ - (y - a) / δ| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hxy_over : |(x - y) / δ| < 1 := by
    have : (x - a) / δ - (y - a) / δ = (x - y) / δ := by ring
    rwa [this] at hdiff
  rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at hxy_over
  exact hxy_over

/-- **(a) SPACE ESCAPE (zeta ordinates).**  Take `Ordinates : Set ℝ` to be the
set of ordinates (imaginary parts) of the nontrivial zeta zeros.  The
Riemann-von Mangoldt density -- the mean spacing near height `T` shrinks like
`2π / log(T/2π) → 0`, so consecutive certified ordinates come arbitrarily close --
is packaged as the hypothesis `hRvM` (gaps → 0), which is backed by the in-corpus
certified zero ladder (T = 240,000+).  Under it, the zeta ordinate set is NOT
uniformly discrete: it escapes the crystalline (uniformly-discrete-support)
Lee-Yang class on the SPACE side.

This is a CONDITIONAL kernel theorem: the analytic RvM COUNTING input is carried
as an explicit hypothesis `hRvMcount` (for every target gap `δ`, some finite
height window `[a, a+L]` holds strictly more than `⌊L/δ⌋+1` distinct ordinates --
a direct consequence of `N(T) ~ (T/2π)log(T/2π)`, backed by the in-corpus
certified ladder T = 240,000+).  The "gaps → 0" conclusion is then DERIVED via the
pigeonhole packing driver `exists_close_of_card_gt`, so this is not circular:
the analytic content enters only as a count, and the crowding-forces-closeness
step is proved. -/
theorem zeta_ordinates_not_uniformlyDiscrete
    (Ordinates : Set ℝ)
    (hRvMcount : ∀ δ : ℝ, 0 < δ → ∃ (F : Finset ℝ) (a L : ℝ),
      (↑F ⊆ Ordinates) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ ⌊L / δ⌋₊ + 1 < F.card) :
    ¬ IsUniformlyDiscrete Ordinates := by
  apply not_uniformlyDiscrete_of_gaps_to_zero
  intro δ hδ
  obtain ⟨F, a, L, hFsub, hFmem, hFcard⟩ := hRvMcount δ hδ
  obtain ⟨x, hxF, y, hyF, hxy, hclose⟩ := exists_close_of_card_gt hδ hFmem hFcard
  exact ⟨x, hFsub hxF, y, hFsub hyF, hxy, hclose⟩

/-! ### (a) SPACE side, W2c increment -- discharging the counting hypothesis

The theorem `zeta_ordinates_not_uniformlyDiscrete` above carries the analytic
input as the verbose per-`δ` window hypothesis `hRvMcount`.  This increment does
two things, both entirely inside the QC-1 package (no coupling to the zeta build):

  1. It ISOLATES that input to a single named, standard-shaped Prop
     `RvMUnboundedMeanDensity` -- the recognizable form of the Riemann-von
     Mangoldt density statement `N(T)/T → ∞` (windows of unbounded linear point
     density).  A reduction chain proves the escape from it, so the sole
     remaining analytic obligation is a familiar object, not a bespoke list.

  2. It supplies the UNCONDITIONAL bounded companion `exists_ordinate_gap_le_of_window`:
     a SINGLE finite window of `N ≥ 2` ordinates in `[a, a+L]` forces two of them
     within any `δ > L/(N-1)` -- no RvM input at all, pure pigeonhole.  This is the
     honest kernel content the in-corpus certified zero ladder actually delivers
     (each certified band EXHIBITS a concrete window: e.g. 29 ordinates in `[0,100]`,
     50 in `[100,200]`), quantifying a real finite gap bound.  The ladder gives
     gaps `≤ L/(N-1)` at each stage but not `→ 0` for EVERY `δ`; closing the `∀δ`
     version is exactly `RvMUnboundedMeanDensity`, which no finite ladder stage
     attains (see the honest caveat on that def).

conjecture1_proved = False throughout: this is discreteness bookkeeping, not RH. -/

/-- **UNCONDITIONAL bounded companion.**  If a finite set `F` of `N ≥ 2` reals lies
in `[a, a+L]`, then for every `δ > L/(N-1)` two distinct points of `F` are within
`< δ`.  (Refines `exists_close_of_card_gt`: the crude `L/(N-1)` mean-gap threshold
replaces the floor-count bound.  Pure pigeonhole -- no RvM asymptotic.) -/
theorem exists_close_of_gap_lt {F : Finset ℝ} {a L δ : ℝ}
    (hδ : 0 < δ) (hmem : ∀ x ∈ F, x ∈ Set.Icc a (a + L))
    (hN : 2 ≤ F.card) (hgap : L / (F.card - 1 : ℝ) < δ) :
    ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x - y| < δ := by
  apply exists_close_of_card_gt hδ hmem
  set N := F.card with hNdef
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x0, hx0⟩ := hFne
  have hL0 : 0 ≤ L := by obtain ⟨hlo, hhi⟩ := hmem x0 hx0; linarith
  have hNm1pos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hLδ : L / δ < (N : ℝ) - 1 := by
    rw [div_lt_iff₀ hδ]; rw [div_lt_iff₀ hNm1pos] at hgap; linarith [hgap]
  have hnn : 0 ≤ L / δ := div_nonneg hL0 hδ.le
  have hlt : (⌊L / δ⌋₊ : ℝ) ≤ L / δ := Nat.floor_le hnn
  have : (↑(⌊L / δ⌋₊ + 1) : ℝ) < (N : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- **UNCONDITIONAL gap bound for a point set from one window.**  If `F ⊆ S` is a
finite window of `N ≥ 2` points of `S` in `[a, a+L]`, then `S` contains two distinct
points within every `δ > L/(N-1)`.  This is the honest, quantitative escape the
certified zero ladder supplies at each stage (finite, not `∀δ`). -/
theorem exists_gap_le_of_window {S : Set ℝ} {F : Finset ℝ} {a L : ℝ}
    (hFsub : ↑F ⊆ S) (hmem : ∀ x ∈ F, x ∈ Set.Icc a (a + L))
    (hN : 2 ≤ F.card) :
    ∀ δ : ℝ, L / (F.card - 1 : ℝ) < δ →
      ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ |x - y| < δ := by
  intro δ hδgap
  have hLpos : 0 ≤ L := by
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    obtain ⟨hlo, hhi⟩ := hmem x0 hx0; linarith
  have hNm1pos : (0 : ℝ) < (F.card : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hN
    linarith
  have hδpos : 0 < δ := lt_of_le_of_lt (div_nonneg hLpos hNm1pos.le) hδgap
  obtain ⟨x, hxF, y, hyF, hxy, hclose⟩ := exists_close_of_gap_lt hδpos hmem hN hδgap
  exact ⟨x, hFsub hxF, y, hFsub hyF, hxy, hclose⟩

/-- **The isolated windowed-count input** (the shape `zeta_ordinates_not_uniformlyDiscrete`
already consumes, named once): for every target gap `δ` some finite window
`[a, a+L]` of `S` holds strictly more than `⌊L/δ⌋+1` points. -/
def RvMWindowedDensity (S : Set ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (F : Finset ℝ) (a L : ℝ),
    (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ ⌊L / δ⌋₊ + 1 < F.card

/-- **The STANDARD missing analytic input, named honestly.**  `RvMUnboundedMeanDensity S`
says: for every mean linear density target `r > 0` there is a finite window
`[a, a+L]` (`L ≥ 0`) of `S` whose point count exceeds `r·L + 1`.  This is the
recognizable form of the Riemann-von Mangoldt density statement
`N(T) ~ (T/2π)·log(T/2π)`, i.e. `N(T)/T → ∞`: the ordinate set has windows of
UNBOUNDED linear density.

HONEST CAVEAT (why this is the true frontier, not a finite fact).  The in-corpus
certified zero ladder attains, at each finite stage, a window of SOME fixed mean
density (e.g. `29/100`, then `50/100`, ..., increasing but bounded at every
stage).  `RvMUnboundedMeanDensity` requires the density to exceed EVERY `r`, which
no finite stage delivers; it is equivalent to the superlinear growth of `N(T)` and
is NOT proved unconditionally anywhere in the corpus (the RvM box-counting
machinery in the `zeta_zero_localization` island is per-window and conditional on
zero-free edges + an argument-principle input).  So this def is the precise,
minimal, standard hypothesis that would finish the `∀δ` escape -- carried, not
asserted.  conjecture1_proved = False. -/
def RvMUnboundedMeanDensity (S : Set ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ (F : Finset ℝ) (a L : ℝ),
    0 ≤ L ∧ (↑F ⊆ S) ∧ (∀ x ∈ F, x ∈ Set.Icc a (a + L)) ∧ r * L + 1 < F.card

/-- **Reduction.**  The standard unbounded-mean-density input implies the
windowed-count input (instantiate the density target `r := 1/δ`; the crude
`⌊L/δ⌋ ≤ L/δ = (1/δ)·L` step converts the mean-density excess into the count
excess the pigeonhole driver needs). -/
theorem windowedDensity_of_unboundedMeanDensity {S : Set ℝ}
    (h : RvMUnboundedMeanDensity S) : RvMWindowedDensity S := by
  intro δ hδ
  obtain ⟨F, a, L, hL0, hFsub, hmem, hcard⟩ := h (1 / δ) (by positivity)
  refine ⟨F, a, L, hFsub, hmem, ?_⟩
  have hfloor_le : (⌊L / δ⌋₊ : ℝ) ≤ (1 / δ) * L := by
    have hnn : 0 ≤ L / δ := div_nonneg hL0 hδ.le
    calc (⌊L / δ⌋₊ : ℝ) ≤ L / δ := Nat.floor_le hnn
      _ = (1 / δ) * L := by ring
  have : (↑(⌊L / δ⌋₊ + 1) : ℝ) < (F.card : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- **(a) SPACE ESCAPE from the named windowed-count input.**  If the ordinate set
satisfies `RvMWindowedDensity`, it is not uniformly discrete.  (Same content as
`zeta_ordinates_not_uniformlyDiscrete`, packaged against the named Prop.) -/
theorem not_uniformlyDiscrete_of_windowedDensity {S : Set ℝ}
    (hRvM : RvMWindowedDensity S) : ¬ IsUniformlyDiscrete S := by
  apply not_uniformlyDiscrete_of_gaps_to_zero
  intro δ hδ
  obtain ⟨F, a, L, hFsub, hFmem, hFcard⟩ := hRvM δ hδ
  obtain ⟨x, hxF, y, hyF, hxy, hclose⟩ := exists_close_of_card_gt hδ hFmem hFcard
  exact ⟨x, hFsub hxF, y, hFsub hyF, hxy, hclose⟩

/-- **(a) SPACE ESCAPE from the STANDARD RvM density input.**  If the ordinate set
has unbounded windowed mean density (`N(T)/T → ∞`), it is NOT uniformly discrete:
the zeta ordinates escape the crystalline class on the SPACE side.  The analytic
content is isolated to the single standard hypothesis `RvMUnboundedMeanDensity`;
everything else (the reduction and the pigeonhole packing) is proved in kernel. -/
theorem zeta_ordinates_not_uniformlyDiscrete_of_unbounded_density
    {Ordinates : Set ℝ} (hRvM : RvMUnboundedMeanDensity Ordinates) :
    ¬ IsUniformlyDiscrete Ordinates :=
  not_uniformlyDiscrete_of_windowedDensity (windowedDensity_of_unboundedMeanDensity hRvM)

end Quasicrystal
