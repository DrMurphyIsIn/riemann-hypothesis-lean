/-  HeightFloorCheck.lean -- brick H3 (AND_height_floor_kernel), part 1: the kernel box checker.

    M6GAP CROSS-PIN PORT (lane m6gap, 2026-09-23): a copy of
    telperion/examples/zeta_reflection/lean/HeightFloorCheck.lean (Lean v4.32.0, Mathlib v4.32.0) onto the dbn
    island (Lean v4.34.0-rc1, Mathlib de5ce8a9).  The ONLY edits are: module names prefixed `M6gap`
    in the imports, every namespace prefixed `M6gap.` (so no declaration can clash with a sibling
    lane's port), and comment wording on this island's word-level placeholder scan.  No proof was
    changed.  Consumed by M6gapHeightFloor (the 55/16 height floor on this island).


    An EXACT dyadic interval arithmetic (no rounding, no `Rat`, no division: `Int` mantissas over
    `2^e`, exponents add under multiplication and align by exact left shifts under addition),
    a fixed-formula evaluator `evalAB` for the two real quantities

        A = 24 (σ - 1) + m (C Pr + S Pi),        B = 24 t + m (C Pi - S Pr),
        Pr = σ² - t² + 11 σ + 36,                Pi = t (2 σ + 11),

    and the Boolean test `checkAB` certifying `36 < A² + B²`.  With `m = 2^{-σ}`,
    `C = cos (t log 2)`, `S = sin (t log 2)`, `A / 24` and `B / 24` are the real and imaginary parts
    of `G2 (σ + t i) = (s - 1) + 2^{-s} (s² + 11 s + 36) / 24` (see `HeightFloorEM`), so a passing
    check certifies `|G2| > 1/4` on the whole box.

    Everything is proved once here (`evalAB_sound`, `checkAB_sound`, `box_sound`); the per-box
    instances only run `decide` on small `Int` literals.

    conjecture1_proved = False.  Finite interval arithmetic at low height; nothing here is about RH.
-/
import Mathlib

namespace M6gap.HeightFloor

/-- `2^k` as an `Int`, computed through the kernel-accelerated `Nat.pow`. -/
def pow2 (k : Nat) : Int := ((2 ^ k : Nat) : Int)

theorem pow2_cast (k : Nat) : ((pow2 k : Int) : ℝ) = (2 : ℝ) ^ k := by
  unfold pow2; push_cast; ring

/-- Exact dyadic interval `[lo / 2^e, hi / 2^e]`. -/
structure DI where
  lo : Int
  hi : Int
  e : Nat
deriving Repr

namespace DI

/-- Real membership. -/
def mem (x : ℝ) (I : DI) : Prop :=
  (I.lo : ℝ) / 2 ^ I.e ≤ x ∧ x ≤ (I.hi : ℝ) / 2 ^ I.e

/-- Exact integer point. -/
def ofInt (z : Int) : DI := ⟨z, z, 0⟩

/-- Exact negation. -/
def neg (I : DI) : DI := ⟨-I.hi, -I.lo, I.e⟩

/-- Exact addition: both summands are shifted (exactly) to the larger exponent. -/
def add (I J : DI) : DI :=
  ⟨I.lo * pow2 (max I.e J.e - I.e) + J.lo * pow2 (max I.e J.e - J.e),
   I.hi * pow2 (max I.e J.e - I.e) + J.hi * pow2 (max I.e J.e - J.e),
   max I.e J.e⟩

/-- Exact multiplication: four corner products, exponents add. -/
def mul (I J : DI) : DI :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi)),
   I.e + J.e⟩

/-- Distance from `0` to the interval, in mantissa units: `max (lo, -hi, 0)`. -/
def gap (I : DI) : Int := max (max I.lo (-I.hi)) 0

/-! ### Soundness -/

theorem two_pow_pos (k : Nat) : (0 : ℝ) < (2 : ℝ) ^ k := by positivity

theorem ofInt_sound (z : Int) : (ofInt z).mem (z : ℝ) := by
  unfold ofInt mem; simp

theorem neg_sound {x : ℝ} {I : DI} (hx : I.mem x) : I.neg.mem (-x) := by
  obtain ⟨h1, h2⟩ := hx
  unfold neg mem
  simp only [Int.cast_neg, neg_div]
  exact ⟨neg_le_neg h2, neg_le_neg h1⟩

/-- Exact shift: `(z * 2^(E - e)) / 2^E = z / 2^e` when `e ≤ E`. -/
theorem shift_eq (z : Int) {e E : Nat} (h : e ≤ E) :
    ((z * pow2 (E - e) : Int) : ℝ) / (2 : ℝ) ^ E = (z : ℝ) / (2 : ℝ) ^ e := by
  have hE : (2 : ℝ) ^ E = (2 : ℝ) ^ (E - e) * (2 : ℝ) ^ e := by
    rw [← pow_add, Nat.sub_add_cancel h]
  rw [Int.cast_mul, pow2_cast, hE]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (E - e) := two_pow_pos _
  have h2 : (0 : ℝ) < (2 : ℝ) ^ e := two_pow_pos _
  field_simp

theorem add_sound {x y : ℝ} {I J : DI} (hx : I.mem x) (hy : J.mem y) : (I.add J).mem (x + y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hI : I.e ≤ max I.e J.e := le_max_left _ _
  have hJ : J.e ≤ max I.e J.e := le_max_right _ _
  unfold add mem
  simp only
  have e1 := shift_eq I.lo hI
  have e2 := shift_eq J.lo hJ
  have e3 := shift_eq I.hi hI
  have e4 := shift_eq J.hi hJ
  constructor
  · rw [Int.cast_add, add_div]
    rw [e1, e2]
    exact add_le_add hx1 hy1
  · rw [Int.cast_add, add_div]
    rw [e3, e4]
    exact add_le_add hx2 hy2

/-- Real bilinear corner bound. -/
theorem corners {a b c d u v : ℝ} (hau : a ≤ u) (hub : u ≤ b) (hcv : c ≤ v) (hvd : v ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ u * v ∧
      u * v ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  constructor
  · rcases le_total 0 v with hv0 | hv0
    · have step1 : a * v ≤ u * v := mul_le_mul_of_nonneg_right hau hv0
      have step2 : min (a*c) (a*d) ≤ a * v := by
        rcases le_total 0 a with ha0 | ha0
        · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hcv ha0)
        · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hvd ha0)
      exact le_trans (le_trans (min_le_left _ _) step2) step1
    · have step1 : b * v ≤ u * v := by
        have := mul_le_mul_of_nonpos_right hub hv0; linarith [this]
      have step2 : min (b*c) (b*d) ≤ b * v := by
        rcases le_total 0 b with hb0 | hb0
        · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hcv hb0)
        · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hvd hb0)
      exact le_trans (le_trans (min_le_right _ _) step2) step1
  · rcases le_total 0 v with hv0 | hv0
    · have step1 : u * v ≤ b * v := mul_le_mul_of_nonneg_right hub hv0
      have step2 : b * v ≤ max (b*c) (b*d) := by
        rcases le_total 0 b with hb0 | hb0
        · exact le_trans (mul_le_mul_of_nonneg_left hvd hb0) (le_max_right _ _)
        · exact le_trans (mul_le_mul_of_nonpos_left hcv hb0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_right _ _))
    · have step1 : u * v ≤ a * v := by
        have := mul_le_mul_of_nonpos_right hau hv0; linarith [this]
      have step2 : a * v ≤ max (a*c) (a*d) := by
        rcases le_total 0 a with ha0 | ha0
        · exact le_trans (mul_le_mul_of_nonneg_left hvd ha0) (le_max_right _ _)
        · exact le_trans (mul_le_mul_of_nonpos_left hcv ha0) (le_max_left _ _)
      exact le_trans step1 (le_trans step2 (le_max_left _ _))

theorem mul_sound {x y : ℝ} {I J : DI} (hx : I.mem x) (hy : J.mem y) : (I.mul J).mem (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hpI := two_pow_pos I.e
  have hpJ := two_pow_pos J.e
  -- unscaled coordinates
  set u : ℝ := x * 2 ^ I.e with hu
  set v : ℝ := y * 2 ^ J.e with hv
  have hu1 : (I.lo : ℝ) ≤ u := by rw [hu]; rwa [div_le_iff₀ hpI] at hx1
  have hu2 : u ≤ (I.hi : ℝ) := by rw [hu]; rwa [le_div_iff₀ hpI] at hx2
  have hv1 : (J.lo : ℝ) ≤ v := by rw [hv]; rwa [div_le_iff₀ hpJ] at hy1
  have hv2 : v ≤ (J.hi : ℝ) := by rw [hv]; rwa [le_div_iff₀ hpJ] at hy2
  obtain ⟨hlow, hupp⟩ := corners hu1 hu2 hv1 hv2
  have hxy : x * y = (u * v) / (2 : ℝ) ^ (I.e + J.e) := by
    rw [hu, hv, pow_add]; field_simp
  unfold mul mem
  simp only
  rw [hxy]
  have hp : (0 : ℝ) < (2 : ℝ) ^ (I.e + J.e) := two_pow_pos _
  constructor
  · apply div_le_div_of_nonneg_right _ hp.le
    push_cast
    exact hlow
  · apply div_le_div_of_nonneg_right _ hp.le
    push_cast
    exact hupp

/-- The gap bounds the square from below: `x ∈ I ⇒ (gap I / 2^e)² ≤ x²`. -/
theorem gap_sq_le {x : ℝ} {I : DI} (hx : I.mem x) :
    ((I.gap : ℝ) / 2 ^ I.e) ^ 2 ≤ x ^ 2 := by
  obtain ⟨h1, h2⟩ := hx
  have hp := two_pow_pos I.e
  have hlohiR : (I.lo : ℝ) ≤ I.hi := (div_le_div_iff_of_pos_right hp).mp (le_trans h1 h2)
  have hlohi : I.lo ≤ I.hi := by exact_mod_cast hlohiR
  unfold gap
  rcases le_total 0 I.lo with hlo | hlo
  · -- lo ≥ 0: gap = lo (since -hi ≤ -lo ≤ 0 ≤ lo)
    have hin : max I.lo (-I.hi) = I.lo := max_eq_left (by omega)
    have hg : max (max I.lo (-I.hi)) 0 = I.lo := by
      rw [hin]; exact max_eq_left hlo
    rw [hg]
    have h0 : (0 : ℝ) ≤ (I.lo : ℝ) / 2 ^ I.e := div_nonneg (by exact_mod_cast hlo) hp.le
    exact pow_le_pow_left₀ h0 h1 2
  · rcases le_total I.hi 0 with hhi | hhi
    · -- hi ≤ 0: gap = -hi
      have hin : max I.lo (-I.hi) = -I.hi := max_eq_right (by omega)
      have hg : max (max I.lo (-I.hi)) 0 = -I.hi := by
        rw [hin]; exact max_eq_left (by omega)
      rw [hg]
      have hnn : (0 : ℝ) ≤ ((-I.hi : Int) : ℝ) := by
        have : (0 : Int) ≤ -I.hi := by omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ ((-I.hi : Int) : ℝ) / 2 ^ I.e := div_nonneg hnn hp.le
      have hle : ((-I.hi : Int) : ℝ) / 2 ^ I.e ≤ -x := by
        push_cast; rw [neg_div]; exact neg_le_neg h2
      have := pow_le_pow_left₀ h0 hle 2
      rwa [neg_sq] at this
    · -- straddles: gap = 0
      have hin : max I.lo (-I.hi) ≤ 0 := max_le hlo (by omega)
      have hg : max (max I.lo (-I.hi)) 0 = 0 := max_eq_right hin
      rw [hg]; simp; positivity

/-! ### The fixed formula -/

/-- Interval evaluation of `(A, B)` from intervals for `σ, t, m, C, S`. -/
def evalAB (Iσ It Im IC IS : DI) : DI × DI :=
  let sq := Iσ.mul Iσ
  let tq := It.mul It
  let Pr := ((sq.add tq.neg).add ((ofInt 11).mul Iσ)).add (ofInt 36)
  let Pi := It.mul (((ofInt 2).mul Iσ).add (ofInt 11))
  let X := (IC.mul Pr).add (IS.mul Pi)
  let Y := (IC.mul Pi).add ((IS.mul Pr).neg)
  (((ofInt 24).mul (Iσ.add (ofInt (-1)))).add (Im.mul X),
   ((ofInt 24).mul It).add (Im.mul Y))

/-- The Boolean certificate test `36 < A² + B²` (all in `Int`). -/
def checkAB (A B : DI) : Bool :=
  decide (36 * pow2 (2 * A.e) * pow2 (2 * B.e) <
    A.gap * A.gap * pow2 (2 * B.e) + B.gap * B.gap * pow2 (2 * A.e))

/-- The real `A`. -/
noncomputable def realA (σ t m C S : ℝ) : ℝ :=
  24 * (σ - 1) + m * (C * (σ ^ 2 - t ^ 2 + 11 * σ + 36) + S * (t * (2 * σ + 11)))

/-- The real `B`. -/
noncomputable def realB (σ t m C S : ℝ) : ℝ :=
  24 * t + m * (C * (t * (2 * σ + 11)) - S * (σ ^ 2 - t ^ 2 + 11 * σ + 36))

theorem evalAB_sound {σ t m C S : ℝ} {Iσ It Im IC IS : DI}
    (hσ : Iσ.mem σ) (ht : It.mem t) (hm : Im.mem m) (hC : IC.mem C) (hS : IS.mem S) :
    (evalAB Iσ It Im IC IS).1.mem (realA σ t m C S) ∧
      (evalAB Iσ It Im IC IS).2.mem (realB σ t m C S) := by
  have hsq := mul_sound hσ hσ
  have htq := mul_sound ht ht
  have h11 := mul_sound (ofInt_sound 11) hσ
  have hPr := add_sound (add_sound (add_sound hsq (neg_sound htq)) h11) (ofInt_sound 36)
  have hPi := mul_sound ht (add_sound (mul_sound (ofInt_sound 2) hσ) (ofInt_sound 11))
  have hX := add_sound (mul_sound hC hPr) (mul_sound hS hPi)
  have hY := add_sound (mul_sound hC hPi) (neg_sound (mul_sound hS hPr))
  have hA := add_sound (mul_sound (ofInt_sound 24) (add_sound hσ (ofInt_sound (-1))))
    (mul_sound hm hX)
  have hB := add_sound (mul_sound (ofInt_sound 24) ht) (mul_sound hm hY)
  refine ⟨?_, ?_⟩
  · have e : realA σ t m C S = ((24 : Int) : ℝ) * (σ + ((-1 : Int) : ℝ)) +
        m * (C * (σ * σ + -(t * t) + ((11 : Int) : ℝ) * σ + ((36 : Int) : ℝ)) +
          S * (t * (((2 : Int) : ℝ) * σ + ((11 : Int) : ℝ)))) := by
      unfold realA; push_cast; ring
    rw [e]; exact hA
  · have e : realB σ t m C S = ((24 : Int) : ℝ) * t +
        m * (C * (t * (((2 : Int) : ℝ) * σ + ((11 : Int) : ℝ))) +
          -(S * (σ * σ + -(t * t) + ((11 : Int) : ℝ) * σ + ((36 : Int) : ℝ)))) := by
      unfold realB; push_cast; ring
    rw [e]; exact hB

theorem checkAB_sound {a b : ℝ} {A B : DI} (ha : A.mem a) (hb : B.mem b)
    (h : checkAB A B = true) : 36 < a ^ 2 + b ^ 2 := by
  unfold checkAB at h
  have hint := of_decide_eq_true h
  have hreal : ((36 * pow2 (2 * A.e) * pow2 (2 * B.e) : Int) : ℝ) <
      ((A.gap * A.gap * pow2 (2 * B.e) + B.gap * B.gap * pow2 (2 * A.e) : Int) : ℝ) := by
    exact_mod_cast hint
  push_cast [pow2_cast] at hreal
  have hga := gap_sq_le ha
  have hgb := gap_sq_le hb
  have hpa := two_pow_pos A.e
  have hpb := two_pow_pos B.e
  -- divide the integer inequality by 2^(2 eA) 2^(2 eB)
  have key : 36 < ((A.gap : ℝ) / 2 ^ A.e) ^ 2 + ((B.gap : ℝ) / 2 ^ B.e) ^ 2 := by
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul]
    have hA2 : (0 : ℝ) < (2 : ℝ) ^ (A.e * 2) := two_pow_pos _
    have hB2 : (0 : ℝ) < (2 : ℝ) ^ (B.e * 2) := two_pow_pos _
    rw [mul_comm A.e 2, mul_comm B.e 2]
    rw [div_add_div _ _ (ne_of_gt (by rw [mul_comm]; exact hA2))
      (ne_of_gt (by rw [mul_comm]; exact hB2))]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hreal]
  linarith [hga, hgb, key]

/-- **Box soundness.**  If `checkAB` passes on the interval evaluation, then `36 < A² + B²` at
    every real point of the input intervals. -/
theorem box_sound {σ t m C S : ℝ} {Iσ It Im IC IS : DI}
    (hσ : Iσ.mem σ) (ht : It.mem t) (hm : Im.mem m) (hC : IC.mem C) (hS : IS.mem S)
    (h : checkAB (evalAB Iσ It Im IC IS).1 (evalAB Iσ It Im IC IS).2 = true) :
    36 < realA σ t m C S ^ 2 + realB σ t m C S ^ 2 := by
  obtain ⟨hA, hB⟩ := evalAB_sound hσ ht hm hC hS
  exact checkAB_sound hA hB h

end DI

end M6gap.HeightFloor
