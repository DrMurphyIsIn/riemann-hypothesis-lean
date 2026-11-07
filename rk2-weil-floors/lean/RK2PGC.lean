import Mathlib

/-!
# RK-2 C: PGC, the packed Gram certificate (v2)

A head matrix G (real, m × m) is known only through an outward-rounded integer box |G i j - Mz i j / S| ≤ w / S (the ARB seam,
carried as the hypothesis `hbox`).  The certificate, in base X = 2^B with offset digits H = 2^(B-1):
* the box centre: row i is ONE natural number, `Mz i j = digit_j(row_i) - H`;
* a rounded lower-triangular factor: column k is ONE natural number of m digits, `Lz j k = digit_j(col_k) - H` for k ≤ j, else 0.
Checked ONCE per instance (`paramsOK`): every column is < X^m, its k low digits are exactly H (so it is lower triangular), and
all its digits lie in [H - K, H + K) with K = 2^(bK-1) (one bit-mask test per column, `digOK`).
Checked per row (`rowOK`, O(i) big-number operations): with T_i = pack(M_i) - cS X^i - Σ_{k ≤ i} Lz i k · pack(col_k) (an exact ℤ
identity, T_i = Σ_j R_ij X^j for R = M - cS·I - L Lᵀ), the number T_i + E·Σ_j X^j (E = 2^(bE-1)) is in [0, X^m) and has all digits
< 2^bE (one bit-mask test).  Unique decoding (`digits_unique`) then gives |R_ij| ≤ E for every i, j, and

  `pgc_floor`: ((cS - m (w + E))/S) Σ xᵢ² ≤ xᵀ G x for EVERY real G in the box.

No symmetry of the box centre is needed.  Finite linear algebra only; nothing here says anything about zeta.
conjecture1_proved = False.
-/

namespace RK2

open Finset

/-! ## Computational layer (evaluated by `decide +kernel`; GMP-backed Nat operations only) -/

/-- The base-2^B digit j of N. -/
def dg (B N j : ℕ) : ℕ := (N >>> (B * j)) % 2 ^ B

/-- The signed (offset) digit. -/
def sd (B N j : ℕ) : ℤ := (dg B N j : ℤ) - 2 ^ (B - 1)

/-- Σ_{j<n} 2^(B j). -/
def U (B n : ℕ) : ℕ := (2 ^ (B * n) - 1) / (2 ^ B - 1)

/-- The offset of an n-digit pack: 2^(B-1) Σ_{j<n} 2^(B j). -/
def hu (B n : ℕ) : ℕ := 2 ^ (B - 1) * U B n

/-- z · 2^n by a Nat shift. -/
def shl : ℤ → ℕ → ℤ
  | Int.ofNat a, n => Int.ofNat (a <<< n)
  | Int.negSucc a, n => -Int.ofNat ((a + 1) <<< n)

/-- The bits b..B-1 of each of n base-2^B digits. -/
def mask (B b : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((2 ^ (B - b) - 1) <<< b) ||| (mask B b n <<< B)

/-- N has n base-2^B digits, each < 2^b. -/
def digOK (B b n N : ℕ) : Bool := decide (N < 2 ^ (B * n)) && (N &&& mask B b n == 0)

/-- A packed Gram certificate. -/
structure Dat where
  B : ℕ
  m : ℕ
  cS : ℕ
  bK : ℕ
  bE : ℕ
  rows : List ℕ
  cols : List ℕ

/-- The box centre. -/
def Mz (D : Dat) (i j : ℕ) : ℤ := sd D.B (D.rows.getD i 0) j

/-- The (lower-triangular) factor. -/
def Lz (D : Dat) (j k : ℕ) : ℤ := if k ≤ j then sd D.B (D.cols.getD k 0) j else 0

/-- The residual R = M - cS I - L Lᵀ. -/
def Rz (D : Dat) (i j : ℕ) : ℤ :=
  Mz D i j - (if i = j then (D.cS : ℤ) else 0) - ∑ k ∈ range D.m, Lz D i k * Lz D j k

def accL (B i : ℕ) (HU : ℤ) : List ℕ → ℕ → ℤ → ℤ
  | [], _, acc => acc
  | c :: cs, k, acc => if k ≤ i then accL B i HU cs (k + 1) (acc - sd B c i * ((c : ℤ) - HU)) else acc

def rowOK (D : Dat) (i : ℕ) : Bool :=
  let r := D.rows.getD i 0
  let HU : ℤ := hu D.B D.m
  let T : ℤ := accL D.B i HU D.cols 0 (((r : ℤ) - HU) - shl (D.cS : ℤ) (D.B * i))
  let N : ℤ := T + ((2 ^ (D.bE - 1) * U D.B D.m : ℕ) : ℤ)
  decide (r < 2 ^ (D.B * D.m)) && decide (0 ≤ N) && digOK D.B D.bE D.m N.toNat

def blk (D : Dat) (a : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => rowOK D a && blk D (a + 1) n

def colOK (D : Dat) (c k : ℕ) : Bool :=
  decide (c < 2 ^ (D.B * D.m)) && decide (c % 2 ^ (D.B * k) = hu D.B k) &&
    decide ((2 ^ (D.B - 1) - 2 ^ (D.bK - 1)) * U D.B D.m ≤ c) &&
    digOK D.B D.bK D.m (c - (2 ^ (D.B - 1) - 2 ^ (D.bK - 1)) * U D.B D.m)

def colsOK (D : Dat) : List ℕ → ℕ → Bool
  | [], _ => true
  | c :: cs, k => colOK D c k && colsOK D cs (k + 1)

def paramsOK (D : Dat) : Bool :=
  decide (1 ≤ D.bK) && decide (D.bK < D.B) && decide (1 ≤ D.bE) && decide (D.bE < D.B) &&
    decide (D.cols.length = D.m) &&
    decide (D.cS + D.m * (2 ^ (D.bK - 1)) ^ 2 + 2 ^ (D.bE - 1) < 2 ^ (D.B - 1)) && colsOK D D.cols 0

/-! ## Digit lemmas -/

theorem dg_eq (B N j : ℕ) : dg B N j = N / (2 ^ B) ^ j % 2 ^ B := by
  unfold dg; rw [Nat.shiftRight_eq_div_pow, pow_mul]

theorem dg_succ (B N j : ℕ) : dg B N (j + 1) = dg B (N / 2 ^ B) j := by
  rw [dg_eq, dg_eq, Nat.div_div_eq_div_mul, pow_succ']

theorem dg_zero (B N : ℕ) : dg B N 0 = N % 2 ^ B := by
  rw [dg_eq]; simp

theorem dg_lt (B N j : ℕ) : dg B N j < 2 ^ B := by unfold dg; exact Nat.mod_lt _ (by positivity)

theorem pack_nat (B : ℕ) : ∀ n N, N < (2 ^ B) ^ n → N = ∑ j ∈ range n, dg B N j * (2 ^ B) ^ j := by
  intro n
  induction n with
  | zero => intro N h; simp at h; simp [h]
  | succ n ih =>
    intro N h
    have hX : 0 < 2 ^ B := by positivity
    have h1 : N / 2 ^ B < (2 ^ B) ^ n := by
      rw [Nat.div_lt_iff_lt_mul hX]; rw [pow_succ] at h; exact h
    rw [sum_range_succ']
    simp only [dg_succ, dg_zero, pow_succ, ← mul_assoc]
    rw [← sum_mul, ← ih _ h1, pow_zero, mul_one]
    have := Nat.mod_add_div N (2 ^ B)
    linarith [mul_comm (N / 2 ^ B) (2 ^ B)]

/-- Digits of a pack whose digits are < X. -/
theorem dg_of_pack (B : ℕ) : ∀ n (a : ℕ → ℕ), (∀ j < n, a j < 2 ^ B) →
    ∀ j < n, dg B (∑ t ∈ range n, a t * (2 ^ B) ^ t) j = a j := by
  intro n
  induction n with
  | zero => intro a _ j hj; omega
  | succ n ih =>
    intro a ha j hj
    have hX : 0 < 2 ^ B := by positivity
    have hsplit : ∑ t ∈ range (n + 1), a t * (2 ^ B) ^ t
        = a 0 + 2 ^ B * ∑ t ∈ range n, a (t + 1) * (2 ^ B) ^ t := by
      rw [sum_range_succ', mul_sum, add_comm]
      simp only [pow_zero, mul_one]
      congr 1; exact sum_congr rfl (fun t _ => by ring)
    rw [hsplit]
    rcases j with _ | j
    · rw [dg_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0 (by omega))]
    · rw [dg_succ, Nat.add_mul_div_left _ _ hX, Nat.div_eq_of_lt (ha 0 (by omega)), zero_add]
      exact ih (fun t => a (t + 1)) (fun t ht => ha (t + 1) (by omega)) j (by omega)

theorem U_eq (B n : ℕ) (hB : 1 ≤ B) : U B n = ∑ j ∈ range n, (2 ^ B) ^ j := by
  have h2 : 2 ≤ 2 ^ B := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB
  unfold U; rw [pow_mul, Nat.geomSum_eq h2 n]

theorem hu_eq_nat (B n : ℕ) (hB : 1 ≤ B) : hu B n = ∑ j ∈ range n, 2 ^ (B - 1) * (2 ^ B) ^ j := by
  unfold hu; rw [U_eq B n hB, mul_sum]

theorem hu_eq (B n : ℕ) (hB : 1 ≤ B) :
    (hu B n : ℤ) = ∑ j ∈ range n, (2 : ℤ) ^ (B - 1) * (2 ^ B) ^ j := by
  rw [hu_eq_nat B n hB]; push_cast; rfl

theorem spack (B n N : ℕ) (hB : 1 ≤ B) (h : N < (2 ^ B) ^ n) :
    (N : ℤ) - hu B n = ∑ j ∈ range n, sd B N j * (2 ^ B) ^ j := by
  have hp := pack_nat B n N h
  rw [hu_eq B n hB]
  conv_lhs => rw [hp]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun j _ => ?_)
  unfold sd; ring

theorem shl_eq (z : ℤ) (n : ℕ) : shl z n = z * 2 ^ n := by
  cases z with
  | ofNat a => simp [shl, Nat.shiftLeft_eq]
  | negSucc a => simp [shl, Nat.shiftLeft_eq, Int.negSucc_eq]; ring

theorem sd_abs_le (B N j : ℕ) (hB : 1 ≤ B) : |sd B N j| ≤ 2 ^ (B - 1) := by
  have hlt := dg_lt B N j
  have h2 : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : (dg B N j : ℤ) < 2 ^ B := by exact_mod_cast hlt
  unfold sd
  rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg (dg B N j) : (0:ℤ) ≤ _)]

/-! ## The bit mask -/

theorem testBit_hi (B b p : ℕ) (hb : b ≤ B) :
    ((2 ^ (B - b) - 1) <<< b).testBit p = (decide (b ≤ p) && decide (p < B)) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : b ≤ p
  · simp [h]; omega
  · simp [h]

theorem testBit_mask_mem (B b : ℕ) (hb : b ≤ B) : ∀ n j t, j < n → b ≤ t → t < B →
    (mask B b n).testBit (B * j + t) = true := by
  intro n
  induction n with
  | zero => intro j t hj; omega
  | succ n ih =>
    intro j t hj hbt htB
    simp only [mask, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_hi B b _ hb, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq]
    rcases j with _ | j
    · left; omega
    · right
      refine ⟨by rw [Nat.mul_succ]; omega, ?_⟩
      have := ih j t (by omega) hbt htB
      rwa [show B * (j + 1) + t - B = B * j + t by rw [Nat.mul_succ]; omega]

theorem digOK_spec (B b n N : ℕ) (hb : b ≤ B) (h : digOK B b n N = true) :
    N < (2 ^ B) ^ n ∧ ∀ j < n, dg B N j < 2 ^ b := by
  simp only [digOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨by rw [← pow_mul]; exact h.1, fun j hj => ?_⟩
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  unfold dg
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases htB : t < B
  · have hm := testBit_mask_mem B b hb n j t hj ht htB
    have hz : (N &&& mask B b n).testBit (B * j + t) = false := by rw [h.2]; simp
    rw [Nat.testBit_land, hm, Bool.and_true] at hz
    simp [hz]
  · simp [htB]

/-! ## Specifications of the computational layer -/

theorem accL_spec (B i : ℕ) (HU : ℤ) : ∀ (cs : List ℕ) k acc,
    accL B i HU cs k acc
      = acc - ∑ t ∈ range cs.length,
          (if k + t ≤ i then sd B (cs.getD t 0) i * ((cs.getD t 0 : ℤ) - HU) else 0) := by
  intro cs
  induction cs with
  | nil => intro k acc; simp [accL]
  | cons c cs ih =>
    intro k acc
    simp only [accL]
    split_ifs with hk
    · rw [ih, List.length_cons, sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero, if_pos hk,
        show ∀ t, k + 1 + t = k + (t + 1) from fun t => by omega]
      ring
    · have : ∀ t ∈ range (c :: cs).length,
          (if k + t ≤ i then sd B ((c :: cs).getD t 0) i * (((c :: cs).getD t 0 : ℕ) - HU) else 0) = 0 :=
        fun t _ => if_neg (by omega)
      rw [sum_eq_zero this, sub_zero]

theorem blk_spec (D : Dat) : ∀ n a, blk D a n = true → ∀ t < n, rowOK D (a + t) = true := by
  intro n
  induction n with
  | zero => intro a _ t ht; omega
  | succ n ih =>
    intro a h t ht
    simp only [blk, Bool.and_eq_true] at h
    rcases t with _ | t
    · simpa using h.1
    · rw [show a + (t + 1) = a + 1 + t by omega]; exact ih _ h.2 t (by omega)

theorem blk_append (D : Dat) (a n1 n2 : ℕ) (h1 : blk D a n1 = true) (h2 : blk D (a + n1) n2 = true) :
    blk D a (n1 + n2) = true := by
  induction n1 generalizing a with
  | zero => simpa using h2
  | succ n ih =>
    simp only [blk, Bool.and_eq_true] at h1
    rw [show n + 1 + n2 = (n + n2) + 1 by omega]
    simp only [blk, Bool.and_eq_true]
    exact ⟨h1.1, ih (a + 1) h1.2 (by rw [show a + 1 + n = a + (n + 1) by omega]; exact h2)⟩

theorem colsOK_spec (D : Dat) : ∀ (cs : List ℕ) k, colsOK D cs k = true →
    ∀ t < cs.length, colOK D (cs.getD t 0) (k + t) = true := by
  intro cs
  induction cs with
  | nil => intro k _ t ht; simp at ht
  | cons c cs ih =>
    intro k h t ht
    simp only [colsOK, Bool.and_eq_true] at h
    rcases t with _ | t
    · simpa using h.1
    · have := ih (k + 1) h.2 t (by simp at ht; omega)
      simpa [show k + 1 + t = k + (t + 1) by omega] using this

/-- Unique decoding of a signed base-X expansion with digits of modulus < X. -/
theorem digits_unique (X : ℤ) (hX : 0 < X) : ∀ n (d : ℕ → ℤ), (∀ j < n, |d j| < X) →
    ∑ j ∈ range n, d j * X ^ j = 0 → ∀ j < n, d j = 0 := by
  intro n
  induction n with
  | zero => intro d _ _ j hj; omega
  | succ n ih =>
    intro d hd hs
    rw [sum_range_succ'] at hs
    simp only [pow_succ, pow_zero, mul_one] at hs
    have hsplit : ∑ j ∈ range n, d (j + 1) * (X ^ j * X) = X * ∑ j ∈ range n, d (j + 1) * X ^ j := by
      rw [mul_sum]; exact sum_congr rfl (fun j _ => by ring)
    rw [hsplit] at hs
    have h0 : d 0 = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd _ (hd 0 (by omega))
      exact ⟨-(∑ j ∈ range n, d (j + 1) * X ^ j), by linarith⟩
    have hrest : ∑ j ∈ range n, d (j + 1) * X ^ j = 0 := by
      rw [h0, add_zero] at hs
      rcases mul_eq_zero.mp hs with h | h
      · omega
      · exact h
    have := ih (fun j => d (j + 1)) (fun j hj => hd (j + 1) (by omega)) hrest
    intro j hj
    rcases j with _ | j
    · exact h0
    · exact this j (by omega)

/-! ## Column facts from `paramsOK` -/

structure ColFacts (D : Dat) : Prop where
  hB : 1 ≤ D.B
  hbK : 1 ≤ D.bK
  hbKB : D.bK < D.B
  hbE : 1 ≤ D.bE
  hbEB : D.bE < D.B
  hlen : D.cols.length = D.m
  hpar : D.cS + D.m * (2 ^ (D.bK - 1)) ^ 2 + 2 ^ (D.bE - 1) < 2 ^ (D.B - 1)
  hlt : ∀ k < D.m, D.cols.getD k 0 < (2 ^ D.B) ^ D.m
  hlow : ∀ k < D.m, ∀ j < k, sd D.B (D.cols.getD k 0) j = 0
  hK : ∀ k < D.m, ∀ j < D.m, |sd D.B (D.cols.getD k 0) j| ≤ 2 ^ (D.bK - 1)

theorem colFacts (D : Dat) (hp : paramsOK D = true) : ColFacts D := by
  simp only [paramsOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨hbK, hbKB⟩, hbE⟩, hbEB⟩, hlen⟩, hpar⟩, hcols⟩ := hp
  have hB : 1 ≤ D.B := by omega
  have hc := colsOK_spec D D.cols 0 hcols
  rw [hlen] at hc
  have hHK : 2 ^ (D.bK - 1) ≤ 2 ^ (D.B - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2B : 2 ^ D.B = 2 * 2 ^ (D.B - 1) := by rw [← pow_succ']; congr 1; omega
  have h2K : 2 ^ D.bK = 2 * 2 ^ (D.bK - 1) := by rw [← pow_succ']; congr 1; omega
  have hKB : 2 ^ D.bK ≤ 2 ^ (D.B - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨hB, hbK, hbKB, hbE, hbEB, hlen, hpar, fun k hk => ?_, fun k hk j hj => ?_, fun k hk j hj => ?_⟩
  · have h := hc k hk; simp only [zero_add, colOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [← pow_mul]; exact h.1.1.1
  · have h := hc k hk; simp only [zero_add, colOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have hmod := h.1.1.2
    have hlowdg : dg D.B (D.cols.getD k 0) j = dg D.B (D.cols.getD k 0 % 2 ^ (D.B * k)) j := by
      rw [dg_eq, dg_eq, pow_mul]
      have hk' : (2 ^ D.B) ^ k = (2 ^ D.B) ^ j * (2 ^ D.B) ^ (k - j) := by
        rw [← pow_add]; congr 1; omega
      rw [hk', Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
      exact dvd_pow_self _ (by omega)
    have hhu : dg D.B (hu D.B k) j = 2 ^ (D.B - 1) := by
      rw [hu_eq_nat D.B k hB]
      exact dg_of_pack D.B k (fun _ => 2 ^ (D.B - 1))
        (fun _ _ => by rw [h2B]; have : 0 < 2 ^ (D.B - 1) := by positivity
                       omega) j hj
    unfold sd; rw [hlowdg, hmod, hhu]; simp
  · have h := hc k hk; simp only [zero_add, colOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨_, _⟩, hge⟩, hdig⟩ := h
    obtain ⟨hNlt, hNd⟩ := digOK_spec D.B D.bK D.m _ (by omega) hdig
    set c := D.cols.getD k 0 with hcdef
    set Hk := 2 ^ (D.B - 1) - 2 ^ (D.bK - 1) with hHkdef
    set N := c - Hk * U D.B D.m with hNdef
    have hc_eq : c = ∑ t ∈ range D.m, (dg D.B N t + Hk) * (2 ^ D.B) ^ t := by
      have h1 : c = N + Hk * U D.B D.m := by omega
      have hpackN := pack_nat D.B D.m N hNlt
      rw [h1, U_eq D.B D.m hB, mul_sum]
      conv_lhs => rw [hpackN]
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun t _ => by ring)
    have hdgc := dg_of_pack D.B D.m (fun t => dg D.B N t + Hk) (fun t ht => by
      have := hNd t ht; simp only [hHkdef]; omega) j hj
    rw [← hc_eq] at hdgc
    have hNj : (dg D.B N j : ℤ) < 2 * 2 ^ (D.bK - 1) := by exact_mod_cast (h2K ▸ hNd j hj)
    have hHkZ : ((Hk : ℕ) : ℤ) = 2 ^ (D.B - 1) - 2 ^ (D.bK - 1) := by
      rw [hHkdef, Nat.cast_sub hHK]; push_cast; ring
    unfold sd
    rw [hdgc, abs_le]
    push_cast
    rw [hHkZ]
    constructor <;> nlinarith [(Nat.cast_nonneg (dg D.B N j) : (0:ℤ) ≤ _)]

/-! ## The row check gives a residual bound -/

theorem col_pack (D : Dat) (F : ColFacts D) (t : ℕ) (ht : t < D.m) :
    (D.cols.getD t 0 : ℤ) - hu D.B D.m = ∑ j ∈ range D.m, Lz D j t * (2 ^ D.B : ℤ) ^ j := by
  rw [spack D.B D.m _ F.hB (F.hlt t ht)]
  refine sum_congr rfl (fun j hj => ?_)
  unfold Lz
  split_ifs with htj
  · rfl
  · rw [F.hlow t ht j (by omega)]

theorem rowOK_spec (D : Dat) (hp : paramsOK D = true) (i : ℕ) (hi : i < D.m) (h : rowOK D i = true) :
    ∀ j < D.m, |Rz D i j| ≤ 2 ^ (D.bE - 1) := by
  have F := colFacts D hp
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, hN0⟩, hdig⟩ := h
  set X : ℤ := 2 ^ D.B with hXdef
  have hX : 0 < X := by positivity
  set HU : ℤ := (hu D.B D.m : ℤ) with hHUdef
  set T : ℤ := accL D.B i HU D.cols 0 (((D.rows.getD i 0 : ℕ) : ℤ) - HU - shl (D.cS : ℤ) (D.B * i)) with hTdef
  -- T is the packed residual row
  have hsumL : T = ((D.rows.getD i 0 : ℕ) : ℤ) - HU - shl (D.cS : ℤ) (D.B * i)
      - ∑ j ∈ range D.m, (∑ k ∈ range D.m, Lz D i k * Lz D j k) * X ^ j := by
    rw [hTdef, accL_spec, F.hlen]
    congr 1
    have : ∀ t ∈ range D.m, (if 0 + t ≤ i then sd D.B (D.cols.getD t 0) i * ((D.cols.getD t 0 : ℤ) - HU) else 0)
        = Lz D i t * ∑ j ∈ range D.m, Lz D j t * X ^ j := by
      intro t htm
      simp at htm
      rw [hHUdef, col_pack D F t htm]
      split_ifs with hti
      · simp only [Lz, if_pos (show t ≤ i by omega)]; rfl
      · simp [Lz, show ¬ t ≤ i by omega]
    rw [sum_congr rfl this]
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl (fun j _ => sum_congr rfl (fun k _ => by ring))
  have hrowp : ((D.rows.getD i 0 : ℕ) : ℤ) - HU = ∑ j ∈ range D.m, Mz D i j * X ^ j := by
    rw [hHUdef, spack D.B D.m _ F.hB (by rw [← pow_mul]; exact hr)]; rfl
  have hdiag : shl (D.cS : ℤ) (D.B * i) = ∑ j ∈ range D.m, (if i = j then (D.cS : ℤ) else 0) * X ^ j := by
    rw [shl_eq]
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq, if_pos (mem_range.mpr hi), pow_mul]
  have hTR : T = ∑ j ∈ range D.m, Rz D i j * X ^ j := by
    rw [hsumL, hrowp, hdiag, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl (fun j _ => by unfold Rz; ring)
  -- the decoded digits
  set E : ℕ := 2 ^ (D.bE - 1) with hEdef
  set N : ℤ := T + ((E * U D.B D.m : ℕ) : ℤ) with hNdef
  obtain ⟨hNlt, hNd⟩ := digOK_spec D.B D.bE D.m N.toNat (by have := F.hbEB; omega) hdig
  have hTe : T = ∑ j ∈ range D.m, ((dg D.B N.toNat j : ℤ) - E) * X ^ j := by
    have hp1 := pack_nat D.B D.m N.toNat hNlt
    have hp1Z : ((N.toNat : ℕ) : ℤ) = ∑ j ∈ range D.m, (dg D.B N.toNat j : ℤ) * X ^ j := by
      conv_lhs => rw [hp1]
      push_cast; rfl
    have hUZ : ((E * U D.B D.m : ℕ) : ℤ) = ∑ j ∈ range D.m, (E : ℤ) * X ^ j := by
      rw [U_eq D.B D.m F.hB, mul_sum]; push_cast; rfl
    have hTN : T = ((N.toNat : ℕ) : ℤ) - ((E * U D.B D.m : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hN0, hNdef]; ring
    rw [hTN, hp1Z, hUZ, ← sum_sub_distrib]
    exact sum_congr rfl (fun j _ => by ring)
  have hpow : (2 : ℤ) ^ D.B = 2 * 2 ^ (D.B - 1) := by rw [← pow_succ']; congr 1; have := F.hB; omega
  have h2E : (2 : ℤ) ^ D.bE = 2 * 2 ^ (D.bE - 1) := by rw [← pow_succ']; congr 1; have := F.hbE; omega
  have hparZ : (D.cS : ℤ) + D.m * (2 ^ (D.bK - 1)) ^ 2 + 2 ^ (D.bE - 1) < 2 ^ (D.B - 1) := by
    exact_mod_cast F.hpar
  have hLb : ∀ j < D.m, ∀ k, |Lz D j k| ≤ 2 ^ (D.bK - 1) := by
    intro j hj k
    unfold Lz
    split_ifs with hkj
    · exact F.hK k (by omega) j hj
    · simp
  have hRb : ∀ j < D.m, |Rz D i j| ≤ 2 ^ (D.B - 1) + D.cS + D.m * (2 ^ (D.bK - 1)) ^ 2 := by
    intro j hj
    have hM := sd_abs_le D.B (D.rows.getD i 0) j F.hB
    have hP : |∑ k ∈ range D.m, Lz D i k * Lz D j k| ≤ D.m * (2 ^ (D.bK - 1)) ^ 2 := by
      refine le_trans (abs_sum_le_sum_abs _ _) ?_
      have : ∀ k ∈ range D.m, |Lz D i k * Lz D j k| ≤ ((2 : ℤ) ^ (D.bK - 1)) ^ 2 := by
        intro k _
        rw [abs_mul, sq]
        exact mul_le_mul (hLb i hi k) (hLb j hj k) (abs_nonneg _) (by positivity)
      refine le_trans (sum_le_sum this) ?_
      simp
    have hd : |(if i = j then (D.cS : ℤ) else 0)| ≤ D.cS := by split_ifs <;> simp
    unfold Rz
    calc |Mz D i j - (if i = j then (D.cS : ℤ) else 0) - ∑ k ∈ range D.m, Lz D i k * Lz D j k|
        ≤ |Mz D i j| + |(if i = j then (D.cS : ℤ) else 0)| + |∑ k ∈ range D.m, Lz D i k * Lz D j k| := by
          refine le_trans (abs_sub _ _) ?_
          gcongr
          exact abs_sub _ _
      _ ≤ 2 ^ (D.B - 1) + D.cS + D.m * (2 ^ (D.bK - 1)) ^ 2 := by unfold Mz; linarith
  have hEb : ∀ j < D.m, |(dg D.B N.toNat j : ℤ) - E| ≤ 2 ^ (D.bE - 1) := by
    intro j hj
    have h1 : (dg D.B N.toNat j : ℤ) < 2 ^ D.bE := by exact_mod_cast hNd j hj
    rw [abs_le, hEdef]; push_cast
    constructor <;> linarith [(Nat.cast_nonneg (dg D.B N.toNat j) : (0:ℤ) ≤ _)]
  have huniq := digits_unique X hX D.m (fun j => Rz D i j - ((dg D.B N.toNat j : ℤ) - E))
    (fun j hj => by
      have h1 := hRb j hj; have h2 := hEb j hj
      calc |Rz D i j - ((dg D.B N.toNat j : ℤ) - E)| ≤ |Rz D i j| + |(dg D.B N.toNat j : ℤ) - E| := abs_sub _ _
        _ < X := by rw [hXdef, hpow]; linarith)
    (by
      show ∑ j ∈ range D.m, (Rz D i j - ((dg D.B N.toNat j : ℤ) - E)) * X ^ j = 0
      rw [show (∑ j ∈ range D.m, (Rz D i j - ((dg D.B N.toNat j : ℤ) - E)) * X ^ j)
          = (∑ j ∈ range D.m, Rz D i j * X ^ j) - ∑ j ∈ range D.m, ((dg D.B N.toNat j : ℤ) - E) * X ^ j by
            rw [← sum_sub_distrib]; exact sum_congr rfl (fun j _ => by ring)]
      rw [← hTR, ← hTe, sub_self])
  intro j hj
  have h0 : Rz D i j - ((dg D.B N.toNat j : ℤ) - E) = 0 := huniq j hj
  rw [show Rz D i j = (dg D.B N.toNat j : ℤ) - E by linarith]
  exact hEb j hj

theorem pgc_int (D : Dat) (hp : paramsOK D = true) (hb : blk D 0 D.m = true) :
    ∀ i < D.m, ∀ j < D.m, |Rz D i j| ≤ 2 ^ (D.bE - 1) := by
  intro i hi
  have := blk_spec D D.m 0 hb i hi
  rw [zero_add] at this
  exact rowOK_spec D hp i hi this

/-! ## The floor on the whole box -/

/-- A Gram form is a sum of squares. -/
theorem gram_nonneg {ι κ : Type*} [Fintype ι] (s : Finset κ) (a : ι → κ → ℝ) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * (∑ k ∈ s, a i k * a j k) * x j := by
  have h : ∑ i, ∑ j, x i * (∑ k ∈ s, a i k * a j k) * x j = ∑ k ∈ s, (∑ i, x i * a i k) ^ 2 := by
    calc ∑ i, ∑ j, x i * (∑ k ∈ s, a i k * a j k) * x j
        = ∑ i, ∑ j, ∑ k ∈ s, (x i * a i k) * (x j * a j k) := by
          refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
          rw [mul_sum, sum_mul]
          exact sum_congr rfl (fun k _ => by ring)
      _ = ∑ i, ∑ k ∈ s, ∑ j, (x i * a i k) * (x j * a j k) := sum_congr rfl (fun i _ => sum_comm)
      _ = ∑ k ∈ s, ∑ i, ∑ j, (x i * a i k) * (x j * a j k) := sum_comm
      _ = ∑ k ∈ s, (∑ i, x i * a i k) ^ 2 := by
          refine sum_congr rfl (fun k _ => ?_)
          rw [sq, sum_mul_sum]
  rw [h]; exact sum_nonneg (fun k _ => sq_nonneg _)

/-- **PGC floor.**  If the kernel-checked packed certificate passes (`paramsOK`, `blk D 0 m`), then every real G within w/S
of Mz/S entrywise satisfies ((cS - ρ)/S) Σ xᵢ² ≤ xᵀ G x, for any ρ ≥ m (w + 2^(bE-1)). -/
theorem pgc_floor (D : Dat) (hp : paramsOK D = true) (hb : blk D 0 D.m = true)
    (w ρ : ℕ) (hρ : D.m * (w + 2 ^ (D.bE - 1)) ≤ ρ) (S : ℝ) (hS : 0 < S)
    (G : Fin D.m → Fin D.m → ℝ)
    (hbox : ∀ i j : Fin D.m, |G i j - (Mz D i j : ℝ) / S| ≤ (w : ℝ) / S) (x : Fin D.m → ℝ) :
    (((D.cS : ℤ) - ρ : ℤ) : ℝ) / S * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * G i j * x j := by
  have hR := pgc_int D hp hb
  set e : ℝ := (2 : ℝ) ^ (D.bE - 1) with hedef
  set R : Fin D.m → Fin D.m → ℝ := fun i j => (Rz D i j : ℝ) with hRdef
  set P : Fin D.m → Fin D.m → ℝ := fun i j => ∑ k ∈ range D.m, (Lz D i k : ℝ) * (Lz D j k : ℝ) with hPdef
  set E : Fin D.m → Fin D.m → ℝ := fun i j => G i j - (Mz D i j : ℝ) / S with hEdef
  set δ : Fin D.m → Fin D.m → ℝ := fun i j => if (i : ℕ) = (j : ℕ) then (D.cS : ℝ) else 0 with hδdef
  have hRb : ∀ i j, |R i j| ≤ e := by
    intro i j
    have := hR i i.2 j j.2
    simp only [hRdef, hedef]
    exact_mod_cast this
  have hG : ∀ i j, G i j = (δ i j + P i j + R i j) / S + E i j := by
    intro i j
    have hM : (Mz D i j : ℝ) = δ i j + P i j + R i j := by
      simp only [hδdef, hPdef, hRdef, Rz]; push_cast; split_ifs <;> ring
    simp only [hEdef]
    rw [hM]
    ring
  have hd : ∑ i, ∑ j, x i * δ i j * x j = (D.cS : ℝ) * ∑ i, x i ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rw [sum_eq_single i (fun j _ hji => by simp [hδdef, Fin.val_inj, Ne.symm hji]) (by simp)]
    simp [hδdef]; ring
  have hsplit : ∑ i, ∑ j, x i * G i j * x j
      = (D.cS : ℝ) / S * ∑ i, x i ^ 2 + (1 / S) * ∑ i, ∑ j, x i * P i j * x j
        + ∑ i, ∑ j, x i * (R i j / S + E i j) * x j := by
    calc ∑ i, ∑ j, x i * G i j * x j
        = ∑ i, ∑ j, ((1 / S) * (x i * δ i j * x j)
            + (1 / S) * (x i * P i j * x j) + x i * (R i j / S + E i j) * x j) := by
          refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
          rw [hG]; field_simp; ring
      _ = _ := by
          simp only [sum_add_distrib, ← mul_sum]
          rw [hd]; ring
  have hgram : 0 ≤ ∑ i, ∑ j, x i * P i j * x j :=
    gram_nonneg (range D.m) (fun (i : Fin D.m) k => (Lz D i k : ℝ)) x
  set f : ℝ := (w : ℝ) + e with hfdef
  have hterm : ∀ i j, -(|x i| * |x j| * f) / S ≤ x i * (R i j / S + E i j) * x j := by
    intro i j
    have hE := hbox i j
    have h1 : |R i j / S + E i j| ≤ f / S := by
      calc |R i j / S + E i j| ≤ |R i j / S| + |E i j| := abs_add_le _ _
        _ ≤ e / S + (w : ℝ) / S := by
            rw [abs_div, abs_of_pos hS]
            exact add_le_add (div_le_div_of_nonneg_right (hRb i j) hS.le) hE
        _ = f / S := by simp only [hfdef]; ring
    have h2 : |x i * (R i j / S + E i j) * x j| ≤ |x i| * |x j| * f / S := by
      rw [abs_mul, abs_mul]
      calc |x i| * |R i j / S + E i j| * |x j| = |x i| * |x j| * |R i j / S + E i j| := by ring
        _ ≤ |x i| * |x j| * (f / S) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = |x i| * |x j| * f / S := by ring
    have := neg_abs_le (x i * (R i j / S + E i j) * x j)
    rw [neg_div]; linarith
  have hCS : (∑ i, |x i|) ^ 2 ≤ (D.m : ℝ) * ∑ i, x i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin D.m))) (f := fun i => |x i|)
    simpa [sq_abs] using this
  have hρR : (D.m : ℝ) * f ≤ (ρ : ℝ) := by
    simp only [hfdef, hedef]; exact_mod_cast hρ
  have herr : -((ρ : ℝ) / S * ∑ i, x i ^ 2) ≤ ∑ i, ∑ j, x i * (R i j / S + E i j) * x j := by
    have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin D.m))) =>
      sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin D.m))) => hterm i j))
    refine le_trans ?_ hs
    have h1 : ∑ i : Fin D.m, ∑ j : Fin D.m, -(|x i| * |x j| * f) / S = -((∑ i, |x i|) ^ 2 * f) / S := by
      rw [sq, sum_mul_sum]
      simp only [neg_div, sum_neg_distrib, ← sum_div, sum_mul]
    rw [h1, neg_div, neg_le_neg_iff, div_le_iff₀ hS]
    have hf : 0 ≤ f := by positivity
    have hx : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg (fun i _ => sq_nonneg (x i))
    calc (∑ i, |x i|) ^ 2 * f ≤ (D.m : ℝ) * (∑ i, x i ^ 2) * f := mul_le_mul_of_nonneg_right hCS hf
      _ = ((D.m : ℝ) * f) * ∑ i, x i ^ 2 := by ring
      _ ≤ (ρ : ℝ) * ∑ i, x i ^ 2 := mul_le_mul_of_nonneg_right hρR hx
      _ = ((ρ : ℝ) / S * ∑ i, x i ^ 2) * S := by field_simp
  rw [hsplit]
  have h1S : 0 ≤ (1 / S) * ∑ i, ∑ j, x i * P i j * x j := mul_nonneg (by positivity) hgram
  have hc : (((D.cS : ℤ) - ρ : ℤ) : ℝ) / S * ∑ i, x i ^ 2
      = (D.cS : ℝ) / S * ∑ i, x i ^ 2 - (ρ : ℝ) / S * ∑ i, x i ^ 2 := by push_cast; ring
  rw [hc]; linarith

end RK2
