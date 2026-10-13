/-  HeightFloorTrig.lean -- brick H3 (AND_height_floor_kernel), part 2: the transcendental inputs.

    M6GAP CROSS-PIN PORT (lane m6gap, 2026-09-23): a copy of
    telperion/examples/zeta_reflection/lean/HeightFloorTrig.lean (Lean v4.32.0, Mathlib v4.32.0) onto the dbn
    island (Lean v4.34.0-rc1, Mathlib de5ce8a9).  The ONLY edits are: module names prefixed `M6gap`
    in the imports, every namespace prefixed `M6gap.` (so no declaration can clash with a sibling
    lane's port), and comment wording on this island's word-level placeholder scan.  No proof was
    changed.  Consumed by M6gapHeightFloor (the 55/16 height floor on this island).


    Three once-proved lemma families, all hypothesis-free:

      * `exp_I_partial` / `cos_sin_taylor`: the order-`2n` Taylor bracket of `cos x` and `sin x`
        for ANY real `x` with `|x| / (2n+1) ≤ 1/2`, obtained from Mathlib's `Complex.exp_bound'`
        at `x * I` by splitting the partial sum into its real (even) and imaginary (odd) halves:
            |cos x - Σ_{k<n} (-1)^k x^(2k)/(2k)!|   ≤ |x|^(2n)/(2n)! * 2,
            |sin x - Σ_{k<n} (-1)^k x^(2k+1)/(2k+1)!| ≤ |x|^(2n)/(2n)! * 2.
      * `trig_encl`: the same with the argument known only to within `ε` (Lipschitz absorption,
        `Real.abs_cos_sub_cos_le` / `Real.abs_sin_sub_sin_le`) -- this is how `t * log 2` enters
        through Mathlib's 9-digit `log 2` bracket.
      * `le_two_rpow_neg` / `two_rpow_neg_le`: two-sided bounds on `2^(-p/q)` from integer power
        checks, and the monotonicity bracket `two_rpow_neg_mono`.

      * `mem_cos`, `mem_sin_low`, `mem_sin_high`, `mem_sin_mid`, `mem_m`: the monotonicity
        brackets that turn two table values at the ends of a height slab `[a, b]` (resp. a σ slab)
        into a `DI` enclosure valid on the WHOLE slab (`cos` antitone on `[0, π]`; `sin` monotone on
        `[0, π/2]` and on `[π/2, π]`; `2^(-σ)` antitone).

    The per-height instances (cos/sin at `t_j log 2`, `t_j = 55 j / 256`) and the per-σ
    instances (`2^(-1/2)`, `2^(-3/4)`) live in the generated `HeightFloorBoxes`.

    conjecture1_proved = False.  Elementary real analysis; nothing here is about RH.
-/
import Mathlib
import M6gapHeightFloorCheck

open Complex Finset

namespace M6gap.HeightFloor

/-- Taylor partial sum of `cos` with `n` (even-degree) terms. -/
noncomputable def cosT (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- Taylor partial sum of `sin` with `n` (odd-degree) terms. -/
noncomputable def sinT (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

/-- The partial exponential sum at `x * I` splits into the cos and sin partial sums. -/
theorem exp_I_partial (x : ℝ) (n : ℕ) :
    ∑ m ∈ range (2 * n), ((x : ℂ) * I) ^ m / (m.factorial : ℂ)
      = (cosT x n : ℂ) + (sinT x n : ℂ) * I := by
  induction n with
  | zero => simp [cosT, sinT]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    simp only [cosT, sinT, sum_range_succ]
    have h1 : ((x : ℂ) * I) ^ (2 * n) = (-1 : ℂ) ^ n * (x : ℂ) ^ (2 * n) := by
      rw [mul_pow, pow_mul I, I_sq]; ring
    have h2 : ((x : ℂ) * I) ^ (2 * n + 1) = (-1 : ℂ) ^ n * (x : ℂ) ^ (2 * n + 1) * I := by
      rw [pow_succ, h1]; ring
    rw [h1, h2]
    push_cast
    ring

/-- **Taylor bracket of `cos` and `sin`, any real argument** (from `Complex.exp_bound'`). -/
theorem cos_sin_taylor (x : ℝ) (n : ℕ) (hx : |x| / ((2 * n).succ : ℝ) ≤ 1 / 2) :
    |Real.cos x - cosT x n| ≤ |x| ^ (2 * n) / ((2 * n).factorial : ℝ) * 2 ∧
      |Real.sin x - sinT x n| ≤ |x| ^ (2 * n) / ((2 * n).factorial : ℝ) * 2 := by
  have hnorm : ‖(x : ℂ) * I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.exp_bound' (x := (x : ℂ) * I) (n := 2 * n) (by rw [hnorm]; exact hx)
  rw [hnorm, exp_I_partial, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hb
  have hdiff : (Real.cos x : ℂ) + (Real.sin x : ℂ) * I - ((cosT x n : ℂ) + (sinT x n : ℂ) * I)
      = ((Real.cos x - cosT x n : ℝ) : ℂ) + ((Real.sin x - sinT x n : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hdiff] at hb
  set a : ℝ := Real.cos x - cosT x n with ha
  set b : ℝ := Real.sin x - sinT x n with hb'
  have hre : ((a : ℂ) + (b : ℂ) * I).re = a := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have him : ((a : ℂ) + (b : ℂ) * I).im = b := by
    rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hb
    have := Complex.abs_re_le_norm ((a : ℂ) + (b : ℂ) * I)
    rwa [hre] at this
  · refine le_trans ?_ hb
    have := Complex.abs_im_le_norm ((a : ℂ) + (b : ℂ) * I)
    rwa [him] at this

/-- **Enclosure of `cos θ`, `sin θ` from a nearby Taylor point** `q` (`|θ - q| ≤ ε`). -/
theorem trig_encl (θ q ε : ℝ) (n : ℕ) (hθ : |θ - q| ≤ ε)
    (hq : |q| / ((2 * n).succ : ℝ) ≤ 1 / 2) :
    cosT q n - |q| ^ (2 * n) / ((2 * n).factorial : ℝ) * 2 - ε ≤ Real.cos θ ∧
      Real.cos θ ≤ cosT q n + |q| ^ (2 * n) / ((2 * n).factorial : ℝ) * 2 + ε ∧
      sinT q n - |q| ^ (2 * n) / ((2 * n).factorial : ℝ) * 2 - ε ≤ Real.sin θ ∧
      Real.sin θ ≤ sinT q n + |q| ^ (2 * n) / ((2 * n).factorial : ℝ) * 2 + ε := by
  obtain ⟨hc, hs⟩ := cos_sin_taylor q n hq
  have hlc : |Real.cos θ - Real.cos q| ≤ ε := le_trans (Real.abs_cos_sub_cos_le θ q) hθ
  have hls : |Real.sin θ - Real.sin q| ≤ ε := le_trans (Real.abs_sin_sub_sin_le θ q) hθ
  rw [abs_le] at hc hs hlc hls
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- `|t * log 2 - q| ≤ ε` from Mathlib's 9-digit bracket of `log 2`, for `t ≥ 0`. -/
theorem abs_mul_log_two_sub_le {t q ε : ℝ} (ht : 0 ≤ t)
    (h1 : t * 0.6931471808 - q ≤ ε) (h2 : q - t * 0.6931471803 ≤ ε) :
    |t * Real.log 2 - q| ≤ ε := by
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  rw [abs_le]
  constructor
  · have : t * 0.6931471803 ≤ t * Real.log 2 := mul_le_mul_of_nonneg_left l1.le ht
    linarith
  · have : t * Real.log 2 ≤ t * 0.6931471808 := mul_le_mul_of_nonneg_left l2.le ht
    linarith

/-! ### `2^(-σ)` -/

/-- `(2^(-p/q))^q = 2^(-p)`. -/
theorem two_rpow_neg_div_pow (p q : ℕ) (hq : 0 < q) :
    ((2 : ℝ) ^ (-(p : ℝ) / q)) ^ q = (2 : ℝ) ^ (-(p : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  field_simp

/-- Lower bound on `2^(-p/q)` from an integer power check. -/
theorem le_two_rpow_neg {x : ℝ} {p q : ℕ} (hq : 0 < q) (hx0 : 0 ≤ x)
    (h : x ^ q ≤ (2 : ℝ) ^ (-(p : ℝ))) : x ≤ (2 : ℝ) ^ (-(p : ℝ) / q) := by
  have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p : ℝ) / q) := by positivity
  rw [← two_rpow_neg_div_pow p q hq] at h
  exact (pow_le_pow_iff_left₀ hx0 hy0 (Nat.pos_iff_ne_zero.mp hq)).mp h

/-- Upper bound on `2^(-p/q)` from an integer power check. -/
theorem two_rpow_neg_le {x : ℝ} {p q : ℕ} (hq : 0 < q) (hx0 : 0 ≤ x)
    (h : (2 : ℝ) ^ (-(p : ℝ)) ≤ x ^ q) : (2 : ℝ) ^ (-(p : ℝ) / q) ≤ x := by
  have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p : ℝ) / q) := by positivity
  rw [← two_rpow_neg_div_pow p q hq] at h
  exact (pow_le_pow_iff_left₀ hy0 hx0 (Nat.pos_iff_ne_zero.mp hq)).mp h

/-- `2^(-p) = 1 / 2^p` for natural `p` (so the power checks are pure rational arithmetic). -/
theorem two_rpow_neg_nat (p : ℕ) : (2 : ℝ) ^ (-(p : ℝ)) = 1 / 2 ^ p := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

/-- `σ ↦ 2^(-σ)` is antitone: for `a ≤ σ ≤ b`, `2^(-b) ≤ 2^(-σ) ≤ 2^(-a)`. -/
theorem two_rpow_neg_mono {a b σ : ℝ} (ha : a ≤ σ) (hb : σ ≤ b) :
    (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^ (-σ) ∧ (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-a) :=
  ⟨Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith),
   Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)⟩

/-! ### Slab brackets in `DI` form -/

theorem DI.mem_mk {x : ℝ} {lo hi : ℤ} {e : ℕ} (h1 : (lo : ℝ) / 2 ^ e ≤ x)
    (h2 : x ≤ (hi : ℝ) / 2 ^ e) : (⟨lo, hi, e⟩ : DI).mem x := by
  unfold DI.mem; exact ⟨h1, h2⟩

/-- `cos (t log 2)` on a height slab `[a, b] ⊆ [0, 4]` (angles stay in `[0, π]`). -/
theorem mem_cos {t a b : ℝ} {lo hi : ℤ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 4)
    (hlo : (lo : ℝ) / 2 ^ 32 ≤ Real.cos (b * Real.log 2))
    (hhi : Real.cos (a * Real.log 2) ≤ (hi : ℝ) / 2 ^ 32) :
    (⟨lo, hi, 32⟩ : DI).mem (Real.cos (t * Real.log 2)) := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hpi := Real.pi_gt_three
  have hlog0 : 0 ≤ Real.log 2 := by linarith
  have h1 : a * Real.log 2 ≤ t * Real.log 2 := mul_le_mul_of_nonneg_right hat hlog0
  have h2 : t * Real.log 2 ≤ b * Real.log 2 := mul_le_mul_of_nonneg_right htb hlog0
  have h0 : 0 ≤ a * Real.log 2 := mul_nonneg ha hlog0
  have hb' : b * Real.log 2 ≤ 4 * Real.log 2 := mul_le_mul_of_nonneg_right hb hlog0
  have hπ : b * Real.log 2 ≤ Real.pi := by linarith
  apply DI.mem_mk
  · exact le_trans hlo (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hπ h2)
  · exact le_trans (Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith) h1) hhi

/-- `sin (t log 2)` on a height slab below `π/2` (increasing). -/
theorem mem_sin_low {t a b : ℝ} {lo hi : ℤ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b)
    (hb : b * 0.6931471808 ≤ 3.141592 / 2)
    (hlo : (lo : ℝ) / 2 ^ 32 ≤ Real.sin (a * Real.log 2))
    (hhi : Real.sin (b * Real.log 2) ≤ (hi : ℝ) / 2 ^ 32) :
    (⟨lo, hi, 32⟩ : DI).mem (Real.sin (t * Real.log 2)) := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hpi := Real.pi_gt_d6
  have hlog0 : 0 ≤ Real.log 2 := by linarith
  have h1 : a * Real.log 2 ≤ t * Real.log 2 := mul_le_mul_of_nonneg_right hat hlog0
  have h2 : t * Real.log 2 ≤ b * Real.log 2 := mul_le_mul_of_nonneg_right htb hlog0
  have h0 : 0 ≤ a * Real.log 2 := mul_nonneg ha hlog0
  have hb0 : 0 ≤ b := le_trans (le_trans ha hat) htb
  have hb' : b * Real.log 2 ≤ b * 0.6931471808 := mul_le_mul_of_nonneg_left hu.le hb0
  have hπ : b * Real.log 2 ≤ Real.pi / 2 := by linarith
  apply DI.mem_mk
  · exact le_trans hlo (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) h1)
  · exact le_trans (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hπ h2) hhi

/-- `sin` is antitone on `[π/2, π]`. -/
theorem sin_anti_of_half_pi {x y : ℝ} (hx : Real.pi / 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.pi) :
    Real.sin y ≤ Real.sin x := by
  rw [← Real.sin_pi_sub y, ← Real.sin_pi_sub x]
  apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> linarith [Real.pi_pos]

/-- `sin (t log 2)` on a height slab above `π/2` (decreasing; angles stay below `π`). -/
theorem mem_sin_high {t a b : ℝ} {lo hi : ℤ} (ha : 3.141593 / 2 ≤ a * 0.6931471803)
    (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 4)
    (hlo : (lo : ℝ) / 2 ^ 32 ≤ Real.sin (b * Real.log 2))
    (hhi : Real.sin (a * Real.log 2) ≤ (hi : ℝ) / 2 ^ 32) :
    (⟨lo, hi, 32⟩ : DI).mem (Real.sin (t * Real.log 2)) := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hpi := Real.pi_lt_d6
  have hpi3 := Real.pi_gt_three
  have hlog0 : 0 ≤ Real.log 2 := by linarith
  have ha0 : 0 ≤ a := by nlinarith
  have h1 : a * Real.log 2 ≤ t * Real.log 2 := mul_le_mul_of_nonneg_right hat hlog0
  have h2 : t * Real.log 2 ≤ b * Real.log 2 := mul_le_mul_of_nonneg_right htb hlog0
  have ha' : a * 0.6931471803 ≤ a * Real.log 2 := mul_le_mul_of_nonneg_left hl.le ha0
  have hb' : b * Real.log 2 ≤ 4 * Real.log 2 := mul_le_mul_of_nonneg_right hb hlog0
  have hπa : Real.pi / 2 ≤ a * Real.log 2 := by linarith
  have hπb : b * Real.log 2 ≤ Real.pi := by linarith
  apply DI.mem_mk
  · exact le_trans hlo (sin_anti_of_half_pi (by linarith) h2 hπb)
  · exact le_trans (sin_anti_of_half_pi hπa h1 (by linarith)) hhi

/-- `sin (t log 2)` on a height slab straddling `π/2`: bounded below by the smaller endpoint
    value (increasing then decreasing), above by `1`. -/
theorem mem_sin_mid {t a b : ℝ} {lo : ℤ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 4)
    (hlo1 : (lo : ℝ) / 2 ^ 32 ≤ Real.sin (a * Real.log 2))
    (hlo2 : (lo : ℝ) / 2 ^ 32 ≤ Real.sin (b * Real.log 2)) :
    (⟨lo, 4294967296, 32⟩ : DI).mem (Real.sin (t * Real.log 2)) := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have hpi3 := Real.pi_gt_three
  have hlog0 : 0 ≤ Real.log 2 := by linarith
  have h1 : a * Real.log 2 ≤ t * Real.log 2 := mul_le_mul_of_nonneg_right hat hlog0
  have h2 : t * Real.log 2 ≤ b * Real.log 2 := mul_le_mul_of_nonneg_right htb hlog0
  have h0 : 0 ≤ a * Real.log 2 := mul_nonneg ha hlog0
  have hb' : b * Real.log 2 ≤ 4 * Real.log 2 := mul_le_mul_of_nonneg_right hb hlog0
  have hπb : b * Real.log 2 ≤ Real.pi := by linarith
  apply DI.mem_mk
  · rcases le_total (t * Real.log 2) (Real.pi / 2) with hlt | hgt
    · exact le_trans hlo1 (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hlt h1)
    · exact le_trans hlo2 (sin_anti_of_half_pi hgt h2 hπb)
  · have : ((4294967296 : ℤ) : ℝ) / 2 ^ 32 = 1 := by norm_num
    rw [this]; exact Real.sin_le_one _

/-- `2^(-σ)` on a σ slab `[a, b]`. -/
theorem mem_m {σ a b : ℝ} {lo hi : ℤ} (hσa : a ≤ σ) (hσb : σ ≤ b)
    (hlo : (lo : ℝ) / 2 ^ 32 ≤ (2 : ℝ) ^ (-b)) (hhi : (2 : ℝ) ^ (-a) ≤ (hi : ℝ) / 2 ^ 32) :
    (⟨lo, hi, 32⟩ : DI).mem ((2 : ℝ) ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := two_rpow_neg_mono hσa hσb
  exact DI.mem_mk (le_trans hlo h1) (le_trans h2 hhi)

end M6gap.HeightFloor
