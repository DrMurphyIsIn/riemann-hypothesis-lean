/-
  ArchS9_Analysis -- the analytic core of the certified prolate engine (archimedean stage S9,
  rvm_bridge island, 2026-10-11).

  Objects (Connes-Consani arXiv:2006.13771, (66)-(68), even prolates, c = 2 pi):
    * `ip f g = ∫_0^1 f g`  -- CC's inner product (16) on L²(ℝ)_ev, written on [0, 1];
    * `T f ω = ∫_0^1 2 cos(2 pi x ω) f(x) dx` -- for even f this is `∫_{-1}^{1} f(x) e^{2 pi i x ω} dx`,
      the time-band limiting operator of CC (68): an even prolate ξ_n satisfies `T ξ_n = λ(n) ξ_n`;
    * `Td f ω = ∫_0^1 ∂_ω (2 cos(2 pi x ω)) f(x) dx` -- the ω-derivative of `T f` (`hasDerivAt_T`);
    * `mom j f = ∫_0^1 x^(2j) f`, `aC j = 2 (-1)^j (2 pi)^(2j) / (2j)!`.
  PROVED here (pure real analysis, for continuous f):
    * Cauchy-Schwarz `ip f g ^ 2 ≤ ip f f * ip g g`, `L1 f ^ 2 ≤ ip f f`, Minkowski;
    * the Taylor split of the kernel: for 0 ≤ ω ≤ X with 2 pi X ≤ (2J+1)/2,
        |T f ω - Σ_{j<J} aC j ω^(2j) mom j f| ≤ 4 (2 pi X)^(2J) / (2J)! · L1 f,
      and the same for `Td` with Σ_{j<J} aC j (2j) ω^(2j-1) mom j f and 8 pi (2 pi X)^(2J-1)/(2J-1)!;
    * continuity of `T f`, `Td f` and `HasDerivAt (T f) (Td f ω) ω`.
  The Taylor remainders are KWin_Taylor's `cos_sub_tayl_le` / `sin_sub_tayl_le` (reused).
  conjecture1_proved = False.  No `sorry`.
-/
import KWin_Taylor

noncomputable section

namespace ArchS9

open Real Finset MeasureTheory intervalIntegral

/-! ## A. Definitions. -/

/-- The pairing `∫_0^1 f g` (CC's inner product (16) on even functions). -/
def ip (f g : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, f x * g x

/-- `∫_0^1 |f|`. -/
def L1 (f : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, |f x|

/-- The kernel `2 cos(2 pi x ω)` of the time-band limiting operator on even functions. -/
def K (ω x : ℝ) : ℝ := 2 * Real.cos (2 * π * x * ω)

/-- The time-band limiting operator `T f ω = ∫_0^1 2 cos(2 pi x ω) f(x) dx`
(= `∫_{-1}^{1} f(x) e^{2 pi i x ω} dx` for even `f`, CC (68)). -/
def T (f : ℝ → ℝ) (ω : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, K ω x * f x

/-- `∂_ω K`. -/
def Kd (ω x : ℝ) : ℝ := -(4 * π * x * Real.sin (2 * π * x * ω))

/-- `Td f ω = ∫_0^1 ∂_ω K(ω, x) f(x) dx`, the derivative of `T f` (`hasDerivAt_T`). -/
def Td (f : ℝ → ℝ) (ω : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, Kd ω x * f x

/-- Even moments `∫_0^1 x^(2j) f`. -/
def mom (j : ℕ) (f : ℝ → ℝ) : ℝ := ∫ x in (0 : ℝ)..1, x ^ (2 * j) * f x

/-- Taylor coefficients of the kernel: `K ω x = Σ_j aC j (ω x)^(2j)`. -/
def aC (j : ℕ) : ℝ := 2 * (-1) ^ j * (2 * π) ^ (2 * j) / ((2 * j).factorial : ℝ)

/-! ## B. The pairing. -/

lemma ii {f : ℝ → ℝ} (hf : Continuous f) : IntervalIntegrable f volume 0 1 :=
  hf.intervalIntegrable _ _

lemma ip_comm (f g : ℝ → ℝ) : ip f g = ip g f := by
  unfold ip; congr 1; funext x; ring

lemma ip_self_nonneg (f : ℝ → ℝ) : 0 ≤ ip f f :=
  intervalIntegral.integral_nonneg (by norm_num) fun x _ => mul_self_nonneg _

lemma L1_nonneg (f : ℝ → ℝ) : 0 ≤ L1 f :=
  intervalIntegral.integral_nonneg (by norm_num) fun x _ => abs_nonneg _

lemma ip_add_left {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    ip (fun x => f x + g x) h = ip f h + ip g h := by
  unfold ip
  simp_rw [add_mul]
  exact intervalIntegral.integral_add (ii (hf.mul hh)) (ii (hg.mul hh))

lemma ip_smul_left (c : ℝ) (f h : ℝ → ℝ) : ip (fun x => c * f x) h = c * ip f h := by
  unfold ip
  rw [← intervalIntegral.integral_const_mul]
  congr 1; funext x; ring

lemma ip_sum_left {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ} (hg : ∀ i, Continuous (g i))
    {h : ℝ → ℝ} (hh : Continuous h) :
    ip (fun x => ∑ i ∈ s, g i x) h = ∑ i ∈ s, ip (g i) h := by
  unfold ip
  simp_rw [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i _ => ii ((hg i).mul hh)

/-- The quadratic expansion `ip (f - t g) (f - t g)`. -/
lemma ip_sub_smul_self {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    ip (fun x => f x - t * g x) (fun x => f x - t * g x)
      = ip g g * (t * t) + (-2 * ip f g) * t + ip f f := by
  unfold ip
  have e : (fun x => (f x - t * g x) * (f x - t * g x))
      = fun x => (f x * f x - (2 * t) * (f x * g x)) + (t * t) * (g x * g x) := by
    funext x; ring
  have i1 : IntervalIntegrable (fun x => f x * f x) volume 0 1 := ii (hf.mul hf)
  have i2 : IntervalIntegrable (fun x => f x * g x) volume 0 1 := ii (hf.mul hg)
  have i3 : IntervalIntegrable (fun x => g x * g x) volume 0 1 := ii (hg.mul hg)
  rw [e, intervalIntegral.integral_add (i1.sub (i2.const_mul _)) (i3.const_mul _),
    intervalIntegral.integral_sub i1 (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- **Cauchy-Schwarz** for the pairing. -/
theorem ip_sq_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ip f g ^ 2 ≤ ip f f * ip g g := by
  have h : ∀ t : ℝ, 0 ≤ ip g g * (t * t) + (-2 * ip f g) * t + ip f f := fun t => by
    rw [← ip_sub_smul_self hf hg t]; exact ip_self_nonneg _
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

theorem abs_ip_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    |ip f g| ≤ √(ip f f) * √(ip g g) := by
  rw [← Real.sqrt_mul (ip_self_nonneg f), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (ip_sq_le hf hg)

/-- `(∫_0^1 |f|)^2 ≤ ∫_0^1 f^2`. -/
theorem L1_sq_le {f : ℝ → ℝ} (hf : Continuous f) : L1 f ^ 2 ≤ ip f f := by
  have h : ∀ t : ℝ, 0 ≤ 1 * (t * t) + (-2 * L1 f) * t + ip f f := fun t => by
    have h0 : 0 ≤ ∫ x in (0 : ℝ)..1, (|f x| - t) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) fun x _ => sq_nonneg _
    have e : (fun x => (|f x| - t) ^ 2) = fun x => (f x * f x - (2 * t) * |f x|) + t * t := by
      funext x; rw [sub_sq, sq_abs]; ring
    have i1 : IntervalIntegrable (fun x => f x * f x) volume 0 1 := ii (hf.mul hf)
    have i2 : IntervalIntegrable (fun x => |f x|) volume 0 1 := ii hf.abs
    rw [e, intervalIntegral.integral_add (i1.sub (i2.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub i1 (i2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h0
    simp only [smul_eq_mul, sub_zero, one_mul] at h0
    unfold L1 ip; linarith
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

theorem L1_le_sqrt {f : ℝ → ℝ} (hf : Continuous f) : L1 f ≤ √(ip f f) :=
  Real.le_sqrt_of_sq_le (L1_sq_le hf)

/-- **Minkowski.** -/
theorem sqrt_ip_add_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    √(ip (fun x => f x + g x) (fun x => f x + g x)) ≤ √(ip f f) + √(ip g g) := by
  have e : ip (fun x => f x + g x) (fun x => f x + g x) = ip f f + 2 * ip f g + ip g g := by
    rw [ip_add_left (h := fun x => f x + g x) hf hg (hf.add hg), ip_comm f, ip_comm g,
      ip_add_left hf hg hf, ip_add_left hf hg hg, ip_comm g f]
    ring
  rw [e]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 := abs_ip_le hf hg
  have hf' := Real.sq_sqrt (ip_self_nonneg f)
  have hg' := Real.sq_sqrt (ip_self_nonneg g)
  nlinarith [abs_le.mp h1, Real.sqrt_nonneg (ip f f), Real.sqrt_nonneg (ip g g)]

/-- A pointwise bound on `[0, 1]` bounds the pairing against `|g|`. -/
lemma abs_int_mul_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {B : ℝ}
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    |∫ x in (0 : ℝ)..1, f x * g x| ≤ B * L1 g := by
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
  have hmono : ∫ x in (0 : ℝ)..1, |f x * g x| ≤ ∫ x in (0 : ℝ)..1, B * |g x| := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ii (hf.mul hg).abs
    · exact ii (continuous_const.mul hg.abs)
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hB x hx) (abs_nonneg _)
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]; rfl

lemma ip_self_le_of_bound {f : ℝ → ℝ} (hf : Continuous f) {B : ℝ}
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) : ip f f ≤ B ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have h := abs_int_mul_le hf hf hB
  have hL : L1 f ≤ B := by
    have : L1 f ≤ ∫ x in (0 : ℝ)..1, B := by
      apply intervalIntegral.integral_mono_on (by norm_num) (ii hf.abs) intervalIntegrable_const
      intro x hx; exact hB x hx
    simpa using this
  calc ip f f ≤ |ip f f| := le_abs_self _
    _ ≤ B * L1 f := h
    _ ≤ B * B := mul_le_mul_of_nonneg_left hL hB0
    _ = B ^ 2 := by ring

/-! ## C. The kernel: Taylor split, continuity, derivative. -/

lemma continuous_K_mul {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => K p.1 p.2 * f p.2) := by
  unfold K; fun_prop

lemma continuous_Kd_mul {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => Kd p.1 p.2 * f p.2) := by
  unfold Kd; fun_prop

theorem continuous_T {f : ℝ → ℝ} (hf : Continuous f) : Continuous (T f) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (continuous_K_mul hf) 0 1

theorem continuous_Td {f : ℝ → ℝ} (hf : Continuous f) : Continuous (Td f) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (continuous_Kd_mul hf) 0 1

lemma hasDerivAt_K (x ω : ℝ) : HasDerivAt (fun w => K w x) (Kd ω x) ω := by
  unfold K
  have h1 : HasDerivAt (fun w : ℝ => 2 * π * x * w) (2 * π * x) ω := by
    simpa using (hasDerivAt_id ω).const_mul (2 * π * x)
  have h2 := (h1.cos).const_mul 2
  have e : Kd ω x = 2 * (-Real.sin (2 * π * x * ω) * (2 * π * x)) := by unfold Kd; ring
  rw [e]; exact h2

/-- **Differentiation under the integral sign**: `(T f)' = Td f`. -/
theorem hasDerivAt_T {f : ℝ → ℝ} (hf : Continuous f) (ω₀ : ℝ) :
    HasDerivAt (T f) (Td f ω₀) ω₀ := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := fun ω x => K ω x * f x) (F' := fun ω x => Kd ω x * f x)
    (x₀ := ω₀) (s := Set.univ) (bound := fun x => 4 * π * |f x|) Filter.univ_mem
    (Filter.Eventually.of_forall fun ω =>
      ((continuous_K_mul hf).comp (Continuous.prodMk_right ω)).aestronglyMeasurable)
    (((continuous_K_mul hf).comp (Continuous.prodMk_right ω₀)).intervalIntegrable 0 1)
    (((continuous_Kd_mul hf).comp (Continuous.prodMk_right ω₀)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x hx ω _ => by
      have hx0 : 0 ≤ x := by
        rcases hx with ⟨h1, _⟩
        simp at h1; linarith
      have hx1 : x ≤ 1 := by
        rcases hx with ⟨_, h2⟩
        simp at h2; linarith
      unfold Kd
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg hx0,
        abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
      have hs := Real.abs_sin_le_one (2 * π * x * ω)
      have : 4 * π * x * |Real.sin (2 * π * x * ω)| ≤ 4 * π := by
        have h4 : 0 ≤ 4 * π := by positivity
        calc 4 * π * x * |Real.sin (2 * π * x * ω)| ≤ 4 * π * 1 * 1 := by
              gcongr
          _ = 4 * π := by ring
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _))
    ((continuous_const.mul hf.abs).intervalIntegrable 0 1)
    (Filter.Eventually.of_forall fun x _ ω _ => (hasDerivAt_K x ω).mul_const (f x))
  exact key.2

lemma sum_aC_eq_tayl (J : ℕ) (x ω : ℝ) :
    ∑ j ∈ range J, aC j * ω ^ (2 * j) * x ^ (2 * j) = 2 * KWin.tayl 0 J (2 * π * x * ω) := by
  unfold KWin.tayl aC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [add_zero]
  rw [mul_pow, mul_pow]
  ring

lemma sum_aCd_eq_tayl (M : ℕ) (x ω : ℝ) :
    ∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * x ^ (2 * j)
      = -(4 * π * x * KWin.tayl 1 M (2 * π * x * ω)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  unfold KWin.tayl aC
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
  rw [e1, e2, Nat.factorial_succ]
  push_cast
  rw [mul_pow, mul_pow]
  have hf : ((2 * m + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma sum_mom (s : Finset ℕ) (c : ℕ → ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∑ j ∈ s, c j * mom j f = ∫ x in (0 : ℝ)..1, (∑ j ∈ s, c j * x ^ (2 * j)) * f x := by
  unfold mom
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x; ring
  · intro j _; exact ii (by fun_prop)

lemma continuous_tayl_comp (par M : ℕ) (ω : ℝ) :
    Continuous (fun x : ℝ => KWin.tayl par M (2 * π * x * ω)) :=
  (KWin.continuous_tayl par M).comp (by fun_prop)

/-- **Taylor split of `T`.** -/
theorem T_sub_le (J : ℕ) {f : ℝ → ℝ} (hf : Continuous f) {ω X : ℝ} (hω : 0 ≤ ω) (hωX : ω ≤ X)
    (hX : 2 * π * X ≤ (2 * J + 1) / 2) :
    |T f ω - ∑ j ∈ range J, aC j * ω ^ (2 * j) * mom j f|
      ≤ 4 * (2 * π * X) ^ (2 * J) / ((2 * J).factorial : ℝ) * L1 f := by
  have e : T f ω - ∑ j ∈ range J, aC j * ω ^ (2 * j) * mom j f
      = ∫ x in (0 : ℝ)..1, (K ω x - 2 * KWin.tayl 0 J (2 * π * x * ω)) * f x := by
    rw [sum_mom _ _ hf]
    unfold T
    have iK : IntervalIntegrable (fun x => K ω x * f x) volume 0 1 := ii (by unfold K; fun_prop)
    have iS : IntervalIntegrable
        (fun x => (∑ j ∈ range J, aC j * ω ^ (2 * j) * x ^ (2 * j)) * f x) volume 0 1 :=
      ii ((continuous_finsetSum _ fun j _ => by fun_prop).mul hf)
    rw [← intervalIntegral.integral_sub iK iS]
    congr 1; funext x
    rw [sum_aC_eq_tayl J x ω]
    ring
  rw [e]
  refine abs_int_mul_le (f := fun x => K ω x - 2 * KWin.tayl 0 J (2 * π * x * ω)) ?_ hf ?_
  · have := continuous_tayl_comp 0 J ω
    unfold K; fun_prop
  · intro x hx
    have hy0 : 0 ≤ 2 * π * x * ω := by have := hx.1; positivity
    have hyX : 2 * π * x * ω ≤ 2 * π * X := by
      have h1 : x * ω ≤ 1 * X := mul_le_mul hx.2 hωX hω zero_le_one
      nlinarith [Real.pi_pos]
    have hy : |2 * π * x * ω| ≤ (2 * J + 1) / 2 := by rw [abs_of_nonneg hy0]; linarith
    have h := KWin.cos_sub_tayl_le hy
    unfold K
    rw [show 2 * Real.cos (2 * π * x * ω) - 2 * KWin.tayl 0 J (2 * π * x * ω)
      = 2 * (Real.cos (2 * π * x * ω) - KWin.tayl 0 J (2 * π * x * ω)) by ring, abs_mul,
      abs_two]
    have hp : |2 * π * x * ω| ^ (2 * J) ≤ (2 * π * X) ^ (2 * J) := by
      rw [abs_of_nonneg hy0]; exact pow_le_pow_left₀ hy0 hyX _
    have hfac : (0 : ℝ) < ((2 * J).factorial : ℝ) := by positivity
    calc 2 * |Real.cos (2 * π * x * ω) - KWin.tayl 0 J (2 * π * x * ω)|
        ≤ 2 * (2 * |2 * π * x * ω| ^ (2 * J) / ((2 * J).factorial : ℝ)) := by gcongr
      _ ≤ 2 * (2 * (2 * π * X) ^ (2 * J) / ((2 * J).factorial : ℝ)) := by gcongr
      _ = 4 * (2 * π * X) ^ (2 * J) / ((2 * J).factorial : ℝ) := by ring

/-- **Taylor split of `Td`.** -/
theorem Td_sub_le (M : ℕ) {f : ℝ → ℝ} (hf : Continuous f) {ω X : ℝ} (hω : 0 ≤ ω) (hωX : ω ≤ X)
    (hX : 2 * π * X ≤ (2 * M + 1 + 1) / 2) :
    |Td f ω - ∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * mom j f|
      ≤ 8 * π * (2 * π * X) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) * L1 f := by
  have e : Td f ω - ∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * mom j f
      = ∫ x in (0 : ℝ)..1, (Kd ω x + 4 * π * x * KWin.tayl 1 M (2 * π * x * ω)) * f x := by
    rw [sum_mom _ _ hf]
    unfold Td
    have iK : IntervalIntegrable (fun x => Kd ω x * f x) volume 0 1 :=
      ii ((continuous_Kd_mul hf).comp (Continuous.prodMk_right ω))
    have iS : IntervalIntegrable (fun x => (∑ j ∈ range (M + 1),
        aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * x ^ (2 * j)) * f x) volume 0 1 :=
      ii ((continuous_finsetSum _ fun j _ => by fun_prop).mul hf)
    rw [← intervalIntegral.integral_sub iK iS]
    congr 1; funext x
    rw [sum_aCd_eq_tayl M x ω]
    ring
  rw [e]
  refine abs_int_mul_le
    (f := fun x => Kd ω x + 4 * π * x * KWin.tayl 1 M (2 * π * x * ω)) ?_ hf ?_
  · have := continuous_tayl_comp 1 M ω
    unfold Kd; fun_prop
  · intro x hx
    have hx0 := hx.1
    have hy0 : 0 ≤ 2 * π * x * ω := by positivity
    have hyX : 2 * π * x * ω ≤ 2 * π * X := by
      have h1 : x * ω ≤ 1 * X := mul_le_mul hx.2 hωX hω zero_le_one
      nlinarith [Real.pi_pos]
    have hy : |2 * π * x * ω| ≤ (2 * M + 1 + 1) / 2 := by rw [abs_of_nonneg hy0]; linarith
    have h := KWin.sin_sub_tayl_le hy
    unfold Kd
    rw [show -(4 * π * x * Real.sin (2 * π * x * ω)) + 4 * π * x * KWin.tayl 1 M (2 * π * x * ω)
      = -(4 * π * x) * (Real.sin (2 * π * x * ω) - KWin.tayl 1 M (2 * π * x * ω)) by ring,
      abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 4 * π * x)]
    have hp : |2 * π * x * ω| ^ (2 * M + 1) ≤ (2 * π * X) ^ (2 * M + 1) := by
      rw [abs_of_nonneg hy0]; exact pow_le_pow_left₀ hy0 hyX _
    have h4 : 4 * π * x ≤ 4 * π := by nlinarith [Real.pi_pos, hx.2]
    calc 4 * π * x * |Real.sin (2 * π * x * ω) - KWin.tayl 1 M (2 * π * x * ω)|
        ≤ 4 * π * (2 * |2 * π * x * ω| ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) := by
          gcongr
      _ ≤ 4 * π * (2 * (2 * π * X) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) := by gcongr
      _ = 8 * π * (2 * π * X) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) := by ring

/-- Crude bounds: `|T f ω| ≤ 2 L1 f`, `|mom j f| ≤ L1 f`. -/
theorem abs_T_le {f : ℝ → ℝ} (hf : Continuous f) (ω : ℝ) : |T f ω| ≤ 2 * L1 f := by
  refine abs_int_mul_le (f := fun x => K ω x) ?_ hf ?_
  · unfold K; fun_prop
  · intro x _
    unfold K
    rw [abs_mul, abs_two]
    have := Real.abs_cos_le_one (2 * π * x * ω)
    linarith

theorem abs_mom_le (j : ℕ) {f : ℝ → ℝ} (hf : Continuous f) : |mom j f| ≤ L1 f := by
  have h := abs_int_mul_le (f := fun x => x ^ (2 * j)) (by fun_prop) hf (B := 1) (fun x hx => by
    rw [abs_of_nonneg (by have := hx.1; positivity)]
    exact pow_le_one₀ hx.1 hx.2)
  simpa [mom] using h

end ArchS9

end
