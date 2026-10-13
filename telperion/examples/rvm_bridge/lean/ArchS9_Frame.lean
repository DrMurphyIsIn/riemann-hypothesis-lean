/-
  ArchS9_Frame -- the generic certified-eigenpair frame of stage S9 (rvm_bridge island, 2026-10-11).

  Data-independent.  Given ANY real table `B n k` (n, k < J) defining even polynomials
  `psi n x = Σ_k B n k x^(2k)`, reals `θ n`, `aR j`, put `Em j k = [j = k] aR j - Σ_n θ n B n j B n k`.
  Then for every continuous f and every ω (pure algebra + KWin Taylor):

      T f ω = Σ_n θ n · ip f (psi n) · psi n ω + errF f ω,
      |errF f ω| ≤ (η + Σ_j |aC j - aR j| X^(2j) + Σ_{j,k} |Em j k| X^(2j)) · L1 f   (0 ≤ ω ≤ X),

  and the same for `Td` with `psid` (the ω-derivative).  If moreover the Gram matrix of the psi's
  is within γ of the identity, a unit eigenfunction ξ (T ξ = λ ξ, ip ξ ξ = 1, ξ continuous) with
  p n = ip ξ (psi n) satisfies
      (P1) |p n| ≤ 1 + γ,
      (P2) |(λ - θ m) p m| ≤ ε,
      (P3) (|λ| - ζ1)² ≤ Σ_m θ m² p m² + C          (when ζ1 ≤ |λ|),
  and the finite lemmas `round_step`, `localize`, `value_bound` turn (P1)-(P3) into eigenvalue
  windows, eigenvector overlap and pointwise values.  Nothing here assumes the spectral theorem,
  self-adjointness of T, or anything about prolate spheroidal functions: the eigenpair is an
  arbitrary hypothesis.  conjecture1_proved = False.  No `sorry`.
-/
import ArchS9_Analysis

noncomputable section

namespace ArchS9

open Real Finset MeasureTheory intervalIntegral

/-! ## A. Even polynomials. -/

section Poly

variable (J : ℕ) (B : ℕ → ℕ → ℝ)

/-- `psi n x = Σ_{k<J} B n k x^(2k)`. -/
def psi (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ range J, B n k * x ^ (2 * k)

/-- `psid n x = Σ_{k<J} B n k (2k) x^(2k-1)`, the derivative of `psi n`. -/
def psid (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ range J, B n k * (2 * k : ℝ) * x ^ (2 * k - 1)

lemma continuous_psi (n : ℕ) : Continuous (psi J B n) := by
  unfold psi; fun_prop

lemma hasDerivAt_psi (n : ℕ) (x : ℝ) : HasDerivAt (psi J B n) (psid J B n x) x := by
  unfold psi psid
  apply HasDerivAt.fun_sum
  intro k _
  have h := (hasDerivAt_pow (2 * k) x).const_mul (B n k)
  have e : B n k * (2 * k : ℝ) * x ^ (2 * k - 1) = B n k * (((2 * k : ℕ) : ℝ) * x ^ (2 * k - 1)) := by
    push_cast; ring
  rw [e]; exact h

/-- `ip f (psi n) = Σ_k B n k mom k f`. -/
lemma ip_psi_right {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    ip f (psi J B n) = ∑ k ∈ range J, B n k * mom k f := by
  rw [sum_mom _ _ hf]
  unfold ip psi
  congr 1; funext x; ring

lemma mom_monomial (j k : ℕ) : mom j (fun x => x ^ (2 * k)) = 1 / (2 * j + 2 * k + 1 : ℝ) := by
  unfold mom
  have e : (fun x : ℝ => x ^ (2 * j) * x ^ (2 * k)) = fun x => x ^ (2 * j + 2 * k) := by
    funext x; rw [pow_add]
  rw [e, integral_pow]
  push_cast; simp

/-- The Gram entries as an explicit finite sum. -/
lemma ip_psi_psi (n m : ℕ) :
    ip (psi J B n) (psi J B m)
      = ∑ k ∈ range J, ∑ l ∈ range J, B n k * B m l / (2 * k + 2 * l + 1 : ℝ) := by
  rw [ip_psi_right J B (continuous_psi J B n), Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hm : mom l (psi J B n) = ∑ k ∈ range J, B n k * mom l (fun x => x ^ (2 * k)) := by
    unfold mom psi
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
    · intro k _; exact ii (by fun_prop)
  rw [hm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mom_monomial]
  ring_nf

/-- `|psi n x| ≤ Σ_k |B n k| X^(2k)` for `|x| ≤ X`. -/
lemma abs_psi_le (n : ℕ) {x X : ℝ} (hx : |x| ≤ X) :
    |psi J B n x| ≤ ∑ k ∈ range J, |B n k| * X ^ (2 * k) := by
  unfold psi
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx _) (abs_nonneg _)

lemma abs_psid_le (n : ℕ) {x X : ℝ} (hx : |x| ≤ X) :
    |psid J B n x| ≤ ∑ k ∈ range J, |B n k| * (2 * k : ℝ) * X ^ (2 * k - 1) := by
  unfold psid
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx _) (by positivity)

end Poly

/-! ## B. The algebraic identity and the error terms. -/

section Err

variable (J : ℕ) (B : ℕ → ℕ → ℝ) (θ : ℕ → ℝ) (aR : ℕ → ℝ)

/-- `Em j k = [j = k] aR j - Σ_n θ n B n j B n k`. -/
def Em (j k : ℕ) : ℝ := (if j = k then aR j else 0) - ∑ n ∈ range J, θ n * B n j * B n k

/-- The rank-J identity, for any moment vector `m` and any weights `u`. -/
lemma rankJ_identity (m u : ℕ → ℝ) :
    ∑ j ∈ range J, aR j * u j * m j
      = ∑ n ∈ range J, θ n * (∑ k ∈ range J, B n k * m k) * (∑ j ∈ range J, B n j * u j)
        + ∑ j ∈ range J, ∑ k ∈ range J, Em J B θ aR j k * m k * u j := by
  unfold Em
  have h1 : ∑ j ∈ range J, ∑ k ∈ range J, (if j = k then aR j else 0) * m k * u j
      = ∑ j ∈ range J, aR j * u j * m j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_eq_single j]
    · simp; ring
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd hj h
  have h2 : ∑ j ∈ range J, ∑ k ∈ range J, (∑ n ∈ range J, θ n * B n j * B n k) * m k * u j
      = ∑ n ∈ range J, θ n * (∑ k ∈ range J, B n k * m k) * (∑ j ∈ range J, B n j * u j) := by
    have l1 : ∀ j k, (∑ n ∈ range J, θ n * B n j * B n k) * m k * u j
        = ∑ n ∈ range J, θ n * B n j * B n k * m k * u j := fun j k => by
      rw [Finset.sum_mul, Finset.sum_mul]
    have r1 : ∀ n, θ n * (∑ k ∈ range J, B n k * m k) * (∑ j ∈ range J, B n j * u j)
        = ∑ j ∈ range J, ∑ k ∈ range J, θ n * B n j * B n k * m k * u j := fun n => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp_rw [l1, r1]
    calc ∑ j ∈ range J, ∑ k ∈ range J, ∑ n ∈ range J, θ n * B n j * B n k * m k * u j
        = ∑ j ∈ range J, ∑ n ∈ range J, ∑ k ∈ range J, θ n * B n j * B n k * m k * u j :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [h1, h2]; ring

/-- The error of the rank-J model of `T`. -/
def errF (f : ℝ → ℝ) (ω : ℝ) : ℝ :=
  T f ω - ∑ n ∈ range J, θ n * ip f (psi J B n) * psi J B n ω

/-- The error of the rank-J model of `Td`. -/
def errdF (f : ℝ → ℝ) (ω : ℝ) : ℝ :=
  Td f ω - ∑ n ∈ range J, θ n * ip f (psi J B n) * psid J B n ω

lemma abs_weighted_mom_le {f : ℝ → ℝ} (hf : Continuous f) (s : Finset ℕ) (c u U : ℕ → ℝ)
    (hu : ∀ j ∈ s, |u j| ≤ U j) :
    |∑ j ∈ s, c j * u j * mom j f| ≤ (∑ j ∈ s, |c j| * U j) * L1 f := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [abs_mul, abs_mul]
  have h1 := abs_mom_le j hf
  have h2 := hu j hj
  have := L1_nonneg f
  have hU : 0 ≤ U j := (abs_nonneg _).trans h2
  calc |c j| * |u j| * |mom j f| ≤ |c j| * U j * L1 f := by gcongr
    _ = _ := by ring

lemma abs_Em_mom_le {f : ℝ → ℝ} (hf : Continuous f) (u U : ℕ → ℝ)
    (hu : ∀ j ∈ range J, |u j| ≤ U j) :
    |∑ j ∈ range J, ∑ k ∈ range J, Em J B θ aR j k * mom k f * u j|
      ≤ (∑ j ∈ range J, ∑ k ∈ range J, |Em J B θ aR j k| * U j) * L1 f := by
  simp_rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := abs_mom_le k hf
  have h2 := hu j hj
  have := L1_nonneg f
  have hU : 0 ≤ U j := (abs_nonneg _).trans h2
  calc |Em J B θ aR j k| * |mom k f| * |u j| ≤ |Em J B θ aR j k| * L1 f * U j := by gcongr
    _ = _ := by ring

/-- **The error bound for `T`** on `[0, X]`. -/
theorem abs_errF_le {f : ℝ → ℝ} (hf : Continuous f) {X η dA EE : ℝ}
    (hX : 2 * π * X ≤ (2 * J + 1) / 2)
    (hη : 4 * (2 * π * X) ^ (2 * J) / ((2 * J).factorial : ℝ) ≤ η)
    (hdA : ∑ j ∈ range J, |aC j - aR j| * X ^ (2 * j) ≤ dA)
    (hE : ∑ j ∈ range J, ∑ k ∈ range J, |Em J B θ aR j k| * X ^ (2 * j) ≤ EE)
    {ω : ℝ} (hω : 0 ≤ ω) (hωX : ω ≤ X) :
    |errF J B θ f ω| ≤ (η + dA + EE) * L1 f := by
  have hL := L1_nonneg f
  have hid := rankJ_identity J B θ aR (fun k => mom k f) (fun j => ω ^ (2 * j))
  have hip : ∀ n, ip f (psi J B n) = ∑ k ∈ range J, B n k * mom k f :=
    fun n => ip_psi_right J B hf n
  have hps : ∀ n, psi J B n ω = ∑ j ∈ range J, B n j * ω ^ (2 * j) := fun n => rfl
  have e : errF J B θ f ω
      = (T f ω - ∑ j ∈ range J, aC j * ω ^ (2 * j) * mom j f)
        + ∑ j ∈ range J, (aC j - aR j) * ω ^ (2 * j) * mom j f
        + ∑ j ∈ range J, ∑ k ∈ range J, Em J B θ aR j k * mom k f * ω ^ (2 * j) := by
    unfold errF
    simp_rw [hip, hps]
    have hsplit : ∑ j ∈ range J, (aC j - aR j) * ω ^ (2 * j) * mom j f
        = ∑ j ∈ range J, aC j * ω ^ (2 * j) * mom j f
          - ∑ j ∈ range J, aR j * ω ^ (2 * j) * mom j f := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [hsplit, hid]; ring
  have hXω : |ω| ≤ X := by rw [abs_of_nonneg hω]; exact hωX
  have hu : ∀ j ∈ range J, |ω ^ (2 * j)| ≤ X ^ (2 * j) := fun j _ => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hXω _
  have t1 := T_sub_le J hf hω hωX hX
  have t2 := abs_weighted_mom_le hf (range J) (fun j => aC j - aR j) (fun j => ω ^ (2 * j))
    (fun j => X ^ (2 * j)) hu
  have t3 := abs_Em_mom_le J B θ aR hf (fun j => ω ^ (2 * j)) (fun j => X ^ (2 * j)) hu
  rw [e]
  calc _ ≤ |T f ω - ∑ j ∈ range J, aC j * ω ^ (2 * j) * mom j f|
        + |∑ j ∈ range J, (aC j - aR j) * ω ^ (2 * j) * mom j f|
        + |∑ j ∈ range J, ∑ k ∈ range J, Em J B θ aR j k * mom k f * ω ^ (2 * j)| :=
        abs_add_three _ _ _
    _ ≤ η * L1 f + dA * L1 f + EE * L1 f := by
        gcongr
        · exact t1.trans (mul_le_mul_of_nonneg_right hη hL)
        · exact t2.trans (mul_le_mul_of_nonneg_right hdA hL)
        · exact t3.trans (mul_le_mul_of_nonneg_right hE hL)
    _ = _ := by ring

/-- **The error bound for `Td`** on `[0, X]` (`J = M + 1`). -/
theorem abs_errdF_le (M : ℕ) (hJ : J = M + 1) {f : ℝ → ℝ} (hf : Continuous f) {X η dA EE : ℝ}
    (hX : 2 * π * X ≤ (2 * M + 1 + 1) / 2)
    (hη : 8 * π * (2 * π * X) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) ≤ η)
    (hdA : ∑ j ∈ range J, |aC j - aR j| * ((2 * j : ℝ) * X ^ (2 * j - 1)) ≤ dA)
    (hE : ∑ j ∈ range J, ∑ k ∈ range J, |Em J B θ aR j k| * ((2 * j : ℝ) * X ^ (2 * j - 1)) ≤ EE)
    {ω : ℝ} (hω : 0 ≤ ω) (hωX : ω ≤ X) :
    |errdF J B θ f ω| ≤ (η + dA + EE) * L1 f := by
  subst hJ
  have hL := L1_nonneg f
  have hid := rankJ_identity (M + 1) B θ aR (fun k => mom k f)
    (fun j => (2 * j : ℝ) * ω ^ (2 * j - 1))
  have hip : ∀ n, ip f (psi (M + 1) B n) = ∑ k ∈ range (M + 1), B n k * mom k f :=
    fun n => ip_psi_right (M + 1) B hf n
  have hps : ∀ n, psid (M + 1) B n ω
      = ∑ j ∈ range (M + 1), B n j * ((2 * j : ℝ) * ω ^ (2 * j - 1)) := fun n => by
    unfold psid; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e : errdF (M + 1) B θ f ω
      = (Td f ω - ∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * mom j f)
        + ∑ j ∈ range (M + 1), (aC j - aR j) * ((2 * j : ℝ) * ω ^ (2 * j - 1)) * mom j f
        + ∑ j ∈ range (M + 1), ∑ k ∈ range (M + 1),
            Em (M + 1) B θ aR j k * mom k f * ((2 * j : ℝ) * ω ^ (2 * j - 1)) := by
    unfold errdF
    simp_rw [hip, hps]
    have hsplit : ∑ j ∈ range (M + 1), (aC j - aR j) * ((2 * j : ℝ) * ω ^ (2 * j - 1)) * mom j f
        = ∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * mom j f
          - ∑ j ∈ range (M + 1), aR j * ((2 * j : ℝ) * ω ^ (2 * j - 1)) * mom j f := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [hsplit, hid]; ring
  have hXω : |ω| ≤ X := by rw [abs_of_nonneg hω]; exact hωX
  have hu : ∀ j ∈ range (M + 1), |(2 * j : ℝ) * ω ^ (2 * j - 1)| ≤ (2 * j : ℝ) * X ^ (2 * j - 1) :=
    fun j _ => by
      rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * j)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hXω _) (by positivity)
  have t1 := Td_sub_le M hf hω hωX hX
  have t2 := abs_weighted_mom_le hf (range (M + 1)) (fun j => aC j - aR j)
    (fun j => (2 * j : ℝ) * ω ^ (2 * j - 1)) (fun j => (2 * j : ℝ) * X ^ (2 * j - 1)) hu
  have t3 := abs_Em_mom_le (M + 1) B θ aR hf (fun j => (2 * j : ℝ) * ω ^ (2 * j - 1))
    (fun j => (2 * j : ℝ) * X ^ (2 * j - 1)) hu
  rw [e]
  calc _ ≤ |Td f ω - ∑ j ∈ range (M + 1), aC j * (2 * j : ℝ) * ω ^ (2 * j - 1) * mom j f|
        + |∑ j ∈ range (M + 1), (aC j - aR j) * ((2 * j : ℝ) * ω ^ (2 * j - 1)) * mom j f|
        + |∑ j ∈ range (M + 1), ∑ k ∈ range (M + 1),
            Em (M + 1) B θ aR j k * mom k f * ((2 * j : ℝ) * ω ^ (2 * j - 1))| :=
        abs_add_three _ _ _
    _ ≤ η * L1 f + dA * L1 f + EE * L1 f := by
        gcongr
        · exact t1.trans (mul_le_mul_of_nonneg_right hη hL)
        · exact t2.trans (mul_le_mul_of_nonneg_right hdA hL)
        · exact t3.trans (mul_le_mul_of_nonneg_right hE hL)
    _ = _ := by ring

end Err

/-! ## C. A unit eigenfunction against the frame: (P1), (P2), (P3). -/

section Eig

variable (J : ℕ) (B : ℕ → ℕ → ℝ) (θ : ℕ → ℝ)

lemma continuous_model (c : ℕ → ℝ) : Continuous (fun ω => ∑ n ∈ range J, c n * psi J B n ω) :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_psi J B n)

lemma continuous_errF {f : ℝ → ℝ} (hf : Continuous f) : Continuous (errF J B θ f) := by
  unfold errF
  exact (continuous_T hf).sub (continuous_model J B fun n => θ n * ip f (psi J B n))

lemma T_eq_model_add (f : ℝ → ℝ) :
    T f = fun ω => (∑ n ∈ range J, θ n * ip f (psi J B n) * psi J B n ω) + errF J B θ f ω := by
  funext ω; unfold errF; ring

lemma sqrt_ip_psi_le {γ : ℝ} (hγ : 0 ≤ γ) {n : ℕ}
    (hG : |ip (psi J B n) (psi J B n) - 1| ≤ γ) : √(ip (psi J B n) (psi J B n)) ≤ 1 + γ := by
  rw [Real.sqrt_le_iff]
  refine ⟨by linarith, ?_⟩
  have := (abs_le.mp hG).2
  nlinarith

/-- (P1). -/
theorem P1 {ξ : ℝ → ℝ} (hξ : Continuous ξ) (hn : ip ξ ξ = 1) {γ : ℝ} (hγ : 0 ≤ γ) {n : ℕ}
    (hG : |ip (psi J B n) (psi J B n) - 1| ≤ γ) : |ip ξ (psi J B n)| ≤ 1 + γ := by
  have h := abs_ip_le hξ (continuous_psi J B n)
  rw [hn, Real.sqrt_one, one_mul] at h
  exact h.trans (sqrt_ip_psi_le J B hγ hG)

/-- `ip (T ξ) g = λ ip ξ g` for an eigenfunction. -/
lemma ip_T_eig {ξ : ℝ → ℝ} {lam : ℝ} (heig : ∀ ω, T ξ ω = lam * ξ ω) (g : ℝ → ℝ) :
    ip (T ξ) g = lam * ip ξ g := by
  rw [show T ξ = fun ω => lam * ξ ω from funext heig, ip_smul_left]

/-- The model part paired with `psi m`. -/
lemma ip_model_psi (c : ℕ → ℝ) (m : ℕ) :
    ip (fun ω => ∑ n ∈ range J, c n * psi J B n ω) (psi J B m)
      = ∑ n ∈ range J, c n * ip (psi J B n) (psi J B m) := by
  rw [ip_sum_left (g := fun n ω => c n * psi J B n ω) _
    (fun n => continuous_const.mul (continuous_psi J B n)) (continuous_psi J B m)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ip_smul_left]

/-- (P2): the residual identity `(λ - θ m) p m = Σ_n θ n p n (G n m - δ) + ip err (psi m)`, bounded. -/
theorem P2 {ξ : ℝ → ℝ} (hξ : Continuous ξ) {lam : ℝ} (heig : ∀ ω, T ξ ω = lam * ξ ω)
    (hn : ip ξ ξ = 1) {γ Θ1 ζ1 ε : ℝ} (hγ : 0 ≤ γ)
    (hG : ∀ n < J, ∀ m < J, |ip (psi J B n) (psi J B m) - if n = m then 1 else 0| ≤ γ)
    (hΘ : ∑ n ∈ range J, |θ n| ≤ Θ1)
    (hζ : ∀ ω ∈ Set.Icc (0 : ℝ) 1, |errF J B θ ξ ω| ≤ ζ1)
    (hε : (γ * Θ1 + ζ1) * (1 + γ) ≤ ε) {m : ℕ} (hm : m < J) :
    |(lam - θ m) * ip ξ (psi J B m)| ≤ ε := by
  set p := fun n => ip ξ (psi J B n) with hp
  have hGd : ∀ n < J, |ip (psi J B n) (psi J B n) - 1| ≤ γ := fun n hn' => by
    simpa using hG n hn' n hn'
  have hpb : ∀ n < J, |p n| ≤ 1 + γ := fun n hn' => P1 J B hξ hn hγ (hGd n hn')
  have e1 := ip_T_eig heig (psi J B m)
  rw [T_eq_model_add J B θ ξ, ip_add_left (continuous_model J B _) (continuous_errF J B θ hξ)
    (continuous_psi J B m), ip_model_psi] at e1
  -- e1 : Σ_n θ n p n G n m + ip err (psi m) = λ p m
  have hsplit : ∑ n ∈ range J, θ n * ip ξ (psi J B n) * ip (psi J B n) (psi J B m)
      = ∑ n ∈ range J, θ n * p n * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0)
        + θ m * p m := by
    have : ∑ n ∈ range J, θ n * p n * (if n = m then (1 : ℝ) else 0) = θ m * p m := by
      rw [Finset.sum_eq_single m]
      · simp
      · intro n _ hnm; simp [hnm]
      · intro h; exact absurd (Finset.mem_range.mpr hm) h
    rw [← this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hp]; ring
  have key : (lam - θ m) * p m
      = ∑ n ∈ range J, θ n * p n * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0)
        + ip (errF J B θ ξ) (psi J B m) := by
    rw [hsplit] at e1; linarith
  have hζ0 : 0 ≤ ζ1 := (abs_nonneg _).trans (hζ 0 ⟨le_rfl, zero_le_one⟩)
  have b1 : |∑ n ∈ range J, θ n * p n * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0)|
      ≤ Θ1 * (1 + γ) * γ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ range J, |θ n * p n * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0)|
        ≤ ∑ n ∈ range J, |θ n| * ((1 + γ) * γ) := by
          refine Finset.sum_le_sum fun n hn' => ?_
          have hn'' := Finset.mem_range.mp hn'
          rw [abs_mul, abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hpb n hn'') (hG n hn'' m hm) (abs_nonneg _) (by linarith)) (abs_nonneg _)
      _ = (∑ n ∈ range J, |θ n|) * ((1 + γ) * γ) := by rw [Finset.sum_mul]
      _ ≤ Θ1 * ((1 + γ) * γ) := mul_le_mul_of_nonneg_right hΘ (by positivity)
      _ = Θ1 * (1 + γ) * γ := by ring
  have b2 : |ip (errF J B θ ξ) (psi J B m)| ≤ ζ1 * (1 + γ) := by
    have h := abs_int_mul_le (continuous_errF J B θ hξ) (continuous_psi J B m) hζ
    have hL := (L1_le_sqrt (continuous_psi J B m)).trans (sqrt_ip_psi_le J B hγ (hGd m hm))
    exact h.trans (mul_le_mul_of_nonneg_left hL hζ0)
  show |(lam - θ m) * p m| ≤ ε
  rw [key]
  refine (abs_add_le _ _).trans ?_
  nlinarith

/-- (P3): the norm inequality. -/
theorem P3 {ξ : ℝ → ℝ} (hξ : Continuous ξ) {lam : ℝ} (heig : ∀ ω, T ξ ω = lam * ξ ω)
    (hn : ip ξ ξ = 1) {γ Θ1 ζ1 C : ℝ} (hγ : 0 ≤ γ)
    (hG : ∀ n < J, ∀ m < J, |ip (psi J B n) (psi J B m) - if n = m then 1 else 0| ≤ γ)
    (hΘ : ∑ n ∈ range J, |θ n| ≤ Θ1)
    (hζ : ∀ ω ∈ Set.Icc (0 : ℝ) 1, |errF J B θ ξ ω| ≤ ζ1)
    (hC : γ * (Θ1 * (1 + γ)) ^ 2 ≤ C) (hlam : ζ1 ≤ |lam|) :
    (|lam| - ζ1) ^ 2 ≤ ∑ n ∈ range J, θ n ^ 2 * ip ξ (psi J B n) ^ 2 + C := by
  set p := fun n => ip ξ (psi J B n) with hp
  set a := fun n => θ n * p n with ha
  have hGd : ∀ n < J, |ip (psi J B n) (psi J B n) - 1| ≤ γ := fun n hn' => by
    simpa using hG n hn' n hn'
  have hpb : ∀ n < J, |p n| ≤ 1 + γ := fun n hn' => P1 J B hξ hn hγ (hGd n hn')
  set v := fun ω => ∑ n ∈ range J, θ n * ip ξ (psi J B n) * psi J B n ω with hv
  have hvc : Continuous v := continuous_model J B _
  have hec := continuous_errF J B θ hξ
  -- |λ| = ‖T ξ‖ ≤ ‖v‖ + ‖err‖ ≤ ‖v‖ + ζ1
  have hTT : ip (T ξ) (T ξ) = lam ^ 2 := by
    rw [ip_T_eig heig, ip_comm, ip_T_eig heig, hn]; ring
  have hmink := sqrt_ip_add_le hvc hec
  rw [← T_eq_model_add J B θ ξ, hTT, Real.sqrt_sq_eq_abs] at hmink
  have hζ0 : 0 ≤ ζ1 := (abs_nonneg _).trans (hζ 0 ⟨le_rfl, zero_le_one⟩)
  have herr : √(ip (errF J B θ ξ) (errF J B θ ξ)) ≤ ζ1 := by
    rw [Real.sqrt_le_left hζ0]
    exact ip_self_le_of_bound hec hζ
  have h1 : |lam| - ζ1 ≤ √(ip v v) := by linarith
  have h2 : (|lam| - ζ1) ^ 2 ≤ ip v v := by
    have := Real.sq_sqrt (ip_self_nonneg v)
    nlinarith [Real.sqrt_nonneg (ip v v)]
  -- ip v v = Σ_n Σ_m a n a m G n m
  have hvv : ip v v = ∑ n ∈ range J, ∑ m ∈ range J, a n * a m * ip (psi J B n) (psi J B m) := by
    rw [hv, ip_sum_left (g := fun n ω => θ n * ip ξ (psi J B n) * psi J B n ω) _
      (fun n => continuous_const.mul (continuous_psi J B n)) hvc]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ip_smul_left, ip_comm (psi J B n) v, hv, ip_model_psi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [ip_comm (psi J B m)]
    simp only [ha, hp]; ring
  have hdiag : ∑ n ∈ range J, ∑ m ∈ range J, a n * a m * (if n = m then (1 : ℝ) else 0)
      = ∑ n ∈ range J, a n ^ 2 := by
    refine Finset.sum_congr rfl fun n hn' => ?_
    rw [Finset.sum_eq_single n]
    · simp; ring
    · intro m _ hmn; simp [Ne.symm hmn]
    · intro h; exact absurd hn' h
  have hoff : ∑ n ∈ range J, ∑ m ∈ range J,
      a n * a m * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0)
        ≤ γ * (∑ n ∈ range J, |a n|) ^ 2 := by
    calc _ ≤ ∑ n ∈ range J, ∑ m ∈ range J, γ * (|a n| * |a m|) := by
          refine Finset.sum_le_sum fun n hn' => Finset.sum_le_sum fun m hm' => ?_
          have := hG n (Finset.mem_range.mp hn') m (Finset.mem_range.mp hm')
          calc a n * a m * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0)
              ≤ |a n * a m * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0)| := le_abs_self _
            _ = |a n| * |a m| * |ip (psi J B n) (psi J B m) - if n = m then 1 else 0| := by
                rw [abs_mul, abs_mul]
            _ ≤ |a n| * |a m| * γ := by gcongr
            _ = γ * (|a n| * |a m|) := by ring
      _ = γ * (∑ n ∈ range J, |a n|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
  have hsa : ∑ n ∈ range J, |a n| ≤ Θ1 * (1 + γ) := by
    calc ∑ n ∈ range J, |a n| ≤ ∑ n ∈ range J, |θ n| * (1 + γ) := by
          refine Finset.sum_le_sum fun n hn' => ?_
          simp only [ha, abs_mul]
          exact mul_le_mul_of_nonneg_left (hpb n (Finset.mem_range.mp hn')) (abs_nonneg _)
      _ = (∑ n ∈ range J, |θ n|) * (1 + γ) := by rw [Finset.sum_mul]
      _ ≤ Θ1 * (1 + γ) := mul_le_mul_of_nonneg_right hΘ (by linarith)
  have hsa0 : 0 ≤ ∑ n ∈ range J, |a n| := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hsq : (∑ n ∈ range J, |a n|) ^ 2 ≤ (Θ1 * (1 + γ)) ^ 2 := pow_le_pow_left₀ hsa0 hsa 2
  have hsplit : ip v v = ∑ n ∈ range J, a n ^ 2 + ∑ n ∈ range J, ∑ m ∈ range J,
      a n * a m * (ip (psi J B n) (psi J B m) - if n = m then 1 else 0) := by
    rw [hvv, ← hdiag, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hsum : ∑ n ∈ range J, a n ^ 2 = ∑ n ∈ range J, θ n ^ 2 * ip ξ (psi J B n) ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha, hp]; ring
  rw [hsum] at hsplit
  nlinarith [mul_le_mul_of_nonneg_left hsq hγ]

/-- An eigenfunction (with `λ ≠ 0`) is differentiable, with `λ ξ' = Td ξ`. -/
theorem hasDerivAt_eig {ξ : ℝ → ℝ} (hξ : Continuous ξ) {lam : ℝ} (hlam : lam ≠ 0)
    (heig : ∀ ω, T ξ ω = lam * ξ ω) (ω : ℝ) : HasDerivAt ξ (Td ξ ω / lam) ω := by
  refine ((hasDerivAt_T hξ ω).div_const lam).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w => ?_)
  show ξ w = T ξ w / lam
  rw [heig]; field_simp

end Eig

/-! ## D. Finite consequences: windows, localization, values, simplicity. -/

section Finite

/-- For `m ≠ n` in a window around `θ n`: `θ m² p m² ≤ θ m² ε² / g²`. -/
lemma sq_le_of_gap {lam θm θn pm ε w : ℝ} (hP2 : |(lam - θm) * pm| ≤ ε)
    (hw : |lam - θn| ≤ w) (hg : 0 < |θn - θm| - w) :
    θm ^ 2 * pm ^ 2 ≤ θm ^ 2 * ε ^ 2 / (|θn - θm| - w) ^ 2 := by
  have hd : |θn - θm| - w ≤ |lam - θm| := by
    have := abs_sub_le θn lam θm
    rw [abs_sub_comm θn lam] at this
    linarith
  have hε : 0 ≤ ε := (abs_nonneg _).trans hP2
  have h1 : (|θn - θm| - w) * |pm| ≤ ε := by
    calc (|θn - θm| - w) * |pm| ≤ |lam - θm| * |pm| :=
          mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = |(lam - θm) * pm| := (abs_mul _ _).symm
      _ ≤ ε := hP2
  have h2 : pm ^ 2 ≤ ε ^ 2 / (|θn - θm| - w) ^ 2 := by
    rw [le_div_iff₀ (by positivity), ← sq_abs pm, ← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (by positivity) h1 2
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)

/-- **One refinement round.**  From a window `|λ - θ n| ≤ w` get `π0 ≤ p n²` and `|λ - θ n| ≤ w1`. -/
theorem round_step {J n : ℕ} (hn : n < J) {θ p : ℕ → ℝ} {lam ε ζ1 C w R π0 w1 : ℝ}
    (hP2 : ∀ m < J, |(lam - θ m) * p m| ≤ ε)
    (hP3 : ζ1 ≤ |lam| → (|lam| - ζ1) ^ 2 ≤ ∑ m ∈ range J, θ m ^ 2 * p m ^ 2 + C)
    (hw : |lam - θ n| ≤ w)
    (hgap : ∀ m < J, m ≠ n → 0 < |θ n - θ m| - w)
    (hR : ∑ m ∈ (range J).erase n, θ m ^ 2 * ε ^ 2 / (|θ n - θ m| - w) ^ 2 ≤ R)
    (hlow : 0 < |θ n| - w - ζ1)
    (hπ : π0 * θ n ^ 2 ≤ (|θ n| - w - ζ1) ^ 2 - R - C)
    (hπ0 : 0 < π0) (hw1 : ε ^ 2 ≤ w1 ^ 2 * π0) (hw10 : 0 ≤ w1) (hζ0 : 0 ≤ ζ1) :
    π0 ≤ p n ^ 2 ∧ |lam - θ n| ≤ w1 := by
  have hθn : 0 < θ n ^ 2 := by
    have : 0 < |θ n| := by
      have := abs_nonneg (lam - θ n); have := (abs_nonneg _).trans hw; linarith
    have : θ n ≠ 0 := fun h => by simp [h] at this
    positivity
  have hsum : ∑ m ∈ (range J).erase n, θ m ^ 2 * p m ^ 2 ≤ R := by
    refine le_trans (Finset.sum_le_sum fun m hm => ?_) hR
    have hm' := Finset.mem_erase.mp hm
    exact sq_le_of_gap (hP2 m (Finset.mem_range.mp hm'.2)) hw
      (hgap m (Finset.mem_range.mp hm'.2) hm'.1)
  have hsplit := Finset.add_sum_erase (range J) (fun m => θ m ^ 2 * p m ^ 2)
    (Finset.mem_range.mpr hn)
  have hl : |θ n| - w ≤ |lam| := by
    have := abs_sub_abs_le_abs_sub (θ n) lam
    rw [abs_sub_comm] at this; linarith
  have h3 := hP3 (by linarith)
  have h4 : (|θ n| - w - ζ1) ^ 2 ≤ (|lam| - ζ1) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hp : π0 ≤ p n ^ 2 := by
    have : π0 * θ n ^ 2 ≤ θ n ^ 2 * p n ^ 2 := by linarith
    nlinarith
  refine ⟨hp, ?_⟩
  have h5 := hP2 n hn
  have h6 : (lam - θ n) ^ 2 * p n ^ 2 ≤ ε ^ 2 := by
    rw [← mul_pow, ← sq_abs ((lam - θ n) * p n)]
    exact pow_le_pow_left₀ (abs_nonneg _) h5 2
  have h7 : (lam - θ n) ^ 2 * π0 ≤ w1 ^ 2 * π0 := by
    nlinarith [sq_nonneg (lam - θ n)]
  have h8 : (lam - θ n) ^ 2 ≤ w1 ^ 2 := le_of_mul_le_mul_right h7 hπ0
  by_contra hc
  push Not at hc
  nlinarith [sq_abs (lam - θ n), abs_nonneg (lam - θ n)]

/-- **Localization.**  Outside every window, `|λ| ≤ δ0`. -/
theorem localize {J Nc : ℕ} {θ p w : ℕ → ℝ} {lam ε ζ1 C δ0 θc SA : ℝ}
    (hP2 : ∀ m < J, |(lam - θ m) * p m| ≤ ε)
    (hP3 : ζ1 ≤ |lam| → (|lam| - ζ1) ^ 2 ≤ ∑ m ∈ range J, θ m ^ 2 * p m ^ 2 + C)
    (hout : ∀ n ≤ Nc, w n < |lam - θ n|) (hw0 : ∀ n ≤ Nc, 0 < w n)
    (hcut : ∀ m < J, Nc < m → |θ m| ≤ θc) (hδ : θc < δ0) (hζ : ζ1 ≤ δ0)
    (hSA : ∑ m ∈ range J, (if m ≤ Nc then θ m ^ 2 * ε ^ 2 / w m ^ 2
      else θ m ^ 2 * ε ^ 2 / (δ0 - θc) ^ 2) ≤ SA)
    (hfin : SA + C < (δ0 - ζ1) ^ 2) :
    |lam| ≤ δ0 := by
  by_contra hcon
  push Not at hcon
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hP2 0 (by
    by_contra h0; push Not at h0
    have : J = 0 := by omega
    subst this
    have := hP3 (by linarith)
    simp at this
    nlinarith))
  have hterm : ∀ m ∈ range J, θ m ^ 2 * p m ^ 2 ≤ (if m ≤ Nc then θ m ^ 2 * ε ^ 2 / w m ^ 2
      else θ m ^ 2 * ε ^ 2 / (δ0 - θc) ^ 2) := by
    intro m hm
    have hm' := Finset.mem_range.mp hm
    split_ifs with h
    · have := sq_le_of_gap (lam := lam) (θn := lam) (θm := θ m) (pm := p m) (w := 0)
        (hP2 m hm') (by simp) (by
          rw [sub_zero]; exact (hw0 m h).trans (hout m h))
      refine this.trans ?_
      rw [sub_zero]
      apply div_le_div_of_nonneg_left (by positivity) (by have := hw0 m h; positivity)
      exact pow_le_pow_left₀ (hw0 m h).le (hout m h).le 2
    · push Not at h
      have hc := hcut m hm' h
      have hg : δ0 - θc ≤ |lam - θ m| := by
        have := abs_sub_abs_le_abs_sub lam (θ m)
        linarith
      have := sq_le_of_gap (lam := lam) (θn := lam) (θm := θ m) (pm := p m) (w := 0)
        (hP2 m hm') (by simp) (by rw [sub_zero]; linarith)
      refine this.trans ?_
      rw [sub_zero]
      apply div_le_div_of_nonneg_left (by positivity) (by nlinarith)
      exact pow_le_pow_left₀ (by linarith) hg 2
  have h1 := hP3 (by linarith)
  have h2 : ∑ m ∈ range J, θ m ^ 2 * p m ^ 2 ≤ SA := (Finset.sum_le_sum hterm).trans hSA
  have h3 : (δ0 - ζ1) ^ 2 < (|lam| - ζ1) ^ 2 := by
    apply pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
  linarith

/-- `|p - s| ≤ 1 - π1 + γ` for the sign `s` of `p`, when `π1 ≤ p²` and `|p| ≤ 1 + γ`. -/
lemma abs_sub_sign_le {pn π1 γ : ℝ} (hπ : π1 ≤ pn ^ 2) (hπ1 : π1 ≤ 1) (hγ : 0 ≤ γ)
    (hp : |pn| ≤ 1 + γ) :
    |pn - (if 0 ≤ pn then 1 else -1)| ≤ 1 - π1 + γ := by
  have key : |(|pn| - 1)| ≤ 1 - π1 + γ := by
    rcases le_total (|pn|) 1 with h | h
    · have h0 := abs_nonneg pn
      have : pn ^ 2 ≤ |pn| := by rw [← sq_abs]; nlinarith
      rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  split_ifs with h
  · rwa [abs_of_nonneg h] at key
  · push Not at h
    rw [abs_of_neg h] at key
    rw [show pn - -1 = -(-pn - 1) by ring, abs_neg]; exact key

/-- **Values.**  `|val - s θ n ψv n| ≤ V` from the model expansion of `val`. -/
theorem value_bound {J n : ℕ} (hn : n < J) {θ p ψv Ψ : ℕ → ℝ} {lam ε γ π1 w2 ζ V err val s : ℝ}
    (hval : val = ∑ m ∈ range J, θ m * p m * ψv m + err) (herr : |err| ≤ ζ)
    (hψ : ∀ m < J, |ψv m| ≤ Ψ m)
    (hP2 : ∀ m < J, |(lam - θ m) * p m| ≤ ε)
    (hw2 : |lam - θ n| ≤ w2) (hgap : ∀ m < J, m ≠ n → 0 < |θ n - θ m| - w2)
    (hs : |p n - s| ≤ 1 - π1 + γ)
    (hV : |θ n| * (1 - π1 + γ) * Ψ n
      + ∑ m ∈ (range J).erase n, |θ m| * (ε / (|θ n - θ m| - w2)) * Ψ m + ζ ≤ V) :
    |val - s * θ n * ψv n| ≤ V := by
  have hsplit := Finset.add_sum_erase (range J) (fun m => θ m * p m * ψv m)
    (Finset.mem_range.mpr hn)
  have e : val - s * θ n * ψv n = θ n * (p n - s) * ψv n
      + ∑ m ∈ (range J).erase n, θ m * p m * ψv m + err := by
    rw [hval, ← hsplit]; ring
  have hΨn : |ψv n| ≤ Ψ n := hψ n hn
  have hs0 : 0 ≤ 1 - π1 + γ := (abs_nonneg _).trans hs
  have hΨ0 : 0 ≤ Ψ n := (abs_nonneg _).trans hΨn
  have b1 : |θ n * (p n - s) * ψv n| ≤ |θ n| * (1 - π1 + γ) * Ψ n := by
    rw [abs_mul, abs_mul]
    gcongr
  have b2 : |∑ m ∈ (range J).erase n, θ m * p m * ψv m|
      ≤ ∑ m ∈ (range J).erase n, |θ m| * (ε / (|θ n - θ m| - w2)) * Ψ m := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    have hm' := Finset.mem_erase.mp hm
    have hmJ := Finset.mem_range.mp hm'.2
    have hg := hgap m hmJ hm'.1
    have hd : |θ n - θ m| - w2 ≤ |lam - θ m| := by
      have := abs_sub_le (θ n) lam (θ m)
      rw [abs_sub_comm (θ n) lam] at this
      linarith
    have hp : |p m| ≤ ε / (|θ n - θ m| - w2) := by
      rw [le_div_iff₀ hg]
      calc |p m| * (|θ n - θ m| - w2) ≤ |p m| * |lam - θ m| :=
            mul_le_mul_of_nonneg_left hd (abs_nonneg _)
        _ = |(lam - θ m) * p m| := by rw [abs_mul]; ring
        _ ≤ ε := hP2 m hmJ
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hP2 m hmJ)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (abs_nonneg _)) (hψ m hmJ) (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (div_nonneg hε0 hg.le))
  rw [e]
  calc _ ≤ |θ n * (p n - s) * ψv n| + |∑ m ∈ (range J).erase n, θ m * p m * ψv m| + |err| :=
        abs_add_three _ _ _
    _ ≤ _ := by linarith

/-! ## E. Simplicity: one eigenfunction per window. -/

lemma ip_sub_smul_sub_smul {f g h k : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) (hk : Continuous k) (a b : ℝ) :
    ip (fun x => f x - a * g x) (fun x => h x - b * k x)
      = ip f h - b * ip f k - a * ip g h + a * b * ip g k := by
  unfold ip
  have e : (fun x => (f x - a * g x) * (h x - b * k x))
      = fun x => f x * h x - b * (f x * k x) - a * (g x * h x) + (a * b) * (g x * k x) := by
    funext x; ring
  have i1 : IntervalIntegrable (fun x => f x * h x) volume 0 1 := ii (hf.mul hh)
  have i2 : IntervalIntegrable (fun x => f x * k x) volume 0 1 := ii (hf.mul hk)
  have i3 : IntervalIntegrable (fun x => g x * h x) volume 0 1 := ii (hg.mul hh)
  have i4 : IntervalIntegrable (fun x => g x * k x) volume 0 1 := ii (hg.mul hk)
  rw [e, intervalIntegral.integral_add ((i1.sub (i2.const_mul _)).sub (i3.const_mul _))
      (i4.const_mul _), intervalIntegral.integral_sub (i1.sub (i2.const_mul _)) (i3.const_mul _),
    intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- **Simplicity.**  Two unit vectors that both have overlap `p² ≥ π1` with the same nearly unit
`ψ` (`|ip ψ ψ - 1| ≤ γ`) are not orthogonal once `π1 (1 - γ) > 1/2`. -/
theorem ip_ne_zero_of_overlap {ξ η ψ : ℝ → ℝ} (hξ : Continuous ξ) (hη : Continuous η)
    (hψ : Continuous ψ) (hξn : ip ξ ξ = 1) (hηn : ip η η = 1) {γ π1 : ℝ} (hγ1 : γ < 1)
    (hG : |ip ψ ψ - 1| ≤ γ) (hp : π1 ≤ ip ξ ψ ^ 2) (hq : π1 ≤ ip η ψ ^ 2)
    (hhalf : 1 / 2 < π1 * (1 - γ)) : ip ξ η ≠ 0 := by
  set p := ip ξ ψ
  set q := ip η ψ
  set G := ip ψ ψ
  have hGl : 1 - γ ≤ G := by have := (abs_le.mp hG).1; linarith
  have hGu : G ≤ 1 + γ := by have := (abs_le.mp hG).2; linarith
  have huu : ip (fun x => ξ x - p * ψ x) (fun x => ξ x - p * ψ x) ≤ 1 - π1 * (1 - γ) := by
    rw [ip_sub_smul_sub_smul hξ hψ hξ hψ, hξn, ip_comm ψ ξ]
    nlinarith
  have hvv : ip (fun x => η x - q * ψ x) (fun x => η x - q * ψ x) ≤ 1 - π1 * (1 - γ) := by
    rw [ip_sub_smul_sub_smul hη hψ hη hψ, hηn, ip_comm ψ η]
    nlinarith
  have huv := ip_sub_smul_sub_smul hξ hψ hη hψ p q
  rw [ip_comm ψ η] at huv
  have hcs := ip_sq_le (f := fun x => ξ x - p * ψ x) (g := fun x => η x - q * ψ x)
    (hξ.sub (continuous_const.mul hψ)) (hη.sub (continuous_const.mul hψ))
  set U := ip (fun x => ξ x - p * ψ x) (fun x => ξ x - p * ψ x)
  set V := ip (fun x => η x - q * ψ x) (fun x => η x - q * ψ x)
  have hU0 : 0 ≤ U := ip_self_nonneg _
  have hV0 : 0 ≤ V := ip_self_nonneg _
  set d := 1 - π1 * (1 - γ)
  have hd0 : 0 ≤ d := hU0.trans huu
  have hUV : U * V ≤ d ^ 2 := by nlinarith
  have hpq : π1 ≤ |p * q| := by
    have h1 : π1 ^ 2 ≤ (p * q) ^ 2 := by
      have : 0 ≤ π1 := by nlinarith
      rw [mul_pow]; nlinarith
    have : 0 ≤ π1 := by nlinarith
    rw [← sq_abs (p * q)] at h1
    nlinarith [abs_nonneg (p * q)]
  intro h0
  rw [h0] at huv
  -- ip u v = - p q (2 - G)
  have key : ip (fun x => ξ x - p * ψ x) (fun x => η x - q * ψ x) = -(p * q * (2 - G)) := by
    rw [huv]; ring
  rw [key] at hcs
  have h2G : 1 - γ ≤ 2 - G := by linarith
  have hlow : π1 * (1 - γ) ≤ |p * q * (2 - G)| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 - G)]
    exact mul_le_mul hpq h2G (by linarith) (abs_nonneg _)
  have : (π1 * (1 - γ)) ^ 2 ≤ (p * q * (2 - G)) ^ 2 := by
    rw [← sq_abs (p * q * (2 - G))]
    exact pow_le_pow_left₀ (by nlinarith) hlow 2
  nlinarith

end Finite

end ArchS9

end
