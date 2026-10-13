/-
  ArchS10_Tail -- stage S10, part 2: the TAIL n > 12 of CC's series (98)/(99), unconditionally.

  For an orthonormal family of continuous eigenfunctions e_k of S9's operator T whose eigenvalues
  satisfy |λ_k| ≤ d0Q ≈ 9.70e-22 (this is what every eigenvalue outside S9's 13 windows satisfies),
  and every finite set S of indices,
      Σ_{k∈S} (T e_k (ω))²  ≤ AQ  ≈ 5.8e-9    (ω ∈ [0, 2]),
      Σ_{k∈S} (Td e_k (ω))² ≤ AdQ ≈ 9.9e-7    (ω ∈ [0, 2]),
      Σ_{k∈S} (T e_k (ω))²  ≤ A1Q ≈ 1.2e-22   (ω ∈ [0, 1]).
  Since T e_k = λ_k e_k, these are Bessel-type bounds on Σ λ_k² e_k(ω)², uniform in ω.  The proof
  uses only S9's rank-40 frame:
      T f (ω) = Σ_m θ_m ⟨f, ψ_m⟩ ψ_m(ω) + ⟨f, E_ω⟩,     ‖E_ω‖² ≤ ζ²        (errF as an inner product),
      (λ - θ_m) ⟨e, ψ_m⟩ = ⟨e, T ψ_m - θ_m ψ_m⟩,       ‖T ψ_m - θ_m ψ_m‖ ≤ rhoQ (S9's residual),
  a weighted Cauchy-Schwarz over the 41 pieces, and Bessel's inequality for each piece.  No sup
  bound M_n on ξ_n (S8's open item 5, S6's obligation) is needed for these numbers.
  Consequence (`tail_CC_sum_le`): Σ_{k∈S} |C(T e_k, Td e_k)(t)| / (1 - λ_k²) ≤ tauQ ≈ 6.4e-6 on
  t ∈ [0, log 2], i.e. the whole tail of Σ w_n C_n.
  No sorry, no axiom.  conjecture1_proved = False.
-/
import ArchS10_Exact
import ArchS9_Bridge
import ArchS10_Cert

open MeasureTheory Set Finset
open scoped Interval

noncomputable section

namespace ArchS10

open ArchS9

/-! ## Unpacking the tail checks. -/

/-- The real form of `Data.Abnd`. -/
def AbndR (Ψ : ℕ → ℝ) (ζ : ℝ) (c : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range (Data.Jd + 1), c i) *
    ((∑ m ∈ range Data.Jd, (if m ≤ Data.NCw then thR m ^ 2 * Ψ m ^ 2 * (Data.rhoQ : ℝ) ^ 2
        / ((|thR m| - Data.d0Q) ^ 2 * c m) else thR m ^ 2 * Ψ m ^ 2 * (1 + Data.gamQ) / c m))
      + ζ ^ 2 / c Data.Jd)

lemma Abnd_cast (Ψ : ℕ → ℚ) (ζ : ℚ) (c : ℕ → ℚ) :
    ((ArchS10.Data.Abnd Ψ ζ c : ℚ) : ℝ) = AbndR (fun m => (Ψ m : ℝ)) ζ (fun i => (c i : ℝ)) := by
  unfold ArchS10.Data.Abnd AbndR thR
  push_cast
  congr 2
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> push_cast <;> rfl

lemma tail_facts :
    (∀ i < Data.Jd + 1, (0 : ℝ) < ArchS10.Data.cA i ∧ (0 : ℝ) < ArchS10.Data.cAd i ∧
      (0 : ℝ) < ArchS10.Data.cA1 i) ∧
    (∀ m ≤ Data.NCw, (Data.d0Q : ℝ) < |thR m|) ∧
    AbndR (fun m => (Data.PsiQ m : ℝ)) Data.zeta2Q (fun i => (ArchS10.Data.cA i : ℝ))
      ≤ ArchS10.Data.AQ ∧
    AbndR (fun m => (Data.PsidQ m : ℝ)) Data.zetad2Q (fun i => (ArchS10.Data.cAd i : ℝ))
      ≤ ArchS10.Data.AdQ ∧
    AbndR (fun m => (Data.Psi1Q m : ℝ)) Data.zeta1Q (fun i => (ArchS10.Data.cA1 i : ℝ))
      ≤ ArchS10.Data.A1Q ∧
    (Data.d0Q : ℝ) < 1 ∧
    (4 * (ArchS10.Data.AdQ : ℝ) + (ArchS10.Data.AdQ + ArchS10.Data.AQ) / 2
        + 2 * (ArchS10.Data.AQ + ArchS10.Data.AdQ)) / (1 - (Data.d0Q : ℝ) ^ 2)
      ≤ ArchS10.Data.tauQ ∧
    (ArchS10.Data.A1Q : ℝ) / (1 - (Data.d0Q : ℝ) ^ 2) ≤ ArchS10.Data.tauE := by
  have h := ArchS10.Data.tail_ok
  simp only [ArchS10.Data.tailOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, hd⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun i hi => ?_, fun m hm => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨⟨a, b⟩, c⟩ := hc i hi
    exact ⟨by exact_mod_cast a, by exact_mod_cast b, by exact_mod_cast c⟩
  · have := hd m (Nat.lt_succ_of_le hm); unfold thR; exact_mod_cast this
  · rw [← Abnd_cast]; exact_mod_cast h1
  · rw [← Abnd_cast]; exact_mod_cast h2
  · rw [← Abnd_cast]; exact_mod_cast h3
  · exact_mod_cast h4
  · have := (Rat.cast_le (K := ℝ)).2 h5; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).2 h6; push_cast at this; exact this

/-! ## The frame pieces as inner products. -/

/-- The residual of the certified ψ_m. -/
def res (m : ℕ) : ℝ → ℝ := fun x => T (psiS m) x - thR m * psiS m x

lemma continuous_psiS (m : ℕ) : Continuous (psiS m) := continuous_psi Data.Jd BR m

lemma continuous_res (m : ℕ) : Continuous (res m) :=
  (continuous_T (continuous_psiS m)).sub (continuous_const.mul (continuous_psiS m))

lemma ip_res_self {m : ℕ} (hm : m < Data.Jd) : ip (res m) (res m) ≤ (Data.rhoQ : ℝ) ^ 2 :=
  ip_self_le_of_bound (continuous_res m) fun _ hω => psi_residual hm hω

lemma ip_res_eig {φ : ℝ → ℝ} {lam : ℝ} (hφ : Continuous φ) (heig : ∀ ω, T φ ω = lam * φ ω)
    (m : ℕ) : ip φ (res m) = (lam - thR m) * ip φ (psiS m) := by
  have hψ := continuous_psiS m
  have h1 : ip (res m) φ = ip (T (psiS m)) φ - thR m * ip (psiS m) φ :=
    ip_sub_smul_left (continuous_T hψ) hψ hφ (thR m)
  have h2 : ip (T (psiS m)) φ = lam * ip (psiS m) φ := by
    rw [T_symm hψ hφ, show T φ = fun ω => lam * φ ω from funext heig, ip_comm, ip_smul_left,
      ip_comm]
  rw [ip_comm, h1, h2, ip_comm (psiS m) φ]; ring

/-- The error row of the rank-40 model of `T` at `ω`. -/
def Erow (ω : ℝ) : ℝ → ℝ := fun x => K ω x - ∑ m ∈ range Data.Jd, thR m * psiS m ω * psiS m x
/-- The error row of the rank-40 model of `Td` at `ω`. -/
def Edrow (ω : ℝ) : ℝ → ℝ := fun x => Kd ω x - ∑ m ∈ range Data.Jd, thR m * psidS m ω * psiS m x

lemma continuous_Erow (ω : ℝ) : Continuous (Erow ω) := by
  unfold Erow K
  exact (by fun_prop : Continuous fun x => 2 * Real.cos (2 * Real.pi * x * ω)).sub
    (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_psiS m))

lemma continuous_Edrow (ω : ℝ) : Continuous (Edrow ω) := by
  unfold Edrow Kd
  exact (by fun_prop : Continuous fun x => -(4 * Real.pi * x * Real.sin (2 * Real.pi * x * ω))).sub
    (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_psiS m))

lemma errF_eq_ip {f : ℝ → ℝ} (hf : Continuous f) (ω : ℝ) :
    errF Data.Jd BR thR f ω = ip f (Erow ω) := by
  unfold errF Erow ip T
  have e : (fun x => f x * (K ω x - ∑ m ∈ range Data.Jd, thR m * psiS m ω * psiS m x))
      = fun x => K ω x * f x - ∑ m ∈ range Data.Jd, thR m * psiS m ω * (f x * psiS m x) := by
    funext x; rw [mul_sub, Finset.mul_sum]; congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  rw [e, intervalIntegral.integral_sub, intervalIntegral.integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_const_mul]
    unfold psiS; ring
  all_goals first
    | (intro m _; exact ii (continuous_const.mul (hf.mul (continuous_psiS m))))
    | exact ii (by unfold K; fun_prop)
    | exact ii (continuous_finsetSum _ fun m _ => continuous_const.mul (hf.mul (continuous_psiS m)))

lemma errdF_eq_ip {f : ℝ → ℝ} (hf : Continuous f) (ω : ℝ) :
    errdF Data.Jd BR thR f ω = ip f (Edrow ω) := by
  unfold errdF Edrow ip Td
  have e : (fun x => f x * (Kd ω x - ∑ m ∈ range Data.Jd, thR m * psidS m ω * psiS m x))
      = fun x => Kd ω x * f x - ∑ m ∈ range Data.Jd, thR m * psidS m ω * (f x * psiS m x) := by
    funext x; rw [mul_sub, Finset.mul_sum]; congr 1
    · ring
    · exact Finset.sum_congr rfl fun m _ => by ring
  rw [e, intervalIntegral.integral_sub, intervalIntegral.integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_const_mul]
    unfold psiS psidS; ring
  all_goals first
    | (intro m _; exact ii (continuous_const.mul (hf.mul (continuous_psiS m))))
    | exact ii (by unfold Kd; fun_prop)
    | exact ii (continuous_finsetSum _ fun m _ => continuous_const.mul (hf.mul (continuous_psiS m)))

/-- `‖E‖² ≤ ζ²` from `|⟨E, E⟩| ≤ ζ ‖E‖₁`. -/
lemma ip_le_sq_of {E : ℝ → ℝ} (hE : Continuous E) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (h : |ip E E| ≤ ζ * L1 E) : ip E E ≤ ζ ^ 2 := by
  have hL := L1_le_sqrt hE
  have hs := Real.sq_sqrt (ip_self_nonneg E)
  have hs0 := Real.sqrt_nonneg (ip E E)
  set s := √(ip E E)
  have h1 : s ^ 2 ≤ ζ * s := by
    rw [hs]; exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_left hL hζ))
  have h2 : s ≤ ζ := by
    rcases eq_or_lt_of_le hs0 with h0 | h0
    · rw [← h0]; exact hζ
    · nlinarith
  rw [← hs]; exact pow_le_pow_left₀ hs0 h2 2

/-! ## The generic tail bound. -/

/-- The hypotheses on the tail family. -/
structure TailFam (e : ℕ → ℝ → ℝ) (lamk : ℕ → ℝ) : Prop where
  cont : ∀ k, Continuous (e k)
  eig : ∀ k ω, T (e k) ω = lamk k * e k ω
  orth : ∀ k l, ip (e k) (e l) = if k = l then 1 else 0
  small : ∀ k, |lamk k| ≤ (Data.d0Q : ℝ)

lemma sum_sq_mul_le {S : Finset ℕ} {a b : ℕ → ℝ} {α : ℝ} (ha : ∀ k, |a k| ≤ α) :
    ∑ k ∈ S, (a k * b k) ^ 2 ≤ α ^ 2 * ∑ k ∈ S, b k ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mul_pow, ← sq_abs (a k)]
  have := ha k
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) this 2) (sq_nonneg _)

/-- **The generic tail bound.**  `val k` is either `T (e k) ω` (with `v m = ψ_m(ω)`) or
`Td (e k) ω` (with `v m = ψ_m'(ω)`); `E` is the corresponding error row. -/
theorem tail_sum_le {e : ℕ → ℝ → ℝ} {lamk : ℕ → ℝ} (hF : TailFam e lamk) (S : Finset ℕ)
    (val v Ψ : ℕ → ℝ) (hv : ∀ m, |v m| ≤ Ψ m) {E : ℝ → ℝ} (hE : Continuous E) {ζ : ℝ}
    (hEE : ip E E ≤ ζ ^ 2)
    (hval : ∀ k, val k = (∑ m ∈ range Data.Jd, thR m * ip (e k) (psiS m) * v m) + ip (e k) E)
    (c : ℕ → ℝ) (hc : ∀ i < Data.Jd + 1, 0 < c i) :
    ∑ k ∈ S, val k ^ 2 ≤ AbndR Ψ ζ c := by
  obtain ⟨-, hd, -, -, -, -, -, -⟩ := tail_facts
  have hJ : Data.Jd = 40 := rfl
  -- the 41 pieces
  set Z : ℕ → ℕ → ℝ := fun k i => if i < Data.Jd then
      (if i ≤ Data.NCw then thR i * v i / (lamk k - thR i) * ip (e k) (res i)
        else thR i * v i * ip (e k) (psiS i)) else ip (e k) E with hZ
  have hgap : ∀ k, ∀ i ≤ Data.NCw, |thR i| - Data.d0Q ≤ |lamk k - thR i| := fun k i hi => by
    have := abs_sub_abs_le_abs_sub (thR i) (lamk k)
    rw [abs_sub_comm] at this; linarith [hF.small k]
  have hgap0 : ∀ i ≤ Data.NCw, 0 < |thR i| - Data.d0Q := fun i hi => by linarith [hd i hi]
  have hsplit : ∀ k, val k = ∑ i ∈ range (Data.Jd + 1), Z k i := fun k => by
    rw [Finset.sum_range_succ, hval k]
    simp only [hZ, lt_irrefl, if_false]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos (Finset.mem_range.mp hi)]
    split_ifs with h12
    · have hne : lamk k - thR i ≠ 0 := fun h0 => by
        have := hgap k i h12; rw [h0, abs_zero] at this; linarith [hgap0 i h12]
      rw [ip_res_eig (hF.cont k) (hF.eig k) i]
      field_simp
    · ring
  -- per-piece Bessel bounds
  set Bd : ℕ → ℝ := fun i => if i < Data.Jd then
      (if i ≤ Data.NCw then thR i ^ 2 * Ψ i ^ 2 * (Data.rhoQ : ℝ) ^ 2 / (|thR i| - Data.d0Q) ^ 2
        else thR i ^ 2 * Ψ i ^ 2 * (1 + Data.gamQ)) else ζ ^ 2 with hBd
  have hbes : ∀ r : ℝ → ℝ, Continuous r → ∑ k ∈ S, ip (e k) r ^ 2 ≤ ip r r := fun r hr => by
    have := bessel_finite e hF.cont hF.orth hr S
    simpa only [ip_comm r] using this
  have hpiece : ∀ i < Data.Jd + 1, ∑ k ∈ S, Z k i ^ 2 ≤ Bd i := by
    intro i hi
    by_cases hiJ : i < Data.Jd
    · simp only [hZ, hBd, if_pos hiJ]
      split_ifs with h12
      · have ha : ∀ k, |thR i * v i / (lamk k - thR i)| ≤ |thR i| * Ψ i / (|thR i| - Data.d0Q) :=
          fun k => by
            rw [abs_div, abs_mul]
            have hΨ := hv i
            have hden := hgap k i h12
            have h0 := hgap0 i h12
            rw [div_le_div_iff₀ (lt_of_lt_of_le h0 hden) h0]
            have hΨ0 : 0 ≤ Ψ i := (abs_nonneg _).trans hΨ
            calc |thR i| * |v i| * (|thR i| - Data.d0Q) ≤ |thR i| * Ψ i * (|thR i| - Data.d0Q) := by
                  gcongr
              _ ≤ |thR i| * Ψ i * |lamk k - thR i| := by gcongr
        refine (sum_sq_mul_le ha).trans ?_
        have hb := (hbes (res i) (continuous_res i)).trans (ip_res_self hiJ)
        have : (|thR i| * Ψ i / (|thR i| - Data.d0Q)) ^ 2
            = thR i ^ 2 * Ψ i ^ 2 / (|thR i| - Data.d0Q) ^ 2 := by
          rw [div_pow, mul_pow, sq_abs]
        rw [this]
        calc thR i ^ 2 * Ψ i ^ 2 / (|thR i| - Data.d0Q) ^ 2 * ∑ k ∈ S, ip (e k) (res i) ^ 2
            ≤ thR i ^ 2 * Ψ i ^ 2 / (|thR i| - Data.d0Q) ^ 2 * (Data.rhoQ : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = _ := by ring
      · have ha : ∀ _k : ℕ, |thR i * v i| ≤ |thR i| * Ψ i := fun _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
        refine (sum_sq_mul_le ha).trans ?_
        have hG := gram_sound hiJ hiJ
        simp only [if_true] at hG
        have hγ : ip (psiS i) (psiS i) ≤ 1 + Data.gamQ := by
          have := (abs_le.mp hG).2; linarith
        have hb := (hbes (psiS i) (continuous_psiS i)).trans hγ
        rw [mul_pow, sq_abs]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    · have hi40 : i = Data.Jd := by omega
      simp only [hZ, hBd, if_neg hiJ]
      exact (hbes E hE).trans hEE
  -- weighted Cauchy-Schwarz per k, then swap
  have hcs : ∀ k, val k ^ 2 ≤ (∑ i ∈ range (Data.Jd + 1), c i)
      * ∑ i ∈ range (Data.Jd + 1), Z k i ^ 2 / c i := fun k => by
    have hpos : 0 < ∑ i ∈ range (Data.Jd + 1), c i :=
      Finset.sum_pos (fun i hi => hc i (Finset.mem_range.mp hi)) ⟨0, by simp⟩
    have := Finset.sq_sum_div_le_sum_sq_div (range (Data.Jd + 1)) (Z k)
      (fun i hi => hc i (Finset.mem_range.mp hi))
    rw [hsplit k]
    rwa [div_le_iff₀ hpos, mul_comm] at this
  calc ∑ k ∈ S, val k ^ 2
      ≤ ∑ k ∈ S, (∑ i ∈ range (Data.Jd + 1), c i) * ∑ i ∈ range (Data.Jd + 1), Z k i ^ 2 / c i :=
        Finset.sum_le_sum fun k _ => hcs k
    _ = (∑ i ∈ range (Data.Jd + 1), c i) * ∑ i ∈ range (Data.Jd + 1), (∑ k ∈ S, Z k i ^ 2) / c i := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_div]
    _ ≤ (∑ i ∈ range (Data.Jd + 1), c i) * ∑ i ∈ range (Data.Jd + 1), Bd i / c i := by
        have hpos : 0 ≤ ∑ i ∈ range (Data.Jd + 1), c i :=
          Finset.sum_nonneg (fun i hi => (hc i (Finset.mem_range.mp hi)).le)
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hpos
        have hi' := Finset.mem_range.mp hi
        exact div_le_div_of_nonneg_right (hpiece i hi') (hc i hi').le
    _ = AbndR Ψ ζ c := by
        unfold AbndR
        congr 1
        rw [Finset.sum_range_succ]
        simp only [hBd, lt_irrefl, if_false]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [if_pos (Finset.mem_range.mp hi)]
        split_ifs <;> field_simp

/-! ## The three instances. -/

lemma abs_psiS_le_two (m : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h2 : ω ≤ 2) : |psiS m ω| ≤ (Data.PsiQ m : ℝ) := by
  have hxa : |ω| ≤ 2 := by rw [abs_of_nonneg h0]; exact h2
  refine (abs_psi_le Data.Jd BR m hxa).trans (le_of_eq ?_)
  unfold Data.PsiQ BR; push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_mul]; norm_num

lemma abs_psidS_le_two (m : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h2 : ω ≤ 2) :
    |psidS m ω| ≤ (Data.PsidQ m : ℝ) := by
  have hxa : |ω| ≤ 2 := by rw [abs_of_nonneg h0]; exact h2
  refine (abs_psid_le Data.Jd BR m hxa).trans (le_of_eq ?_)
  unfold Data.PsidQ BR; push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma abs_psiS_le_one (m : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1) : |psiS m ω| ≤ (Data.Psi1Q m : ℝ) := by
  have hxa : |ω| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  refine (abs_psi_le Data.Jd BR m hxa).trans (le_of_eq ?_)
  unfold Data.Psi1Q BR; push_cast; simp

lemma T_eq_frame {f : ℝ → ℝ} (hf : Continuous f) (ω : ℝ) :
    T f ω = (∑ m ∈ range Data.Jd, thR m * ip f (psiS m) * psiS m ω) + ip f (Erow ω) := by
  rw [← errF_eq_ip hf]; unfold errF psiS; ring

lemma Td_eq_frame {f : ℝ → ℝ} (hf : Continuous f) (ω : ℝ) :
    Td f ω = (∑ m ∈ range Data.Jd, thR m * ip f (psiS m) * psidS m ω) + ip f (Edrow ω) := by
  rw [← errdF_eq_ip hf]; unfold errdF psiS psidS; ring

lemma ip_Erow_two {ω : ℝ} (h0 : 0 ≤ ω) (h2 : ω ≤ 2) :
    ip (Erow ω) (Erow ω) ≤ (Data.zeta2Q : ℝ) ^ 2 := by
  have hz : (0 : ℝ) ≤ Data.zeta2Q := by
    have : (0 : ℚ) ≤ Data.zeta2Q := by unfold Data.zeta2Q; norm_num
    exact_mod_cast this
  refine ip_le_sq_of (continuous_Erow ω) hz ?_
  rw [← errF_eq_ip (continuous_Erow ω)]
  exact errF_le_two (continuous_Erow ω) h0 h2

lemma ip_Erow_one {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :
    ip (Erow ω) (Erow ω) ≤ (Data.zeta1Q : ℝ) ^ 2 := by
  have hz : (0 : ℝ) ≤ Data.zeta1Q := by
    have : (0 : ℚ) ≤ Data.zeta1Q := by unfold Data.zeta1Q; norm_num
    exact_mod_cast this
  refine ip_le_sq_of (continuous_Erow ω) hz ?_
  rw [← errF_eq_ip (continuous_Erow ω)]
  exact errF_le_one (continuous_Erow ω) h0 h1

lemma ip_Edrow_two {ω : ℝ} (h0 : 0 ≤ ω) (h2 : ω ≤ 2) :
    ip (Edrow ω) (Edrow ω) ≤ (Data.zetad2Q : ℝ) ^ 2 := by
  have hz : (0 : ℝ) ≤ Data.zetad2Q := by
    have : (0 : ℚ) ≤ Data.zetad2Q := by unfold Data.zetad2Q; norm_num
    exact_mod_cast this
  refine ip_le_sq_of (continuous_Edrow ω) hz ?_
  rw [← errdF_eq_ip (continuous_Edrow ω)]
  exact errdF_le_two (continuous_Edrow ω) h0 h2

variable {e : ℕ → ℝ → ℝ} {lamk : ℕ → ℝ}

theorem tail_T_sq_two (hF : TailFam e lamk) (S : Finset ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h2 : ω ≤ 2) :
    ∑ k ∈ S, T (e k) ω ^ 2 ≤ (ArchS10.Data.AQ : ℝ) := by
  obtain ⟨hc, -, hA, -⟩ := tail_facts
  exact (tail_sum_le hF S (fun k => T (e k) ω) (fun m => psiS m ω) (fun m => (Data.PsiQ m : ℝ))
    (fun m => abs_psiS_le_two m h0 h2) (continuous_Erow ω) (ip_Erow_two h0 h2)
    (fun k => T_eq_frame (hF.cont k) ω) _ (fun i hi => (hc i hi).1)).trans hA

theorem tail_Td_sq_two (hF : TailFam e lamk) (S : Finset ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h2 : ω ≤ 2) :
    ∑ k ∈ S, Td (e k) ω ^ 2 ≤ (ArchS10.Data.AdQ : ℝ) := by
  obtain ⟨hc, -, -, hA, -⟩ := tail_facts
  exact (tail_sum_le hF S (fun k => Td (e k) ω) (fun m => psidS m ω) (fun m => (Data.PsidQ m : ℝ))
    (fun m => abs_psidS_le_two m h0 h2) (continuous_Edrow ω) (ip_Edrow_two h0 h2)
    (fun k => Td_eq_frame (hF.cont k) ω) _ (fun i hi => (hc i hi).2.1)).trans hA

theorem tail_T_sq_one (hF : TailFam e lamk) (S : Finset ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :
    ∑ k ∈ S, T (e k) ω ^ 2 ≤ (ArchS10.Data.A1Q : ℝ) := by
  obtain ⟨hc, -, -, -, hA, -⟩ := tail_facts
  exact (tail_sum_le hF S (fun k => T (e k) ω) (fun m => psiS m ω) (fun m => (Data.Psi1Q m : ℝ))
    (fun m => abs_psiS_le_one m h0 h1) (continuous_Erow ω) (ip_Erow_one h0 h1)
    (fun k => T_eq_frame (hF.cont k) ω) _ (fun i hi => (hc i hi).2.2)).trans hA

/-! ## The tail of CC's series. -/

lemma sum_abs_mul_le {S : Finset ℕ} {u w : ℕ → ℝ} {A B : ℝ} (hu : ∑ k ∈ S, u k ^ 2 ≤ A)
    (hw : ∑ k ∈ S, w k ^ 2 ≤ B) : ∑ k ∈ S, |u k| * |w k| ≤ (A + B) / 2 := by
  have : ∑ k ∈ S, |u k| * |w k| ≤ ∑ k ∈ S, (u k ^ 2 + w k ^ 2) / 2 :=
    Finset.sum_le_sum fun k _ => by
      nlinarith [sq_nonneg (|u k| - |w k|), sq_abs (u k), sq_abs (w k)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at this
  linarith

/-- Pointwise bound of one `CC` term by its three pieces. -/
lemma abs_CC_pieces (f f' : ℝ → ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ Real.log 2) :
    |CC f f' t| ≤ 2 * (∫ x in (Real.exp (-t))..1,
        |(x * f' x) * (Real.exp t * x * f' (Real.exp t * x))|)
      + |f' (Real.exp (-t))| * |f 1| + 4 * (|f 1| * |f' (Real.exp t)|) := by
  have hi1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hI := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun x => (x * f' x) * (Real.exp t * x * f' (Real.exp t * x))) hi1
  have hc1 := exp_half_le_two ht0 ht
  have hc2 := exp_neg_three_half_le_one ht0
  have hc3 := exp_three_half_le_four ht0 ht
  have p1 := Real.exp_pos (t / 2)
  have p2 := Real.exp_pos (-(3 / 2) * t)
  have p3 := Real.exp_pos ((3 / 2) * t)
  have hInn : 0 ≤ ∫ x in (Real.exp (-t))..1, |(x * f' x) * (Real.exp t * x * f' (Real.exp t * x))| :=
    intervalIntegral.integral_nonneg hi1 fun x _ => abs_nonneg _
  unfold CC
  calc _ ≤ |Real.exp (t / 2) * (∫ x in (Real.exp (-t))..1, (x * f' x) * (Real.exp t * x * f' (Real.exp t * x)))|
        + |Real.exp (-(3 / 2) * t) * f' (Real.exp (-t)) * f 1|
        + |Real.exp ((3 / 2) * t) * f 1 * f' (Real.exp t)| := by
        refine (abs_sub _ _).trans ?_
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos p1, abs_of_pos p2, abs_of_pos p3]
        have a1 : Real.exp (t / 2) * |∫ x in (Real.exp (-t))..1, (x * f' x) * (Real.exp t * x * f' (Real.exp t * x))|
            ≤ 2 * ∫ x in (Real.exp (-t))..1, |(x * f' x) * (Real.exp t * x * f' (Real.exp t * x))| :=
          mul_le_mul hc1 hI (abs_nonneg _) (by norm_num)
        have a2 : Real.exp (-(3 / 2) * t) * |f' (Real.exp (-t))| * |f 1| ≤ |f' (Real.exp (-t))| * |f 1| := by
          have := mul_nonneg (abs_nonneg (f' (Real.exp (-t)))) (abs_nonneg (f 1))
          nlinarith
        have a3 : Real.exp ((3 / 2) * t) * |f 1| * |f' (Real.exp t)| ≤ 4 * (|f 1| * |f' (Real.exp t)|) := by
          have := mul_nonneg (abs_nonneg (f 1)) (abs_nonneg (f' (Real.exp t)))
          nlinarith
        linarith

/-- **The tail of Σ w_n C_n**: for the tail family, Σ_{k∈S} |C(λφ, λφ')(t)|/(1 - λ²) ≤ tauQ. -/
theorem tail_CC_sum_le (hF : TailFam e lamk) (S : Finset ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ Real.log 2) :
    ∑ k ∈ S, |CC (T (e k)) (Td (e k)) t| / (1 - lamk k ^ 2) ≤ (ArchS10.Data.tauQ : ℝ) := by
  obtain ⟨-, -, -, -, -, hd1, hτ, -⟩ := tail_facts
  have hρ := exp_le_two ht
  have hρ1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.2 ht0
  have hi := half_le_exp_neg ht
  have hi1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hd0 : (0 : ℝ) ≤ Data.d0Q := (abs_nonneg _).trans (hF.small 0)
  have hden : 0 < 1 - (Data.d0Q : ℝ) ^ 2 := by nlinarith
  set A := (ArchS10.Data.AQ : ℝ)
  set Ad := (ArchS10.Data.AdQ : ℝ)
  have cT : ∀ k, Continuous (T (e k)) := fun k => continuous_T (hF.cont k)
  have cTd : ∀ k, Continuous (Td (e k)) := fun k => continuous_Td (hF.cont k)
  -- integral part
  have hint : ∑ k ∈ S, (∫ x in (Real.exp (-t))..1,
      |(x * Td (e k) x) * (Real.exp t * x * Td (e k) (Real.exp t * x))|) ≤ 2 * Ad := by
    rw [← intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable; have := cTd k; fun_prop)]
    have hb := intervalIntegral.integral_mono_on (μ := volume) (a := Real.exp (-t)) (b := 1)
      (f := fun x => ∑ k ∈ S, |(x * Td (e k) x) * (Real.exp t * x * Td (e k) (Real.exp t * x))|)
      (g := fun _ => 2 * Ad) hi1
      (by apply Continuous.intervalIntegrable
          exact continuous_finsetSum _ fun k _ => by have := cTd k; fun_prop)
      intervalIntegrable_const (fun x hx => ?_)
    · refine hb.trans ?_
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have : 0 ≤ Ad := (Finset.sum_nonneg (fun k _ => sq_nonneg _)).trans
        (tail_Td_sq_two hF ∅ (by norm_num : (0 : ℝ) ≤ 0) (by norm_num))
      nlinarith [Real.exp_pos (-t)]
    · obtain ⟨hx1, hx2⟩ := hx
      have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
      have hρx2 : Real.exp t * x ≤ 2 := by nlinarith
      have hxx : x * (Real.exp t * x) ≤ 2 := by nlinarith
      have e1 : ∀ k, |(x * Td (e k) x) * (Real.exp t * x * Td (e k) (Real.exp t * x))|
          = (x * (Real.exp t * x)) * (|Td (e k) x| * |Td (e k) (Real.exp t * x)|) := fun k => by
        rw [show (x * Td (e k) x) * (Real.exp t * x * Td (e k) (Real.exp t * x))
            = (x * (Real.exp t * x)) * (Td (e k) x * Td (e k) (Real.exp t * x)) by ring,
          abs_mul (x * (Real.exp t * x)), abs_of_pos (by positivity : 0 < x * (Real.exp t * x)),
          abs_mul]
      simp only [e1]
      rw [← Finset.mul_sum]
      have hs := sum_abs_mul_le (tail_Td_sq_two hF S hx0.le (by linarith))
        (tail_Td_sq_two hF S (by positivity) hρx2)
      have hs0 : 0 ≤ ∑ k ∈ S, |Td (e k) x| * |Td (e k) (Real.exp t * x)| :=
        Finset.sum_nonneg fun k _ => by positivity
      calc x * (Real.exp t * x) * ∑ k ∈ S, |Td (e k) x| * |Td (e k) (Real.exp t * x)|
          ≤ 2 * ((Ad + Ad) / 2) := mul_le_mul hxx hs hs0 (by norm_num)
        _ = 2 * Ad := by ring
  have hb1 := sum_abs_mul_le (tail_Td_sq_two hF S (Real.exp_pos _).le (by linarith))
    (tail_T_sq_two hF S (by norm_num : (0 : ℝ) ≤ 1) (by norm_num))
  have hb2 := sum_abs_mul_le (tail_T_sq_two hF S (by norm_num : (0 : ℝ) ≤ 1) (by norm_num))
    (tail_Td_sq_two hF S (by linarith) hρ)
  have hsum : ∑ k ∈ S, |CC (T (e k)) (Td (e k)) t|
      ≤ 4 * Ad + (Ad + A) / 2 + 2 * (A + Ad) := by
    calc ∑ k ∈ S, |CC (T (e k)) (Td (e k)) t|
        ≤ ∑ k ∈ S, (2 * (∫ x in (Real.exp (-t))..1,
            |(x * Td (e k) x) * (Real.exp t * x * Td (e k) (Real.exp t * x))|)
          + |Td (e k) (Real.exp (-t))| * |T (e k) 1| + 4 * (|T (e k) 1| * |Td (e k) (Real.exp t)|)) :=
          Finset.sum_le_sum fun k _ => abs_CC_pieces _ _ ht0 ht
      _ = 2 * ∑ k ∈ S, (∫ x in (Real.exp (-t))..1,
            |(x * Td (e k) x) * (Real.exp t * x * Td (e k) (Real.exp t * x))|)
          + ∑ k ∈ S, |Td (e k) (Real.exp (-t))| * |T (e k) 1|
          + 4 * ∑ k ∈ S, |T (e k) 1| * |Td (e k) (Real.exp t)| := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ ≤ 2 * (2 * Ad) + (Ad + A) / 2 + 4 * ((A + Ad) / 2) := by gcongr
      _ = _ := by ring
  have hterm : ∀ k ∈ S, |CC (T (e k)) (Td (e k)) t| / (1 - lamk k ^ 2)
      ≤ |CC (T (e k)) (Td (e k)) t| / (1 - (Data.d0Q : ℝ) ^ 2) := fun k _ => by
    have hl := hF.small k
    have : lamk k ^ 2 ≤ (Data.d0Q : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
    exact div_le_div_of_nonneg_left (abs_nonneg _) hden (by linarith)
  calc _ ≤ ∑ k ∈ S, |CC (T (e k)) (Td (e k)) t| / (1 - (Data.d0Q : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (∑ k ∈ S, |CC (T (e k)) (Td (e k)) t|) / (1 - (Data.d0Q : ℝ) ^ 2) := by rw [Finset.sum_div]
    _ ≤ (4 * Ad + (Ad + A) / 2 + 2 * (A + Ad)) / (1 - (Data.d0Q : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hsum hden.le
    _ ≤ _ := hτ

/-- **The tail of ε'(1⁺)**: Σ_{k∈S} (λ_k e_k(1))²/(1 - λ_k²) ≤ tauE ≈ 1.2e-22. -/
theorem tail_eps_sum_le (hF : TailFam e lamk) (S : Finset ℕ) :
    ∑ k ∈ S, T (e k) 1 ^ 2 / (1 - lamk k ^ 2) ≤ (ArchS10.Data.tauE : ℝ) := by
  obtain ⟨-, -, -, -, -, hd1, -, hτ⟩ := tail_facts
  have hd0 : (0 : ℝ) ≤ Data.d0Q := (abs_nonneg _).trans (hF.small 0)
  have hden : 0 < 1 - (Data.d0Q : ℝ) ^ 2 := by nlinarith
  have hA := tail_T_sq_one hF S (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  calc _ ≤ ∑ k ∈ S, T (e k) 1 ^ 2 / (1 - (Data.d0Q : ℝ) ^ 2) := Finset.sum_le_sum fun k _ => by
        have hl := hF.small k
        have : lamk k ^ 2 ≤ (Data.d0Q : ℝ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hl 2
        exact div_le_div_of_nonneg_left (sq_nonneg _) hden (by linarith)
    _ = (∑ k ∈ S, T (e k) 1 ^ 2) / (1 - (Data.d0Q : ℝ) ^ 2) := by rw [Finset.sum_div]
    _ ≤ (ArchS10.Data.A1Q : ℝ) / (1 - (Data.d0Q : ℝ) ^ 2) := div_le_div_of_nonneg_right hA hden.le
    _ ≤ _ := hτ

end ArchS10
