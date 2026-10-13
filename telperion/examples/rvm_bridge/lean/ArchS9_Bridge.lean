/-
  ArchS9_Bridge -- the interface of the certified prolate engine with stages S6-S10
  (archimedean stage S9, rvm_bridge island, 2026-10-11).

  1. `continuous_representative` (L²/L¹ -> continuous).  If ξ is only interval-integrable on [0,1]
     (e.g. a representative of an element of Lp 2 on (0,1), as stages S5/S6 produce) and
     T ξ = λ ξ almost everywhere on (0,1] with λ ≠ 0, then ξc := T ξ / λ is continuous, satisfies
     T ξc = λ ξc EVERYWHERE, agrees with ξ a.e. on (0,1], and has the same norm ip ξc ξc = ip ξ ξ.
     So every theorem of ArchS9_Prolate applies to S6's eigenvectors through ξc.
  2. `T_symm` : ip (T f) g = ip f (T g) for continuous f, g (Fubini on [0,1]², symmetric kernel).
  3. `psi_residual` : sup_[0,1] |T ψ_n - θ_n ψ_n| ≤ rhoQ ≈ 6.72e-43.
  4. COMPLETENESS (`prolate_spectrum_complete`).  For any orthonormal family of continuous
     eigenfunctions (e k, λ k) of T for which ψ_n satisfies Parseval (true for a complete
     eigenbasis of L²(0,1), S6), and for every n ≤ 12, EXACTLY ONE index k has λ k in window n;
     every λ k outside the 13 windows has |λ k| ≤ d0Q ≈ 9.70e-22.

  Dictionary to CC (arXiv:2006.13771 (66)-(68)), for later stages:
    * CC's even prolate PS on [-1,1] with ∫_{-1}^{1} PS(x) e^{2πixω} dx = λ(n) PS(ω) is, restricted
      to [0,1], an eigenfunction of `T` with eigenvalue λ(n) (for even PS the exponential integral
      is ∫_0^1 2 cos(2πxω) PS(x) dx);  CC's ξ_n = PS/‖PS‖ with ‖·‖² = ∫_0^1 |·|² is `ip ξ ξ = 1`;
    * the eigenvalues here are CC's signed λ(n) (θ_0 > 0, θ_1 < 0, ...), not λ(n)²;
      P₁ P̂₁ P₁ restricted to even functions has eigenvalues λ(n)² (CC after (68)), with the same
      eigenvectors;
    * values for ω ∈ (1, 2] are those of the entire extension ω ↦ (T ξ)(ω)/λ, which is CC's
      ξ_n(ω) there (CC use the same extension via (68)).
  conjecture1_proved = False.  No `sorry`.
-/
import ArchS9_Prolate
import ArchS9_CertRes

noncomputable section

namespace ArchS9

open Real Finset MeasureTheory intervalIntegral Set
open scoped Interval

lemma ip_sub_smul_left {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (a : ℝ) : ip (fun x => f x - a * g x) h = ip f h - a * ip g h := by
  unfold ip
  have e : (fun x => (f x - a * g x) * h x) = fun x => f x * h x - a * (g x * h x) := by
    funext x; ring
  have i1 : IntervalIntegrable (fun x => f x * h x) volume 0 1 := ii (hf.mul hh)
  have i2 : IntervalIntegrable (fun x => g x * h x) volume 0 1 := ii (hg.mul hh)
  rw [e, intervalIntegral.integral_sub i1 (i2.const_mul a), intervalIntegral.integral_const_mul]

/-! ## 1. Continuous representatives. -/

lemma continuous_K_left (x : ℝ) : Continuous fun ω => K ω x := by unfold K; fun_prop

theorem continuous_T_of_integrable {ξ : ℝ → ℝ} (hξ : IntervalIntegrable ξ volume 0 1) :
    Continuous (T ξ) := by
  unfold T
  refine intervalIntegral.continuous_of_dominated_interval (bound := fun x => 2 * |ξ x|)
    (fun ω => ?_) (fun ω => Filter.Eventually.of_forall fun x _ => ?_) ((hξ.abs).const_mul 2)
    (Filter.Eventually.of_forall fun x _ => (continuous_K_left x).mul continuous_const)
  · exact ((by unfold K; fun_prop : Continuous fun x => K ω x).aestronglyMeasurable).mul
      hξ.def'.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    unfold K
    rw [abs_mul, abs_two]
    have := Real.abs_cos_le_one (2 * π * x * ω)
    nlinarith [abs_nonneg (ξ x)]

/-- **The bridge lemma.**  An integrable a.e.-eigenfunction has a continuous everywhere-eigenfunction
representative with the same norm. -/
theorem continuous_representative {ξ : ℝ → ℝ} {lam : ℝ} (hξ : IntervalIntegrable ξ volume 0 1)
    (hlam : lam ≠ 0) (hae : ∀ᵐ x ∂volume, x ∈ Ι (0 : ℝ) 1 → T ξ x = lam * ξ x) :
    Continuous (fun ω => T ξ ω / lam) ∧
    (∀ ω, T (fun w => T ξ w / lam) ω = lam * (T ξ ω / lam)) ∧
    (∀ᵐ x ∂volume, x ∈ Ι (0 : ℝ) 1 → T ξ x / lam = ξ x) ∧
    ip (fun w => T ξ w / lam) (fun w => T ξ w / lam) = ip ξ ξ := by
  have hc := continuous_T_of_integrable hξ
  have hae' : ∀ᵐ x ∂volume, x ∈ Ι (0 : ℝ) 1 → T ξ x / lam = ξ x :=
    hae.mono fun x hx hmem => by rw [hx hmem]; field_simp
  refine ⟨hc.div_const lam, fun ω => ?_, hae', ?_⟩
  · have h1 : T (fun w => T ξ w / lam) ω = T ξ ω := by
      show (∫ x in (0 : ℝ)..1, K ω x * (T ξ x / lam)) = ∫ x in (0 : ℝ)..1, K ω x * ξ x
      exact intervalIntegral.integral_congr_ae
        (hae'.mono fun x hx hmem => by rw [hx hmem])
    rw [h1]; field_simp
  · show (∫ x in (0 : ℝ)..1, (T ξ x / lam) * (T ξ x / lam)) = ∫ x in (0 : ℝ)..1, ξ x * ξ x
    exact intervalIntegral.integral_congr_ae (hae'.mono fun x hx hmem => by rw [hx hmem])

/-! ## 2. Symmetry of `T`. -/

lemma K_symm (ω x : ℝ) : K ω x = K x ω := by unfold K; ring_nf

theorem T_symm {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ip (T f) g = ip f (T g) := by
  unfold ip T
  have e1 : (fun ω => (∫ x in (0 : ℝ)..1, K ω x * f x) * g ω)
      = fun ω => ∫ x in (0 : ℝ)..1, K ω x * f x * g ω := by
    funext ω; rw [← intervalIntegral.integral_mul_const]
  have e2 : (fun x => f x * ∫ ω in (0 : ℝ)..1, K x ω * g ω)
      = fun x => ∫ ω in (0 : ℝ)..1, K ω x * f x * g ω := by
    funext x; rw [← intervalIntegral.integral_const_mul]
    congr 1; funext ω; rw [K_symm]; ring
  rw [e1, e2]
  simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  have hcont : Continuous (Function.uncurry fun ω x => K ω x * f x * g ω) := by
    unfold Function.uncurry K; fun_prop
  have hint : Integrable (Function.uncurry fun ω x => K ω x * f x * g ω)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  exact integral_integral_swap hint

/-! ## 3. The residual of the certified ψ_n. -/

lemma res_facts : Data.gamQ * (∑ m ∈ range Data.Jd, |Data.thq m| * Data.Psi1Q m)
      + Data.zeta1Q * (1 + Data.gamQ) ≤ Data.rhoQ ∧
    ∀ n ≤ Data.NCw, Data.rhoQ ^ 2 < Data.w0q n ^ 2 * (1 - Data.gamQ) := by
  have h := Data.res_ok
  simp only [Data.resOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  exact ⟨h.1, fun n hn => h.2 n (Nat.lt_succ_of_le hn)⟩

theorem psi_residual {n : ℕ} (hn : n < Data.Jd) {ω : ℝ} (hω : ω ∈ Icc (0 : ℝ) 1) :
    |T (psiS n) ω - thR n * psiS n ω| ≤ (Data.rhoQ : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hγ0, -, hz0⟩ := const_facts
  have hγ : (0 : ℝ) ≤ Data.gamQ := by exact_mod_cast hγ0
  have hz : (0 : ℝ) ≤ Data.zeta1Q := by exact_mod_cast hz0
  have hc := continuous_psi Data.Jd BR n
  have hω' : |ω| ≤ 1 := by rw [abs_of_nonneg hω.1]; exact hω.2
  -- T ψ_n = Σ_m θ_m G_nm ψ_m + err
  have e : T (psiS n) ω - thR n * psiS n ω
      = ∑ m ∈ range Data.Jd, thR m * (ip (psiS n) (psiS m) - if n = m then 1 else 0) * psiS m ω
        + errF Data.Jd BR thR (psiS n) ω := by
    have hsum : ∑ m ∈ range Data.Jd, thR m * (if n = m then (1 : ℝ) else 0) * psiS m ω
        = thR n * psiS n ω := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro m _ hmn; simp [Ne.symm hmn]
      · intro h; exact absurd (Finset.mem_range.mpr hn) h
    have h2 : ∑ m ∈ range Data.Jd, thR m * (ip (psiS n) (psiS m) - if n = m then 1 else 0) * psiS m ω
        = ∑ m ∈ range Data.Jd, thR m * ip (psiS n) (psiS m) * psiS m ω - thR n * psiS n ω := by
      rw [← hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [h2]
    unfold errF psiS
    ring
  rw [e]
  have hL : L1 (psiS n) ≤ 1 + Data.gamQ := by
    have hG := gram_sound hn hn
    simp only [if_true] at hG
    exact (L1_le_sqrt hc).trans (sqrt_ip_psi_le Data.Jd BR hγ hG)
  have herr := errF_le_one hc hω.1 hω.2
  have b1 : |∑ m ∈ range Data.Jd, thR m * (ip (psiS n) (psiS m) - if n = m then 1 else 0)
      * psiS m ω| ≤ Data.gamQ * ∑ m ∈ range Data.Jd, |thR m| * (Data.Psi1Q m : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hG := gram_sound hn (Finset.mem_range.mp hm)
    have hψ : |psiS m ω| ≤ (Data.Psi1Q m : ℝ) := by
      refine (abs_psi_le Data.Jd BR m hω').trans (le_of_eq ?_)
      unfold Data.Psi1Q BR; push_cast; simp
    rw [abs_mul, abs_mul]
    calc |thR m| * |ip (psiS n) (psiS m) - if n = m then 1 else 0| * |psiS m ω|
        ≤ |thR m| * Data.gamQ * (Data.Psi1Q m : ℝ) := by gcongr
      _ = _ := by ring
  have hres := res_facts.1
  have hres' : (Data.gamQ : ℝ) * (∑ m ∈ range Data.Jd, |thR m| * (Data.Psi1Q m : ℝ))
      + Data.zeta1Q * (1 + Data.gamQ) ≤ Data.rhoQ := by
    unfold thR; exact_mod_cast hres
  calc _ ≤ |∑ m ∈ range Data.Jd, thR m * (ip (psiS n) (psiS m) - if n = m then 1 else 0)
        * psiS m ω| + |errF Data.Jd BR thR (psiS n) ω| := abs_add_le _ _
    _ ≤ Data.gamQ * ∑ m ∈ range Data.Jd, |thR m| * (Data.Psi1Q m : ℝ)
        + Data.zeta1Q * (1 + Data.gamQ) := by
        gcongr
        exact herr.trans (mul_le_mul_of_nonneg_left hL hz)
    _ ≤ _ := hres'

/-! ## 4. Completeness. -/

/-- Finite Bessel inequality for an orthonormal family. -/
lemma bessel_finite {ι : Type*} [DecidableEq ι] (e : ι → ℝ → ℝ) (he : ∀ k, Continuous (e k))
    (horth : ∀ k l, ip (e k) (e l) = if k = l then 1 else 0) {r : ℝ → ℝ} (hr : Continuous r)
    (S : Finset ι) : ∑ k ∈ S, ip r (e k) ^ 2 ≤ ip r r := by
  set v := fun x => ∑ k ∈ S, ip r (e k) * e k x with hv
  have hvc : Continuous v := continuous_finsetSum _ fun k _ => continuous_const.mul (he k)
  have h0 := ip_self_nonneg (fun x => r x - 1 * v x)
  rw [ip_sub_smul_self hr hvc] at h0
  have hrv : ip r v = ∑ k ∈ S, ip r (e k) ^ 2 := by
    rw [ip_comm, hv, ip_sum_left (g := fun k x => ip r (e k) * e k x) _
      (fun k => continuous_const.mul (he k)) hr]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ip_smul_left, ip_comm]; ring
  have hvv : ip v v = ∑ k ∈ S, ip r (e k) ^ 2 := by
    rw [hv, ip_sum_left (g := fun k x => ip r (e k) * e k x) _
      (fun k => continuous_const.mul (he k)) hvc]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [ip_smul_left, ip_comm (e k) v, hv, ip_sum_left (g := fun k x => ip r (e k) * e k x) _
      (fun k => continuous_const.mul (he k)) (he k)]
    rw [Finset.sum_eq_single k]
    · rw [ip_smul_left, horth]; simp; ring
    · intro l _ hlk; rw [ip_smul_left, horth, if_neg hlk]; ring
    · intro h; exact absurd hk h
  rw [hrv, hvv] at h0
  nlinarith

/-- **Every certified window is occupied** by an eigenvalue of any orthonormal eigenfamily for
which `ψ_n` satisfies Parseval. -/
theorem prolate_window_occupied {ι : Type*} [DecidableEq ι] (e : ι → ℝ → ℝ) (lamk : ι → ℝ)
    (he : ∀ k, Continuous (e k)) (heig : ∀ k ω, T (e k) ω = lamk k * e k ω)
    (horth : ∀ k l, ip (e k) (e l) = if k = l then 1 else 0) {n : ℕ} (hnN : n ≤ Data.NCw)
    (hpar : HasSum (fun k => ip (psiS n) (e k) ^ 2) (ip (psiS n) (psiS n))) :
    ∃ k, |lamk k - thR n| ≤ (Data.w0q n : ℝ) := by
  have hnJ : n < Data.Jd := lt_of_le_of_lt hnN (by decide)
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hγ0, hγ1, -⟩ := const_facts
  have hc : Continuous (psiS n) := continuous_psi Data.Jd BR n
  set r := fun ω => T (psiS n) ω - thR n * psiS n ω with hr
  have hrc : Continuous r := (continuous_T hc).sub (continuous_const.mul hc)
  have hrr : ip r r ≤ (Data.rhoQ : ℝ) ^ 2 := ip_self_le_of_bound hrc fun ω hω => psi_residual hnJ hω
  have hrk : ∀ k, ip r (e k) = (lamk k - thR n) * ip (psiS n) (e k) := fun k => by
    have h1 : ip r (e k) = ip (T (psiS n)) (e k) - thR n * ip (psiS n) (e k) :=
      ip_sub_smul_left (continuous_T hc) hc (he k) (thR n)
    rw [h1, T_symm hc (he k)]
    rw [show T (e k) = fun ω => lamk k * e k ω from funext (heig k), ip_comm, ip_smul_left,
      ip_comm]
    ring
  have hw0 : (0 : ℝ) < Data.w0q n := by
    have h := Data.loc_ok
    simp only [Data.locOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at h
    exact_mod_cast h.2 n (Nat.lt_succ_of_le hnN)
  have hS : ∀ S : Finset ι, ∑ k ∈ S, ip (psiS n) (e k) ^ 2 ≤ (Data.rhoQ : ℝ) ^ 2 / (Data.w0q n) ^ 2 := by
    intro S
    rw [le_div_iff₀ (by positivity), Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) ((bessel_finite e he horth hrc S).trans hrr)
    rw [hrk, mul_pow]
    have := hcon k
    have h2 : (Data.w0q n : ℝ) ^ 2 ≤ (lamk k - thR n) ^ 2 := by
      rw [← sq_abs (lamk k - thR n)]; exact pow_le_pow_left₀ hw0.le this.le 2
    nlinarith [sq_nonneg (ip (psiS n) (e k))]
  have htsum := Real.tsum_le_of_sum_le (fun k => sq_nonneg _) hS
  rw [hpar.tsum_eq] at htsum
  have hG := gram_sound hnJ hnJ
  simp only [if_true] at hG
  have hGl : 1 - (Data.gamQ : ℝ) ≤ ip (psiS n) (psiS n) := by
    have := (abs_le.mp hG).1; linarith
  have hfin := res_facts.2 n hnN
  have hfin' : (Data.rhoQ : ℝ) ^ 2 < (Data.w0q n : ℝ) ^ 2 * (1 - Data.gamQ) := by exact_mod_cast hfin
  have : ip (psiS n) (psiS n) * (Data.w0q n : ℝ) ^ 2 ≤ (Data.rhoQ : ℝ) ^ 2 := by
    rwa [le_div_iff₀ (by positivity)] at htsum
  nlinarith

/-- **Completeness of the certified spectrum.**  For an orthonormal family of continuous unit
eigenfunctions of `T` for which every `ψ_n` (n ≤ 12) satisfies Parseval:
  (a) every eigenvalue is either `|λ k| ≤ d0Q ≈ 9.70e-22` or in one of the 13 windows;
  (b) every window contains EXACTLY ONE index k (no eigenvalue missing, none doubled);
  (c) that eigenvalue is within `w2q n ≈ 6.73e-43` of θ_n, and `e k` is certified by
      `prolate_window`. -/
theorem prolate_spectrum_complete {ι : Type*} [DecidableEq ι] (e : ι → ℝ → ℝ) (lamk : ι → ℝ)
    (he : ∀ k, Continuous (e k)) (heig : ∀ k ω, T (e k) ω = lamk k * e k ω)
    (horth : ∀ k l, ip (e k) (e l) = if k = l then 1 else 0)
    (hpar : ∀ n ≤ Data.NCw, HasSum (fun k => ip (psiS n) (e k) ^ 2) (ip (psiS n) (psiS n))) :
    (∀ k, |lamk k| ≤ (Data.d0Q : ℝ) ∨ ∃ n ≤ Data.NCw, |lamk k - thR n| ≤ (Data.w0q n : ℝ)) ∧
    (∀ n ≤ Data.NCw, ∃! k, |lamk k - thR n| ≤ (Data.w0q n : ℝ)) ∧
    (∀ n ≤ Data.NCw, ∀ k, |lamk k - thR n| ≤ (Data.w0q n : ℝ) → |lamk k - thR n| ≤ (Data.w2q n : ℝ)) := by
  have hn1 : ∀ k, ip (e k) (e k) = 1 := fun k => by rw [horth]; simp
  refine ⟨fun k => prolate_localization (he k) (heig k) (hn1 k), fun n hnN => ?_,
    fun n hnN k hk => (prolate_window (he k) (heig k) (hn1 k) hnN hk).1⟩
  obtain ⟨k, hk⟩ := prolate_window_occupied e lamk he heig horth hnN (hpar n hnN)
  refine ⟨k, hk, fun l hl => ?_⟩
  by_contra hlk
  have := prolate_simple (he l) (heig l) (hn1 l) (he k) (heig k) (hn1 k) hnN hl hk
  rw [horth, if_neg hlk] at this
  exact this rfl

/-! ## 5. The fields of S8's `ProlateData` (arda-arch-s8, ArchS8_ProlateData.lean), n ≤ 12. -/

/-- Kernel check: every certified eigenvalue has |θ n| + w2q n < 1, so λ(n)² < 1. -/
def Data.lamOK : Bool :=
  (List.range (Data.NCw + 1)).all fun n => decide (|Data.thq n| + Data.w2q n < 1)

set_option maxRecDepth 100000 in
theorem Data.lam_ok : Data.lamOK = true := by decide +kernel

/-- Sup bound for |ξ| on [0, 2] in window n. -/
def Data.MxQ (n : ℕ) : ℚ := (|Data.thq n| * Data.PsiQ n + Data.Vq n) / (|Data.thq n| - Data.w0q n)
/-- Sup bound for |ξ'| on [0, 2] in window n. -/
def Data.MdQ (n : ℕ) : ℚ := (|Data.thq n| * Data.PsidQ n + Data.Vdq n) / (|Data.thq n| - Data.w0q n)

/-- **S8 interface.**  A continuous unit eigenfunction ξ of `T` with eigenvalue in window n
(n ≤ 12) supplies the S8 fields: λ² < 1, ξ is C¹ on ℝ (it is its own analytic continuation
T ξ / λ), and on [0, 2] (which contains [e^{-T}, 1] ∪ [1, e^T] for T ≤ log 2)
|ξ| ≤ MxQ n and |ξ'| ≤ MdQ n. -/
theorem prolate_S8_fields {ξ : ℝ → ℝ} {lam : ℝ} (hξ : Continuous ξ)
    (heig : ∀ ω, T ξ ω = lam * ξ ω) (hn : ip ξ ξ = 1) {n : ℕ} (hnN : n ≤ Data.NCw)
    (hw : |lam - thR n| ≤ (Data.w0q n : ℝ)) :
    lam ^ 2 < 1 ∧ ContDiff ℝ 1 ξ ∧
      ∀ x ∈ Icc (0 : ℝ) 2, |ξ x| ≤ (Data.MxQ n : ℝ) ∧ |deriv ξ x| ≤ (Data.MdQ n : ℝ) := by
  obtain ⟨hw2, -, s, hs, hval⟩ := prolate_window hξ heig hn hnN hw
  have hW := window_facts hnN
  simp only [Data.windowOK, Data.roundOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hW
  obtain ⟨-, -, l1, -⟩ := hW
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz0⟩ := const_facts
  have hl1 : (0 : ℝ) < |thR n| - Data.w0q n - Data.zeta1Q := by unfold thR; exact_mod_cast l1
  have hz : (0 : ℝ) ≤ Data.zeta1Q := by exact_mod_cast hz0
  have hden : (0 : ℝ) < |thR n| - Data.w0q n := by linarith
  have hlow : |thR n| - Data.w0q n ≤ |lam| := by
    have := abs_sub_abs_le_abs_sub (thR n) lam
    rw [abs_sub_comm] at this; linarith
  have hlam : lam ≠ 0 := fun h0 => by rw [h0, abs_zero] at hlow; linarith
  have hs1 : |s| = 1 := by rcases hs with h | h <;> simp [h]
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · have hlt := Data.lam_ok
    simp only [Data.lamOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hlt
    have h1 : |thR n| + Data.w2q n < 1 := by
      have := hlt n (Nat.lt_succ_of_le hnN); unfold thR; exact_mod_cast this
    have h2 : |lam| < 1 := by
      have := abs_sub_abs_le_abs_sub lam (thR n); linarith
    have h3 := abs_nonneg lam
    nlinarith [sq_abs lam]
  · rw [contDiff_one_iff_deriv]
    have hd : deriv ξ = fun ω => Td ξ ω / lam :=
      funext fun ω => (hasDerivAt_eig hξ hlam heig ω).deriv
    exact ⟨fun ω => (hasDerivAt_eig hξ hlam heig ω).differentiableAt,
      by rw [hd]; exact (continuous_Td hξ).div_const lam⟩
  · have hxa : |x| ≤ 2 := by rw [abs_of_nonneg hx.1]; exact hx.2
    obtain ⟨hv, hvd⟩ := hval x hx.1 hx.2
    have hψ : |psiS n x| ≤ (Data.PsiQ n : ℝ) := by
      refine (abs_psi_le Data.Jd BR n hxa).trans (le_of_eq ?_)
      unfold Data.PsiQ BR; push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_mul]; norm_num
    have hψd : |psidS n x| ≤ (Data.PsidQ n : ℝ) := by
      refine (abs_psid_le Data.Jd BR n hxa).trans (le_of_eq ?_)
      unfold Data.PsidQ BR; push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have key : ∀ {v a B V : ℝ}, |lam * v - s * thR n * a| ≤ V → |a| ≤ B →
        |v| ≤ (|thR n| * B + V) / (|thR n| - Data.w0q n) := fun {v a B V} h1 h2 => by
      rw [le_div_iff₀ hden]
      have e1 : |lam * v| ≤ |thR n| * B + V := by
        have : |s * thR n * a| ≤ |thR n| * B := by
          rw [abs_mul, abs_mul, hs1, one_mul]
          exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        have := abs_sub_abs_le_abs_sub (lam * v) (s * thR n * a)
        linarith
      rw [abs_mul] at e1
      nlinarith [abs_nonneg v]
    constructor
    · have := key hv hψ
      refine this.trans (le_of_eq ?_)
      unfold Data.MxQ thR; push_cast; rfl
    · have := key hvd hψd
      refine this.trans (le_of_eq ?_)
      unfold Data.MdQ thR; push_cast; rfl

/-! ## 6. In S8's variable: `phi n x = λ⁻¹ · 2 ∫_0^1 ξ(y) cos(2πxy) dy = T ξ x / λ`. -/

/-- **The certified values in S8's form.**  For the eigenfunction of window n, S8's
`phi = fun x => T ξ x / λ` (CC's ξ_n^an) equals ξ, and on [1/2, 2] (the range used by the kernel χ
on [0, log 2]) its values and derivative are certified:
|λ phi(x) - s θ_n ψ_n(x)| ≤ Vq n and |λ phi'(x) - s θ_n ψ_n'(x)| ≤ Vdq n, with λ within w2q n of
θ_n.  S8's weight is w_n = λ²/(1-λ²) with λ² < 1 (`prolate_S8_fields`); phi(1) is the case x = 1. -/
theorem prolate_phi_values {ξ : ℝ → ℝ} {lam : ℝ} (hξ : Continuous ξ)
    (heig : ∀ ω, T ξ ω = lam * ξ ω) (hn : ip ξ ξ = 1) {n : ℕ} (hnN : n ≤ Data.NCw)
    (hw : |lam - thR n| ≤ (Data.w0q n : ℝ)) :
    (fun x => T ξ x / lam) = ξ ∧ |lam - thR n| ≤ (Data.w2q n : ℝ) ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ x ∈ Icc (1 / 2 : ℝ) 2,
        |lam * (T ξ x / lam) - s * thR n * psiS n x| ≤ (Data.Vq n : ℝ) ∧
        |lam * deriv (fun y => T ξ y / lam) x - s * thR n * psidS n x| ≤ (Data.Vdq n : ℝ) := by
  have hlam : lam ≠ 0 := by
    intro h0
    have hW := window_facts hnN
    simp only [Data.windowOK, Data.roundOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hW
    obtain ⟨-, -, l1, -⟩ := hW
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hz0⟩ := const_facts
    have hl1 : (0 : ℝ) < |thR n| - Data.w0q n - Data.zeta1Q := by unfold thR; exact_mod_cast l1
    have hz : (0 : ℝ) ≤ Data.zeta1Q := by exact_mod_cast hz0
    rw [h0, zero_sub, abs_neg] at hw
    linarith
  have hphi : (fun x => T ξ x / lam) = ξ := funext fun x => by rw [heig]; field_simp
  obtain ⟨hw2, -, s, hs, hval⟩ := prolate_window hξ heig hn hnN hw
  refine ⟨hphi, hw2, s, hs, fun x hx => ?_⟩
  have e : T ξ x / lam = ξ x := congrFun hphi x
  rw [e, hphi]
  exact hval x (by linarith [hx.1]) hx.2

end ArchS9

end
