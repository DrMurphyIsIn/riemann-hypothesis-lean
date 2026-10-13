/-
  KWin_Tail -- the projection tail and the sector floor of the split form (rvm_bridge island,
  2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; PR #604: the 1.3e-3
  full-class margin at this window is zero content; not Connes-Consani, whose theorem is for the
  pole-free class.)

  PROVED HERE (`Rb_floor`): for EVERY continuous v and each sector,
      lam' int_{-l}^{l} v^2 <= Rb par v v,     lam' = 9/10000,
  from the head certificate (KWin_Head.head_floor) and a PROJECTION tail that needs no Legendre
  completeness: h = sum_{k<N} a_k (x/l)^(2k+par) with a = G^{-1} (int v (x/l)^(2k+par))_k (the
  exact inverse G^{-1} is kernel-checked), r = v - h is orthogonal to (x/l)^(2m+par), m < N, so
    * the Taylor part of cos/sin(t x) (degree < 2N+par) and of cosh/sinh(x/2) is invisible to r:
      |Tr r t| <= eps_N(t) int|r|, |Pl r| <= delta_N int|r|  (KWin_Taylor);
    * int h r = 0, so int v^2 = int h^2 + int r^2 and the beta0 coupling vanishes;
    * |Rb h r| <= kapT int|h| int|r|,  Rb r r >= dT int r^2,
  and (lam - lam')(dT - lam') >= 4 kapT^2 l^2 (kernel-checked) closes the 2x2 bound through
  (int|f|)^2 <= 2 l int f^2.  No `sorry`.
-/
import KWin_Head

open Real Finset MeasureTheory intervalIntegral

noncomputable section

namespace KWin
open RvMBridge11

/-! ## A. Linearity. -/

lemma int_add_mul {f g w : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hw : Continuous w) (a b : ℝ) :
    ∫ x in a..b, (f x + g x) * w x = (∫ x in a..b, f x * w x) + ∫ x in a..b, g x * w x := by
  have h1 : IntervalIntegrable (fun x => f x * w x) volume a b := (hf.mul hw).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => g x * w x) volume a b := (hg.mul hw).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add h1 h2]
  congr 1; funext x; ring

lemma Pl_add {par : ℕ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Pl ellR par (fun x => f x + g x) = Pl ellR par f + Pl ellR par g :=
  int_add_mul hf hg (continuous_poleF par) _ _

lemma Tr_add {par : ℕ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    Tr ellR par (fun x => f x + g x) t = Tr ellR par f t + Tr ellR par g t :=
  int_add_mul hf hg ((continuous_phiF par).comp (continuous_const.mul continuous_id)) _ _

lemma ip_add_left {f g w : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hw : Continuous w) :
    ip ellR (fun x => f x + g x) w = ip ellR f w + ip ellR g w :=
  int_add_mul hf hg hw _ _

lemma ip_comm (f g : ℝ → ℝ) : ip ellR f g = ip ellR g f := by
  unfold ip; congr 1; funext x; ring

lemma mo_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (n : ℕ) :
    mo ellR (fun x => f x - g x) n = mo ellR f n - mo ellR g n := by
  unfold mo
  have h1 : IntervalIntegrable (fun x => f x * (x / ellR) ^ n) volume (-ellR) ellR :=
    (hf.mul (by fun_prop)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => g x * (x / ellR) ^ n) volume (-ellR) ellR :=
    (hg.mul (by fun_prop)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub h1 h2]
  congr 1; funext x; beta_reduce; ring

lemma Rb_comm (par : ℕ) (f g : ℝ → ℝ) : Rb par f g = Rb par g f := by
  unfold Rb
  rw [ip_comm f g]
  have e : (fun t => (Psi t - beta0R) * (Tr ellR par f t * Tr ellR par g t))
      = fun t => (Psi t - beta0R) * (Tr ellR par g t * Tr ellR par f t) := by funext t; ring
  rw [e]
  ring

/-- The bilinear expansion `R(h + r) = R(h) + 2 R(h, r) + R(r)`. -/
theorem Rb_expand (par : ℕ) {h r : ℝ → ℝ} (hh : Continuous h) (hr : Continuous r) :
    Rb par (fun x => h x + r x) (fun x => h x + r x) = Rb par h h + 2 * Rb par h r + Rb par r r := by
  have hs : Continuous (fun x => h x + r x) := hh.add hr
  unfold Rb
  rw [Pl_add hh hr, ip_add_left hh hr hs, ip_comm h, ip_comm r, ip_add_left hh hr hh,
    ip_add_left hh hr hr, ip_comm r h]
  have cTh := continuous_Tr ellR par hh
  have cTr := continuous_Tr ellR par hr
  have cP : Continuous fun t => Psi t - beta0R := continuous_Psi.sub continuous_const
  have e : (fun t => (Psi t - beta0R) * (Tr ellR par (fun x => h x + r x) t
        * Tr ellR par (fun x => h x + r x) t))
      = fun t => ((Psi t - beta0R) * (Tr ellR par h t * Tr ellR par h t)
        + 2 * ((Psi t - beta0R) * (Tr ellR par h t * Tr ellR par r t)))
        + (Psi t - beta0R) * (Tr ellR par r t * Tr ellR par r t) := by
    funext t; rw [Tr_add hh hr t]; ring
  rw [e, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul]
  ring

/-! ## B. Integral bounds on [0, 20]. -/

lemma abs_int_le_of_abs_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 20, |f t| ≤ g t) :
    |∫ t in (0 : ℝ)..20, f t| ≤ ∫ t in (0 : ℝ)..20, g t := by
  refine (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans ?_
  exact intervalIntegral.integral_mono_on (by norm_num) (hf.abs.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _) h

/-! ## C. The sector floor. -/

set_option maxHeartbeats 1000000 in
theorem Rb_floor {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam : ℚ}
    (htail : tailCond par N lam = true) (hcert : psdCert (headMat par N lam) N = true)
    (hginv : ginvCheck par N = true) {v : ℝ → ℝ} (hv : Continuous v) :
    ((lamFloor : ℚ) : ℝ) * ip ellR v v ≤ Rb par v v := by
  obtain ⟨hl1, hl2, hl3, _, _, hN, _⟩ := tailCond_sound htail
  have hl := ellR_pos
  -- the projection
  set b : ℕ → ℝ := fun l => mo ellR v (2 * l + par) with hbdef
  set a : ℕ → ℝ := fun j => ∑ l ∈ range N, ((mget (ginv par) j l : ℚ) : ℝ) * b l with hadef
  set h := hfun par N a with hhdef
  have hc : Continuous h := continuous_hfun par N a
  set r : ℝ → ℝ := fun x => v x - h x with hrdef
  have hrc : Continuous r := hv.sub hc
  have hvhr : v = fun x => h x + r x := by funext x; simp only [hrdef]; ring
  -- orthogonality
  have horth : ∀ m < N, mo ellR r (2 * m + par) = 0 := by
    intro m hm
    rw [hrdef, mo_sub hv hc, hhdef, mo_hfun]
    have hsum : ∑ k ∈ range N, a k * ((Gm par k m : ℚ) : ℝ) = b m := by
      rw [hadef]
      simp only
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      have hδ : ∀ l ∈ range N, ∑ k ∈ range N, ((mget (ginv par) k l : ℚ) : ℝ) * b l * ((Gm par k m : ℚ) : ℝ)
          = if m = l then b l else 0 := by
        intro l hlN
        have hG := ginvCheck_sound hginv hm (Finset.mem_range.mp hlN)
        have hG' : ∑ k ∈ range N, ((Gm par m k : ℚ) : ℝ) * ((mget (ginv par) k l : ℚ) : ℝ)
            = if m = l then 1 else 0 := by
          have := congrArg (fun q : ℚ => (q : ℝ)) hG
          push_cast at this
          rw [this]
          split_ifs <;> simp
        have e : ∑ k ∈ range N, ((mget (ginv par) k l : ℚ) : ℝ) * b l * ((Gm par k m : ℚ) : ℝ)
            = (∑ k ∈ range N, ((Gm par m k : ℚ) : ℝ) * ((mget (ginv par) k l : ℚ) : ℝ)) * b l := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Gm_symm par k m]
          ring
        rw [e, hG']
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hδ, Finset.sum_ite_eq]
      simp [Finset.mem_range.mpr hm]
    rw [hsum]
    simp [hbdef]
  -- int h r = 0
  have hhr : ip ellR h r = 0 := by
    rw [hhdef, ip_hfun_left par N a hrc]
    exact Finset.sum_eq_zero fun k hk => by rw [horth k (Finset.mem_range.mp hk), mul_zero]
  -- tail transform and pole bounds
  set A := A1 ellR h with hAdef
  set B := A1 ellR r with hBdef
  have hA0 : 0 ≤ A := A1_nonneg hl.le h
  have hB0 : 0 ≤ B := A1_nonneg hl.le r
  set X := ip ellR h h with hXdef
  set Y := ip ellR r r with hYdef
  have hsqX : A ^ 2 ≤ 2 * ellR * X := by
    have := A1_sq_le hl hc
    rw [hXdef]; unfold ip
    have e : (fun x => h x ^ 2) = fun x => h x * h x := by funext x; ring
    rwa [e] at this
  have hsqY : B ^ 2 ≤ 2 * ellR * Y := by
    have := A1_sq_le hl hrc
    rw [hYdef]; unfold ip
    have e : (fun x => r x ^ 2) = fun x => r x * r x := by funext x; ring
    rwa [e] at this
  have hX0 : 0 ≤ X := by
    rw [hXdef]; unfold ip
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => mul_self_nonneg _
  have hY0 : 0 ≤ Y := by
    rw [hYdef]; unfold ip
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => mul_self_nonneg _
  have hTr : ∀ t ∈ Set.Icc (0 : ℝ) 20, |Tr ellR par r t| ≤ epsW (2 * N + par) t * B := by
    intro t ht
    have htl : t * ellR ≤ (2 * N + par + 1) / 2 := by
      have h1 : t * ellR ≤ 20 * ellR := mul_le_mul_of_nonneg_right ht.2 hl.le
      have h2 := (Rat.cast_le (K := ℝ)).mpr hN
      unfold TQ at h2
      push_cast at h2
      have e : (20 : ℝ) * ellR = (20 : ℝ) * ((ellQ : ℚ) : ℝ) := rfl
      linarith
    have := Tr_sub_le hl hpar hrc ht.1 htl
    have hz : ∑ m ∈ range N, (-1) ^ m * (t * ellR) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo ellR r (2 * m + par) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [horth m (Finset.mem_range.mp hm), mul_zero]
    rw [hz, sub_zero] at this
    unfold epsW
    exact this
  set dN : ℝ := 2 * (ellR / 2) ^ (2 * N + par) / ((2 * N + par).factorial : ℝ) with hdN
  have hdN0 : 0 ≤ dN := by rw [hdN]; positivity
  have hPr : |Pl ellR par r| ≤ dN * B := by
    have hNpos : 0 < 2 * N + par := by
      by_contra hc'
      have h0 : N = 0 ∧ par = 0 := by omega
      obtain ⟨h1, h2⟩ := h0
      subst h1 h2
      unfold TQ ellQ at hN
      norm_num at hN
    have := Pl_sub_le hl (by rw [ellR_eq]; norm_num) hpar hNpos hrc
    have hz : ∑ m ∈ range N, (ellR / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo ellR r (2 * m + par) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [horth m (Finset.mem_range.mp hm), mul_zero]
    rw [hz, sub_zero] at this
    rw [hdN]; exact this
  have hPh : |Pl ellR par h| ≤ ((CpQ : ℚ) : ℝ) * A := by
    have h1 := abs_Pl_le hl par hc
    have h2 := cosh_half_ell_le
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hA0)
  have hTh : ∀ t, |Tr ellR par h t| ≤ A := fun t => abs_Tr_le hl par hc t
  -- constants
  have hpi := Real.pi_pos
  have hpi3 : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hS0 : (0 : ℝ) ≤ ((S0Q : ℚ) : ℝ) := by unfold S0Q; push_cast; norm_num
  have hCp : (0 : ℝ) ≤ ((CpQ : ℚ) : ℝ) := by unfold CpQ; push_cast; norm_num
  set I1 := ∫ t in (0 : ℝ)..20, epsW (2 * N + par) t with hI1
  set I2 := ∫ t in (0 : ℝ)..20, epsW (2 * N + par) t ^ 2 with hI2
  have hI10 : 0 ≤ I1 := intervalIntegral.integral_nonneg (by norm_num) fun t ht => epsW_nonneg _ ht.1
  have hI20 : 0 ≤ I2 := intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have hkap : ((kapT par N : ℚ) : ℝ) = 2 * ((CpQ : ℚ) : ℝ) * dN + ((S0Q : ℚ) : ℝ) / 3 * I1 := by
    rw [hI1, int_epsW]
    unfold kapT dPT I1T
    rw [hdN]
    unfold ellR TQ
    push_cast
    ring
  have hdT : ((dT par N : ℚ) : ℝ) = beta0R - 2 * ellR * (2 * dN ^ 2 + ((S0Q : ℚ) : ℝ) / 3 * I2) := by
    rw [hI2, int_epsW_sq]
    unfold dT dPT I2T
    rw [hdN]
    unfold ellR TQ beta0R
    push_cast
    ring
  have hcP : Continuous fun t => Psi t - beta0R := continuous_Psi.sub continuous_const
  have cTh := continuous_Tr ellR par hc
  have cTr := continuous_Tr ellR par hrc
  have hce := continuous_epsW (2 * N + par)
  -- the coupling
  have hcross : |Rb par h r| ≤ ((kapT par N : ℚ) : ℝ) * (A * B) := by
    unfold Rb
    rw [hhr, mul_zero, add_zero]
    have h1 : |2 * epsR par * Pl ellR par h * Pl ellR par r| ≤ 2 * ((CpQ : ℚ) : ℝ) * dN * (A * B) := by
      have he : |epsR par| = 1 := by unfold epsR; split_ifs <;> simp
      rw [abs_mul, abs_mul, abs_mul, he, abs_two]
      calc 2 * 1 * |Pl ellR par h| * |Pl ellR par r| ≤ 2 * 1 * (((CpQ : ℚ) : ℝ) * A) * (dN * B) := by
            gcongr
        _ = 2 * ((CpQ : ℚ) : ℝ) * dN * (A * B) := by ring
    have h2 : |(1 / Real.pi) * ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par h t * Tr ellR par r t)|
        ≤ ((S0Q : ℚ) : ℝ) / 3 * I1 * (A * B) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      have hb := abs_int_le_of_abs_le (f := fun t => (Psi t - beta0R) * (Tr ellR par h t * Tr ellR par r t))
        (g := fun t => ((S0Q : ℚ) : ℝ) * (A * (epsW (2 * N + par) t * B))) (by fun_prop) (by fun_prop)
        (by
          intro t ht
          rw [abs_mul, abs_mul]
          exact mul_le_mul (abs_Psi_sub_beta0_le ht.1 ht.2)
            (mul_le_mul (hTh t) (hTr t ht) (abs_nonneg _) hA0) (by positivity) hS0)
      have e : ∫ t in (0 : ℝ)..20, ((S0Q : ℚ) : ℝ) * (A * (epsW (2 * N + par) t * B))
          = ((S0Q : ℚ) : ℝ) * I1 * (A * B) := by
        rw [hI1]
        have e2 : (fun t => ((S0Q : ℚ) : ℝ) * (A * (epsW (2 * N + par) t * B)))
            = fun t => (((S0Q : ℚ) : ℝ) * (A * B)) * epsW (2 * N + par) t := by funext t; ring
        rw [e2, intervalIntegral.integral_const_mul]
        ring
      rw [e] at hb
      have hSIAB : 0 ≤ ((S0Q : ℚ) : ℝ) * I1 * (A * B) := by positivity
      calc 1 / Real.pi * |∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par h t * Tr ellR par r t)|
          ≤ 1 / Real.pi * (((S0Q : ℚ) : ℝ) * I1 * (A * B)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ 1 / 3 * (((S0Q : ℚ) : ℝ) * I1 * (A * B)) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hpi3) hSIAB
        _ = ((S0Q : ℚ) : ℝ) / 3 * I1 * (A * B) := by ring
    rw [hkap]
    calc |2 * epsR par * Pl ellR par h * Pl ellR par r
          + (1 / Real.pi) * ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par h t * Tr ellR par r t)|
        ≤ |2 * epsR par * Pl ellR par h * Pl ellR par r|
          + |(1 / Real.pi) * ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par h t * Tr ellR par r t)| :=
          abs_add_le _ _
      _ ≤ 2 * ((CpQ : ℚ) : ℝ) * dN * (A * B) + ((S0Q : ℚ) : ℝ) / 3 * I1 * (A * B) := add_le_add h1 h2
      _ = (2 * ((CpQ : ℚ) : ℝ) * dN + ((S0Q : ℚ) : ℝ) / 3 * I1) * (A * B) := by ring
  -- the tail term
  have htailR : ((dT par N : ℚ) : ℝ) * Y ≤ Rb par r r := by
    unfold Rb
    rw [← hYdef]
    have h1 : -2 * dN ^ 2 * B ^ 2 ≤ 2 * epsR par * Pl ellR par r * Pl ellR par r := by
      have hP2 : Pl ellR par r ^ 2 ≤ (dN * B) ^ 2 :=
        sq_le_sq' (abs_le.mp hPr).1 (abs_le.mp hPr).2
      unfold epsR
      split_ifs
      · nlinarith [sq_nonneg (Pl ellR par r)]
      · nlinarith
    have h2 : -(((S0Q : ℚ) : ℝ) / 3 * I2 * B ^ 2)
        ≤ (1 / Real.pi) * ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par r t * Tr ellR par r t) := by
      have hb := abs_int_le_of_abs_le (f := fun t => (Psi t - beta0R) * (Tr ellR par r t * Tr ellR par r t))
        (g := fun t => ((S0Q : ℚ) : ℝ) * (epsW (2 * N + par) t ^ 2 * B ^ 2)) (by fun_prop) (by fun_prop)
        (by
          intro t ht
          rw [abs_mul, abs_mul]
          have hT := hTr t ht
          have hTT : |Tr ellR par r t| * |Tr ellR par r t| ≤ epsW (2 * N + par) t ^ 2 * B ^ 2 := by
            have := mul_le_mul hT hT (abs_nonneg _) (by have := epsW_nonneg (2 * N + par) ht.1; positivity)
            nlinarith
          exact mul_le_mul (abs_Psi_sub_beta0_le ht.1 ht.2) hTT (by positivity) hS0)
      have e : ∫ t in (0 : ℝ)..20, ((S0Q : ℚ) : ℝ) * (epsW (2 * N + par) t ^ 2 * B ^ 2)
          = ((S0Q : ℚ) : ℝ) * I2 * B ^ 2 := by
        rw [hI2]
        have e2 : (fun t => ((S0Q : ℚ) : ℝ) * (epsW (2 * N + par) t ^ 2 * B ^ 2))
            = fun t => (((S0Q : ℚ) : ℝ) * B ^ 2) * epsW (2 * N + par) t ^ 2 := by funext t; ring
        rw [e2, intervalIntegral.integral_const_mul]
        ring
      rw [e] at hb
      have hSIB : 0 ≤ ((S0Q : ℚ) : ℝ) * I2 * B ^ 2 := by positivity
      have hq := neg_abs_le (∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par r t * Tr ellR par r t))
      have h3 : -(1 / Real.pi) * (((S0Q : ℚ) : ℝ) * I2 * B ^ 2)
          ≤ (1 / Real.pi) * ∫ t in (0 : ℝ)..20, (Psi t - beta0R) * (Tr ellR par r t * Tr ellR par r t) := by
        have := mul_le_mul_of_nonneg_left (le_trans (neg_le_neg hb) hq) (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
        linarith
      have h4 : (1 / Real.pi) * (((S0Q : ℚ) : ℝ) * I2 * B ^ 2) ≤ 1 / 3 * (((S0Q : ℚ) : ℝ) * I2 * B ^ 2) :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hpi3) hSIB
      linarith
    rw [hdT]
    have hK0 : (0 : ℝ) ≤ 2 * dN ^ 2 + ((S0Q : ℚ) : ℝ) / 3 * I2 := by positivity
    have hK := mul_le_mul_of_nonneg_left hsqY hK0
    have e1 : (beta0R - 2 * ellR * (2 * dN ^ 2 + ((S0Q : ℚ) : ℝ) / 3 * I2)) * Y
        = beta0R * Y - (2 * dN ^ 2 + ((S0Q : ℚ) : ℝ) / 3 * I2) * (2 * ellR * Y) := by ring
    have e2 : (2 * dN ^ 2 + ((S0Q : ℚ) : ℝ) / 3 * I2) * B ^ 2
        = 2 * dN ^ 2 * B ^ 2 + ((S0Q : ℚ) : ℝ) / 3 * I2 * B ^ 2 := by ring
    rw [e1]
    linarith [h1, h2, hK, e2]
  -- the head term
  have hhead : ((lam : ℚ) : ℝ) * X ≤ Rb par h h := by
    rw [hXdef, hhdef]
    exact head_floor hpar htail hcert a
  -- assembly
  have hRv : Rb par v v = Rb par h h + 2 * Rb par h r + Rb par r r := by
    rw [hvhr]; exact Rb_expand par hc hrc
  have hIv : ip ellR v v = X + Y := by
    have hs : Continuous (fun x => h x + r x) := hc.add hrc
    rw [hvhr, ip_add_left hc hrc hs, ip_comm h, ip_comm r, ip_add_left hc hrc hc,
      ip_add_left hc hrc hrc, ip_comm r h, hhr, hXdef, hYdef]
    ring
  rw [hRv, hIv]
  have hl1R : ((lamFloor : ℚ) : ℝ) ≤ ((lam : ℚ) : ℝ) := by exact_mod_cast hl1
  have hl2R : ((lamFloor : ℚ) : ℝ) ≤ ((dT par N : ℚ) : ℝ) := by exact_mod_cast hl2
  have hl3R : 4 * ((kapT par N : ℚ) : ℝ) ^ 2 * ellR ^ 2
      ≤ (((lam : ℚ) : ℝ) - ((lamFloor : ℚ) : ℝ)) * (((dT par N : ℚ) : ℝ) - ((lamFloor : ℚ) : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hl3
    push_cast at this
    exact this
  have hk0 : 0 ≤ ((kapT par N : ℚ) : ℝ) := by rw [hkap]; positivity
  -- 2x2: (lam - lam') X + (d - lam') Y >= 2 kap A B
  set α := ((lam : ℚ) : ℝ) - ((lamFloor : ℚ) : ℝ) with hα
  set δ := ((dT par N : ℚ) : ℝ) - ((lamFloor : ℚ) : ℝ) with hδ
  set κ := ((kapT par N : ℚ) : ℝ) with hκ
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hAB : (A * B) ^ 2 ≤ 4 * ellR ^ 2 * (X * Y) := by
    have := mul_le_mul hsqX hsqY (sq_nonneg B) (by positivity)
    nlinarith
  have hkey : 2 * κ * (A * B) ≤ α * X + δ * Y := by
    have hsq1 : (2 * κ * (A * B)) ^ 2 ≤ (α * X + δ * Y) ^ 2 := by
      have e1 : (2 * κ * (A * B)) ^ 2 = 4 * κ ^ 2 * (A * B) ^ 2 := by ring
      have e2 : 4 * κ ^ 2 * (A * B) ^ 2 ≤ 4 * κ ^ 2 * (4 * ellR ^ 2 * (X * Y)) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
      have e3 : 4 * κ ^ 2 * (4 * ellR ^ 2 * (X * Y)) ≤ 4 * (α * δ) * (X * Y) := by
        have := mul_le_mul_of_nonneg_right hl3R (by positivity : (0 : ℝ) ≤ 4 * (X * Y))
        nlinarith
      have e4 : 4 * (α * δ) * (X * Y) ≤ (α * X + δ * Y) ^ 2 := by
        nlinarith [sq_nonneg (α * X - δ * Y)]
      linarith
    have hpos : 0 ≤ α * X + δ * Y := by positivity
    exact (pow_le_pow_iff_left₀ (by positivity) hpos (by norm_num : (2 : ℕ) ≠ 0)).mp hsq1
  have hcr := (abs_le.mp hcross).1
  have hl' : ((lam : ℚ) : ℝ) = α + ((lamFloor : ℚ) : ℝ) := by rw [hα]; ring
  have hd' : ((dT par N : ℚ) : ℝ) = δ + ((lamFloor : ℚ) : ℝ) := by rw [hδ]; ring
  rw [hl'] at hhead
  rw [hd'] at htailR
  have e3 : (α + ((lamFloor : ℚ) : ℝ)) * X = α * X + ((lamFloor : ℚ) : ℝ) * X := by ring
  have e4 : (δ + ((lamFloor : ℚ) : ℝ)) * Y = δ * Y + ((lamFloor : ℚ) : ℝ) * Y := by ring
  rw [e3] at hhead
  rw [e4] at htailR
  have e5 : ((lamFloor : ℚ) : ℝ) * (X + Y) = ((lamFloor : ℚ) : ℝ) * X + ((lamFloor : ℚ) : ℝ) * Y := by ring
  rw [e5]
  linarith [hkey, hhead, htailR, hcr]

end KWin

end
