/-
  KWin2_Tail -- the projection tail and the sector floor of the split form, parametric in the window
  and abstract in the symbol (rvm_bridge island, 2026-09-24).

  conjecture1_proved = False.  (Finite-window Weil positivity is not RH; not Connes-Consani, whose
  theorem is for the pole-free class; cf. PR #604.)

  PROVED HERE (`Rb_floor`): for EVERY continuous v, each sector and every symbol satisfying
  `SymHyp P sym`,
      lamFloor int_{-l}^{l} v^2 <= Rb P sym par v v,
  from the head certificate (KWin2_Head.head_floor) and KWin's PROJECTION tail: the projection
  coefficients a = G^{-1} (int v (x/l)^(2k+par))_k use the kernel-checked Cauchy inverse
  (KWin2_Data.ginvCheck), r = v - h is orthogonal to the head monomials, so the Taylor part of the
  transform and of the pole functional is invisible to r; the coupling |Rb h r| <= kapT A1(h) A1(r)
  and the tail floor Rb r r >= dT int r^2 use only |sym - beta0| <= S0 on [0, T]; the 2x2 bound
  closes with the kernel-checked (lam - lamFloor)(dT - lamFloor) >= 4 kapT^2 l^2.  The prime comb
  lives inside `sym`: in frequency space it is a bounded multiplier on [0, T], where the tail's
  transform is Taylor-small, so it never couples the head to the tail.  No `sorry`.
-/
import KWin2_Head

open Real Finset MeasureTheory intervalIntegral

noncomputable section

namespace KWin2
open KWin (Tr Pl ip mo A1 phiF poleF continuous_Tr Tr_sub_le Pl_sub_le abs_Tr_le abs_Pl_le A1_nonneg
  A1_sq_le continuous_phiF continuous_poleF psdCert psdCert_sound mget mget_map_range getD_map_range
  piLoQ piHiQ piEQ epsQ pi_gt_Q pi_lt_Q epsR)

variable (P : KPar)

/-! ## A. Linearity. -/

lemma int_add_mul' {f g w : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hw : Continuous w)
    (a b : ℝ) :
    ∫ x in a..b, (f x + g x) * w x = (∫ x in a..b, f x * w x) + ∫ x in a..b, g x * w x := by
  have h1 : IntervalIntegrable (fun x => f x * w x) volume a b := (hf.mul hw).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => g x * w x) volume a b := (hg.mul hw).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add h1 h2]
  congr 1; funext x; ring

lemma Pl_add' (l : ℝ) {par : ℕ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Pl l par (fun x => f x + g x) = Pl l par f + Pl l par g :=
  int_add_mul' hf hg (continuous_poleF par) _ _

lemma Tr_add' (l : ℝ) {par : ℕ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    Tr l par (fun x => f x + g x) t = Tr l par f t + Tr l par g t :=
  int_add_mul' hf hg ((continuous_phiF par).comp (continuous_const.mul continuous_id)) _ _

lemma ip_add_left' (l : ℝ) {f g w : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hw : Continuous w) :
    ip l (fun x => f x + g x) w = ip l f w + ip l g w :=
  int_add_mul' hf hg hw _ _

lemma ip_comm' (l : ℝ) (f g : ℝ → ℝ) : ip l f g = ip l g f := by
  unfold ip; congr 1; funext x; ring

lemma mo_sub' (l : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (n : ℕ) :
    mo l (fun x => f x - g x) n = mo l f n - mo l g n := by
  unfold mo
  have h1 : IntervalIntegrable (fun x => f x * (x / l) ^ n) volume (-l) l :=
    (hf.mul (by fun_prop)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => g x * (x / l) ^ n) volume (-l) l :=
    (hg.mul (by fun_prop)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub h1 h2]
  congr 1; funext x; beta_reduce; ring

/-- The bilinear expansion `R(h + r) = R(h) + 2 R(h, r) + R(r)`. -/
theorem Rb_expand {sym : ℝ → ℝ} (hsc : Continuous sym) (par : ℕ) {h r : ℝ → ℝ} (hh : Continuous h)
    (hr : Continuous r) :
    Rb P sym par (fun x => h x + r x) (fun x => h x + r x)
      = Rb P sym par h h + 2 * Rb P sym par h r + Rb P sym par r r := by
  have hs : Continuous (fun x => h x + r x) := hh.add hr
  unfold Rb
  rw [Pl_add' _ hh hr, ip_add_left' _ hh hr hs, ip_comm' _ h, ip_comm' _ r, ip_add_left' _ hh hr hh,
    ip_add_left' _ hh hr hr, ip_comm' _ r h]
  have cTh := continuous_Tr (lR P) par hh
  have cTr := continuous_Tr (lR P) par hr
  have cP : Continuous fun t => sym t - b0R P := hsc.sub continuous_const
  have e : (fun t => (sym t - b0R P) * (Tr (lR P) par (fun x => h x + r x) t
        * Tr (lR P) par (fun x => h x + r x) t))
      = fun t => ((sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par h t)
        + 2 * ((sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par r t)))
        + (sym t - b0R P) * (Tr (lR P) par r t * Tr (lR P) par r t) := by
    funext t; rw [Tr_add' _ hh hr t]; ring
  rw [e, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul]
  ring

/-! ## B. Integral bounds on [0, T]. -/

lemma abs_int_le_of_abs_le' (hpc : parCheck P = true) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ t ∈ Set.Icc (0 : ℝ) (TR P), |f t| ≤ g t) :
    |∫ t in (0 : ℝ)..(TR P), f t| ≤ ∫ t in (0 : ℝ)..(TR P), g t := by
  have hT := (TR_pos P hpc).le
  refine (intervalIntegral.abs_integral_le_integral_abs hT).trans ?_
  exact intervalIntegral.integral_mono_on hT (hf.abs.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _) h

/-! ## C. The sector floor. -/

set_option maxHeartbeats 2000000 in
theorem Rb_floor {sym : ℝ → ℝ} (hs : SymHyp P sym) (hpc : parCheck P = true)
    (hb : brkCheck P = true) {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam : ℚ}
    (htail : tailCond P par N lam = true) (hcert : HeadPSD (headMat P par N lam) N)
    (hginv : ginvCheck P par N = true) {v : ℝ → ℝ} (hv : Continuous v) :
    ((P.lamFloor : ℚ) : ℝ) * ip (lR P) v v ≤ Rb P sym par v v := by
  obtain ⟨hl1, hl2, hl3, _, _, hN, _, hN1⟩ := tailCond_sound P htail
  have hl := lR_pos P hpc
  have hT := (TR_pos P hpc).le
  have hsc := hs.cont
  -- the projection
  set b : ℕ → ℝ := fun l => mo (lR P) v (2 * l + par) with hbdef
  set a : ℕ → ℝ := fun j => ∑ l ∈ range N, ((mget (ginvM P par N) j l : ℚ) : ℝ) * b l with hadef
  set h := hfun P par N a with hhdef
  have hc : Continuous h := continuous_hfun P par N a
  set r : ℝ → ℝ := fun x => v x - h x with hrdef
  have hrc : Continuous r := hv.sub hc
  have hvhr : v = fun x => h x + r x := by funext x; simp only [hrdef]; ring
  -- orthogonality
  have horth : ∀ m < N, mo (lR P) r (2 * m + par) = 0 := by
    intro m hm
    rw [hrdef, mo_sub' _ hv hc, hhdef, mo_hfun P hpc]
    have hsum : ∑ k ∈ range N, a k * ((Gm P par k m : ℚ) : ℝ) = b m := by
      rw [hadef]
      simp only
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      have hδ : ∀ l ∈ range N, ∑ k ∈ range N,
          ((mget (ginvM P par N) k l : ℚ) : ℝ) * b l * ((Gm P par k m : ℚ) : ℝ)
            = if m = l then b l else 0 := by
        intro l hlN
        have hG := ginvCheck_sound P hginv hm (Finset.mem_range.mp hlN)
        have hG' : ∑ k ∈ range N, ((Gm P par m k : ℚ) : ℝ) * ((mget (ginvM P par N) k l : ℚ) : ℝ)
            = if m = l then 1 else 0 := by
          have := congrArg (fun q : ℚ => (q : ℝ)) hG
          push_cast at this
          rw [this]
          split_ifs <;> simp
        have e : ∑ k ∈ range N, ((mget (ginvM P par N) k l : ℚ) : ℝ) * b l * ((Gm P par k m : ℚ) : ℝ)
            = (∑ k ∈ range N, ((Gm P par m k : ℚ) : ℝ) * ((mget (ginvM P par N) k l : ℚ) : ℝ)) * b l := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Gm_symm P par k m]
          ring
        rw [e, hG']
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hδ, Finset.sum_ite_eq]
      simp [Finset.mem_range.mpr hm]
    rw [hsum]
    simp [hbdef]
  -- int h r = 0
  have hhr : ip (lR P) h r = 0 := by
    rw [hhdef, ip_hfun_left P par N a hrc]
    exact Finset.sum_eq_zero fun k hk => by rw [horth k (Finset.mem_range.mp hk), mul_zero]
  -- tail transform and pole bounds
  set A := A1 (lR P) h with hAdef
  set B := A1 (lR P) r with hBdef
  have hA0 : 0 ≤ A := A1_nonneg hl.le h
  have hB0 : 0 ≤ B := A1_nonneg hl.le r
  set X := ip (lR P) h h with hXdef
  set Y := ip (lR P) r r with hYdef
  have hsqX : A ^ 2 ≤ 2 * lR P * X := by
    have := A1_sq_le hl hc
    rw [hXdef]; unfold ip
    have e : (fun x => h x ^ 2) = fun x => h x * h x := by funext x; ring
    rwa [e] at this
  have hsqY : B ^ 2 ≤ 2 * lR P * Y := by
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
  have hTr : ∀ t ∈ Set.Icc (0 : ℝ) (TR P), |Tr (lR P) par r t| ≤ epsW P (2 * N + par) t * B := by
    intro t ht
    have htl : t * lR P ≤ (2 * N + par + 1) / 2 := by
      have h1 : t * lR P ≤ TR P * lR P := mul_le_mul_of_nonneg_right ht.2 hl.le
      have h2 := (Rat.cast_le (K := ℝ)).mpr hN
      push_cast at h2
      have e : TR P * lR P = ((P.T : ℚ) : ℝ) * ((P.ell : ℚ) : ℝ) := rfl
      linarith
    have := Tr_sub_le hl hpar hrc ht.1 htl
    have hz : ∑ m ∈ range N, (-1) ^ m * (t * lR P) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo (lR P) r (2 * m + par) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [horth m (Finset.mem_range.mp hm), mul_zero]
    rw [hz, sub_zero] at this
    unfold epsW
    exact this
  set dN : ℝ := 2 * (lR P / 2) ^ (2 * N + par) / ((2 * N + par).factorial : ℝ) with hdN
  have hdN0 : 0 ≤ dN := by rw [hdN]; positivity
  have hPr : |Pl (lR P) par r| ≤ dN * B := by
    have hNpos : 0 < 2 * N + par := by omega
    have := Pl_sub_le hl (lR_half_le P hpc) hpar hNpos hrc
    have hz : ∑ m ∈ range N, (lR P / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo (lR P) r (2 * m + par) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [horth m (Finset.mem_range.mp hm), mul_zero]
    rw [hz, sub_zero] at this
    rw [hdN]; exact this
  have hPh : |Pl (lR P) par h| ≤ ((P.Cp : ℚ) : ℝ) * A := by
    have h1 := abs_Pl_le hl par hc
    exact h1.trans (mul_le_mul_of_nonneg_right hs.cosh hA0)
  have hTh : ∀ t, |Tr (lR P) par h t| ≤ A := fun t => abs_Tr_le hl par hc t
  -- constants
  have hpi := Real.pi_pos
  have hpi3 : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hS0 := S0_nonneg P hpc
  have hCp := Cp_nonneg P hpc
  set I1 := ∫ t in (0 : ℝ)..(TR P), epsW P (2 * N + par) t with hI1
  set I2 := ∫ t in (0 : ℝ)..(TR P), epsW P (2 * N + par) t ^ 2 with hI2
  have hI10 : 0 ≤ I1 := intervalIntegral.integral_nonneg hT fun t ht => epsW_nonneg P hpc _ ht.1
  have hI20 : 0 ≤ I2 := intervalIntegral.integral_nonneg hT fun t _ => sq_nonneg _
  have hkap : ((kapT P par N : ℚ) : ℝ) = 2 * ((P.Cp : ℚ) : ℝ) * dN + ((P.S0 : ℚ) : ℝ) / 3 * I1 := by
    rw [hI1, int_epsW]
    unfold kapT dPT I1T
    rw [hdN]
    unfold lR TR
    push_cast
    ring
  have hdT : ((dT P par N : ℚ) : ℝ)
      = b0R P - 2 * lR P * (2 * dN ^ 2 + ((P.S0 : ℚ) : ℝ) / 3 * I2) := by
    rw [hI2, int_epsW_sq]
    unfold dT dPT I2T
    rw [hdN]
    unfold lR TR b0R
    push_cast
    ring
  have hcP : Continuous fun t => sym t - b0R P := hsc.sub continuous_const
  have cTh := continuous_Tr (lR P) par hc
  have cTr := continuous_Tr (lR P) par hrc
  have hce := continuous_epsW P (2 * N + par)
  -- the coupling
  have hcross : |Rb P sym par h r| ≤ ((kapT P par N : ℚ) : ℝ) * (A * B) := by
    unfold Rb
    rw [hhr, mul_zero, add_zero]
    have h1 : |2 * epsR par * Pl (lR P) par h * Pl (lR P) par r|
        ≤ 2 * ((P.Cp : ℚ) : ℝ) * dN * (A * B) := by
      have he : |epsR par| = 1 := by unfold epsR; split_ifs <;> simp
      rw [abs_mul, abs_mul, abs_mul, he, abs_two]
      calc 2 * 1 * |Pl (lR P) par h| * |Pl (lR P) par r|
          ≤ 2 * 1 * (((P.Cp : ℚ) : ℝ) * A) * (dN * B) := by gcongr
        _ = 2 * ((P.Cp : ℚ) : ℝ) * dN * (A * B) := by ring
    have h2 : |(1 / Real.pi) * ∫ t in (0 : ℝ)..(TR P),
          (sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par r t)|
        ≤ ((P.S0 : ℚ) : ℝ) / 3 * I1 * (A * B) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      have hb' := abs_int_le_of_abs_le' P hpc
        (f := fun t => (sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par r t))
        (g := fun t => ((P.S0 : ℚ) : ℝ) * (A * (epsW P (2 * N + par) t * B))) (by fun_prop) (by fun_prop)
        (by
          intro t ht
          rw [abs_mul, abs_mul]
          exact mul_le_mul (hs.bound t ht.1 ht.2)
            (mul_le_mul (hTh t) (hTr t ht) (abs_nonneg _) hA0) (by positivity) hS0)
      have e : ∫ t in (0 : ℝ)..(TR P), ((P.S0 : ℚ) : ℝ) * (A * (epsW P (2 * N + par) t * B))
          = ((P.S0 : ℚ) : ℝ) * I1 * (A * B) := by
        rw [hI1]
        have e2 : (fun t => ((P.S0 : ℚ) : ℝ) * (A * (epsW P (2 * N + par) t * B)))
            = fun t => (((P.S0 : ℚ) : ℝ) * (A * B)) * epsW P (2 * N + par) t := by funext t; ring
        rw [e2, intervalIntegral.integral_const_mul]
        ring
      rw [e] at hb'
      have hSIAB : 0 ≤ ((P.S0 : ℚ) : ℝ) * I1 * (A * B) := by positivity
      calc 1 / Real.pi * |∫ t in (0 : ℝ)..(TR P),
            (sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par r t)|
          ≤ 1 / Real.pi * (((P.S0 : ℚ) : ℝ) * I1 * (A * B)) :=
            mul_le_mul_of_nonneg_left hb' (by positivity)
        _ ≤ 1 / 3 * (((P.S0 : ℚ) : ℝ) * I1 * (A * B)) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hpi3) hSIAB
        _ = ((P.S0 : ℚ) : ℝ) / 3 * I1 * (A * B) := by ring
    rw [hkap]
    calc |2 * epsR par * Pl (lR P) par h * Pl (lR P) par r
          + (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR P),
              (sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par r t)|
        ≤ |2 * epsR par * Pl (lR P) par h * Pl (lR P) par r|
          + |(1 / Real.pi) * ∫ t in (0 : ℝ)..(TR P),
              (sym t - b0R P) * (Tr (lR P) par h t * Tr (lR P) par r t)| :=
          abs_add_le _ _
      _ ≤ 2 * ((P.Cp : ℚ) : ℝ) * dN * (A * B) + ((P.S0 : ℚ) : ℝ) / 3 * I1 * (A * B) :=
          add_le_add h1 h2
      _ = (2 * ((P.Cp : ℚ) : ℝ) * dN + ((P.S0 : ℚ) : ℝ) / 3 * I1) * (A * B) := by ring
  -- the tail term
  have htailR : ((dT P par N : ℚ) : ℝ) * Y ≤ Rb P sym par r r := by
    unfold Rb
    rw [← hYdef]
    have h1 : -2 * dN ^ 2 * B ^ 2 ≤ 2 * epsR par * Pl (lR P) par r * Pl (lR P) par r := by
      have hP2 : Pl (lR P) par r ^ 2 ≤ (dN * B) ^ 2 :=
        sq_le_sq' (abs_le.mp hPr).1 (abs_le.mp hPr).2
      unfold epsR
      split_ifs
      · nlinarith [sq_nonneg (Pl (lR P) par r)]
      · nlinarith
    have h2 : -(((P.S0 : ℚ) : ℝ) / 3 * I2 * B ^ 2)
        ≤ (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR P),
            (sym t - b0R P) * (Tr (lR P) par r t * Tr (lR P) par r t) := by
      have hb' := abs_int_le_of_abs_le' P hpc
        (f := fun t => (sym t - b0R P) * (Tr (lR P) par r t * Tr (lR P) par r t))
        (g := fun t => ((P.S0 : ℚ) : ℝ) * (epsW P (2 * N + par) t ^ 2 * B ^ 2)) (by fun_prop) (by fun_prop)
        (by
          intro t ht
          rw [abs_mul, abs_mul]
          have hT' := hTr t ht
          have hTT : |Tr (lR P) par r t| * |Tr (lR P) par r t| ≤ epsW P (2 * N + par) t ^ 2 * B ^ 2 := by
            have := mul_le_mul hT' hT' (abs_nonneg _)
              (by have := epsW_nonneg P hpc (2 * N + par) ht.1; positivity)
            nlinarith
          exact mul_le_mul (hs.bound t ht.1 ht.2) hTT (by positivity) hS0)
      have e : ∫ t in (0 : ℝ)..(TR P), ((P.S0 : ℚ) : ℝ) * (epsW P (2 * N + par) t ^ 2 * B ^ 2)
          = ((P.S0 : ℚ) : ℝ) * I2 * B ^ 2 := by
        rw [hI2]
        have e2 : (fun t => ((P.S0 : ℚ) : ℝ) * (epsW P (2 * N + par) t ^ 2 * B ^ 2))
            = fun t => (((P.S0 : ℚ) : ℝ) * B ^ 2) * epsW P (2 * N + par) t ^ 2 := by funext t; ring
        rw [e2, intervalIntegral.integral_const_mul]
        ring
      rw [e] at hb'
      have hSIB : 0 ≤ ((P.S0 : ℚ) : ℝ) * I2 * B ^ 2 := by positivity
      have hq := neg_abs_le (∫ t in (0 : ℝ)..(TR P),
        (sym t - b0R P) * (Tr (lR P) par r t * Tr (lR P) par r t))
      have h3 : -(1 / Real.pi) * (((P.S0 : ℚ) : ℝ) * I2 * B ^ 2)
          ≤ (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR P),
              (sym t - b0R P) * (Tr (lR P) par r t * Tr (lR P) par r t) := by
        have := mul_le_mul_of_nonneg_left (le_trans (neg_le_neg hb') hq)
          (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
        linarith
      have h4 : (1 / Real.pi) * (((P.S0 : ℚ) : ℝ) * I2 * B ^ 2)
          ≤ 1 / 3 * (((P.S0 : ℚ) : ℝ) * I2 * B ^ 2) :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hpi3) hSIB
      linarith
    rw [hdT]
    have hK0 : (0 : ℝ) ≤ 2 * dN ^ 2 + ((P.S0 : ℚ) : ℝ) / 3 * I2 := by positivity
    have hK := mul_le_mul_of_nonneg_left hsqY hK0
    have e1 : (b0R P - 2 * lR P * (2 * dN ^ 2 + ((P.S0 : ℚ) : ℝ) / 3 * I2)) * Y
        = b0R P * Y - (2 * dN ^ 2 + ((P.S0 : ℚ) : ℝ) / 3 * I2) * (2 * lR P * Y) := by ring
    have e2 : (2 * dN ^ 2 + ((P.S0 : ℚ) : ℝ) / 3 * I2) * B ^ 2
        = 2 * dN ^ 2 * B ^ 2 + ((P.S0 : ℚ) : ℝ) / 3 * I2 * B ^ 2 := by ring
    rw [e1]
    linarith [h1, h2, hK, e2]
  -- the head term
  have hhead : ((lam : ℚ) : ℝ) * X ≤ Rb P sym par h h := by
    rw [hXdef, hhdef]
    exact head_floor P hs hpc hb hpar htail hcert a
  -- assembly
  have hRv : Rb P sym par v v = Rb P sym par h h + 2 * Rb P sym par h r + Rb P sym par r r := by
    rw [hvhr]; exact Rb_expand P hsc par hc hrc
  have hIv : ip (lR P) v v = X + Y := by
    have hs' : Continuous (fun x => h x + r x) := hc.add hrc
    rw [hvhr, ip_add_left' _ hc hrc hs', ip_comm' _ h, ip_comm' _ r, ip_add_left' _ hc hrc hc,
      ip_add_left' _ hc hrc hrc, ip_comm' _ r h, hhr, hXdef, hYdef]
    ring
  rw [hRv, hIv]
  have hl1R : ((P.lamFloor : ℚ) : ℝ) ≤ ((lam : ℚ) : ℝ) := by exact_mod_cast hl1
  have hl2R : ((P.lamFloor : ℚ) : ℝ) ≤ ((dT P par N : ℚ) : ℝ) := by exact_mod_cast hl2
  have hl3R : 4 * ((kapT P par N : ℚ) : ℝ) ^ 2 * lR P ^ 2
      ≤ (((lam : ℚ) : ℝ) - ((P.lamFloor : ℚ) : ℝ)) * (((dT P par N : ℚ) : ℝ) - ((P.lamFloor : ℚ) : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hl3
    push_cast at this
    exact this
  have hk0 : 0 ≤ ((kapT P par N : ℚ) : ℝ) := by rw [hkap]; positivity
  -- 2x2: (lam - lam') X + (d - lam') Y >= 2 kap A B
  set α := ((lam : ℚ) : ℝ) - ((P.lamFloor : ℚ) : ℝ) with hα
  set δ := ((dT P par N : ℚ) : ℝ) - ((P.lamFloor : ℚ) : ℝ) with hδ
  set κ := ((kapT P par N : ℚ) : ℝ) with hκ
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hAB : (A * B) ^ 2 ≤ 4 * lR P ^ 2 * (X * Y) := by
    have := mul_le_mul hsqX hsqY (sq_nonneg B) (by positivity)
    nlinarith
  have hkey : 2 * κ * (A * B) ≤ α * X + δ * Y := by
    have hsq1 : (2 * κ * (A * B)) ^ 2 ≤ (α * X + δ * Y) ^ 2 := by
      have e1 : (2 * κ * (A * B)) ^ 2 = 4 * κ ^ 2 * (A * B) ^ 2 := by ring
      have e2 : 4 * κ ^ 2 * (A * B) ^ 2 ≤ 4 * κ ^ 2 * (4 * lR P ^ 2 * (X * Y)) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
      have e3 : 4 * κ ^ 2 * (4 * lR P ^ 2 * (X * Y)) ≤ 4 * (α * δ) * (X * Y) := by
        have := mul_le_mul_of_nonneg_right hl3R (by positivity : (0 : ℝ) ≤ 4 * (X * Y))
        nlinarith
      have e4 : 4 * (α * δ) * (X * Y) ≤ (α * X + δ * Y) ^ 2 := by
        nlinarith [sq_nonneg (α * X - δ * Y)]
      linarith
    have hpos : 0 ≤ α * X + δ * Y := by positivity
    exact (pow_le_pow_iff_left₀ (by positivity) hpos (by norm_num : (2 : ℕ) ≠ 0)).mp hsq1
  have hcr := (abs_le.mp hcross).1
  have hl' : ((lam : ℚ) : ℝ) = α + ((P.lamFloor : ℚ) : ℝ) := by rw [hα]; ring
  have hd' : ((dT P par N : ℚ) : ℝ) = δ + ((P.lamFloor : ℚ) : ℝ) := by rw [hδ]; ring
  rw [hl'] at hhead
  rw [hd'] at htailR
  have e3 : (α + ((P.lamFloor : ℚ) : ℝ)) * X = α * X + ((P.lamFloor : ℚ) : ℝ) * X := by ring
  have e4 : (δ + ((P.lamFloor : ℚ) : ℝ)) * Y = δ * Y + ((P.lamFloor : ℚ) : ℝ) * Y := by ring
  rw [e3] at hhead
  rw [e4] at htailR
  have e5 : ((P.lamFloor : ℚ) : ℝ) * (X + Y)
      = ((P.lamFloor : ℚ) : ℝ) * X + ((P.lamFloor : ℚ) : ℝ) * Y := by ring
  rw [e5]
  linarith [hkey, hhead, htailR, hcr]

end KWin2

end
