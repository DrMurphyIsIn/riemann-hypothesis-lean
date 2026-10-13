/-
  Hodge1_TailP -- the projection tail and the sector floor of the HODGE-1 strip form (2026-10-12,
  Phase 1b-A): KWin2_Tail with the penalty pc in place of 2 eps and with the strip block.

  conjecture1_proved = False.  No zeros, no primes.

  PROVED HERE (`RbP_floor`): for EVERY continuous v, each sector and every symbol with `SymHyp`,
      lamFloor int_{-l}^{l} v^2 <= RbP H sym par v v - w2up Sform s0 l v v,
  from the head certificate (Hodge1_HeadP.head_floorP) and KWin2's projection tail.  With
  v = h + r (h the L^2[-l, l] projection on the head monomials, by the kernel-checked Cauchy inverse,
  r orthogonal to every head monomial):
    * RbP v = RbP h + 2 RbP(h, r) + RbP r;  |RbP(h, r)| <= kapTP A1(h) A1(r) (pc |Pl h| |Pl r| uses
      the tail pole remainder dPT; the Fourier part as in KWin2);  RbP r >= (beta0 - 2l S0/3 I2T) int r^2
      (the tail pole term pc (Pl r)^2 >= 0 is dropped);
    * the strip: Sform v v = Sform h h + 2 Sform(h, r) + Sform r r,  Sform r r <= int r^2, and, for the
      leakage polynomial p (any head polynomial, int p r = 0),
          Sform_{[s0,l]}(h, r) = Sform_{[s0,l]}(h - p, r) - Sform_{[0,s0]}(p, r),
      so Young's inequality gives 2 Sform(h, r) <= eta Bleak + int r^2 / eta;
    * the head bracket RbP h - w2up (Sform h h + eta Bleak) >= lam int h^2 (head_floorP), the tail
      bracket RbP r - w2up (1 + 1/eta) int r^2 >= dTP int r^2, and KWin2's 2x2 closure.
  No `sorry`.
-/
import Hodge1_HeadP
import KWin2_Tail

open Real Finset MeasureTheory intervalIntegral

noncomputable section

namespace Hodge1
open KWin (Tr Pl ip mo A1 phiF poleF continuous_Tr Tr_sub_le Pl_sub_le abs_Tr_le abs_Pl_le A1_nonneg
  A1_sq_le continuous_phiF continuous_poleF mget mget_map_range getD_map_range
  piLoQ piHiQ pi_gt_Q pi_lt_Q)
open KWin2

variable (H : HPar)

/-! ## A. Linearity. -/

/-- The bilinear expansion `RbP(h + r) = RbP(h) + 2 RbP(h, r) + RbP(r)`. -/
theorem RbP_expand {sym : ℝ → ℝ} (hsc : Continuous sym) (par : ℕ) {h r : ℝ → ℝ} (hh : Continuous h)
    (hr : Continuous r) :
    RbP H sym par (fun x => h x + r x) (fun x => h x + r x)
      = RbP H sym par h h + 2 * RbP H sym par h r + RbP H sym par r r := by
  have hs : Continuous (fun x => h x + r x) := hh.add hr
  unfold RbP
  rw [Pl_add' _ hh hr, ip_add_left' _ hh hr hs, ip_comm' _ h, ip_comm' _ r, ip_add_left' _ hh hr hh,
    ip_add_left' _ hh hr hr, ip_comm' _ r h]
  have cTh := continuous_Tr (lR H.K) par hh
  have cTr := continuous_Tr (lR H.K) par hr
  have cP : Continuous fun t => sym t - b0R H.K := hsc.sub continuous_const
  have e : (fun t => (sym t - b0R H.K) * (Tr (lR H.K) par (fun x => h x + r x) t
        * Tr (lR H.K) par (fun x => h x + r x) t))
      = fun t => ((sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par h t)
        + 2 * ((sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par r t)))
        + (sym t - b0R H.K) * (Tr (lR H.K) par r t * Tr (lR H.K) par r t) := by
    funext t; rw [Tr_add' _ hh hr t]; ring
  rw [e, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul]
  ring

/-- The strip expansion `S(h + r) = S(h) + 2 S(h, r) + S(r)`. -/
lemma Sform_expand (a b : ℝ) {h r : ℝ → ℝ} (hh : Continuous h) (hr : Continuous r) :
    Sform a b (fun x => h x + r x) (fun x => h x + r x)
      = Sform a b h h + 2 * Sform a b h r + Sform a b r r := by
  have hs : Continuous (fun x => h x + r x) := hh.add hr
  rw [Sform_add_left a b hh hr hs, Sform_comm a b h, Sform_comm a b r, Sform_add_left a b hh hr hh,
    Sform_add_left a b hh hr hr, Sform_comm a b r h]
  ring

/-- Young from below: `-(eta S(f, f) + S(g, g)/eta) <= 2 S(f, g)`. -/
lemma neg_two_Sform_le {a b : ℝ} (hab : a ≤ b) {η : ℝ} (hη : 0 < η) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    -(η * Sform a b f f + (1 / η) * Sform a b g g) ≤ 2 * Sform a b f g := by
  have hfn : Continuous fun x => -f x := hf.neg
  have h1 := two_Sform_le hab hη hfn hg
  have e1 : Sform a b (fun x => -f x) g = -Sform a b f g := by
    unfold Sform; rw [← intervalIntegral.integral_neg]; congr 1; funext x; ring
  have e2 : Sform a b (fun x => -f x) (fun x => -f x) = Sform a b f f := by
    unfold Sform; congr 1; funext x; ring
  rw [e1, e2] at h1
  linarith

/-! ## B. The sector floor. -/

set_option maxHeartbeats 4000000 in
theorem RbP_floor {sym : ℝ → ℝ} (hs : SymHyp H.K sym) (hpc : parCheck H.K = true)
    (hb : brkCheck H.K = true) {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam eta : ℚ}
    (htail : tailCondP H par N lam eta = true) {D : List (List ℚ)}
    (hcert : HeadPSD (headMatP H par N lam eta D) N) (hginv : ginvCheck H.K par N = true)
    {v : ℝ → ℝ} (hv : Continuous v) :
    ((H.K.lamFloor : ℚ) : ℝ) * ip (lR H.K) v v
      ≤ RbP H sym par v v - w2R H * Sform (s0R H) (lR H.K) v v := by
  obtain ⟨hl1, hl2, hl3, _, _, hN, _, hN1, _, _, _, _, _⟩ := tailCondP_sound H htail
  have hl := lR_pos H.K hpc
  have hT := (TR_pos H.K hpc).le
  have hsc := hs.cont
  have hpcR := pcR_nonneg H htail
  have hw2 := w2R_nonneg H htail
  have heta := eta_pos H htail
  have hs0 := s0R_nonneg H htail
  have hsl := s0R_le H htail
  -- the projection
  set b : ℕ → ℝ := fun l => mo (lR H.K) v (2 * l + par) with hbdef
  set a : ℕ → ℝ := fun j => ∑ l ∈ range N, ((mget (ginvM H.K par N) j l : ℚ) : ℝ) * b l with hadef
  set h := hfun H.K par N a with hhdef
  have hc : Continuous h := continuous_hfun H.K par N a
  set r : ℝ → ℝ := fun x => v x - h x with hrdef
  have hrc : Continuous r := hv.sub hc
  have hvhr : v = fun x => h x + r x := by funext x; simp only [hrdef]; ring
  -- orthogonality
  have horth : ∀ m < N, mo (lR H.K) r (2 * m + par) = 0 := by
    intro m hm
    rw [hrdef, mo_sub' _ hv hc, hhdef, mo_hfun H.K hpc]
    have hsum : ∑ k ∈ range N, a k * ((Gm H.K par k m : ℚ) : ℝ) = b m := by
      rw [hadef]
      simp only
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      have hδ : ∀ l ∈ range N, ∑ k ∈ range N,
          ((mget (ginvM H.K par N) k l : ℚ) : ℝ) * b l * ((Gm H.K par k m : ℚ) : ℝ)
            = if m = l then b l else 0 := by
        intro l hlN
        have hG := ginvCheck_sound H.K hginv hm (Finset.mem_range.mp hlN)
        have hG' : ∑ k ∈ range N, ((Gm H.K par m k : ℚ) : ℝ) * ((mget (ginvM H.K par N) k l : ℚ) : ℝ)
            = if m = l then 1 else 0 := by
          have := congrArg (fun q : ℚ => (q : ℝ)) hG
          push_cast at this
          rw [this]
          split_ifs <;> simp
        have e : ∑ k ∈ range N, ((mget (ginvM H.K par N) k l : ℚ) : ℝ) * b l * ((Gm H.K par k m : ℚ) : ℝ)
            = (∑ k ∈ range N, ((Gm H.K par m k : ℚ) : ℝ) * ((mget (ginvM H.K par N) k l : ℚ) : ℝ)) * b l := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Gm_symm H.K par k m]
          ring
        rw [e, hG']
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hδ, Finset.sum_ite_eq]
      simp [Finset.mem_range.mpr hm]
    rw [hsum]
    simp [hbdef]
  -- int h r = 0 and int p r = 0
  have hhr : ip (lR H.K) h r = 0 := by
    rw [hhdef, ip_hfun_left H.K par N a hrc]
    exact Finset.sum_eq_zero fun k hk => by rw [horth k (Finset.mem_range.mp hk), mul_zero]
  set p := pfun H par N D a with hpdef
  have hpc' : Continuous p := continuous_pfun H par N D a
  have hpr : ip (lR H.K) p r = 0 := by
    rw [hpdef, pfun, ip_hfun_left H.K par N _ hrc]
    exact Finset.sum_eq_zero fun k hk => by rw [horth k (Finset.mem_range.mp hk), mul_zero]
  -- tail transform and pole bounds
  set A := A1 (lR H.K) h with hAdef
  set B := A1 (lR H.K) r with hBdef
  have hA0 : 0 ≤ A := A1_nonneg hl.le h
  have hB0 : 0 ≤ B := A1_nonneg hl.le r
  set X := ip (lR H.K) h h with hXdef
  set Y := ip (lR H.K) r r with hYdef
  have hsqX : A ^ 2 ≤ 2 * lR H.K * X := by
    have := A1_sq_le hl hc
    rw [hXdef]; unfold ip
    have e : (fun x => h x ^ 2) = fun x => h x * h x := by funext x; ring
    rwa [e] at this
  have hsqY : B ^ 2 ≤ 2 * lR H.K * Y := by
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
  have hTr : ∀ t ∈ Set.Icc (0 : ℝ) (TR H.K), |Tr (lR H.K) par r t| ≤ epsW H.K (2 * N + par) t * B := by
    intro t ht
    have htl : t * lR H.K ≤ (2 * N + par + 1) / 2 := by
      have h1 : t * lR H.K ≤ TR H.K * lR H.K := mul_le_mul_of_nonneg_right ht.2 hl.le
      have h2 := (Rat.cast_le (K := ℝ)).mpr hN
      push_cast at h2
      have e : TR H.K * lR H.K = ((H.K.T : ℚ) : ℝ) * ((H.K.ell : ℚ) : ℝ) := rfl
      linarith
    have := Tr_sub_le hl hpar hrc ht.1 htl
    have hz : ∑ m ∈ range N, (-1) ^ m * (t * lR H.K) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo (lR H.K) r (2 * m + par) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [horth m (Finset.mem_range.mp hm), mul_zero]
    rw [hz, sub_zero] at this
    unfold epsW
    exact this
  set dN : ℝ := 2 * (lR H.K / 2) ^ (2 * N + par) / ((2 * N + par).factorial : ℝ) with hdN
  have hdN0 : 0 ≤ dN := by rw [hdN]; positivity
  have hPr : |Pl (lR H.K) par r| ≤ dN * B := by
    have hNpos : 0 < 2 * N + par := by omega
    have := Pl_sub_le hl (lR_half_le H.K hpc) hpar hNpos hrc
    have hz : ∑ m ∈ range N, (lR H.K / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
        * mo (lR H.K) r (2 * m + par) = 0 :=
      Finset.sum_eq_zero fun m hm => by rw [horth m (Finset.mem_range.mp hm), mul_zero]
    rw [hz, sub_zero] at this
    rw [hdN]; exact this
  have hPh : |Pl (lR H.K) par h| ≤ ((H.K.Cp : ℚ) : ℝ) * A := by
    have h1 := abs_Pl_le hl par hc
    exact h1.trans (mul_le_mul_of_nonneg_right hs.cosh hA0)
  have hTh : ∀ t, |Tr (lR H.K) par h t| ≤ A := fun t => abs_Tr_le hl par hc t
  -- constants
  have hpi := Real.pi_pos
  have hpi3 : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hS0 := S0_nonneg H.K hpc
  have hCp := Cp_nonneg H.K hpc
  set I1 := ∫ t in (0 : ℝ)..(TR H.K), epsW H.K (2 * N + par) t with hI1
  set I2 := ∫ t in (0 : ℝ)..(TR H.K), epsW H.K (2 * N + par) t ^ 2 with hI2
  have hI10 : 0 ≤ I1 := intervalIntegral.integral_nonneg hT fun t ht => epsW_nonneg H.K hpc _ ht.1
  have hI20 : 0 ≤ I2 := intervalIntegral.integral_nonneg hT fun t _ => sq_nonneg _
  have hkap : ((kapTP H par N : ℚ) : ℝ) = pcR H * ((H.K.Cp : ℚ) : ℝ) * dN + ((H.K.S0 : ℚ) : ℝ) / 3 * I1 := by
    rw [hI1, int_epsW]
    unfold kapTP dPT I1T pcR
    rw [hdN]
    unfold lR TR
    push_cast
    ring
  have hdT : ((dTP H par N eta : ℚ) : ℝ)
      = b0R H.K - 2 * lR H.K * (((H.K.S0 : ℚ) : ℝ) / 3 * I2) - w2R H * (1 + 1 / (eta : ℝ)) := by
    rw [hI2, int_epsW_sq]
    unfold dTP I2T w2R
    unfold lR TR b0R
    push_cast
    ring
  have hcP : Continuous fun t => sym t - b0R H.K := hsc.sub continuous_const
  have cTh := continuous_Tr (lR H.K) par hc
  have cTr := continuous_Tr (lR H.K) par hrc
  have hce := continuous_epsW H.K (2 * N + par)
  -- the coupling
  have hcross : |RbP H sym par h r| ≤ ((kapTP H par N : ℚ) : ℝ) * (A * B) := by
    unfold RbP
    rw [hhr, mul_zero, add_zero]
    have h1 : |pcR H * Pl (lR H.K) par h * Pl (lR H.K) par r|
        ≤ pcR H * ((H.K.Cp : ℚ) : ℝ) * dN * (A * B) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hpcR]
      calc pcR H * |Pl (lR H.K) par h| * |Pl (lR H.K) par r|
          ≤ pcR H * (((H.K.Cp : ℚ) : ℝ) * A) * (dN * B) := by gcongr
        _ = pcR H * ((H.K.Cp : ℚ) : ℝ) * dN * (A * B) := by ring
    have h2 : |(1 / Real.pi) * ∫ t in (0 : ℝ)..(TR H.K),
          (sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par r t)|
        ≤ ((H.K.S0 : ℚ) : ℝ) / 3 * I1 * (A * B) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      have hb' := abs_int_le_of_abs_le' H.K hpc
        (f := fun t => (sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par r t))
        (g := fun t => ((H.K.S0 : ℚ) : ℝ) * (A * (epsW H.K (2 * N + par) t * B))) (by fun_prop)
        (by fun_prop)
        (by
          intro t ht
          rw [abs_mul, abs_mul]
          exact mul_le_mul (hs.bound t ht.1 ht.2)
            (mul_le_mul (hTh t) (hTr t ht) (abs_nonneg _) hA0) (by positivity) hS0)
      have e : ∫ t in (0 : ℝ)..(TR H.K), ((H.K.S0 : ℚ) : ℝ) * (A * (epsW H.K (2 * N + par) t * B))
          = ((H.K.S0 : ℚ) : ℝ) * I1 * (A * B) := by
        rw [hI1]
        have e2 : (fun t => ((H.K.S0 : ℚ) : ℝ) * (A * (epsW H.K (2 * N + par) t * B)))
            = fun t => (((H.K.S0 : ℚ) : ℝ) * (A * B)) * epsW H.K (2 * N + par) t := by funext t; ring
        rw [e2, intervalIntegral.integral_const_mul]
        ring
      rw [e] at hb'
      have hSIAB : 0 ≤ ((H.K.S0 : ℚ) : ℝ) * I1 * (A * B) := by positivity
      calc 1 / Real.pi * |∫ t in (0 : ℝ)..(TR H.K),
            (sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par r t)|
          ≤ 1 / Real.pi * (((H.K.S0 : ℚ) : ℝ) * I1 * (A * B)) :=
            mul_le_mul_of_nonneg_left hb' (by positivity)
        _ ≤ 1 / 3 * (((H.K.S0 : ℚ) : ℝ) * I1 * (A * B)) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hpi3) hSIAB
        _ = ((H.K.S0 : ℚ) : ℝ) / 3 * I1 * (A * B) := by ring
    rw [hkap]
    calc |pcR H * Pl (lR H.K) par h * Pl (lR H.K) par r
          + (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR H.K),
              (sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par r t)|
        ≤ |pcR H * Pl (lR H.K) par h * Pl (lR H.K) par r|
          + |(1 / Real.pi) * ∫ t in (0 : ℝ)..(TR H.K),
              (sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par r t)| :=
          abs_add_le _ _
      _ ≤ pcR H * ((H.K.Cp : ℚ) : ℝ) * dN * (A * B) + ((H.K.S0 : ℚ) : ℝ) / 3 * I1 * (A * B) :=
          add_le_add h1 h2
      _ = (pcR H * ((H.K.Cp : ℚ) : ℝ) * dN + ((H.K.S0 : ℚ) : ℝ) / 3 * I1) * (A * B) := by ring
  -- the tail term
  have htailR : (b0R H.K - 2 * lR H.K * (((H.K.S0 : ℚ) : ℝ) / 3 * I2)) * Y ≤ RbP H sym par r r := by
    unfold RbP
    rw [← hYdef]
    have h1 : 0 ≤ pcR H * Pl (lR H.K) par r * Pl (lR H.K) par r := by
      rw [mul_assoc]; exact mul_nonneg hpcR (mul_self_nonneg _)
    have h2 : -(((H.K.S0 : ℚ) : ℝ) / 3 * I2 * B ^ 2)
        ≤ (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR H.K),
            (sym t - b0R H.K) * (Tr (lR H.K) par r t * Tr (lR H.K) par r t) := by
      have hb' := abs_int_le_of_abs_le' H.K hpc
        (f := fun t => (sym t - b0R H.K) * (Tr (lR H.K) par r t * Tr (lR H.K) par r t))
        (g := fun t => ((H.K.S0 : ℚ) : ℝ) * (epsW H.K (2 * N + par) t ^ 2 * B ^ 2)) (by fun_prop)
        (by fun_prop)
        (by
          intro t ht
          rw [abs_mul, abs_mul]
          have hT' := hTr t ht
          have hTT : |Tr (lR H.K) par r t| * |Tr (lR H.K) par r t|
              ≤ epsW H.K (2 * N + par) t ^ 2 * B ^ 2 := by
            have := mul_le_mul hT' hT' (abs_nonneg _)
              (by have := epsW_nonneg H.K hpc (2 * N + par) ht.1; positivity)
            nlinarith
          exact mul_le_mul (hs.bound t ht.1 ht.2) hTT (by positivity) hS0)
      have e : ∫ t in (0 : ℝ)..(TR H.K), ((H.K.S0 : ℚ) : ℝ) * (epsW H.K (2 * N + par) t ^ 2 * B ^ 2)
          = ((H.K.S0 : ℚ) : ℝ) * I2 * B ^ 2 := by
        rw [hI2]
        have e2 : (fun t => ((H.K.S0 : ℚ) : ℝ) * (epsW H.K (2 * N + par) t ^ 2 * B ^ 2))
            = fun t => (((H.K.S0 : ℚ) : ℝ) * B ^ 2) * epsW H.K (2 * N + par) t ^ 2 := by
          funext t; ring
        rw [e2, intervalIntegral.integral_const_mul]
        ring
      rw [e] at hb'
      have hSIB : 0 ≤ ((H.K.S0 : ℚ) : ℝ) * I2 * B ^ 2 := by positivity
      have hq := neg_abs_le (∫ t in (0 : ℝ)..(TR H.K),
        (sym t - b0R H.K) * (Tr (lR H.K) par r t * Tr (lR H.K) par r t))
      have h3 : -(1 / Real.pi) * (((H.K.S0 : ℚ) : ℝ) * I2 * B ^ 2)
          ≤ (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR H.K),
              (sym t - b0R H.K) * (Tr (lR H.K) par r t * Tr (lR H.K) par r t) := by
        have := mul_le_mul_of_nonneg_left (le_trans (neg_le_neg hb') hq)
          (by positivity : (0 : ℝ) ≤ 1 / Real.pi)
        linarith
      have h4 : (1 / Real.pi) * (((H.K.S0 : ℚ) : ℝ) * I2 * B ^ 2)
          ≤ 1 / 3 * (((H.K.S0 : ℚ) : ℝ) * I2 * B ^ 2) :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) hpi3) hSIB
      linarith
    have hK0 : (0 : ℝ) ≤ ((H.K.S0 : ℚ) : ℝ) / 3 * I2 := by positivity
    have hK := mul_le_mul_of_nonneg_left hsqY hK0
    nlinarith [h1, h2, hK]
  -- the strip: S(v) = S(h) + 2 S(h, r) + S(r), S(r) <= Y, 2 S(h, r) <= eta Bleak + Y / eta
  have hSv : Sform (s0R H) (lR H.K) v v
      = Sform (s0R H) (lR H.K) h h + 2 * Sform (s0R H) (lR H.K) h r + Sform (s0R H) (lR H.K) r r := by
    rw [hvhr]; exact Sform_expand _ _ hc hrc
  have hYS : Y = Sform 0 (s0R H) r r + Sform (s0R H) (lR H.K) r r := by
    rw [hYdef]; exact ip_eq_Sform _ _ hrc hrc
  have hSr0 := Sform_self_nonneg hs0 r
  have hSr : Sform (s0R H) (lR H.K) r r ≤ Y := by linarith
  have hdp : Continuous fun x => h x - p x := hc.sub hpc'
  have hShr : Sform (s0R H) (lR H.K) h r
      = Sform (s0R H) (lR H.K) (fun x => h x - p x) r - Sform 0 (s0R H) p r := by
    have e1 := Sform_sub_left (s0R H) (lR H.K) hc hpc' hrc
    have e2 := ip_eq_Sform (lR H.K) (s0R H) hpc' hrc
    rw [hpr] at e2
    linarith
  have hY1 := two_Sform_le hsl heta hdp hrc
  have hY2 := neg_two_Sform_le hs0 heta hpc' hrc
  have hBl : Bleak H par N D a
      = Sform (s0R H) (lR H.K) (fun x => h x - p x) (fun x => h x - p x) + Sform 0 (s0R H) p p := rfl
  have hcrossS : 2 * Sform (s0R H) (lR H.K) h r ≤ (eta : ℝ) * Bleak H par N D a + (1 / (eta : ℝ)) * Y := by
    rw [hShr, hBl, hYS]
    linarith
  -- the head term
  have hhead : ((lam : ℚ) : ℝ) * X
      ≤ RbP H sym par h h - w2R H * (Sform (s0R H) (lR H.K) h h + (eta : ℝ) * Bleak H par N D a) := by
    rw [hXdef, hhdef]
    exact head_floorP H hs hpc hb hpar htail hcert a
  -- assembly
  have hRv : RbP H sym par v v = RbP H sym par h h + 2 * RbP H sym par h r + RbP H sym par r r := by
    rw [hvhr]; exact RbP_expand H hsc par hc hrc
  have hIv : ip (lR H.K) v v = X + Y := by
    have hs' : Continuous (fun x => h x + r x) := hc.add hrc
    rw [hvhr, ip_add_left' _ hc hrc hs', ip_comm' _ h, ip_comm' _ r, ip_add_left' _ hc hrc hc,
      ip_add_left' _ hc hrc hrc, ip_comm' _ r h, hhr, hXdef, hYdef]
    ring
  -- the strip part of the form, in one inequality
  have hstrip : w2R H * Sform (s0R H) (lR H.K) v v
      ≤ w2R H * (Sform (s0R H) (lR H.K) h h + (eta : ℝ) * Bleak H par N D a)
        + w2R H * (1 + 1 / (eta : ℝ)) * Y := by
    rw [hSv]
    have := mul_le_mul_of_nonneg_left (add_le_add hcrossS hSr) hw2
    nlinarith
  rw [hRv, hIv]
  have hl1R : ((H.K.lamFloor : ℚ) : ℝ) ≤ ((lam : ℚ) : ℝ) := by exact_mod_cast hl1
  have hl2R : ((H.K.lamFloor : ℚ) : ℝ) ≤ ((dTP H par N eta : ℚ) : ℝ) := by exact_mod_cast hl2
  have hl3R : 4 * ((kapTP H par N : ℚ) : ℝ) ^ 2 * lR H.K ^ 2
      ≤ (((lam : ℚ) : ℝ) - ((H.K.lamFloor : ℚ) : ℝ))
        * (((dTP H par N eta : ℚ) : ℝ) - ((H.K.lamFloor : ℚ) : ℝ)) := by
    have := (Rat.cast_le (K := ℝ)).mpr hl3
    push_cast at this
    exact this
  have hk0 : 0 ≤ ((kapTP H par N : ℚ) : ℝ) := by rw [hkap]; positivity
  -- 2x2: (lam - lam') X + (d - lam') Y >= 2 kap A B
  set α := ((lam : ℚ) : ℝ) - ((H.K.lamFloor : ℚ) : ℝ) with hα
  set δ := ((dTP H par N eta : ℚ) : ℝ) - ((H.K.lamFloor : ℚ) : ℝ) with hδ
  set κ := ((kapTP H par N : ℚ) : ℝ) with hκ
  have hα0 : 0 ≤ α := by rw [hα]; linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hAB : (A * B) ^ 2 ≤ 4 * lR H.K ^ 2 * (X * Y) := by
    have := mul_le_mul hsqX hsqY (sq_nonneg B) (by positivity)
    nlinarith
  have hkey : 2 * κ * (A * B) ≤ α * X + δ * Y := by
    have hsq1 : (2 * κ * (A * B)) ^ 2 ≤ (α * X + δ * Y) ^ 2 := by
      have e1 : (2 * κ * (A * B)) ^ 2 = 4 * κ ^ 2 * (A * B) ^ 2 := by ring
      have e2 : 4 * κ ^ 2 * (A * B) ^ 2 ≤ 4 * κ ^ 2 * (4 * lR H.K ^ 2 * (X * Y)) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
      have e3 : 4 * κ ^ 2 * (4 * lR H.K ^ 2 * (X * Y)) ≤ 4 * (α * δ) * (X * Y) := by
        have := mul_le_mul_of_nonneg_right hl3R (by positivity : (0 : ℝ) ≤ 4 * (X * Y))
        nlinarith
      have e4 : 4 * (α * δ) * (X * Y) ≤ (α * X + δ * Y) ^ 2 := by
        nlinarith [sq_nonneg (α * X - δ * Y)]
      linarith
    have hpos : 0 ≤ α * X + δ * Y := by positivity
    exact (pow_le_pow_iff_left₀ (by positivity) hpos (by norm_num : (2 : ℕ) ≠ 0)).mp hsq1
  have hcr := (abs_le.mp hcross).1
  have hdT' : ((dTP H par N eta : ℚ) : ℝ) * Y
      = (b0R H.K - 2 * lR H.K * (((H.K.S0 : ℚ) : ℝ) / 3 * I2)) * Y - w2R H * (1 + 1 / (eta : ℝ)) * Y := by
    rw [hdT]; ring
  have hlX : ((lam : ℚ) : ℝ) * X = α * X + ((H.K.lamFloor : ℚ) : ℝ) * X := by rw [hα]; ring
  have hdY : ((dTP H par N eta : ℚ) : ℝ) * Y = δ * Y + ((H.K.lamFloor : ℚ) : ℝ) * Y := by rw [hδ]; ring
  have e5 : ((H.K.lamFloor : ℚ) : ℝ) * (X + Y)
      = ((H.K.lamFloor : ℚ) : ℝ) * X + ((H.K.lamFloor : ℚ) : ℝ) * Y := by ring
  rw [e5]
  linarith [hkey, hhead, htailR, hcr, hstrip, hdT', hlX, hdY]

end Hodge1

end
