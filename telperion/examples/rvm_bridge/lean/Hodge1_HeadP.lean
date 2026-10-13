/-
  Hodge1_HeadP -- the head inequality of the HODGE-1 archimedean strip certificate: KWin2_Head with the
  pole coefficient 2 eps replaced by a penalty pc >= 0 and with the strip block (2026-10-12, Phase 1b-A).

  conjecture1_proved = False.  No zeros, no primes.

  THE FORMS.  For an HPar H, a symbol `sym`, a sector par and continuous f, g on [-l, l]:
      RbP H sym par f g = pc Pl f Pl g + beta0 int_{-l}^{l} f g
                          + (1/pi) int_0^T (sym(t) - beta0) Tr f t Tr g t dt,
      Sform a b f g     = int_a^b (f g)(x) + (f g)(-x) dx        (Sform s0 l f f = int_{s0 <= |x| <= l} f^2),
  and, for the head polynomial h = sum_k a_k (x/l)^(2k+par) and any rational matrix D, the leakage
      Bleak = Sform s0 l (h - p) (h - p) + Sform 0 s0 p p,    p = sum_k (D a)_k (x/l)^(2k+par),
  i.e. Bleak = int_{-l}^{l} (1_S' h - p)^2 with S' = {s0 <= |x| <= l}.

  PROVED HERE (`head_floorP`): whenever tailCondP evaluates to true and the head matrix headMatP is PSD,
      lam int h^2 <= RbP h h - w2up (Sform s0 l h h + eta Bleak).
  The same chain as KWin2_Head.head_floor (Taylor truncations of the transform and of the pole
  functional with errors <= Econst, exact moments of the minorant), plus the closed forms
      Sform s0 l h h = a^T Pim a,   Bleak = a^T leakQ a,
  with pi <= pi_hi on the (nonnegative) strip block.  No `sorry`.
-/
import Hodge1_KPen
import KWin2_Head

open Real Finset MeasureTheory intervalIntegral

noncomputable section

namespace Hodge1
open KWin (Tr Pl ip mo A1 phiF poleF continuous_Tr Tr_sub_le Pl_sub_le abs_Tr_le abs_Pl_le A1_nonneg
  A1_sq_le continuous_phiF continuous_poleF mget mget_map_range getD_map_range
  piLoQ piHiQ pi_gt_Q pi_lt_Q quad_outer quad_hankel)
open KWin2

variable (H : HPar)

/-! ## A. The forms. -/

def s0R : ℝ := ((H.s0 : ℚ) : ℝ)
def w2R : ℝ := ((H.w2up : ℚ) : ℝ)
def pcR : ℝ := ((H.pc : ℚ) : ℝ)

/-- The symmetric strip form `int_a^b (f g)(x) + (f g)(-x) dx`. -/
def Sform (a b : ℝ) (f g : ℝ → ℝ) : ℝ := ∫ x in a..b, (f x * g x + f (-x) * g (-x))

/-- The penalised split form (KWin2's `Rb` with `2 eps` replaced by `pc`). -/
def RbP (sym : ℝ → ℝ) (par : ℕ) (f g : ℝ → ℝ) : ℝ :=
  pcR H * Pl (lR H.K) par f * Pl (lR H.K) par g + b0R H.K * ip (lR H.K) f g
    + (1 / Real.pi) * ∫ t in (0 : ℝ)..(TR H.K),
        (sym t - b0R H.K) * (Tr (lR H.K) par f t * Tr (lR H.K) par g t)

/-- The leakage coefficients `d = D a`. -/
def dvec (N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ range N, ((mget D i k : ℚ) : ℝ) * a k

/-- The leakage polynomial `p = sum_i d_i (x/l)^(2i+par)`. -/
def pfun (par N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) : ℝ → ℝ := hfun H.K par N (dvec N D a)

/-- The leakage `int_{-l}^{l} (1_S' h - p)^2`, split at `s0`. -/
def Bleak (par N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) : ℝ :=
  Sform (s0R H) (lR H.K) (fun x => hfun H.K par N a x - pfun H par N D a x)
      (fun x => hfun H.K par N a x - pfun H par N D a x)
    + Sform 0 (s0R H) (pfun H par N D a) (pfun H par N D a)

/-! ## B. Algebra of the strip form. -/

lemma Sform_integrable {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun x => f x * g x + f (-x) * g (-x)) volume a b :=
  Continuous.intervalIntegrable (by fun_prop) a b

lemma Sform_comm (a b : ℝ) (f g : ℝ → ℝ) : Sform a b f g = Sform a b g f := by
  unfold Sform; congr 1; funext x; ring

lemma Sform_add_left (a b : ℝ) {f g w : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hw : Continuous w) :
    Sform a b (fun x => f x + g x) w = Sform a b f w + Sform a b g w := by
  unfold Sform
  rw [← intervalIntegral.integral_add (Sform_integrable hf hw a b) (Sform_integrable hg hw a b)]
  congr 1; funext x; ring

lemma Sform_sub_left (a b : ℝ) {f g w : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hw : Continuous w) :
    Sform a b (fun x => f x - g x) w = Sform a b f w - Sform a b g w := by
  unfold Sform
  rw [← intervalIntegral.integral_sub (Sform_integrable hf hw a b) (Sform_integrable hg hw a b)]
  congr 1; funext x; ring

lemma Sform_self_nonneg {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) : 0 ≤ Sform a b f f :=
  intervalIntegral.integral_nonneg hab fun _ _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- Young's inequality under the strip form: `2 S(f, g) <= eta S(f, f) + S(g, g)/eta`. -/
lemma two_Sform_le {a b : ℝ} (hab : a ≤ b) {η : ℝ} (hη : 0 < η) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    2 * Sform a b f g ≤ η * Sform a b f f + (1 / η) * Sform a b g g := by
  have key : ∀ x, 2 * (f x * g x + f (-x) * g (-x))
      ≤ η * (f x * f x + f (-x) * f (-x)) + (1 / η) * (g x * g x + g (-x) * g (-x)) := by
    intro x
    have h1 : 0 ≤ (η * f x - g x) ^ 2 / η := by positivity
    have h2 : 0 ≤ (η * f (-x) - g (-x)) ^ 2 / η := by positivity
    have e1 : (η * f x - g x) ^ 2 / η = η * (f x * f x) - 2 * (f x * g x) + (1 / η) * (g x * g x) := by
      field_simp; ring
    have e2 : (η * f (-x) - g (-x)) ^ 2 / η
        = η * (f (-x) * f (-x)) - 2 * (f (-x) * g (-x)) + (1 / η) * (g (-x) * g (-x)) := by
      field_simp; ring
    nlinarith
  unfold Sform
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((Sform_integrable hf hf a b).const_mul _)
      ((Sform_integrable hg hg a b).const_mul _)]
  exact intervalIntegral.integral_mono_on hab ((Sform_integrable hf hg a b).const_mul _)
    (((Sform_integrable hf hf a b).const_mul _).add ((Sform_integrable hg hg a b).const_mul _))
    fun x _ => key x

/-- `int_{-l}^{l} F = int_0^l (F x + F (-x))`. -/
lemma integral_symm_split (l : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ x in (-l)..l, F x = ∫ x in (0 : ℝ)..l, (F x + F (-x)) := by
  have hneg : IntervalIntegrable (fun x => F (-x)) volume 0 l :=
    (hF.comp continuous_neg).intervalIntegrable _ _
  have e1 : ∫ x in (0 : ℝ)..l, (F x + F (-x)) = (∫ x in (0 : ℝ)..l, F x) + ∫ x in (0 : ℝ)..l, F (-x) :=
    intervalIntegral.integral_add (hF.intervalIntegrable _ _) hneg
  have e2 : ∫ x in (0 : ℝ)..l, F (-x) = ∫ x in (-l)..0, F x := by
    rw [intervalIntegral.integral_comp_neg (fun x => F x)]
    simp
  rw [e1, e2, ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hF.intervalIntegrable _ _)
    (hF.intervalIntegrable _ _)]
  ring

/-- `int_{-l}^{l} f g = S_{[0, s0]}(f, g) + S_{[s0, l]}(f, g)`. -/
lemma ip_eq_Sform (l s : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ip l f g = Sform 0 s f g + Sform s l f g := by
  unfold ip Sform
  rw [integral_symm_split l (F := fun x => f x * g x) (hf.mul hg)]
  exact (intervalIntegral.integral_add_adjacent_intervals (Sform_integrable hf hg _ _)
    (Sform_integrable hf hg _ _)).symm

/-! ## C. Closed forms on the head polynomials. -/

lemma hfun_mul_sym (par N : ℕ) (a b : ℕ → ℝ) (x : ℝ) :
    hfun H.K par N a x * hfun H.K par N b x + hfun H.K par N a (-x) * hfun H.K par N b (-x)
      = ∑ j ∈ range N, ∑ k ∈ range N, a j * b k * (2 * (x / lR H.K) ^ (2 * j + 2 * k + 2 * par)) := by
  unfold hfun
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e1 : (x / lR H.K) ^ (2 * j + par) * (x / lR H.K) ^ (2 * k + par)
      = (x / lR H.K) ^ (2 * j + 2 * k + 2 * par) := by
    rw [← pow_add]; congr 1; ring
  have e2 : (-x / lR H.K) ^ (2 * j + par) * (-x / lR H.K) ^ (2 * k + par)
      = (x / lR H.K) ^ (2 * j + 2 * k + 2 * par) := by
    rw [← pow_add, show 2 * j + par + (2 * k + par) = 2 * (j + k + par) by ring, pow_mul, neg_div,
      neg_sq, ← pow_mul]
    congr 1; ring
  calc a j * (x / lR H.K) ^ (2 * j + par) * (b k * (x / lR H.K) ^ (2 * k + par))
        + a j * (-x / lR H.K) ^ (2 * j + par) * (b k * (-x / lR H.K) ^ (2 * k + par))
      = a j * b k * ((x / lR H.K) ^ (2 * j + par) * (x / lR H.K) ^ (2 * k + par)
          + (-x / lR H.K) ^ (2 * j + par) * (-x / lR H.K) ^ (2 * k + par)) := by ring
    _ = a j * b k * (2 * (x / lR H.K) ^ (2 * j + 2 * k + 2 * par)) := by rw [e1, e2]; ring

lemma int_pow_strip (hpc : parCheck H.K = true) (n : ℕ) :
    ∫ x in (s0R H)..(lR H.K), (x / lR H.K) ^ n
      = lR H.K / (n + 1) * (1 - (s0R H / lR H.K) ^ (n + 1)) := by
  have hl := lR_pos H.K hpc
  rw [intervalIntegral.integral_comp_div (fun x => x ^ n) hl.ne', integral_pow, smul_eq_mul,
    div_self hl.ne']
  field_simp
  ring

lemma Sform_hfun (hpc : parCheck H.K = true) (par N : ℕ) (a b : ℕ → ℝ) :
    Sform (s0R H) (lR H.K) (hfun H.K par N a) (hfun H.K par N b)
      = ∑ j ∈ range N, ∑ k ∈ range N, a j * b k * ((Pim H par j k : ℚ) : ℝ) := by
  unfold Sform
  simp_rw [hfun_mul_sym H par N a b]
  rw [intervalIntegral.integral_finsetSum fun j _ => Continuous.intervalIntegrable
    (continuous_finsetSum _ fun k _ => by fun_prop) _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, int_pow_strip H hpc]
  unfold Pim s0R lR
  push_cast
  ring

/-! ## D. The leakage as a quadratic form. -/

lemma quad_PD (par N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((mget (PDmat H par N D) j k : ℚ) : ℝ)
      = ∑ j ∈ range N, ∑ i ∈ range N, a j * dvec N D a i * ((Pim H par j i : ℚ) : ℝ) := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hrow : ∀ k ∈ range N, ((mget (PDmat H par N D) j k : ℚ) : ℝ)
      = ∑ i ∈ range N, ((Pim H par j i : ℚ) : ℝ) * ((mget D i k : ℚ) : ℝ) := by
    intro k hk
    unfold PDmat
    rw [mget_map_range _ (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)]
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun k hk => by rw [hrow k hk]]
  unfold dvec
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma quad_PDT (par N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((mget (PDmat H par N D) k j : ℚ) : ℝ)
      = ∑ j ∈ range N, ∑ i ∈ range N, a j * dvec N D a i * ((Pim H par j i : ℚ) : ℝ) := by
  rw [← quad_PD H par N D a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma sum4_swap (N : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, ∑ i ∈ range N, ∑ i' ∈ range N, f j k i i'
      = ∑ i ∈ range N, ∑ i' ∈ range N, ∑ j ∈ range N, ∑ k ∈ range N, f j k i i' := by
  calc _ = ∑ j ∈ range N, ∑ i ∈ range N, ∑ k ∈ range N, ∑ i' ∈ range N, f j k i i' :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j ∈ range N, ∑ i ∈ range N, ∑ i' ∈ range N, ∑ k ∈ range N, f j k i i' :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ range N, ∑ j ∈ range N, ∑ i' ∈ range N, ∑ k ∈ range N, f j k i i' := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

lemma quad_DGD (par N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((mget (DGDmat H par N D) j k : ℚ) : ℝ)
      = ∑ i ∈ range N, ∑ i' ∈ range N, dvec N D a i * dvec N D a i' * ((Gm H.K par i i' : ℚ) : ℝ) := by
  have hent : ∀ j ∈ range N, ∀ k ∈ range N, ((mget (DGDmat H par N D) j k : ℚ) : ℝ)
      = ∑ i ∈ range N, ∑ i' ∈ range N,
          ((mget D i j : ℚ) : ℝ) * ((Gm H.K par i i' : ℚ) : ℝ) * ((mget D i' k : ℚ) : ℝ) := by
    intro j hj k hk
    unfold DGDmat
    rw [mget_map_range _ (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    unfold GDmat
    rw [mget_map_range _ (Finset.mem_range.mp hi) (Finset.mem_range.mp hk)]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    ring
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by rw [hent j hj k hk]]
  have hL : ∀ j ∈ range N, ∀ k ∈ range N, a j * a k * ∑ i ∈ range N, ∑ i' ∈ range N,
        ((mget D i j : ℚ) : ℝ) * ((Gm H.K par i i' : ℚ) : ℝ) * ((mget D i' k : ℚ) : ℝ)
      = ∑ i ∈ range N, ∑ i' ∈ range N,
        a j * a k * (((mget D i j : ℚ) : ℝ) * ((Gm H.K par i i' : ℚ) : ℝ) * ((mget D i' k : ℚ) : ℝ)) := by
    intro j _ k _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hL j hj k hk, sum4_swap]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  unfold dvec
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma continuous_pfun (par N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) : Continuous (pfun H par N D a) :=
  continuous_hfun H.K par N _

/-- The leakage is the quadratic form of `leakQ`. -/
theorem quad_leakQ (hpc : parCheck H.K = true) (par N : ℕ) (D : List (List ℚ)) (a : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((leakQ H par N D j k : ℚ) : ℝ) = Bleak H par N D a := by
  set h := hfun H.K par N a with hh
  set p := pfun H par N D a with hp
  have hc : Continuous h := continuous_hfun H.K par N a
  have pc : Continuous p := continuous_pfun H par N D a
  -- the function side
  have hB : Bleak H par N D a
      = Sform (s0R H) (lR H.K) h h - 2 * Sform (s0R H) (lR H.K) h p + ip (lR H.K) p p := by
    unfold Bleak
    rw [← hh, ← hp]
    have hd : Continuous fun x => h x - p x := hc.sub pc
    have e1 := Sform_sub_left (s0R H) (lR H.K) hc pc hd
    have e2 : Sform (s0R H) (lR H.K) h (fun x => h x - p x)
        = Sform (s0R H) (lR H.K) h h - Sform (s0R H) (lR H.K) p h := by
      rw [Sform_comm, Sform_sub_left _ _ hc pc hc]
    have e3 : Sform (s0R H) (lR H.K) p (fun x => h x - p x)
        = Sform (s0R H) (lR H.K) h p - Sform (s0R H) (lR H.K) p p := by
      rw [Sform_comm, Sform_sub_left _ _ hc pc pc]
    have e4 := Sform_comm (s0R H) (lR H.K) p h
    have e5 := ip_eq_Sform (lR H.K) (s0R H) pc pc
    rw [e1, e2, e3, e4, e5]
    ring
  rw [hB, hh, hp, Sform_hfun H hpc, pfun, Sform_hfun H hpc, ip_hfun_self H.K hpc]
  -- the matrix side
  have hsplit : ∀ j k, ((leakQ H par N D j k : ℚ) : ℝ)
      = ((Pim H par j k : ℚ) : ℝ) - ((mget (PDmat H par N D) j k : ℚ) : ℝ)
        - ((mget (PDmat H par N D) k j : ℚ) : ℝ) + ((mget (DGDmat H par N D) j k : ℚ) : ℝ) := by
    intro j k; unfold leakQ; push_cast; ring
  simp_rw [hsplit, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [quad_PD, quad_PDT, quad_DGD]
  ring

lemma Bleak_nonneg (hs0 : 0 ≤ s0R H) (hsl : s0R H ≤ lR H.K) (par N : ℕ) (D : List (List ℚ))
    (a : ℕ → ℝ) : 0 ≤ Bleak H par N D a :=
  add_nonneg (Sform_self_nonneg hsl _) (Sform_self_nonneg hs0 _)

/-! ## E. The quadratic form of the certified matrix. -/

lemma quad_headEntryP {par N : ℕ} (lam eta : ℚ) (D : List (List ℚ)) (a : ℕ → ℝ) :
    ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((headEntryP H par N lam eta D j k : ℚ) : ℝ)
      = ((piLoQ : ℚ) : ℝ) * pcR H * (∑ j ∈ range N, a j * ((pv H.K par j : ℚ) : ℝ)) ^ 2
        + ((diagc H.K lam : ℚ) : ℝ) * ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm H.K par j k : ℚ) : ℝ)
        + ∑ m ∈ range H.K.Mt, ∑ m' ∈ range H.K.Mt, (((momList H.K par).getD (m + m') 0 : ℚ) : ℝ)
            * (∑ j ∈ range N, ((Bm H.K par m j : ℚ) : ℝ) * a j)
            * (∑ k ∈ range N, ((Bm H.K par m' k : ℚ) : ℝ) * a k)
        - ((piHiQ : ℚ) : ℝ) * w2R H * (∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Pim H par j k : ℚ) : ℝ)
            + (eta : ℝ) * ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((leakQ H par N D j k : ℚ) : ℝ)) := by
  have hentry : ∀ j ∈ range N, ∀ k ∈ range N, ((headEntryP H par N lam eta D j k : ℚ) : ℝ)
      = ((piLoQ : ℚ) : ℝ) * pcR H * ((pv H.K par j : ℚ) : ℝ) * ((pv H.K par k : ℚ) : ℝ)
        + ((diagc H.K lam : ℚ) : ℝ) * ((Gm H.K par j k : ℚ) : ℝ)
        + ∑ m ∈ range H.K.Mt, ((Bm H.K par m j : ℚ) : ℝ) * ∑ m' ∈ range H.K.Mt,
            (((momList H.K par).getD (m + m') 0 : ℚ) : ℝ) * ((Bm H.K par m' k : ℚ) : ℝ)
        - ((piHiQ : ℚ) : ℝ) * w2R H * (((Pim H par j k : ℚ) : ℝ) + (eta : ℝ) * ((leakQ H par N D j k : ℚ) : ℝ)) := by
    intro j _ k hk
    unfold headEntryP pcR w2R
    push_cast
    congr 2
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    unfold WBmat
    rw [getD_map_range _ _ (Finset.mem_range.mp hm)]
    unfold WBrow
    rw [getD_map_range _ _ (Finset.mem_range.mp hk)]
    push_cast
    rfl
  have key : ∀ j ∈ range N, ∀ k ∈ range N, a j * a k * ((headEntryP H par N lam eta D j k : ℚ) : ℝ)
      = a j * a k * ((((piLoQ : ℚ) : ℝ) * pcR H) * ((pv H.K par j : ℚ) : ℝ) * ((pv H.K par k : ℚ) : ℝ))
        + ((diagc H.K lam : ℚ) : ℝ) * (a j * a k * ((Gm H.K par j k : ℚ) : ℝ))
        + a j * a k * ∑ m ∈ range H.K.Mt, ((Bm H.K par m j : ℚ) : ℝ) * ∑ m' ∈ range H.K.Mt,
            (((momList H.K par).getD (m + m') 0 : ℚ) : ℝ) * ((Bm H.K par m' k : ℚ) : ℝ)
        - (((piHiQ : ℚ) : ℝ) * w2R H) * (a j * a k * ((Pim H par j k : ℚ) : ℝ))
        - (((piHiQ : ℚ) : ℝ) * w2R H * (eta : ℝ)) * (a j * a k * ((leakQ H par N D j k : ℚ) : ℝ)) := by
    intro j hj k hk
    rw [hentry j hj k hk]
    ring
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => key j hj k hk]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [quad_outer N a (fun j => ((pv H.K par j : ℚ) : ℝ)) (((piLoQ : ℚ) : ℝ) * pcR H),
    quad_hankel N H.K.Mt a (fun m j => ((Bm H.K par m j : ℚ) : ℝ))
      (fun s => (((momList H.K par).getD s 0 : ℚ) : ℝ))]
  ring

/-! ## F. The pole term with a penalty. -/

lemma pole_sq_boundP {pc Pv Pt A dP Cp : ℝ} (hpc : 0 ≤ pc) (hA : 0 ≤ A) (hdP : 0 ≤ dP) (hCp : 0 ≤ Cp)
    (h1 : |Pv - Pt| ≤ dP * A) (h2 : |Pv| ≤ Cp * A) :
    ((piLoQ : ℚ) : ℝ) * pc * Pt ^ 2 - pc * ((piHiQ : ℚ) : ℝ) * (dP * (2 * Cp + dP)) * A ^ 2
      ≤ Real.pi * pc * Pv ^ 2 := by
  have hlo := pi_gt_Q
  have hhi := pi_lt_Q
  have hd : |Pv ^ 2 - Pt ^ 2| ≤ dP * (2 * Cp + dP) * A ^ 2 := by
    have hPt : |Pt| ≤ (Cp + dP) * A := by
      have := abs_sub_abs_le_abs_sub Pt Pv
      rw [abs_sub_comm] at this
      nlinarith [abs_nonneg Pv]
    rw [sq_sub_sq, abs_mul]
    have h3 : |Pv + Pt| ≤ (2 * Cp + dP) * A := by
      refine (abs_add_le _ _).trans ?_
      nlinarith
    calc |Pv + Pt| * |Pv - Pt| ≤ ((2 * Cp + dP) * A) * (dP * A) :=
          mul_le_mul h3 h1 (abs_nonneg _) (by positivity)
      _ = dP * (2 * Cp + dP) * A ^ 2 := by ring
  have hE : 0 ≤ dP * (2 * Cp + dP) * A ^ 2 := by positivity
  rw [abs_le] at hd
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hPt2 : 0 ≤ Pt ^ 2 := sq_nonneg _
  have e1 : ((piLoQ : ℚ) : ℝ) * pc * Pt ^ 2 ≤ Real.pi * pc * Pt ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo.le hpc) hPt2
  have e2 : Real.pi * pc * (dP * (2 * Cp + dP) * A ^ 2)
      ≤ ((piHiQ : ℚ) : ℝ) * pc * (dP * (2 * Cp + dP) * A ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhi.le hpc) hE
  have e3 : Real.pi * pc * (Pt ^ 2 - dP * (2 * Cp + dP) * A ^ 2) ≤ Real.pi * pc * Pv ^ 2 :=
    mul_le_mul_of_nonneg_left (by linarith [hd.1]) (by positivity)
  nlinarith

/-! ## G. The head floor. -/

lemma pcR_nonneg {par N : ℕ} {lam eta : ℚ} (htail : tailCondP H par N lam eta = true) : 0 ≤ pcR H := by
  unfold pcR; exact_mod_cast (tailCondP_sound H htail).2.2.2.2.2.2.2.2.1

lemma w2R_nonneg {par N : ℕ} {lam eta : ℚ} (htail : tailCondP H par N lam eta = true) : 0 ≤ w2R H := by
  unfold w2R; exact_mod_cast (tailCondP_sound H htail).2.2.2.2.2.2.2.2.2.2.1

lemma eta_pos {par N : ℕ} {lam eta : ℚ} (htail : tailCondP H par N lam eta = true) : (0 : ℝ) < eta := by
  exact_mod_cast (tailCondP_sound H htail).2.2.2.2.2.2.2.2.2.1

lemma s0R_nonneg {par N : ℕ} {lam eta : ℚ} (htail : tailCondP H par N lam eta = true) : 0 ≤ s0R H := by
  unfold s0R; exact_mod_cast (tailCondP_sound H htail).2.2.2.2.2.2.2.2.2.2.2.1

lemma s0R_le {par N : ℕ} {lam eta : ℚ} (htail : tailCondP H par N lam eta = true) : s0R H ≤ lR H.K := by
  unfold s0R lR; exact_mod_cast (tailCondP_sound H htail).2.2.2.2.2.2.2.2.2.2.2.2

set_option maxHeartbeats 1000000 in
theorem head_floorP {sym : ℝ → ℝ} (hs : SymHyp H.K sym) (hpc : parCheck H.K = true)
    (hb : brkCheck H.K = true) {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam eta : ℚ}
    (htail : tailCondP H par N lam eta = true) {D : List (List ℚ)}
    (hcert : HeadPSD (headMatP H par N lam eta D) N) (a : ℕ → ℝ) :
    (lam : ℝ) * ip (lR H.K) (hfun H.K par N a) (hfun H.K par N a)
      ≤ RbP H sym par (hfun H.K par N a) (hfun H.K par N a)
        - w2R H * (Sform (s0R H) (lR H.K) (hfun H.K par N a) (hfun H.K par N a)
          + (eta : ℝ) * Bleak H par N D a) := by
  obtain ⟨_, _, _, hE, hlam, _, hM, _, _, _, _, _, _⟩ := tailCondP_sound H htail
  have hpcR := pcR_nonneg H htail
  have hw2 := w2R_nonneg H htail
  have heta := eta_pos H htail
  set h := hfun H.K par N a with hh
  have hc : Continuous h := continuous_hfun H.K par N a
  have hl := lR_pos H.K hpc
  set X := ip (lR H.K) h h with hX
  set A := A1 (lR H.K) h with hA
  have hA0 : 0 ≤ A := A1_nonneg hl.le h
  have hA2 : A ^ 2 ≤ 2 * lR H.K * X := by
    have := A1_sq_le hl hc
    rw [hX]
    unfold ip
    have e : (fun x => h x ^ 2) = fun x => h x * h x := by funext x; ring
    rw [e] at this
    exact this
  have hX0 : 0 ≤ X := by
    rw [hX]; unfold ip
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => mul_self_nonneg _
  -- the strip block
  set SB := Sform (s0R H) (lR H.K) h h + (eta : ℝ) * Bleak H par N D a with hSB
  have hSB0 : 0 ≤ SB := by
    rw [hSB]
    have h1 := Sform_self_nonneg (s0R_le H htail) h
    have h2 := Bleak_nonneg H (s0R_nonneg H htail) (s0R_le H htail) par N D a
    positivity
  -- the pole term
  set Pt := ∑ k ∈ range N, a k * ((pv H.K par k : ℚ) : ℝ) with hPt
  set dP : ℝ := 2 * (lR H.K / 2) ^ (2 * H.K.Mp + par) / ((2 * H.K.Mp + par).factorial : ℝ) with hdP
  have hdP0 : 0 ≤ dP := by rw [hdP]; positivity
  have hPt_eq : ∑ m ∈ range H.K.Mp, (lR H.K / 2) ^ (2 * m + par) / ((2 * m + par).factorial : ℝ)
      * mo (lR H.K) h (2 * m + par) = Pt := by
    rw [hPt, hh]
    simp_rw [mo_hfun H.K hpc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold pv
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Gm_symm H.K par k m]
    unfold lR
    ring
  have hP1 : |Pl (lR H.K) par h - Pt| ≤ dP * A := by
    have hM0 : 0 < 2 * H.K.Mp + par := by
      have := (parCheck_sound H.K hpc).2.2.2.2.2.2.2; omega
    have := Pl_sub_le hl (lR_half_le H.K hpc) hpar (M := H.K.Mp) hM0 hc
    rw [hPt_eq] at this
    rw [hdP]; exact this
  have hP2 : |Pl (lR H.K) par h| ≤ ((H.K.Cp : ℚ) : ℝ) * A := by
    have h1 := abs_Pl_le hl par hc
    exact h1.trans (mul_le_mul_of_nonneg_right hs.cosh hA0)
  have hpole := pole_sq_boundP hpcR hA0 hdP0 (Cp_nonneg H.K hpc) hP1 hP2
  -- the transform term
  set c : ℕ → ℝ := fun m => ∑ k ∈ range N, ((Bm H.K par m k : ℚ) : ℝ) * a k with hcdef
  set pt : ℝ → ℝ := fun t => ∑ m ∈ range H.K.Mt, c m * t ^ (2 * m + par) with hpt
  have hptc : Continuous pt := by rw [hpt]; fun_prop
  have hpt_eq : ∀ t, ∑ m ∈ range H.K.Mt, (-1) ^ m * (t * lR H.K) ^ (2 * m + par)
      / ((2 * m + par).factorial : ℝ) * mo (lR H.K) h (2 * m + par) = pt t := by
    intro t
    rw [hpt]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcdef, hh, mo_hfun H.K hpc]
    simp only
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Gm_symm H.K par k m]
    unfold Bm
    push_cast
    rw [mul_pow]
    unfold lR
    ring
  have hT1 : ∀ t ∈ Set.Icc (0 : ℝ) (TR H.K),
      |Tr (lR H.K) par h t - pt t| ≤ epsW H.K (2 * H.K.Mt + par) t * A := by
    intro t ht
    have htl : t * lR H.K ≤ (2 * H.K.Mt + par + 1) / 2 := by
      have h1 : t * lR H.K ≤ TR H.K * lR H.K := mul_le_mul_of_nonneg_right ht.2 hl.le
      have h2 := (Rat.cast_le (K := ℝ)).mpr hM
      push_cast at h2
      have e : TR H.K * lR H.K = ((H.K.T : ℚ) : ℝ) * ((H.K.ell : ℚ) : ℝ) := rfl
      linarith
    have := Tr_sub_le hl hpar hc ht.1 htl
    rw [hpt_eq] at this
    unfold epsW
    exact this
  have hT2 : ∀ t ∈ Set.Icc (0 : ℝ) (TR H.K), |Tr (lR H.K) par h t| ≤ A := fun t _ => abs_Tr_le hl par hc t
  have hint := int_sq_perturb H.K hpc hs (continuous_Tr (lR H.K) par hc) hptc hA0 (2 * H.K.Mt + par) hT1 hT2
  have hmom := moment_floor H.K hs hb par c
  -- the error constant
  have hEle : pcR H * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((H.K.Cp : ℚ) : ℝ) + dP))
      + ((H.K.S0 : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..(TR H.K), epsW H.K (2 * H.K.Mt + par) t)
        + ∫ t in (0 : ℝ)..(TR H.K), epsW H.K (2 * H.K.Mt + par) t ^ 2) ≤ ((H.K.Econst : ℚ) : ℝ) := by
    rw [int_epsW, int_epsW_sq]
    have h1 : ((EheadP H par : ℚ) : ℝ) ≤ ((H.K.Econst : ℚ) : ℝ) := by exact_mod_cast hE
    refine le_trans (le_of_eq ?_) h1
    unfold EheadP pcR
    rw [hdP]
    unfold lR TR
    push_cast
    ring
  -- the quadratic form
  have hquad := quad_headEntryP H (par := par) (N := N) lam eta D a
  have hGX : ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Gm H.K par j k : ℚ) : ℝ) = X := by
    rw [hX, hh, ip_hfun_self H.K hpc]
  have hPiS : ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((Pim H par j k : ℚ) : ℝ)
      = Sform (s0R H) (lR H.K) h h := by
    rw [hh, Sform_hfun H hpc]
  rw [hGX, hPiS, quad_leakQ H hpc] at hquad
  have hWc : ∑ m ∈ range H.K.Mt, ∑ m' ∈ range H.K.Mt, (((momList H.K par).getD (m + m') 0 : ℚ) : ℝ)
        * (∑ j ∈ range N, ((Bm H.K par m j : ℚ) : ℝ) * a j)
        * (∑ k ∈ range N, ((Bm H.K par m' k : ℚ) : ℝ) * a k)
      = ∑ m ∈ range H.K.Mt, ∑ m' ∈ range H.K.Mt, (((momList H.K par).getD (m + m') 0 : ℚ) : ℝ)
          * c m * c m' := rfl
  rw [hWc] at hquad
  have hpsd := hcert a
  have hmat : ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((mget (headMatP H par N lam eta D) j k : ℚ) : ℝ)
      = ∑ j ∈ range N, ∑ k ∈ range N, a j * a k * ((headEntryP H par N lam eta D j k : ℚ) : ℝ) := by
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    unfold headMatP
    rw [mget_map_range _ (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)]
  rw [hmat, hquad] at hpsd
  rw [← hSB] at hpsd
  -- assemble
  have hpi := Real.pi_pos
  have hlo := pi_gt_Q
  have hhi := pi_lt_Q
  have hbl : (lam : ℝ) < b0R H.K := by unfold b0R; exact_mod_cast hlam
  have hdiag : ((diagc H.K lam : ℚ) : ℝ)
      = ((piLoQ : ℚ) : ℝ) * (b0R H.K - lam) - 2 * lR H.K * ((H.K.Econst : ℚ) : ℝ) := by
    unfold diagc b0R lR; push_cast; ring
  rw [hdiag] at hpsd
  have hRb : Real.pi * (RbP H sym par h h - w2R H * SB - (lam : ℝ) * X)
      = Real.pi * pcR H * (Pl (lR H.K) par h) ^ 2 + Real.pi * (b0R H.K - lam) * X
        + (∫ t in (0 : ℝ)..(TR H.K), (sym t - b0R H.K) * (Tr (lR H.K) par h t) ^ 2)
        - Real.pi * w2R H * SB := by
    unfold RbP
    rw [← hX]
    have e : (fun t => (sym t - b0R H.K) * (Tr (lR H.K) par h t * Tr (lR H.K) par h t))
        = fun t => (sym t - b0R H.K) * (Tr (lR H.K) par h t) ^ 2 := by funext t; ring
    rw [e]
    field_simp
    ring
  have hfin : 0 ≤ Real.pi * (RbP H sym par h h - w2R H * SB - (lam : ℝ) * X) := by
    rw [hRb]
    have hEc := Econst_nonneg H.K hpc
    have h1 : ((piLoQ : ℚ) : ℝ) * (b0R H.K - lam) * X ≤ Real.pi * (b0R H.K - lam) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo.le (by linarith)) hX0
    have h2 : ((H.K.S0 : ℚ) : ℝ) * (2 * (∫ t in (0 : ℝ)..(TR H.K), epsW H.K (2 * H.K.Mt + par) t)
        + ∫ t in (0 : ℝ)..(TR H.K), epsW H.K (2 * H.K.Mt + par) t ^ 2) * A ^ 2
          + pcR H * ((piHiQ : ℚ) : ℝ) * (dP * (2 * ((H.K.Cp : ℚ) : ℝ) + dP)) * A ^ 2
        ≤ ((H.K.Econst : ℚ) : ℝ) * (2 * lR H.K * X) := by
      have := mul_le_mul hEle hA2 (sq_nonneg A) hEc
      linarith
    have h3 : Real.pi * w2R H * SB ≤ ((piHiQ : ℚ) : ℝ) * w2R H * SB :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhi.le hw2) hSB0
    linarith
  have := (mul_nonneg_iff_of_pos_left hpi).mp hfin
  linarith

end Hodge1

end
