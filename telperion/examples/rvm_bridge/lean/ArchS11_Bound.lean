/-
  ArchS11_Bound -- from the kernel-checked S11 data to quadratic-form bounds (stage S11, rvm_bridge
  island, 2026-10-11).

  For a > 0 and the polynomial kernel k(x, y) = pv E (|x/a - y/a|) + c0 on [0, a]:
    * `form_bound_of_cert`: a checked certificate (uOK, rhoOK, dOK, qmatOK, ldlOK, tailOK) gives
          re ⟪T_k f, f⟫ ≤ a λ̂ ‖f‖²   for EVERY f ∈ L²([0, a])   (Galerkin + Schur + HS tail);
    * `form_lower_of_test`: a checked test vector gives a λ̂_lo ‖u‖² ≤ re ⟪T_k u, u⟫, u ≠ 0;
    * `abs_chiPoly_sub_pv`: |chiPoly v - pv E (|v|/a)| ≤ dR for |v| ≤ a (the checked rounding);
    * `re_inner_sub_le`: kernels within δ on [0, a]² have forms within δ a ‖f‖².
  No `sorry`.  conjecture1_proved = False.
-/
import ArchS11_Lp
import ArchS10_Chi

open MeasureTheory Set Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ArchS11

open ArchS5 ArchS11.Data

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## A. Soundness of the Boolean checkers. -/

theorem sum_quad_cert (n : ℕ) (x : ℕ → ℝ) (C : List (ℚ × List ℚ)) :
    ∑ j ∈ range n, ∑ k ∈ range n, x j * x k
        * (((C.map (fun p => p.1 * p.2.getD j 0 * p.2.getD k 0)).sum : ℚ) : ℝ)
      = (C.map (fun p => (p.1 : ℝ) * (∑ j ∈ range n, x j * (p.2.getD j 0 : ℝ)) ^ 2)).sum := by
  induction C with
  | nil => simp
  | cons p C ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul, mul_add,
      Finset.sum_add_distrib, ih]
    congr 1
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem ldlOK_sound {A : List (List ℚ)} {L : List (ℚ × List ℚ)} {n : ℕ} (h : ldlOK A L n = true)
    (x : ℕ → ℝ) : 0 ≤ ∑ j ∈ range n, ∑ k ∈ range n, x j * x k * ((mget A j k : ℚ) : ℝ) := by
  unfold ldlOK at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hpos, heq⟩ := h
  have hA : ∀ j ∈ range n, ∀ k ∈ range n, mget A j k
      = (L.map (fun p => p.1 * p.2.getD j 0 * p.2.getD k 0)).sum := by
    intro j hj k hk
    have := heq j (List.mem_range.mpr (Finset.mem_range.mp hj))
    rw [List.all_eq_true] at this
    exact of_decide_eq_true (this k (List.mem_range.mpr (Finset.mem_range.mp hk)))
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => by rw [hA j hj k hk],
    sum_quad_cert]
  apply List.sum_nonneg
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have := of_decide_eq_true (hpos p hp)
  have h0 : (0 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast this
  positivity

theorem psiOK_sound {E : List ℚ} {Psi : List (List ℚ)} (h : psiOK E Psi = true) :
    Psi.length = NG ∧ ∀ m < NG, hatT E (unitL m) = Psi.getD m [] := by
  simpa only [psiOK, psiRow, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] using h

theorem lenOK_sound {Psi : List (List ℚ)} (h : lenOK Psi = true) :
    ∀ m < NG, (Psi.getD m []).length ≤ DL := by
  simpa only [lenOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] using h

theorem uOK_sound {Psi : List (List ℚ)} {c0 : ℚ} {U : List (List ℚ)} (h : uOK Psi c0 U = true) :
    U.length = NG ∧ ∀ j < NG, U.getD j [] = lc (ucoef c0 j) (Psi ++ [[1]]) DL := by
  simpa only [uOK, uRow, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] using h

theorem rhoOK_sound {U B rho : List (List ℚ)} (h : rhoOK U B rho = true) :
    ∀ j < NG, rho.getD j [] = lc (1 :: (List.range NG).map fun l => -mget B j l) (U.getD j [] :: PhiL) DL := by
  simp only [rhoOK, rhoRow, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.2

theorem dOK_sound {rho : List (List ℚ)} {al dh : List ℚ} (h : dOK rho al dh = true) :
    ∀ j < NG, 0 < al.getD j 0 ∧
      mom (rho.getD j []) (rho.getD j []) * (∑ k ∈ range NG, al.getD k 0) / al.getD j 0 ≤ dh.getD j 0 := by
  simpa only [dOK, dRow, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] using h

theorem qmatOK_sound {U Q : List (List ℚ)} {dh : List ℚ} {lam t : ℚ} (h : qmatOK U Q dh lam t = true) :
    ∀ j < NG, ∀ l < NG, mget Q j l = lam * mom (Phi j) (Phi l) - mom (U.getD j []) (Phi l)
      - (if j = l then t * dh.getD j 0 else 0) := by
  simpa only [qmatOK, qRow, List.all_eq_true, List.mem_range, decide_eq_true_eq] using h

theorem tailOK_sound {E : List ℚ} {c0 : ℚ} {U : List (List ℚ)} {lam t q : ℚ}
    (h : tailOK E c0 U lam t q = true) :
    0 < t ∧ 0 ≤ q ∧ q + 1 / t ≤ lam ∧ q2val E c0 U ≤ q * q := by
  simpa only [tailOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem phi_len (j : ℕ) : (Phi j).length ≤ NG := by
  by_cases h : j < 8
  · interval_cases j <;> decide
  · unfold Phi
    rw [List.getD_eq_default _ _ (by simp [PhiL]; omega)]
    simp

/-! ## B. Semantics of the checked polynomials. -/

theorem integral_kR_mul_pv (hb : binOK = true) {E : List ℚ} (hE : E.length ≤ 47) (c0 : ℚ)
    {Psi : List (List ℚ)} (hpsi : psiOK E Psi = true) {P : List ℚ} (hP : P.length ≤ NG)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∫ t in (0 : ℝ)..1, kR E c0 s t * pv P t
      = ∑ m ∈ range NG, (P.getD m 0 : ℝ) * pv (Psi.getD m []) s + c0 * (mom P [1] : ℝ) := by
  obtain ⟨_, hPsi⟩ := psiOK_sound hpsi
  have hc : ∀ m : ℕ, Continuous fun t : ℝ => pv E |s - t| * t ^ m := fun m =>
    ((continuous_pv E).comp (continuous_const.sub continuous_id).abs).mul (continuous_pow m)
  have hexp : ∀ t : ℝ, kR E c0 s t * pv P t
      = (∑ m ∈ range NG, (P.getD m 0 : ℝ) * (pv E |s - t| * t ^ m)) + c0 * (pv P t * pv [1] t) := by
    intro t
    rw [kR, pv_eq_range hP, pv_one]
    rw [add_mul, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun m _ => by ring
    · ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_add (f := fun t => ∑ m ∈ range NG, (P.getD m 0 : ℝ) * (pv E |s - t| * t ^ m))
      (g := fun t => (c0 : ℝ) * (pv P t * pv [1] t))
      ((continuous_finsetSum _ fun m _ => continuous_const.mul (hc m)).intervalIntegrable _ _)
      ((continuous_const.mul ((continuous_pv P).mul (continuous_pv _))).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (f := fun m t => (P.getD m 0 : ℝ) * (pv E |s - t| * t ^ m))
      fun m _ => (continuous_const.mul (hc m)).intervalIntegrable _ _,
    intervalIntegral.integral_const_mul, integral_pv_mul_pv]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [intervalIntegral.integral_const_mul, ← hPsi m (Finset.mem_range.1 hm), pv_hatT hb hE hs0 hs1]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [pv_unitL]

/-- The checked `U_j` is the hat kernel applied to `Phi_j`. -/
theorem pv_U_of_uOK (hb : binOK = true) {E : List ℚ} (hE : E.length ≤ 47) {Psi : List (List ℚ)}
    (hpsi : psiOK E Psi = true) (hlen : lenOK Psi = true) {c0 : ℚ} {U : List (List ℚ)}
    (hu : uOK Psi c0 U = true) {j : ℕ} (hj : j < NG) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    pv (U.getD j []) s = ∫ t in (0 : ℝ)..1, kR E c0 s t * pv (Phi j) t := by
  obtain ⟨hPl, _⟩ := psiOK_sound hpsi
  have hL := lenOK_sound hlen
  rw [(uOK_sound hu).2 j hj, integral_kR_mul_pv hb hE c0 hpsi (phi_len j) hs0 hs1]
  have hlen' : ∀ m < (ucoef c0 j).length, ((Psi ++ [[1]]).getD m []).length ≤ DL := by
    intro m hm
    simp only [ucoef, List.length_map, List.length_range] at hm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hPl]; exact hm)]
      exact hL m hm
    · rw [List.getD_append_right _ _ _ _ (by rw [hPl])]
      simp [hPl, DL]
  rw [pv_lc hlen']
  simp only [ucoef, List.length_map, List.length_range]
  rw [Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    rw [getD_map_range _ 0 (by omega), if_pos hm',
      List.getD_append _ _ _ _ (by rw [hPl]; exact hm')]
  · rw [getD_map_range _ 0 (by omega), if_neg (lt_irrefl _),
      List.getD_append_right _ _ _ _ (by rw [hPl])]
    simp [hPl, pv_one]

/-- The checked residual `rho_j = U_j - Σ_l B_jl Phi_l`. -/
theorem pv_rho_of_rhoOK {U B rho : List (List ℚ)} (hU : ∀ j < NG, (U.getD j []).length ≤ DL)
    (hr : rhoOK U B rho = true) {j : ℕ} (hj : j < NG) (s : ℝ) :
    pv (rho.getD j []) s = pv (U.getD j []) s - ∑ l ∈ range NG, (mget B j l : ℝ) * pv (Phi l) s := by
  have hlen' : ∀ m < (1 :: (List.range NG).map fun l => -mget B j l).length,
      ((U.getD j [] :: PhiL).getD m []).length ≤ DL := by
    intro m hm
    rcases m with _ | m
    · simpa using hU j hj
    · simpa [Phi] using (phi_len m).trans (by simp [NG, DL])
  rw [rhoOK_sound hr j hj, pv_lc hlen']
  simp only [List.length_cons, List.length_map, List.length_range]
  rw [Finset.sum_range_succ']
  simp only [List.getD_cons_zero, List.getD_cons_succ, Rat.cast_one, one_mul]
  rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [getD_map_range _ 0 (Finset.mem_range.1 hl)]
  simp [Phi]

theorem U_len_of_uOK {Psi : List (List ℚ)} {c0 : ℚ} {U : List (List ℚ)} (hu : uOK Psi c0 U = true) :
    ∀ j < NG, (U.getD j []).length ≤ DL := by
  intro j hj
  rw [(uOK_sound hu).2 j hj, lc_length]

/-! ## C. The certificate theorem. -/

/-- `q2val` is the real double integral `q2R` (the `if` guard drops zero terms). -/
theorem q2val_cast (E : List ℚ) (c0 : ℚ) (U : List (List ℚ)) :
    ((q2val E c0 U : ℚ) : ℝ) = q2R E c0 NG Phi (fun j => U.getD j []) wq := by
  unfold q2val q2R
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rw [h]; push_cast; ring
  · push_cast; ring

/-- **The certificate theorem.**  A checked certificate for `(E, c0)` at scale `a` gives
`re ⟪T_k f, f⟫ ≤ a λ̂ ‖f‖²` for every `f ∈ L²([0, a])`. -/
theorem form_bound_of_cert (hb : binOK = true) {a : ℝ} (ha : 0 < a) {E : List ℚ}
    (hE : E.length ≤ 47) {Psi : List (List ℚ)} (hpsi : psiOK E Psi = true) (hlen : lenOK Psi = true)
    {c0 : ℚ} {U B rho Q : List (List ℚ)} {L : List (ℚ × List ℚ)} {al dh : List ℚ} {lam t q : ℚ}
    (hok : (uOK Psi c0 U && rhoOK U B rho && dOK rho al dh && qmatOK U Q dh lam t &&
      ldlOK Q L NG && tailOK E c0 U lam t q) = true)
    (f : Lp 𝕜 2 (volI 0 a)) :
    RCLike.re ⟪intOp (kerLp a E c0) f, f⟫_𝕜 ≤ a * lam * ‖f‖ ^ 2 := by
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hu, hr⟩, hd⟩, hQ⟩, hL⟩, ht⟩ := hok
  obtain ⟨ht0, hq0, hlt, hq2⟩ := tailOK_sound ht
  have hUs : ∀ j < NG, ∀ s ∈ Icc (0 : ℝ) 1, pv (U.getD j []) s = ∫ t in (0 : ℝ)..1, kR E c0 s t * pv (Phi j) t :=
    fun j hj s hs => pv_U_of_uOK hb hE hpsi hlen hu hj hs.1 hs.2
  have hUlen := U_len_of_uOK hu
  set T := intOp (kerLp (𝕜 := 𝕜) a E c0) with hTdef
  set φ : ℕ → Lp 𝕜 2 (volI 0 a) := fun j => polyLp a (Phi j) with hφ
  set ρ : ℕ → Lp 𝕜 2 (volI 0 a) := fun j => (a : 𝕜) • polyLp a (rho.getD j []) with hρdef
  have hTφ : ∀ j < NG, T (φ j) = (a : 𝕜) • polyLp a (U.getD j []) :=
    fun j hj => intOp_kerLp_polyLp ha (hUs j hj)
  have hG : ∀ j < NG, ∀ l < NG, ⟪φ j, φ l⟫_𝕜 = ((a * mom (Phi j) (Phi l) : ℝ) : 𝕜) :=
    fun j _ l _ => inner_polyLp ha _ _
  have hC : ∀ j < NG, ∀ l < NG,
      ⟪T (φ j), φ l⟫_𝕜 = ((a ^ 2 * mom (U.getD j []) (Phi l) : ℝ) : 𝕜) := by
    intro j hj l _
    rw [hTφ j hj, inner_smul_left, inner_polyLp ha, RCLike.conj_ofReal]
    push_cast
    ring
  have hspan : ∀ j < NG, T (φ j) - ρ j ∈ Submodule.span 𝕜 (Set.range fun l : Fin NG => φ l) := by
    intro j hj
    rw [hTφ j hj, hρdef]
    simp only
    rw [← smul_sub]
    refine Submodule.smul_mem _ _ ?_
    rw [polyLp_sub_eq_sum (b := fun l => mget B j l) (P := Phi) fun s => by
      rw [pv_rho_of_rhoOK hUlen hr hj s]; ring]
    refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨l, Finset.mem_range.1 hl⟩, rfl⟩
  have hdOK := dOK_sound hd
  have hres : ∀ z : ℕ → 𝕜, ‖∑ j ∈ range NG, z j • ρ j‖ ^ 2
      ≤ qf NG (dg fun j => a ^ 3 * (dh.getD j 0 : ℝ)) z := by
    intro z
    refine (norm_sum_sq_le_weighted NG ρ z (fun j => a ^ 3 * (mom (rho.getD j []) (rho.getD j []) : ℝ))
      (fun j => (al.getD j 0 : ℝ)) (fun j hj => by exact_mod_cast (hdOK j hj).1)
      (fun j _ => le_of_eq ?_)).trans ?_
    · rw [hρdef]
      simp only
      rw [norm_smul, mul_pow, norm_polyLp_sq ha, RCLike.norm_ofReal, abs_of_pos ha]
      ring
    · rw [qf_dg, qf_dg]
      refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := (hdOK j (Finset.mem_range.1 hj)).2
      have h2 : ((mom (rho.getD j []) (rho.getD j []) * (∑ k ∈ range NG, al.getD k 0) / al.getD j 0 : ℚ) : ℝ)
          ≤ (dh.getD j 0 : ℝ) := by exact_mod_cast h1
      push_cast at h2
      have ha3 : 0 ≤ a ^ 3 := by positivity
      calc a ^ 3 * (mom (rho.getD j []) (rho.getD j []) : ℝ) * (∑ k ∈ range NG, (al.getD k 0 : ℝ))
            / (al.getD j 0 : ℝ)
          = a ^ 3 * ((mom (rho.getD j []) (rho.getD j []) : ℝ) * (∑ k ∈ range NG, (al.getD k 0 : ℝ))
            / (al.getD j 0 : ℝ)) := by ring
        _ ≤ a ^ 3 * (dh.getD j 0 : ℝ) := mul_le_mul_of_nonneg_left h2 ha3
  -- the tail
  have hKE : ‖(kerLp a E c0 - tailLp a NG Phi (fun j => U.getD j []) wq :
      Lp 𝕜 2 ((volI 0 a).prod (volI 0 a)))‖ ≤ a * q := by
    have h1 := norm_sq_ker_sub_tail (𝕜 := 𝕜) ha E c0 NG Phi (fun j => U.getD j []) wq
      (fun j hj s hs => hUs j hj s hs)
    rw [← q2val_cast] at h1
    have h2 : ((q2val E c0 U : ℚ) : ℝ) ≤ (q : ℝ) * q := by exact_mod_cast hq2
    have h3 : ‖(kerLp a E c0 - tailLp a NG Phi (fun j => U.getD j []) wq :
        Lp 𝕜 2 ((volI 0 a).prod (volI 0 a)))‖ ^ 2 ≤ (a * q) ^ 2 := by
      rw [h1, mul_pow]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg a)
    have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  have hq : ∀ r ∈ (Submodule.span 𝕜 (Set.range fun l : Fin NG => φ l))ᗮ,
      RCLike.re ⟪T r, r⟫_𝕜 ≤ (a * q) * ‖r‖ ^ 2 := by
    intro r hr'
    have hsplit : (kerLp (𝕜 := 𝕜) a E c0) = tailLp a NG Phi (fun j => U.getD j []) wq
        + (kerLp a E c0 - tailLp a NG Phi (fun j => U.getD j []) wq) := by abel
    have horth : ∀ j < NG, ⟪(polyLp a (Phi j) : Lp 𝕜 2 (volI 0 a)), r⟫_𝕜 = 0 :=
      fun j hj => Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span (Set.mem_range.2 ⟨(⟨j, hj⟩ : Fin NG), rfl⟩)) hr'
    rw [hTdef, hsplit, intOp_add, _root_.add_apply, inner_add_left, map_add,
      inner_tail_eq_zero NG Phi _ wq r horth, map_zero, zero_add]
    calc RCLike.re ⟪intOp (kerLp a E c0 - tailLp a NG Phi (fun j => U.getD j []) wq) r, r⟫_𝕜
        ≤ ‖intOp (kerLp a E c0 - tailLp a NG Phi (fun j => U.getD j []) wq) r‖ * ‖r‖ :=
          (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ (‖(kerLp a E c0 - tailLp a NG Phi (fun j => U.getD j []) wq :
            Lp 𝕜 2 ((volI 0 a).prod (volI 0 a)))‖ * ‖r‖) * ‖r‖ :=
          mul_le_mul_of_nonneg_right (norm_intOp_apply_le _ _) (norm_nonneg _)
      _ ≤ (a * q * ‖r‖) * ‖r‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKE (norm_nonneg _)) (norm_nonneg _)
      _ = (a * q) * ‖r‖ ^ 2 := by ring
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  have hlt' : (q : ℝ) + 1 / t ≤ lam := by exact_mod_cast hlt
  have hQs := qmatOK_sound hQ
  have hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ j ∈ range NG, ∑ l ∈ range NG, x j * x l *
      (a * lam * (a * mom (Phi j) (Phi l)) - a ^ 2 * mom (U.getD j []) (Phi l)
        - t / a * dg (fun j => a ^ 3 * (dh.getD j 0 : ℝ)) j l) := by
    intro x
    have h0 := ldlOK_sound hL x
    have e : ∀ j ∈ range NG, ∀ l ∈ range NG, x j * x l *
        (a * lam * (a * mom (Phi j) (Phi l)) - a ^ 2 * mom (U.getD j []) (Phi l)
          - t / a * dg (fun j => a ^ 3 * (dh.getD j 0 : ℝ)) j l)
        = a ^ 2 * (x j * x l * ((mget Q j l : ℚ) : ℝ)) := by
      intro j hj l hl
      rw [hQs j (Finset.mem_range.1 hj) l (Finset.mem_range.1 hl), dg]
      split_ifs with hjl
      · subst hjl
        push_cast
        field_simp
        try ring
      · push_cast
        ring
    rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => e j hj l hl]
    simp_rw [← Finset.mul_sum]
    exact mul_nonneg (sq_nonneg a) h0
  have hmain := galerkin_form T (fun x y => intOp_kerLp_symm a E c0 x y) NG φ ρ
    (fun j l => a * mom (Phi j) (Phi l)) (fun j l => a ^ 2 * mom (U.getD j []) (Phi l))
    (dg fun j => a ^ 3 * (dh.getD j 0 : ℝ)) hG hC hres hspan hq (t := t / a)
    (div_pos ht0' ha) (by
      have : (a : ℝ) * q + 1 / (t / a) = a * (q + 1 / t) := by field_simp
      rw [this]
      nlinarith) hpsd f
  simpa [mul_assoc] using hmain

/-- **The test-vector lower bound**: `a λ̂ ‖u‖² ≤ re ⟪T_k u, u⟫` with `u ≠ 0`. -/
theorem form_lower_of_test (hb : binOK = true) {a : ℝ} (ha : 0 < a) {E : List ℚ}
    (hE : E.length ≤ 47) {Psi : List (List ℚ)} (hpsi : psiOK E Psi = true) (hlen : lenOK Psi = true)
    {ut Ut : List ℚ} {lam : ℚ}
    (hok : (decide (ut.length = NG) && decide (Ut = lc ut Psi DL) && decide (0 < mom ut ut) &&
      decide (lam * mom ut ut ≤ mom Ut ut)) = true) :
    (polyLp a ut : Lp 𝕜 2 (volI 0 a)) ≠ 0 ∧
      a * lam * ‖(polyLp a ut : Lp 𝕜 2 (volI 0 a))‖ ^ 2
        ≤ RCLike.re ⟪intOp (kerLp a E 0) (polyLp a ut), (polyLp a ut : Lp 𝕜 2 (volI 0 a))⟫_𝕜 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hl, hU⟩, hpos⟩, hle⟩ := hok
  obtain ⟨hPl, _⟩ := psiOK_sound hpsi
  have hL := lenOK_sound hlen
  have hUs : ∀ s ∈ Icc (0 : ℝ) 1, pv Ut s = ∫ t in (0 : ℝ)..1, kR E 0 s t * pv ut t := by
    intro s hs
    rw [integral_kR_mul_pv hb hE 0 hpsi hl.le hs.1 hs.2, hU, pv_lc fun m hm => by
      rw [hl] at hm; exact hL m hm]
    simp [hl]
  have hT := intOp_kerLp_polyLp (𝕜 := 𝕜) ha hUs
  have hn := norm_polyLp_sq (𝕜 := 𝕜) ha ut
  have hpos' : (0 : ℝ) < mom ut ut := by exact_mod_cast hpos
  have hle' : (lam : ℝ) * mom ut ut ≤ mom Ut ut := by exact_mod_cast hle
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, norm_zero] at hn
    nlinarith
  · rw [hT, inner_smul_left, inner_polyLp ha, RCLike.conj_ofReal, hn, ← RCLike.ofReal_mul,
      RCLike.ofReal_re]
    calc a * lam * (a * (mom ut ut : ℝ)) = a ^ 2 * ((lam : ℝ) * mom ut ut) := by ring
      _ ≤ a ^ 2 * (mom Ut ut : ℝ) := mul_le_mul_of_nonneg_left hle' (sq_nonneg a)
      _ = a * (a * (mom Ut ut : ℝ)) := by ring

/-! ## D. Rounding and kernel perturbation. -/

/-- The checked rounding: `|chiPoly v - pv E (|v| / a)| ≤ dR` for `|v| ≤ a`. -/
theorem abs_chiPoly_sub_pv {E : List ℚ} {a0 dR : ℚ} (h : roundOK E a0 dR = true) (ha : (0 : ℝ) < a0)
    {v : ℝ} (hv : |v| ≤ a0) : |ArchS10.chiPoly v - pv E (|v| / a0)| ≤ dR := by
  simp only [roundOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hsum⟩ := h
  have hw0 : 0 ≤ |v| / a0 := div_nonneg (abs_nonneg _) ha.le
  have hw1 : |v| / a0 ≤ 1 := (div_le_one ha).2 hv
  have hNP : ArchS10.Data.NP = 67 := rfl
  rw [pv_eq_range (D := ArchS10.Data.NP) (by rw [hlen, hNP]; decide)]
  unfold ArchS10.chiPoly
  rw [← Finset.sum_sub_distrib]
  have e : ∀ i ∈ range ArchS10.Data.NP, (ArchS10.Data.chiCo i : ℝ) * |v| ^ i
      - (E.getD i 0 : ℝ) * (|v| / a0) ^ i
      = ((ArchS10.Data.chiCo i : ℝ) * (a0 : ℝ) ^ i - (E.getD i 0 : ℝ)) * (|v| / a0) ^ i := by
    intro i _
    rw [div_pow]
    field_simp
  rw [Finset.sum_congr rfl e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h2 : ((∑ i ∈ range ArchS10.Data.NP, |ArchS10.Data.chiCo i * a0 ^ i - E.getD i 0| : ℚ) : ℝ)
      ≤ (dR : ℝ) := by exact_mod_cast hsum
  push_cast at h2
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) h2
  rw [abs_mul, abs_of_nonneg (pow_nonneg hw0 i)]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hw0 hw1)

/-- **Kernel perturbation**: kernels within `δ` on `[0, a]²` have forms within `δ a ‖f‖²`. -/
theorem abs_re_inner_sub_le {a : ℝ} (ha : 0 ≤ a) {k k' : ℝ × ℝ → 𝕜} (hk : Continuous k)
    (hk' : Continuous k') {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a, ‖k (x, y) - k' (x, y)‖ ≤ δ)
    (f : Lp 𝕜 2 (volI 0 a)) :
    |RCLike.re ⟪intOp (kernelOfContinuous 0 a k hk) f, f⟫_𝕜
      - RCLike.re ⟪intOp (kernelOfContinuous 0 a k' hk') f, f⟫_𝕜| ≤ δ * a * ‖f‖ ^ 2 := by
  rw [← map_sub, ← inner_sub_left, ← _root_.sub_apply, ← intOp_sub,
    kernelOfContinuous_sub]
  have hK := norm_kernelOfContinuous_le ha (hk.sub hk') hδ fun x hx y hy => h x hx y hy
  rw [sub_zero] at hK
  calc |RCLike.re ⟪intOp (kernelOfContinuous 0 a (k - k') (hk.sub hk')) f, f⟫_𝕜|
      ≤ ‖⟪intOp (kernelOfContinuous 0 a (k - k') (hk.sub hk')) f, f⟫_𝕜‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖intOp (kernelOfContinuous 0 a (k - k') (hk.sub hk')) f‖ * ‖f‖ := norm_inner_le_norm _ _
    _ ≤ (‖kernelOfContinuous 0 a (k - k') (hk.sub hk')‖ * ‖f‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (norm_intOp_apply_le _ _) (norm_nonneg _)
    _ ≤ (δ * a * ‖f‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) (norm_nonneg _)
    _ = δ * a * ‖f‖ ^ 2 := by ring

end ArchS11
