/-
  Hodge1_PoleFreeWindow -- the generic assembly of a DIRECT pole-free window certificate (HODGE-1
  Phase 1b-B, 2026-10-12; design notes, unpublished, section 3(b)): the pole-free analogue of
  KWin2_Window.windowFloor_of_cert, with the prime comb {2} inside the symbol.

  conjecture1_proved = False.  No zeros.

  THE ROUTE, for a real test v of parity par with VANISHING POLE FUNCTIONAL, supported in [-L, L],
  log 2 < 2L <= log 3, L <= l:
      lamFloor int v^2 <= RbP H (weilSymbol L) par v v          (Hodge1_TailP.RbP_floor, strip block off:
                                                                 w2up = 0; penalty pc in place of 2 eps)
                        = Rb H.K (weilSymbol L) par v v          (both pole terms vanish: Pl v = 0)
                       <= Re weilForm (autocorr v)               (KWin2_Split.Q_ge_Rb, verbatim).
  Then the complex assembly on PoleFree2 (int g e^{u/2} = int g e^{-u/2} = 0): Zhu's decoupling
  Q(g) = Q(Re g) + Q(Im g), Q(a) = Q(a_even) + Q(a_odd) (ZhuParity), the four pieces inherit the pole
  conditions (Hodge1_ArchSectors.poleFree2_pieces), and the mass splits (mass_decomp).

  PROVED HERE:
    * poleFree_sector_floor: the real sector floor above;
    * poleFree2_floor_of_sectors: real even/odd pole-free sector floors give the complex floor on PoleFree2;
    * poleFree2_floor_of_cert: a certificate (HPar with w2up = 0) whose kernel checks evaluate to true,
      plus KWin2's rational side conditions (sideCheck), proves
          lamFloor int |g|^2 <= Re weilForm (autocorr g)  for every PoleFree2 g supported in [-L, L].
  No `sorry`.
-/
import Hodge1_ArchSectors
import KWin2_Window

open Real MeasureTheory Set Finset

noncomputable section

namespace Hodge1
open KWin (Psi epsR ip continuous_v Pl poleF)
open KWin2 WeilExplicit WeilWindow RvMBridgeZhu

/-! ## A. The real pole-free sector floor. -/

/-- With vanishing pole functional the penalised form is KWin2's split form. -/
lemma RbP_eq_Rb_of_Pl (H : HPar) (sym : ℝ → ℝ) (par : ℕ) {v : ℝ → ℝ}
    (hPl : Pl (lR H.K) par v = 0) : RbP H sym par v v = Rb H.K sym par v v := by
  unfold RbP Rb
  rw [hPl]
  ring

theorem poleFree_sector_floor (H : HPar) (hw : H.w2up = 0) {L : ℝ} (hS : SymHyp H.K (weilSymbol L))
    (hpc : parCheck H.K = true) (hb : brkCheck H.K = true) (hL1 : Real.log 2 < 2 * L)
    (hL2 : 2 * L ≤ Real.log 3) (hLl : L ≤ lR H.K) (hT : 15 / 4 ≤ TR H.K)
    (hβ : b0R H.K ≤ betaStar L (TR H.K)) {par N : ℕ} (hpar : par = 0 ∨ par = 1) {lam eta : ℚ}
    (htail : tailCondP H par N lam eta = true) {D : List (List ℚ)}
    (hcert : HeadPSD (headMatP H par N lam eta D) N) (hginv : ginvCheck H.K par N = true)
    {v : ℝ → ℝ} (hf : IsWeilTest (fun u => (v u : ℂ))) (hev : ∀ u, v (-u) = epsR par * v u)
    (hs : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L) (hPl : Pl (lR H.K) par v = 0) :
    ((H.K.lamFloor : ℚ) : ℝ) * (∫ x, v x ^ 2)
      ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => (v u : ℂ)))).re := by
  have hR := RbP_floor H hS hpc hb hpar htail hcert hginv (continuous_v hf)
  have hw0 : w2R H = 0 := by unfold w2R; rw [hw]; simp
  rw [hw0, zero_mul, sub_zero, RbP_eq_Rb_of_Pl H _ par hPl] at hR
  have hQ := Q_ge_Rb H.K hpc hL1 hL2 hLl hT hβ hpar hf hev hs
  have hl := lR_pos H.K hpc
  have hip : ip (lR H.K) v v = ∫ x, v x ^ 2 := by
    unfold ip
    rw [← integral_eq_interval' hf hl hLl hs]
    congr 1; funext x; ring
  rw [hip] at hR
  linarith

/-! ## B. The complex assembly on PoleFree2. -/

lemma evenPart_re_eq (g : ℝ → ℂ) :
    evenPart (fun x => ((g x).re : ℂ)) = fun u => (vEr g u : ℂ) := by
  funext u
  apply Complex.ext <;> simp [evenPart, vEr, Complex.div_ofNat_re, Complex.div_ofNat_im]

lemma oddPart_re_eq (g : ℝ → ℂ) :
    oddPart (fun x => ((g x).re : ℂ)) = fun u => (vOr g u : ℂ) := by
  funext u
  apply Complex.ext <;> simp [oddPart, vOr, Complex.div_ofNat_re, Complex.div_ofNat_im]

lemma evenPart_im_eq (g : ℝ → ℂ) :
    evenPart (fun x => ((g x).im : ℂ)) = fun u => (vEi g u : ℂ) := by
  funext u
  apply Complex.ext <;> simp [evenPart, vEi, Complex.div_ofNat_re, Complex.div_ofNat_im]

lemma oddPart_im_eq (g : ℝ → ℂ) :
    oddPart (fun x => ((g x).im : ℂ)) = fun u => (vOi g u : ℂ) := by
  funext u
  apply Complex.ext <;> simp [oddPart, vOi, Complex.div_ofNat_re, Complex.div_ofNat_im]

theorem poleFree2_floor_of_sectors {L l lam : ℝ} (hl : 0 < l) (hLl : L ≤ l)
    (hE : ∀ v : ℝ → ℝ, IsWeilTest (fun u => (v u : ℂ)) → (∀ u, v (-u) = v u) →
      tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L → Pl l 0 v = 0 →
      lam * (∫ x, v x ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => (v u : ℂ)))).re)
    (hO : ∀ v : ℝ → ℝ, IsWeilTest (fun u => (v u : ℂ)) → (∀ u, v (-u) = -v u) →
      tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L → Pl l 1 v = 0 →
      lam * (∫ x, v x ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr (fun u => (v u : ℂ)))).re)
    {g : ℝ → ℂ} (hg : IsWeilTest g) (hP : PoleFree2 g) (hs : tsupport g ⊆ Icc (-L) L) :
    lam * (∫ x, ‖g x‖ ^ 2) ≤ (WeilForm.weilForm (WeilForm.autocorr g)).re := by
  set a : ℝ → ℂ := fun x => ((g x).re : ℂ) with ha
  set b : ℝ → ℂ := fun x => ((g x).im : ℂ) with hb
  have hfab : g = a + fun x => Complex.I * b x := by
    funext x
    exact Complex.ext (by simp [ha, hb]) (by simp [ha, hb])
  have hQ : (WeilForm.weilForm (WeilForm.autocorr g)).re
      = (WeilForm.weilForm (WeilForm.autocorr a)).re + (WeilForm.weilForm (WeilForm.autocorr b)).re := by
    conv_lhs => rw [hfab]
    exact Q_add_I_mul (isWeilTest_re hg) (isWeilTest_im hg) (fun x => by simp [ha]) (fun x => by simp [hb])
  have hQa := Q_evenPart_add_oddPart (isWeilTest_re hg)
  have hQb := Q_evenPart_add_oddPart (isWeilTest_im hg)
  rw [← ha, evenPart_re_eq, oddPart_re_eq] at hQa
  rw [← hb, evenPart_im_eq, oddPart_im_eq] at hQb
  obtain ⟨pE, pI, pO, pJ⟩ := poleFree2_pieces hg hP
  have sE : tsupport (fun u => (vEr g u : ℂ)) ⊆ Icc (-L) L :=
    tsupport_re_subset (tsupport_evenPart_subset hs)
  have sI : tsupport (fun u => (vEi g u : ℂ)) ⊆ Icc (-L) L :=
    tsupport_im_subset (tsupport_evenPart_subset hs)
  have sO : tsupport (fun u => (vOr g u : ℂ)) ⊆ Icc (-L) L :=
    tsupport_re_subset (tsupport_oddPart_subset hs)
  have sJ : tsupport (fun u => (vOi g u : ℂ)) ⊆ Icc (-L) L :=
    tsupport_im_subset (tsupport_oddPart_subset hs)
  have hsub : Icc (-L) L ⊆ Icc (-l) l := Icc_subset_Icc (by linarith) hLl
  have hpE : ∀ u, poleF 0 u = Real.cosh (u / 2) := fun u => by simp [poleF]
  have hpO : ∀ u, poleF 1 u = Real.sinh (u / 2) := fun u => by simp [poleF]
  have e1 := hE (vEr g) (isWeilTest_vEr hg) (vEr_neg g) sE (by
    rw [Pl_eq_integral (isWeilTest_vEr hg) hl (sE.trans hsub)]; simp_rw [hpE]; exact pE)
  have e2 := hE (vEi g) (isWeilTest_vEi hg) (vEi_neg g) sI (by
    rw [Pl_eq_integral (isWeilTest_vEi hg) hl (sI.trans hsub)]; simp_rw [hpE]; exact pI)
  have e3 := hO (vOr g) (isWeilTest_vOr hg) (vOr_neg g) sO (by
    rw [Pl_eq_integral (isWeilTest_vOr hg) hl (sO.trans hsub)]; simp_rw [hpO]; exact pO)
  have e4 := hO (vOi g) (isWeilTest_vOi hg) (vOi_neg g) sJ (by
    rw [Pl_eq_integral (isWeilTest_vOi hg) hl (sJ.trans hsub)]; simp_rw [hpO]; exact pJ)
  rw [hQ, hQa, hQb, mass_decomp hg]
  linarith

/-! ## C. The generic certificate theorem. -/

/-- **The generic pole-free window floor**: a direct pole-free certificate (strip block off) whose
kernel checks evaluate to `true` proves `lamFloor int |g|^2 <= Re weilForm (autocorr g)` for every
PoleFree2 test supported in [-L, L], log 2 < 2L <= log 3, L <= l. -/
theorem poleFree2_floor_of_cert (H : HPar) (hw : H.w2up = 0) {L : ℝ} (NE NO : ℕ) (lamE lamO eta : ℚ)
    (DE DO : List (List ℚ)) (xT : ℚ) (hL1 : Real.log 2 < 2 * L) (hL2 : 2 * L ≤ Real.log 3)
    (hLl : L ≤ lR H.K)
    (hγ : Real.eulerMascheroniConstant ≤ ((H.K.gamUp : ℚ) : ℝ))
    (hlp : Real.log Real.pi ≤ ((H.K.logPiUp : ℚ) : ℝ))
    (hside : sideCheck H.K xT = true) (hpc : parCheck H.K = true) (hb : brkCheck H.K = true)
    (hpcs : pieceCheck H.K = true) (hm : minCheck H.K = true) (hcc : combCheck H.K = true)
    (htE : tailCondP H 0 NE lamE eta = true) (htO : tailCondP H 1 NO lamO eta = true)
    (hgE : ginvCheck H.K 0 NE = true) (hgO : ginvCheck H.K 1 NO = true)
    (hcE : HeadPSD (headMatP H 0 NE lamE eta DE) NE) (hcO : HeadPSD (headMatP H 1 NO lamO eta DO) NO)
    (g : ℝ → ℂ) (hg : IsWeilTest g) (hP : PoleFree2 g) (hs : tsupport g ⊆ Icc (-L) L) :
    ((H.K.lamFloor : ℚ) : ℝ) * (∫ x, ‖g x‖ ^ 2) ≤ (weilForm (autocorr g)).re := by
  have hS : SymHyp H.K (weilSymbol L) :=
    { cont := continuous_weilSymbol_two hL1 hL2
      bound := sym_bound_of hside hlp hL1 hL2
      minor := by
        intro i hi t hti hti'
        have h := sym_minorant H.K hb hpcs hm hcc hγ hlp (log2_near_of hside) (c2_near_of hside)
          hi hti hti'
        rw [weilSymbol_eq_two hL1 hL2]
        exact h
      cosh := cosh_of hside }
  have hT := TR_ge_of hside
  have hβ := beta0_le_betaStar_of hside hL1 hL2
  have hl : (0 : ℝ) < lR H.K := lR_pos H.K hpc
  have h := poleFree2_floor_of_sectors hl hLl
    (fun v hf hev hsv hPl => poleFree_sector_floor H hw hS hpc hb hL1 hL2 hLl hT hβ (par := 0)
      (Or.inl rfl) htE hcE hgE hf (fun u => by rw [hev u]; simp [epsR]) hsv hPl)
    (fun v hf hodd hsv hPl => poleFree_sector_floor H hw hS hpc hb hL1 hL2 hLl hT hβ (par := 1)
      (Or.inr rfl) htO hcO hgO hf (fun u => by rw [hodd u]; simp [epsR]) hsv hPl)
    hg hP hs
  rw [weilForm_autocorr_eq] at h
  exact h

end Hodge1

end
