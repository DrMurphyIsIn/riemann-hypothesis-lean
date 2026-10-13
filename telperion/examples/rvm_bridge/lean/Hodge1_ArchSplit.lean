/-
  Hodge1_ArchSplit -- the archimedean split of archW in the sector form consumed by the HODGE-1 strip
  certificate (2026-10-12, Phase 1b-A).

  conjecture1_proved = False.  No zeros, no primes: archW is the archimedean Weil functional
  W_inf(g * g~) = (1/2pi) int |g^|^2 (Re psi(1/4 + it/2) - log pi) (ArchS3_Delta).

  PROVED HERE (`RbP_le_archW`): for a real test v of parity par, smooth, compactly supported in
  [-L, L] with L <= l, with VANISHING POLE FUNCTIONAL Pl v = 0, and for 15/4 <= T,
  beta0 <= log(T/2pi) - 1/T,
      RbP H Psi par v v <= archW v.
  Route (the comb-free half of KWin2_Split.Q_ge_Rb): |v^(t)|^2 = (Tr v t)^2 (sector transform on
  [-l, l]), Plancherel int v^2 = (1/2pi) int |v^|^2, evenness of |v^|^2 and of Psi, and Zhu's
  envelope Psi(t) >= log(t/2pi) - 1/t >= beta0 for t >= T (ZhuEnvelope.envelopeBound).  The pole
  term pc (Pl v)^2 of RbP is zero because Pl v = 0: this is where the pole-free class enters.
  No `sorry`.
-/
import Hodge1_TailP
import KWin2_Split
import ArchS3_Delta

open Real MeasureTheory Set

noncomputable section

namespace Hodge1
open KWin (Tr Pl ip phiF poleF continuous_Tr epsR phiF_neg continuous_v integrable_line_sq
  integrable_line_sq_mul_psi plancherel_ofReal Psi)
open KWin2 WeilExplicit RvMBridgeZhu

variable (H : HPar)

lemma Psi_neg (t : ℝ) : Psi (-t) = Psi t := by
  unfold Psi; rw [RvMBridge30.psiR_neg]

/-- Zhu's envelope beyond the frequency cut: `beta0 <= Psi t` for `t > T`. -/
lemma b0_le_Psi (hT : 15 / 4 ≤ TR H.K)
    (hβ : b0R H.K ≤ Real.log (TR H.K / (2 * Real.pi)) - 1 / TR H.K) {t : ℝ} (ht : TR H.K < t) :
    b0R H.K ≤ Psi t := by
  have hT0 : 0 < TR H.K := by linarith
  have henv := envelopeBound t (by linarith)
  have hlog : Real.log (TR H.K / (2 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_le_log (by positivity) (by gcongr)
  have hinv : 1 / t ≤ 1 / TR H.K := one_div_le_one_div_of_le hT0 ht.le
  have hP : Psi t = (Complex.digamma (1 / 4 + ((t : ℂ) / 2) * Complex.I)).re - Real.log Real.pi := rfl
  rw [hP]
  linarith

/-- archW of a real test in the line form `(1/2pi) int |weilKernel|^2 Psi`. -/
lemma archW_ofReal (v : ℝ → ℝ) :
    ArchS3.archW (fun u => (v u : ℂ))
      = (1 / (2 * Real.pi)) * ∫ r : ℝ,
          ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2 * Psi r := by
  unfold ArchS3.archW RvMBridge31.hsq Psi
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [RvMBridge4.weilKernel_line]

/-- **The archimedean split** on the pole-free sector: `RbP H Psi par v v <= archW v`. -/
theorem RbP_le_archW (hpc : parCheck H.K = true) (hT : 15 / 4 ≤ TR H.K)
    (hβ : b0R H.K ≤ Real.log (TR H.K / (2 * Real.pi)) - 1 / TR H.K) {v : ℝ → ℝ} {par : ℕ}
    (hpar : par = 0 ∨ par = 1) (hf : IsWeilTest (fun u => (v u : ℂ)))
    (hev : ∀ u, v (-u) = epsR par * v u) {L : ℝ} (hLl : L ≤ lR H.K)
    (hsupp : tsupport (fun u => (v u : ℂ)) ⊆ Icc (-L) L) (hPl : Pl (lR H.K) par v = 0) :
    RbP H Psi par v v ≤ ArchS3.archW (fun u => (v u : ℂ)) := by
  have hl := lR_pos H.K hpc
  set F : ℝ → ℝ := fun r => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2
    with hF
  have hFT : ∀ t, F t = (Tr (lR H.K) par v t) ^ 2 := fun t =>
    norm_sq_line_sector' hpar hf hev hl hLl hsupp t
  have hFi : Integrable F := integrable_line_sq hf
  have hFpsi := integrable_line_sq_mul_psi hf
  have hFSi : Integrable fun t => F t * Psi t := by
    have e : (fun t => F t * Psi t) = fun t => F t * RvMBridge11.psiR t - F t * Real.log Real.pi := by
      funext t; unfold Psi; ring
    rw [e]
    exact hFpsi.sub (hFi.mul_const _)
  have hF0 : ∀ t, 0 ≤ F t := fun t => by rw [hF]; positivity
  have hTneg : ∀ t, Tr (lR H.K) par v (-t) = (if par = 0 then (1 : ℝ) else -1) * Tr (lR H.K) par v t := by
    intro t
    unfold Tr
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [show -t * x = -(t * x) by ring, phiF_neg par hpar]
    ring
  have hFe : ∀ t, F (-t) = F t := by
    intro t
    rw [hFT, hFT, hTneg, mul_pow]
    split_ifs <;> norm_num
  have hSβ : ∀ t, TR H.K < t → b0R H.K ≤ Psi t := fun t ht => b0_le_Psi H hT hβ ht
  have hsplit := split_line' (TR_pos H.K hpc).le hFi hFSi hF0 hFe Psi_neg hSβ
  have hplan := plancherel_ofReal hf
  have hip : ip (lR H.K) v v = ∫ x, v x ^ 2 := by
    unfold ip
    rw [← integral_eq_interval' hf hl hLl hsupp]
    congr 1; funext x; ring
  rw [archW_ofReal]
  unfold RbP
  rw [hPl, hip, hplan]
  have e2 : (fun t => (Psi t - b0R H.K) * (Tr (lR H.K) par v t * Tr (lR H.K) par v t))
      = fun t => (Psi t - b0R H.K) * F t := by funext t; rw [hFT]; ring
  rw [e2]
  have e3 : (fun r : ℝ => ‖weilKernel (fun u => (v u : ℂ)) (1 / 2 + (r : ℂ) * Complex.I)‖ ^ 2) = F := rfl
  rw [e3]
  linarith [hsplit]

end Hodge1

end
