/-
  ArchPipeline_ProlateComplete -- the certified prolate spectrum, UNCONDITIONAL.

  S9's `prolate_spectrum_complete` certifies the 13 largest even prolate eigenvalues (c = 2π) given an orthonormal
  continuous eigenfamily of its operator T that satisfies Parseval on S9's polynomials ψ_n.  S6's `exists_S9_family`
  supplies exactly such a family (the real orthonormal prolate basis of ran P₁, transported to L²[0,1]).  Composing them:
  for the complete prolate eigenbasis, every eigenvalue has |λ| ≤ d0Q (≈ 9.70e-22) or lies in one of 13 certified
  windows, each window holds exactly one eigenvalue, and it is within w2q n (≈ 6.73e-43) of θ_n.
  conjecture1_proved = False.  Nothing here is RH progress.
-/
import ArchS6_Bridge
import ArchS9_Bridge

namespace ArchPipeline
open ArchS9

open Classical in
theorem prolate_spectrum_certified :
    ∃ (ι : Type) (e : ι → ℝ → ℝ) (lam : ι → ℝ),
      (∀ k, Continuous (e k)) ∧
      (∀ j k, ip (e j) (e k) = if j = k then 1 else 0) ∧
      (∀ k ω, T (e k) ω = lam k * e k ω) ∧
      (∀ k, lam k ≠ 0 ∧ |lam k| < 1) ∧
      (∀ k, |lam k| ≤ (Data.d0Q : ℝ) ∨ ∃ n ≤ Data.NCw, |lam k - thR n| ≤ (Data.w0q n : ℝ)) ∧
      (∀ n ≤ Data.NCw, ∃! k, |lam k - thR n| ≤ (Data.w0q n : ℝ)) ∧
      (∀ n ≤ Data.NCw, ∀ k, |lam k - thR n| ≤ (Data.w0q n : ℝ) → |lam k - thR n| ≤ (Data.w2q n : ℝ)) := by
  classical
  obtain ⟨ι, e, lam, hc, ho, he, hl, hpar⟩ := ArchS6.exists_S9_family
  have hT : ∀ k ω, T (e k) ω = lam k * e k ω := fun k ω => by
    have := he k ω; simpa [ArchS6.TS9, T, K] using this
  have hO : ∀ j k, ip (e j) (e k) = if j = k then 1 else 0 := fun j k => by
    have := ho j k; simpa [ArchS6.ipS9, ip] using this
  have hP : ∀ n ≤ Data.NCw, HasSum (fun k => ip (psiS n) (e k) ^ 2) (ip (psiS n) (psiS n)) := fun n _ => by
    have := hpar (psiS n) (continuous_psi Data.Jd BR n); simpa [ArchS6.ipS9, ip] using this
  obtain ⟨h1, h2, h3⟩ := prolate_spectrum_complete e lam hc hT hO hP
  exact ⟨ι, e, lam, hc, hO, hT, hl, h1, h2, h3⟩

end ArchPipeline
