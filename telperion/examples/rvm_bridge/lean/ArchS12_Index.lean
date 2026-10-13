/-
  ArchS12_Index -- STAGE S12, shared bridge A3: the certified enumeration of the prolate basis
  (rvm_bridge island, 2026-10-11).  conjecture1_proved = False.  Nothing here is RH progress.

  S7's `cc_thm47` holds for S6's `prolateData bR σ` with ANY real prolate eigenbasis `bR` and ANY
  enumeration `σ : ℕ ≃ ι`.  S10's and S11's numerics hold under `ArchS10.CertBasis D`, which asks
  (among other things) that indices `0 .. 12` sit in S9's 13 certified windows.  Here, for every
  `bR`, we build an enumeration `σ` that puts S9's window eigenvalues first and prove
  `CertBasis (prolateData bR σ)`.  So the SAME `D = prolateData bR σ` feeds both `cc_thm47` and
  S11's `KI_chi_half` / `KI_chi_log2`.

  Ingredients: S9's `prolate_spectrum_complete` applied to S6's family `(phiR bR, bR.μ)` (each window
  holds exactly one index), pairwise disjointness of the 13 windows (one `decide +kernel` check), and
  an equivalence `ℕ ≃ ι` with prescribed values on `{0, ..., 12}` (sum decomposition plus
  `Cardinal.eq` on the countably infinite complements).  No `sorry`.
-/
import ArchS6_ProlateData
import ArchS6_Bridge
import ArchS9_Bridge
import ArchS10_Chi

open MeasureTheory Set

noncomputable section

namespace ArchS12

open ArchS6 ArchS9

/-! ## A. The 13 windows are pairwise disjoint. -/

/-- Pairwise separation of S9's windows, as a Boolean check. -/
def disjOK : Bool :=
  (List.range (Data.NCw + 1)).all fun n => (List.range (Data.NCw + 1)).all fun m =>
    n == m || decide (Data.w0q n + Data.w0q m < |Data.thq n - Data.thq m|)

set_option maxHeartbeats 0 in
theorem disjOK_eq : disjOK = true := by decide +kernel

theorem window_sep {n m : ℕ} (hn : n ≤ Data.NCw) (hm : m ≤ Data.NCw) (hnm : n ≠ m) :
    (Data.w0q n : ℝ) + Data.w0q m < |thR n - thR m| := by
  have h := disjOK_eq
  unfold disjOK at h
  rw [List.all_eq_true] at h
  have h1 := h n (List.mem_range.2 (Nat.lt_succ_of_le hn))
  rw [List.all_eq_true] at h1
  have h2 := h1 m (List.mem_range.2 (Nat.lt_succ_of_le hm))
  simp only [Bool.or_eq_true, beq_iff_eq, hnm, false_or, decide_eq_true_eq] at h2
  unfold thR
  exact_mod_cast h2

/-- A real number lies in at most one window. -/
theorem window_unique {x : ℝ} {n m : ℕ} (hn : n ≤ Data.NCw) (hm : m ≤ Data.NCw)
    (hxn : |x - thR n| ≤ (Data.w0q n : ℝ)) (hxm : |x - thR m| ≤ (Data.w0q m : ℝ)) : n = m := by
  by_contra hnm
  have hs := window_sep hn hm hnm
  have : |thR n - thR m| ≤ |x - thR n| + |x - thR m| := by
    calc |thR n - thR m| = |(x - thR m) - (x - thR n)| := by ring_nf
      _ ≤ |x - thR m| + |x - thR n| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

/-! ## B. S9's spectral certificate for a given real prolate basis. -/

section Basis

variable {ι : Type*} (bR : EigenBasis CopR ι)

theorem T_phiR' (k : ι) (ω : ℝ) : T (phiR bR k) ω = bR.μ k * phiR bR k ω := by
  have := T_phiR bR k ω; simpa [ArchS6.TS9, T, K] using this

theorem ip_phiR' [DecidableEq ι] (j k : ι) : ip (phiR bR j) (phiR bR k) = if j = k then 1 else 0 := by
  have := ip_phiR bR j k; simpa [ArchS6.ipS9, ip] using this

/-- S9's `prolate_spectrum_complete` for S6's family `(phiR bR, bR.μ)`: window `n` holds exactly one index. -/
theorem window_existsUnique {n : ℕ} (hn : n ≤ Data.NCw) :
    ∃! k : ι, |bR.μ k - thR n| ≤ (Data.w0q n : ℝ) := by
  classical
  have hP : ∀ n ≤ Data.NCw, HasSum (fun k => ip (psiS n) (phiR bR k) ^ 2) (ip (psiS n) (psiS n)) :=
    fun n _ => by
      have := parseval_ip bR (continuous_psi Data.Jd BR n); simpa [ArchS6.ipS9, ip, psiS] using this
  exact (prolate_spectrum_complete (phiR bR) bR.μ (continuous_phiR bR) (T_phiR' bR) (ip_phiR' bR)
    hP).2.1 n hn

/-- The index of window `n` (`n ≤ 12`). -/
def winIdx (n : Fin (Data.NCw + 1)) : ι :=
  (window_existsUnique bR (Nat.lt_succ_iff.1 n.2)).exists.choose

theorem winIdx_spec (n : Fin (Data.NCw + 1)) :
    |bR.μ (winIdx bR n) - thR n| ≤ (Data.w0q n : ℝ) :=
  (window_existsUnique bR (Nat.lt_succ_iff.1 n.2)).exists.choose_spec

theorem winIdx_injective : Function.Injective (winIdx bR) := by
  intro n m h
  have h1 := winIdx_spec bR n
  have h2 := winIdx_spec bR m
  rw [h] at h1
  exact Fin.ext (window_unique (Nat.lt_succ_iff.1 n.2) (Nat.lt_succ_iff.1 m.2) h1 h2)

end Basis

/-! ## C. An enumeration with prescribed first values. -/

section Enum

universe u

variable {ι : Type u}

/-- Given `τ : ℕ ≃ ι` and an injective `f : Fin N → ι`, an enumeration `σ : ℕ ≃ ι` with
`σ n = f n` for `n < N`. -/
theorem exists_equiv_prefix {N : ℕ} (τ : ℕ ≃ ι) (f : Fin N → ι) (hf : Function.Injective f) :
    ∃ σ : ℕ ≃ ι, ∀ n (hn : n < N), σ n = f ⟨n, hn⟩ := by
  classical
  have : Infinite ι := Infinite.of_injective τ τ.injective
  have : Countable ι := τ.symm.injective.countable
  let p : ℕ → Prop := fun n => n < N
  let q : ι → Prop := fun k => k ∈ Set.range f
  let e1 : {n // p n} ≃ {k // q k} := (Fin.equivSubtype (n := N)).symm.trans (Equiv.ofInjective f hf)
  have : Infinite {n // ¬ p n} :=
    ((Set.finite_lt_nat N).infinite_compl).to_subtype
  have : Infinite {k // ¬ q k} := ((Set.finite_range f).infinite_compl).to_subtype
  have hc : Cardinal.lift.{u} (Cardinal.mk {n // ¬ p n}) = Cardinal.lift.{0} (Cardinal.mk {k // ¬ q k}) := by
    rw [Cardinal.mk_eq_aleph0, Cardinal.mk_eq_aleph0, Cardinal.lift_aleph0, Cardinal.lift_aleph0]
  obtain ⟨e2⟩ := Cardinal.lift_mk_eq'.1 hc
  refine ⟨((Equiv.sumCompl p).symm.trans (Equiv.sumCongr e1 e2)).trans (Equiv.sumCompl q),
    fun n hn => ?_⟩
  simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos (p := p) hn, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.sumCompl_apply_inl, e1]
  rfl

end Enum

/-! ## D. The certified enumeration. -/

section Cert

variable {ι : Type*} (bR : EigenBasis CopR ι)

/-- **A3.** For every real prolate basis there is an enumeration putting S9's 13 window
eigenvalues at indices `0 .. 12`; for it, S6's `prolateData bR σ` (the `D` of S7's `cc_thm47`)
satisfies S10's `CertBasis`. -/
theorem exists_certBasis_enumeration : ∃ σ : ℕ ≃ ι, ArchS10.CertBasis (prolateData bR σ) := by
  classical
  obtain ⟨τ⟩ := exists_equiv_nat bR
  obtain ⟨σ, hσ⟩ := exists_equiv_prefix τ (winIdx bR) (winIdx_injective bR)
  refine ⟨σ, ⟨fun n ω => ?_, fun n m => ?_, fun n hn => ?_, ?_⟩⟩
  · exact T_phiR' bR (σ n) ω
  · show ip (phiR bR (σ n)) (phiR bR (σ m)) = if n = m then 1 else 0
    rw [ip_phiR' bR]
    by_cases h : n = m
    · subst h; simp
    · rw [if_neg (fun e => h (σ.injective e)), if_neg h]
  · show |bR.μ (σ n) - thR n| ≤ (Data.w0q n : ℝ)
    rw [hσ n (Nat.lt_succ_of_le hn)]
    exact winIdx_spec bR ⟨n, Nat.lt_succ_of_le hn⟩
  · show Real.log 2 < Real.log 3
    exact Real.log_lt_log (by norm_num) (by norm_num)

/-- The data exist: a real prolate basis with a certified enumeration. -/
theorem exists_certified_prolate :
    ∃ (ι : Type) (bR : EigenBasis CopR ι) (σ : ℕ ≃ ι), ArchS10.CertBasis (prolateData bR σ) := by
  obtain ⟨ι, bR, -⟩ := exists_eigenBasis_CopR
  obtain ⟨σ, hσ⟩ := exists_certBasis_enumeration bR
  exact ⟨ι, bR, σ, hσ⟩

end Cert

end ArchS12
