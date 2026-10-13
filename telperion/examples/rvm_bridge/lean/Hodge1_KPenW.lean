/-
  Hodge1_KPenW -- the head matrix on a GIVEN moment-transform matrix WB (HODGE-1 Phase 1b-B, 2026-10-12):
  the second split of the staged certificate (Hodge1_KPenM).

  conjecture1_proved = False.  Pure bookkeeping.

  WHY.  Every row of the strip-free head matrix `headMatN` needs the whole moment-transform matrix
  WB = (sum_{m'} mom_{m+m'} Bm_{m'k})_{m < Mt, k < N}; recomputing it in each kernel declaration dominates
  memory (about 14 GB macOS per 8-row block at l = 5493/10000).  WB is therefore passed as exact rational
  DATA, checked against `WBmatM` row block by row block, and the head rows are evaluated on the literal WB.
  `headMatN_eq_W` is definitional.  No `sorry`.
-/
import Hodge1_KPenM

open Finset

namespace Hodge1
open KWin (piLoQ piHiQ mget getD_map_range psdCert)
open KWin2

def headEntryW (H : HPar) (par : ℕ) (lam : ℚ) (WB : List (List ℚ)) (j k : ℕ) : ℚ :=
  piLoQ * H.pc * pv H.K par j * pv H.K par k + diagc H.K lam * Gm H.K par j k
  + ∑ m ∈ range H.K.Mt, Bm H.K par m j * ((WB.getD m []).getD k 0)

def headMatW (H : HPar) (par N : ℕ) (lam : ℚ) (WB : List (List ℚ)) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (headEntryW H par lam WB j))

theorem headMatN_eq_W (H : HPar) (par N : ℕ) (lam : ℚ) (ml : List ℚ) :
    headMatN H par N lam ml = headMatW H par N lam (WBmatM H.K par N ml) := rfl

theorem WBmatM_length (P : KPar) (par N : ℕ) (ml : List ℚ) : (WBmatM P par N ml).length = P.Mt := by
  simp [WBmatM]

/-- **The fully staged pipeline**: kernel-checked moment rows, a literal WB checked against `WBmatM`, and a
literal rounded matrix checked against `roundShift (headMatW ...)` turn the monolithic checker into the
exact LDL^T checker on literal data. -/
theorem psdCertR_headMatP_eq (H : HPar) (hw : H.w2up = 0) (par N : ℕ) (lam eta : ℚ)
    (D : List (List ℚ)) (R : ℕ) (rows : List (List ℚ))
    (hrows : ∀ i < nPc H.K, pieceRow H.K par i = rows.getD i []) (WB : List (List ℚ))
    (hWB : WBmatM H.K par N (momListLit H.K par rows) = WB) (B : List (List ℚ))
    (hB : roundShift (headMatW H par N lam WB) N R = B) :
    psdCertR (headMatP H par N lam eta D) N R = psdCert B N := by
  rw [headMatP_eq_M, momList_eq_lit H.K par rows hrows, headMatM_eq_N H hw, headMatN_eq_W, hWB]
  unfold psdCertR
  rw [hB]

/-- Five row blocks (8, 8, 8, 8, n4) cover the rows below 32 + n4. -/
theorem rows_of_five_blocks {f g : ℕ → List ℚ} {n4 : ℕ}
    (h0 : (List.range 8).map (fun i => f (0 + i)) = (List.range 8).map (fun i => g (0 + i)))
    (h1 : (List.range 8).map (fun i => f (8 + i)) = (List.range 8).map (fun i => g (8 + i)))
    (h2 : (List.range 8).map (fun i => f (16 + i)) = (List.range 8).map (fun i => g (16 + i)))
    (h3 : (List.range 8).map (fun i => f (24 + i)) = (List.range 8).map (fun i => g (24 + i)))
    (h4 : (List.range n4).map (fun i => f (32 + i)) = (List.range n4).map (fun i => g (32 + i))) :
    ∀ j < 32 + n4, f j = g j := by
  have hb : ∀ {s n : ℕ}, (List.range n).map (fun i => f (s + i)) = (List.range n).map (fun i => g (s + i)) →
      ∀ i < n, f (s + i) = g (s + i) := by
    intro s n h i hi
    have := congrArg (fun l => l.getD i []) h
    rwa [getD_map_range _ _ hi, getD_map_range _ _ hi] at this
  intro j hj
  rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 32) ∨ 32 ≤ j)
    with h | h | h | h | h
  · obtain ⟨i, rfl⟩ : ∃ i, j = 0 + i := ⟨j, by omega⟩
    exact hb h0 i (by omega)
  · obtain ⟨i, rfl⟩ : ∃ i, j = 8 + i := ⟨j - 8, by omega⟩
    exact hb h1 i (by omega)
  · obtain ⟨i, rfl⟩ : ∃ i, j = 16 + i := ⟨j - 16, by omega⟩
    exact hb h2 i (by omega)
  · obtain ⟨i, rfl⟩ : ∃ i, j = 24 + i := ⟨j - 24, by omega⟩
    exact hb h3 i (by omega)
  · obtain ⟨i, rfl⟩ : ∃ i, j = 32 + i := ⟨j - 32, by omega⟩
    exact hb h4 i (by omega)

end Hodge1
