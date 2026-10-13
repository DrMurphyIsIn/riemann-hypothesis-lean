/-
  Hodge1_KPenM -- STAGED kernel evaluation of a Hodge1 head certificate (HODGE-1 Phase 1b-B, 2026-10-12).

  conjecture1_proved = False.  Pure bookkeeping; nothing about zeros.

  WHY.  A single `decide +kernel` on `psdCertR (headMatP H par N lam eta D) N R` rebuilds the symbol
  minorant, all its moments, the head matrix and its LDL^T inside ONE kernel evaluation, and the kernel's
  reduction cache keeps every intermediate value alive: at l = 5493/10000 (T = 40, nS = 44, Mt = 37,
  N = 32) that single declaration peaks at 36 GB (macOS RSS).  Peak memory is set by the largest single
  declaration, so the evaluation is split into stages that pass exact rational DATA between them:
    * stage 1 (one declaration per minorant piece i and sector):  pieceRow P par i = rows_i  (literal),
      the moments int_{piece i} (w_i - beta0) t^(2s + 2par) of the piece-i minorant polynomial;
    * stage 2: the head check on `headMatM`, the same matrix with the moment list rebuilt from the
      literal rows (momListLit: sum over pieces minus the comb moments, computed in the kernel).
  `momList_eq_lit` (proved, from the stage-1 equalities) and `headMatP_eq_M` (definitional) transport
  the stage-2 certificate back to `headMatP`, so `HeadPSD (headMatP ...)` is a theorem exactly as with the
  monolithic check.  No `sorry`.
-/
import Hodge1_KPen

open Finset

namespace Hodge1
open KWin (piLoQ piHiQ mget getD_map_range psdCert)
open KWin2

/-! ## A. The moments from per-piece rows. -/

/-- The moments of the piece-`i` minorant polynomial (the summands of `mom`), for one sector. -/
def pieceRow (P : KPar) (par i : ℕ) : List ℚ :=
  (List.range (2 * P.Mt)).map (fun s => momPiece P i (2 * s + 2 * par))

/-- The moment list rebuilt from per-piece rows (the comb moments are recomputed). -/
def momListLit (P : KPar) (par : ℕ) (rows : List (List ℚ)) : List ℚ :=
  (List.range (2 * P.Mt)).map (fun s =>
    (∑ i ∈ range (nPc P), (rows.getD i []).getD s 0) - momComb P (2 * s + 2 * par))

theorem momList_eq_lit (P : KPar) (par : ℕ) (rows : List (List ℚ))
    (h : ∀ i < nPc P, pieceRow P par i = rows.getD i []) : momList P par = momListLit P par rows := by
  unfold momList momListLit
  refine List.map_congr_left fun s hs => ?_
  have hs' := List.mem_range.mp hs
  unfold mom
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← h i (Finset.mem_range.mp hi)]
  unfold pieceRow
  rw [getD_map_range _ _ hs']

/-! ## B. The head matrix on a given moment list. -/

def WBmatM (P : KPar) (par N : ℕ) (ml : List ℚ) : List (List ℚ) :=
  (List.range P.Mt).map (fun m => (List.range N).map (fun k =>
    ∑ m' ∈ range P.Mt, ml.getD (m + m') 0 * Bm P par m' k))

def headEntryM (H : HPar) (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ)) (ml : List ℚ) (j k : ℕ) : ℚ :=
  piLoQ * H.pc * pv H.K par j * pv H.K par k + diagc H.K lam * Gm H.K par j k
  + ∑ m ∈ range H.K.Mt, Bm H.K par m j * ((WBmatM H.K par N ml).getD m []).getD k 0
  - piHiQ * H.w2up * (Pim H par j k + eta * leakQ H par N D j k)

def headMatM (H : HPar) (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ)) (ml : List ℚ) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (headEntryM H par N lam eta D ml j))

/-- The monolithic head matrix is the staged one on the computed moment list (definitional). -/
theorem headMatP_eq_M (H : HPar) (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ)) :
    headMatP H par N lam eta D = headMatM H par N lam eta D (momList H.K par) := rfl

/-! ## C. The strip-free head matrix (`w2up = 0`). -/

/-- The head entry without the strip block (the direct pole-free certificate has `w2up = 0`; the kernel
then never builds the strip Gram or the leakage matrices). -/
def headEntryN (H : HPar) (par N : ℕ) (lam : ℚ) (ml : List ℚ) (j k : ℕ) : ℚ :=
  piLoQ * H.pc * pv H.K par j * pv H.K par k + diagc H.K lam * Gm H.K par j k
  + ∑ m ∈ range H.K.Mt, Bm H.K par m j * ((WBmatM H.K par N ml).getD m []).getD k 0

def headMatN (H : HPar) (par N : ℕ) (lam : ℚ) (ml : List ℚ) : List (List ℚ) :=
  (List.range N).map (fun j => (List.range N).map (headEntryN H par N lam ml j))

theorem headMatM_eq_N (H : HPar) (hw : H.w2up = 0) (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ))
    (ml : List ℚ) : headMatM H par N lam eta D ml = headMatN H par N lam ml := by
  unfold headMatM headMatN
  refine List.map_congr_left fun j _ => List.map_congr_left fun k _ => ?_
  unfold headEntryM headEntryN
  rw [hw]
  ring

/-- **Transport**: a staged certificate on literal rows that reproduce the piece moments proves the
semantic PSD statement of the monolithic head matrix. -/
theorem headPSD_of_staged (H : HPar) (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ)) (R : ℕ)
    (rows : List (List ℚ)) (hrows : ∀ i < nPc H.K, pieceRow H.K par i = rows.getD i [])
    (hcert : psdCertR (headMatM H par N lam eta D (momListLit H.K par rows)) N R = true) :
    HeadPSD (headMatP H par N lam eta D) N := by
  rw [headMatP_eq_M, momList_eq_lit H.K par rows hrows]
  exact headPSD_of_psdCertR hcert

end Hodge1

namespace Hodge1
open KWin (piLoQ piHiQ mget getD_map_range psdCert)
open KWin2

/-- **Transport, strip-free and with the rounded matrix as data**: rows-checked moments, a literal
rounded matrix `B` equal to `roundShift (headMatN ...)`, and the exact LDL^T certificate of `B`. -/
theorem headPSD_of_staged_B (H : HPar) (hw : H.w2up = 0) (par N : ℕ) (lam eta : ℚ) (D : List (List ℚ))
    (R : ℕ) (rows : List (List ℚ)) (hrows : ∀ i < nPc H.K, pieceRow H.K par i = rows.getD i [])
    (B : List (List ℚ)) (hB : roundShift (headMatN H par N lam (momListLit H.K par rows)) N R = B)
    (hcert : psdCert B N = true) : HeadPSD (headMatP H par N lam eta D) N := by
  refine headPSD_of_staged H par N lam eta D R rows hrows ?_
  rw [headMatM_eq_N H hw]
  unfold psdCertR
  rw [hB]
  exact hcert

/-- Two lists of length `N` with equal `getD` entries below `N` are equal. -/
theorem list_eq_of_getD {α : Type*} {l₁ l₂ : List α} {N : ℕ} (d : α) (h₁ : l₁.length = N)
    (h₂ : l₂.length = N) (h : ∀ j < N, l₁.getD j d = l₂.getD j d) : l₁ = l₂ := by
  refine List.ext_getElem (h₁.trans h₂.symm) fun j hj1 hj2 => ?_
  have := h j (h₁ ▸ hj1)
  rwa [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj2] at this

theorem roundShift_length (A : List (List ℚ)) (N R : ℕ) : (roundShift A N R).length = N := by
  simp [roundShift]

end Hodge1
