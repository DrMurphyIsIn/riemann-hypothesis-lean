/-
  Hodge1_Rows5493O -- stage 1 of the staged certificate at l = 5493/10000, odd sector (HODGE-1
  Phase 1b-B): the kernel re-derives the moments of each of the 11 minorant pieces and checks them
  against the literal rows, one `decide +kernel` per piece (peak memory is set by the largest single
  declaration).  The heartbeat limit is lifted per declaration (`maxHeartbeats 0`): the kernel enforces
  it on `decide +kernel`.  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Rows5493

namespace Hodge1
open KWin2

set_option maxHeartbeats 0 in
theorem rowO5493_0 : pieceRow P5493 1 0 = rowsO5493.getD 0 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_1 : pieceRow P5493 1 1 = rowsO5493.getD 1 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_2 : pieceRow P5493 1 2 = rowsO5493.getD 2 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_3 : pieceRow P5493 1 3 = rowsO5493.getD 3 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_4 : pieceRow P5493 1 4 = rowsO5493.getD 4 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_5 : pieceRow P5493 1 5 = rowsO5493.getD 5 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_6 : pieceRow P5493 1 6 = rowsO5493.getD 6 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_7 : pieceRow P5493 1 7 = rowsO5493.getD 7 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_8 : pieceRow P5493 1 8 = rowsO5493.getD 8 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_9 : pieceRow P5493 1 9 = rowsO5493.getD 9 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowO5493_10 : pieceRow P5493 1 10 = rowsO5493.getD 10 [] := by decide +kernel

theorem nPc5493O : nPc P5493 = 11 := by decide +kernel

/-- All 11 piece rows of the odd sector agree with the literal data. -/
theorem rowsO5493_ok : ∀ i < nPc P5493, pieceRow P5493 1 i = rowsO5493.getD i [] := by
  intro i hi
  rw [nPc5493O] at hi
  interval_cases i
  exacts [rowO5493_0, rowO5493_1, rowO5493_2, rowO5493_3, rowO5493_4, rowO5493_5,
    rowO5493_6, rowO5493_7, rowO5493_8, rowO5493_9, rowO5493_10]

end Hodge1
