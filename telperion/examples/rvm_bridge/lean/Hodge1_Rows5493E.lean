/-
  Hodge1_Rows5493E -- stage 1 of the staged certificate at l = 5493/10000, even sector (HODGE-1
  Phase 1b-B): the kernel re-derives the moments of each of the 11 minorant pieces and checks them
  against the literal rows, one `decide +kernel` per piece (peak memory is set by the largest single
  declaration).  The heartbeat limit is lifted per declaration (`maxHeartbeats 0`): the kernel enforces
  it on `decide +kernel`.  conjecture1_proved = False.  No `sorry`.
-/
import Hodge1_Rows5493

namespace Hodge1
open KWin2

set_option maxHeartbeats 0 in
theorem rowE5493_0 : pieceRow P5493 0 0 = rowsE5493.getD 0 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_1 : pieceRow P5493 0 1 = rowsE5493.getD 1 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_2 : pieceRow P5493 0 2 = rowsE5493.getD 2 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_3 : pieceRow P5493 0 3 = rowsE5493.getD 3 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_4 : pieceRow P5493 0 4 = rowsE5493.getD 4 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_5 : pieceRow P5493 0 5 = rowsE5493.getD 5 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_6 : pieceRow P5493 0 6 = rowsE5493.getD 6 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_7 : pieceRow P5493 0 7 = rowsE5493.getD 7 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_8 : pieceRow P5493 0 8 = rowsE5493.getD 8 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_9 : pieceRow P5493 0 9 = rowsE5493.getD 9 [] := by decide +kernel

set_option maxHeartbeats 0 in
theorem rowE5493_10 : pieceRow P5493 0 10 = rowsE5493.getD 10 [] := by decide +kernel

theorem nPc5493 : nPc P5493 = 11 := by decide +kernel

/-- All 11 piece rows of the even sector agree with the literal data. -/
theorem rowsE5493_ok : ∀ i < nPc P5493, pieceRow P5493 0 i = rowsE5493.getD i [] := by
  intro i hi
  rw [nPc5493] at hi
  interval_cases i
  exacts [rowE5493_0, rowE5493_1, rowE5493_2, rowE5493_3, rowE5493_4, rowE5493_5,
    rowE5493_6, rowE5493_7, rowE5493_8, rowE5493_9, rowE5493_10]

end Hodge1
