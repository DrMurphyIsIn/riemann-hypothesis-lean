/-
  Dogfood_complex_re_im_split -- the Telperion `complex_re_im_split` kind
  (SHAPES_AUDIT_48H_2026-09-22.md section 2 rank 4; B N3, B D7, C 2.10, D 2.2) regenerating the
  real/imaginary-part splits and cast identities this island proves by hand, 2026-09-22:

    E6Bridge7.lean:78-88     norm_gaussTest's `hre` / `hsq` and its Complex.norm_exp step
                             (e6b7_hre, e6b7_hsq, e6b7_hexp);
    E6Bridge7.lean:105-120   re_gaussTest's `hw2re` / `hw2im` / `hEre` / `hEim`
                             (e6b7_hw2re, e6b7_hw2im, e6b7_hre, e6b7_heim);
    E6Bridge28.lean:786-807  re_pow_two .. re_pow_five, Re (a + b i)^N for N = 2..5
                             (e6b28_re_pow_*, each TIED to the hand lemma);
    E6Bridge5.lean:110-114, E6Bridge7.lean:489-495, E6Bridge11.lean:940-941 / 1336-1337,
    E6Bridge14.lean:155-161  the B D7 cast face (e6b5_hcast, e6b7_pair_hcast, e6b7_pair_hre,
                             e6b11_arch_hcast, e6b14_centre_hcast).

  The block between the telperion provenance header and the first `end DogfoodComplexReImSplit`
  is the FROZEN emitter output (examples/complex_re_im_split/generate.py regenerates it; a test
  pins the bytes).  The hand-written gates after it (1) re-prove RvMBridge7.norm_gaussTest and
  RvMBridge7.re_gaussTest from the emitted splits alone and (2) close each cast site's hand
  `have` statement, copied verbatim from the island, with the emitted theorem applied to the
  island's atoms.  Nothing in E6Bridge5 / 7 / 11 / 14 / 28 is modified.

  Built by `lake build` as the lean_lib DogfoodComplexReImSplit; AxiomGuardRvMBridge.lean prints
  the axioms of all fifteen theorems.  Alone:
    cd telperion/examples/rvm_bridge/lean && lake env lean Probes/Dogfood_complex_re_im_split.lean
  Expected axioms for every theorem: [propext, Classical.choice, Quot.sound].

  conjecture1_proved = False.  Nothing here bears on RH: every statement is a finite polynomial
  identity between the components of a complex expression and real polynomials.
-/
/- telperion 0.1.6 | family DogfoodComplexReImSplit | input-hash eb24b0de3a71b67c
   15 theorems, 135 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import E6Bridge5
import E6Bridge7
import E6Bridge11
import E6Bridge14
import E6Bridge28

namespace DogfoodComplexReImSplit

/-- `e6b7_hre` -- the REAL PART of `-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2)` (mode `re`),
    complex variable `z` (split at `z = x + I y`),
    real parameters ['c', 'lam'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = -(2 * z.re ^ 2 * lam) + 4 * z.re * c * lam + 2 * z.im ^ 2 * lam - 2 * c ^ 2 * lam,
      im = -(4 * z.re * z.im * lam) + 4 * z.im * c * lam.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_hre (c lam : ℝ) (z : ℂ) :
    (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).re = 2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2) := by
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, pow_succ, pow_zero,
    one_mul]
  all_goals ring

example : ∀ (c lam : ℝ) (z : ℂ), (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).re = 2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2) := e6b7_hre

/-- `e6b7_hsq` -- the SQUARED NORM of `z - (c : ℂ)` (mode `norm_sq`),
    complex variable `z` (split at `z = x + I y`),
    real parameters ['c'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = z.re - c,
      im = z.im.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_hsq (c : ℝ) (z : ℂ) :
    ‖(z - (c : ℂ) : ℂ)‖ ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, pow_succ,
    pow_zero, one_mul]
  all_goals ring

example : ∀ (c : ℝ) (z : ℂ), ‖(z - (c : ℂ) : ℂ)‖ ^ 2 = (z.re - c) ^ 2 + z.im ^ 2 := e6b7_hsq

/-- `e6b7_hexp` -- the norm of the complex exponential of `-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2)` (mode `norm_exp`),
    complex variable `z` (split at `z = x + I y`),
    real parameters ['c', 'lam'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = -(2 * z.re ^ 2 * lam) + 4 * z.re * c * lam + 2 * z.im ^ 2 * lam - 2 * c ^ 2 * lam,
      im = -(4 * z.re * z.im * lam) + 4 * z.im * c * lam.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_hexp (c lam : ℝ) (z : ℂ) :
    ‖Complex.exp (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ)‖ = Real.exp (2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2)) := by
  have hre : (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).re = 2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2) := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, pow_succ, pow_zero,
      one_mul]
    all_goals ring
  rw [Complex.norm_exp, hre]

example : ∀ (c lam : ℝ) (z : ℂ), ‖Complex.exp (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ)‖ = Real.exp (2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2)) := e6b7_hexp

/-- `e6b7_hw2re` -- the REAL PART of `(z - (c : ℂ)) ^ 2` (mode `re`),
    complex variable `z` (split at `z = x + I y`),
    real parameters ['c'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = z.re ^ 2 - 2 * z.re * c - z.im ^ 2 + c ^ 2,
      im = 2 * z.re * z.im - 2 * z.im * c.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_hw2re (c : ℝ) (z : ℂ) :
    ((z - (c : ℂ)) ^ 2 : ℂ).re = (z.re - c) ^ 2 - z.im ^ 2 := by
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    pow_succ, pow_zero, one_mul]
  all_goals ring

example : ∀ (c : ℝ) (z : ℂ), ((z - (c : ℂ)) ^ 2 : ℂ).re = (z.re - c) ^ 2 - z.im ^ 2 := e6b7_hw2re

/-- `e6b7_hw2im` -- the IMAGINARY PART of `(z - (c : ℂ)) ^ 2` (mode `im`),
    complex variable `z` (split at `z = x + I y`),
    real parameters ['c'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = z.re ^ 2 - 2 * z.re * c - z.im ^ 2 + c ^ 2,
      im = 2 * z.re * z.im - 2 * z.im * c.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_hw2im (c : ℝ) (z : ℂ) :
    ((z - (c : ℂ)) ^ 2 : ℂ).im = z.im * (2 * z.re - 2 * c) := by
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    pow_succ, pow_zero, one_mul]
  all_goals ring

example : ∀ (c : ℝ) (z : ℂ), ((z - (c : ℂ)) ^ 2 : ℂ).im = z.im * (2 * z.re - 2 * c) := e6b7_hw2im

/-- `e6b7_heim` -- the IMAGINARY PART of `-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2)` (mode `im`),
    complex variable `z` (split at `z = x + I y`),
    real parameters ['c', 'lam'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = -(2 * z.re ^ 2 * lam) + 4 * z.re * c * lam + 2 * z.im ^ 2 * lam - 2 * c ^ 2 * lam,
      im = -(4 * z.re * z.im * lam) + 4 * z.im * c * lam.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_heim (c lam : ℝ) (z : ℂ) :
    (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).im = -(4 * z.im * lam * (z.re - c)) := by
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, pow_succ, pow_zero,
    one_mul]
  all_goals ring

example : ∀ (c lam : ℝ) (z : ℂ), (-(2 * (lam : ℂ) * (z - (c : ℂ)) ^ 2) : ℂ).im = -(4 * z.im * lam * (z.re - c)) := e6b7_heim

/-- `e6b28_re_pow_two` -- the REAL PART of `((a : ℂ) + (b : ℂ) * Complex.I) ^ 2` (mode `re`),
    no complex variable (a parameter-only expression),
    real parameters ['a', 'b'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = a ^ 2 - b ^ 2,
      im = 2 * a * b.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
    Tie gate: the statement is kernel-checked identical to `RvMBridge28.re_pow_two`.
-/
theorem e6b28_re_pow_two (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 : ℂ).re = a ^ 2 - b ^ 2 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, one_mul]
  all_goals ring

example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 : ℂ).re = a ^ 2 - b ^ 2 := e6b28_re_pow_two

-- tie gate: the regenerated statement IS the hand lemma's statement
example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 2 : ℂ).re = a ^ 2 - b ^ 2 := RvMBridge28.re_pow_two

/-- `e6b28_re_pow_three` -- the REAL PART of `((a : ℂ) + (b : ℂ) * Complex.I) ^ 3` (mode `re`),
    no complex variable (a parameter-only expression),
    real parameters ['a', 'b'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = a ^ 3 - 3 * a * b ^ 2,
      im = 3 * a ^ 2 * b - b ^ 3.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
    Tie gate: the statement is kernel-checked identical to `RvMBridge28.re_pow_three`.
-/
theorem e6b28_re_pow_three (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * Complex.I) ^ 3 : ℂ).re = a ^ 3 - 3 * a * b ^ 2 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, one_mul]
  all_goals ring

example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 3 : ℂ).re = a ^ 3 - 3 * a * b ^ 2 := e6b28_re_pow_three

-- tie gate: the regenerated statement IS the hand lemma's statement
example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 3 : ℂ).re = a ^ 3 - 3 * a * b ^ 2 := RvMBridge28.re_pow_three

/-- `e6b28_re_pow_four` -- the REAL PART of `((a : ℂ) + (b : ℂ) * Complex.I) ^ 4` (mode `re`),
    no complex variable (a parameter-only expression),
    real parameters ['a', 'b'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4,
      im = 4 * a ^ 3 * b - 4 * a * b ^ 3.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
    Tie gate: the statement is kernel-checked identical to `RvMBridge28.re_pow_four`.
-/
theorem e6b28_re_pow_four (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * Complex.I) ^ 4 : ℂ).re = a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, one_mul]
  all_goals ring

example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 4 : ℂ).re = a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 := e6b28_re_pow_four

-- tie gate: the regenerated statement IS the hand lemma's statement
example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 4 : ℂ).re = a ^ 4 - 6 * a ^ 2 * b ^ 2 + b ^ 4 := RvMBridge28.re_pow_four

/-- `e6b28_re_pow_five` -- the REAL PART of `((a : ℂ) + (b : ℂ) * Complex.I) ^ 5` (mode `re`),
    no complex variable (a parameter-only expression),
    real parameters ['a', 'b'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4,
      im = 5 * a ^ 4 * b - 10 * a ^ 2 * b ^ 3 + b ^ 5.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    simp only [component lemmas]; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
    Tie gate: the statement is kernel-checked identical to `RvMBridge28.re_pow_five`.
-/
theorem e6b28_re_pow_five (a b : ℝ) :
    (((a : ℂ) + (b : ℂ) * Complex.I) ^ 5 : ℂ).re = a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4 := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, pow_succ, pow_zero, one_mul]
  all_goals ring

example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 5 : ℂ).re = a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4 := e6b28_re_pow_five

-- tie gate: the regenerated statement IS the hand lemma's statement
example : ∀ (a b : ℝ), (((a : ℂ) + (b : ℂ) * Complex.I) ^ 5 : ℂ).re = a ^ 5 - 10 * a ^ 3 * b ^ 2 + 5 * a * b ^ 4 := RvMBridge28.re_pow_five

/-- `e6b5_hcast` -- the REAL CAST IDENTITY of `(m : ℂ) * (u : ℂ) ^ 2` (mode `cast`),
    no complex variable (a parameter-only expression),
    real parameters ['u'],
    natural-number atoms ['m'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = (m : ℝ) * u ^ 2,
      im = 0.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    push_cast; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b5_hcast (m : ℕ) (u : ℝ) :
    ((m : ℂ) * (u : ℂ) ^ 2 : ℂ) = (((m : ℝ) * u ^ 2 : ℝ) : ℂ) := by
  push_cast
  all_goals ring

example : ∀ (m : ℕ) (u : ℝ), ((m : ℂ) * (u : ℂ) ^ 2 : ℂ) = (((m : ℝ) * u ^ 2 : ℝ) : ℂ) := e6b5_hcast

/-- `e6b7_pair_hcast` -- the REAL CAST IDENTITY of `2 * (m : ℂ) * (g : ℂ)` (mode `cast`),
    no complex variable (a parameter-only expression),
    real parameters ['g'],
    natural-number atoms ['m'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = 2 * (m : ℝ) * g,
      im = 0.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    push_cast; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_pair_hcast (m : ℕ) (g : ℝ) :
    (2 * (m : ℂ) * (g : ℂ) : ℂ) = ((2 * (m : ℝ) * g : ℝ) : ℂ) := by
  push_cast
  all_goals ring

example : ∀ (m : ℕ) (g : ℝ), (2 * (m : ℂ) * (g : ℂ) : ℂ) = ((2 * (m : ℝ) * g : ℝ) : ℂ) := e6b7_pair_hcast

/-- `e6b7_pair_hre` -- the REAL PART, through the cast identity, of `2 * (m : ℂ) * (g : ℂ)` (mode `cast_re`),
    no complex variable (a parameter-only expression),
    real parameters ['g'],
    natural-number atoms ['m'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = 2 * (m : ℝ) * g,
      im = 0.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    have hcast := by push_cast; all_goals ring;
    rw [hcast, Complex.ofReal_re].  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b7_pair_hre (m : ℕ) (g : ℝ) :
    (2 * (m : ℂ) * (g : ℂ) : ℂ).re = 2 * (m : ℝ) * g := by
  have hcast : (2 * (m : ℂ) * (g : ℂ) : ℂ) = ((2 * (m : ℝ) * g : ℝ) : ℂ) := by
    push_cast
    all_goals ring
  rw [hcast, Complex.ofReal_re]

example : ∀ (m : ℕ) (g : ℝ), (2 * (m : ℂ) * (g : ℂ) : ℂ).re = 2 * (m : ℝ) * g := e6b7_pair_hre

/-- `e6b11_arch_hcast` -- the REAL CAST IDENTITY of `(A : ℂ) * (L : ℂ)` (mode `cast`),
    no complex variable (a parameter-only expression),
    real parameters ['A', 'L'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = A * L,
      im = 0.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    push_cast; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b11_arch_hcast (A L : ℝ) :
    ((A : ℂ) * (L : ℂ) : ℂ) = ((A * L : ℝ) : ℂ) := by
  push_cast
  all_goals ring

example : ∀ (A L : ℝ), ((A : ℂ) * (L : ℂ) : ℂ) = ((A * L : ℝ) : ℂ) := e6b11_arch_hcast

/-- `e6b14_centre_hcast` -- the REAL CAST IDENTITY of `(m : ℂ) * (v : ℂ)` (mode `cast`),
    no complex variable (a parameter-only expression),
    real parameters ['v'],
    natural-number atoms ['m'].
    Split computed by sympy re/im and re-verified by a symbolic identity, by
    as_real_imag, and by an independent exact Fraction evaluator at seeded
    rational points:
      re = (m : ℝ) * v,
      im = 0.
    The claimed right-hand side is ring-equal to the split (residual 0) and the
    identity is load-bearing (a corrupted claim breaks it).  Frozen skeleton:
    push_cast; all_goals ring.  A finite polynomial identity;
    nothing about RH.  conjecture1_proved = False.
-/
theorem e6b14_centre_hcast (m : ℕ) (v : ℝ) :
    ((m : ℂ) * (v : ℂ) : ℂ) = (((m : ℝ) * v : ℝ) : ℂ) := by
  push_cast
  all_goals ring

example : ∀ (m : ℕ) (v : ℝ), ((m : ℂ) * (v : ℂ) : ℂ) = (((m : ℝ) * v : ℝ) : ℂ) := e6b14_centre_hcast

end DogfoodComplexReImSplit

/-! ## Consumer and instantiation gates (hand-written, frozen in
`examples/complex_re_im_split/generate.py`).

The E6Bridge7 split sites are local `have`s inside `RvMBridge7.norm_gaussTest` /
`RvMBridge7.re_gaussTest`, so they carry no tie gate.  Instead: each hand lemma's statement is
pinned to the hand lemma itself, and then RE-PROVED from the emitted splits above alone.  The
only glue is `neg_mul` (sympy cannot distinguish the groupings `-(2 lam) * w` and
`-(2 lam w)`) and three `ring` reshapings (sympy's canonical term order is not the hand's).
The B D7 cast sites are local `have`s too; each hand statement, copied verbatim from the
island, is closed by the emitted cast theorem applied to the island's atoms (no glue).
Nothing here is emitter output, and nothing here bears on RH.  conjecture1_proved = False. -/

namespace DogfoodComplexReImSplit

/-- Statement pin: the goal of consumer gate 1 IS `RvMBridge7.norm_gaussTest`. -/
example : ∀ (c lam : ℝ) (z : ℂ), ‖RvMBridge6.gaussTest c lam z‖ = ((z.re - c) ^ 2 + z.im ^ 2)
    * Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2)) := RvMBridge7.norm_gaussTest

/-- Consumer gate 1: `RvMBridge7.norm_gaussTest` from `e6b7_hsq` and `e6b7_hexp` alone
(the hand proof's two `have`s, `E6Bridge7.lean:78-88`). -/
example (c lam : ℝ) (z : ℂ) :
    ‖RvMBridge6.gaussTest c lam z‖ = ((z.re - c) ^ 2 + z.im ^ 2)
      * Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2)) := by
  unfold RvMBridge6.gaussTest
  rw [norm_mul, Complex.norm_pow, neg_mul, e6b7_hexp, e6b7_hsq,
    show 2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2)
        = 2 * lam * (z.im ^ 2 - (z.re - c) ^ 2) from by ring]

/-- Statement pin: the goal of consumer gate 2 IS `RvMBridge7.re_gaussTest`. -/
example : ∀ (c lam : ℝ) (z : ℂ), (RvMBridge6.gaussTest c lam z).re
    = Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))
      * (((z.re - c) ^ 2 - z.im ^ 2) * Real.cos (4 * lam * (z.re - c) * z.im)
        + 2 * (z.re - c) * z.im * Real.sin (4 * lam * (z.re - c) * z.im)) :=
  RvMBridge7.re_gaussTest

/-- Consumer gate 2: `RvMBridge7.re_gaussTest` from `e6b7_hw2re`, `e6b7_hw2im`, `e6b7_hre` and
`e6b7_heim` alone (the hand proof's four `have`s, `E6Bridge7.lean:105-120`). -/
example (c lam : ℝ) (z : ℂ) :
    (RvMBridge6.gaussTest c lam z).re = Real.exp (2 * lam * (z.im ^ 2 - (z.re - c) ^ 2))
      * (((z.re - c) ^ 2 - z.im ^ 2) * Real.cos (4 * lam * (z.re - c) * z.im)
        + 2 * (z.re - c) * z.im * Real.sin (4 * lam * (z.re - c) * z.im)) := by
  unfold RvMBridge6.gaussTest
  rw [neg_mul, Complex.mul_re, Complex.exp_re, Complex.exp_im, e6b7_hre, e6b7_heim,
    e6b7_hw2re, e6b7_hw2im,
    show -(4 * z.im * lam * (z.re - c)) = -(4 * lam * (z.re - c) * z.im) from by ring,
    Real.cos_neg, Real.sin_neg,
    show 2 * lam * (-((z.re - c) ^ 2) + z.im ^ 2)
        = 2 * lam * (z.im ^ 2 - (z.re - c) ^ 2) from by ring]
  ring

section CastSites
open Zeta23 WeilExplicit RvMBridge6 RvMBridge11

/-- Instantiation gate: `have hcast` of `RvMBridge5.term_re_nonneg` (`E6Bridge5.lean:110-114`)
IS `e6b5_hcast` at `m := zeroMult ρ`, `u := ‖paperFT g ρ.im‖`. -/
example (g : ℝ → ℂ) (ρ : ℂ) :
    (WeilExplicit.zeroMult ρ : ℂ) * ((‖paperFT g ρ.im‖ : ℂ)) ^ 2
        = (((WeilExplicit.zeroMult ρ : ℝ) * ‖paperFT g ρ.im‖ ^ 2 : ℝ) : ℂ) :=
  e6b5_hcast (WeilExplicit.zeroMult ρ) ‖paperFT g ρ.im‖

/-- Instantiation gate: the inner `have` of `RvMBridge7.re_zeroSide_le` (`E6Bridge7.lean:491-494`)
IS `e6b7_pair_hcast` at `m := zeroMult ρ₁`, `g := (gaussTest c lam (gammaOf ρ₁)).re`. -/
example (c lam : ℝ) (ρ₁ : ℂ) :
    (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ))
        = ((2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re : ℝ) : ℂ) :=
  e6b7_pair_hcast (WeilExplicit.zeroMult ρ₁) (gaussTest c lam (gammaOf ρ₁)).re

/-- Instantiation gate: `have hre` of `RvMBridge7.re_zeroSide_le` (`E6Bridge7.lean:489-495`) IS
`e6b7_pair_hre` (whose proof is that site's `push_cast; ring` then `Complex.ofReal_re`). -/
example (c lam : ℝ) (ρ₁ : ℂ) :
    (2 * (WeilExplicit.zeroMult ρ₁ : ℂ) * ((gaussTest c lam (gammaOf ρ₁)).re : ℂ)).re
      = 2 * (WeilExplicit.zeroMult ρ₁ : ℝ) * (gaussTest c lam (gammaOf ρ₁)).re :=
  e6b7_pair_hre (WeilExplicit.zeroMult ρ₁) (gaussTest c lam (gammaOf ρ₁)).re

/-- Instantiation gate: the first `show` of `RvMBridge11.re_archSide_ge` (`E6Bridge11.lean:940-941`,
repeated in `re_weilForm_gauss_nonneg_of_large_c` at `:1336-1337`) IS `e6b11_arch_hcast` at
`A := gaussA lam`, `L := Real.log Real.pi`. -/
example (lam : ℝ) :
    (gaussA lam : ℂ) * (Real.log Real.pi : ℂ) = ((gaussA lam * Real.log Real.pi : ℝ) : ℂ) :=
  e6b11_arch_hcast (gaussA lam) (Real.log Real.pi)

/-- Instantiation gate: the `have` of `RvMBridge14.re_term_centre` (`E6Bridge14.lean:155-160`) IS
`e6b14_centre_hcast` at `m := zeroMult ρ`, `v := -((1/2 - ρ.re)^2) * exp (2 lam (1/2 - ρ.re)^2)`. -/
example (lam : ℝ) (ρ : ℂ) :
    ((WeilExplicit.zeroMult ρ : ℂ)
      * ((-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2) : ℝ) : ℂ))
      = (((WeilExplicit.zeroMult ρ : ℝ)
        * (-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2)) : ℝ) : ℂ) :=
  e6b14_centre_hcast (WeilExplicit.zeroMult ρ)
    (-((1 / 2 - ρ.re) ^ 2) * Real.exp (2 * lam * (1 / 2 - ρ.re) ^ 2))

end CastSites

end DogfoodComplexReImSplit

#print axioms DogfoodComplexReImSplit.e6b7_hre
#print axioms DogfoodComplexReImSplit.e6b7_hsq
#print axioms DogfoodComplexReImSplit.e6b7_hexp
#print axioms DogfoodComplexReImSplit.e6b7_hw2re
#print axioms DogfoodComplexReImSplit.e6b7_hw2im
#print axioms DogfoodComplexReImSplit.e6b7_heim
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_two
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_three
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_four
#print axioms DogfoodComplexReImSplit.e6b28_re_pow_five
#print axioms DogfoodComplexReImSplit.e6b5_hcast
#print axioms DogfoodComplexReImSplit.e6b7_pair_hcast
#print axioms DogfoodComplexReImSplit.e6b7_pair_hre
#print axioms DogfoodComplexReImSplit.e6b11_arch_hcast
#print axioms DogfoodComplexReImSplit.e6b14_centre_hcast
