"""RK-2 C: e^{L^2/8} brackets (the pole factor of the Zhu (13) tail bound K_2 inside eps_C) at every certified L, by Telperion's
exp_enclosure emitter, imported read-only and UNMODIFIED from ~/telperion-tools/research-main/src.  eps_C as a whole stays ARB.
conjecture1_proved = False."""
import sys
import os
PKG = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.environ.get("TELPERION_SRC", os.path.join(PKG, "..", "..", "..", "..", "telperion-tools", "research-main", "src")))
from fractions import Fraction
import sympy as sp
from flint import arb, ctx
from telperion.emit_exp_enclosure import exp_enclosure_certificate, _exp_lemma
ctx.prec = 200
out = ["import Mathlib\n\n/-! RK-2 C: Telperion exp_enclosure (unmodified) for e^{L^2/8}, L in {1, 1.45, 1.493945, 2, 2.25, 2.4}: the pole factor\n"
       "of K_2 in the Zhu (13) coupling eps_C.  Demonstration of the one chain scalar with an existing emitter shape; eps_C as a\n"
       "whole stays ARB.  conjecture1_proved = False. -/\n\nnamespace RK2.T4\n\n"]
for tag, L in (("L1", "1"), ("L145", "1.45"), ("L1494", "1.493945"), ("L2", "2"), ("L225", "2.25"), ("L24", "2.4")):
    x = Fraction(L) ** 2 / 8
    v = arb(x.numerator) / x.denominator
    e = v.exp()
    q = Fraction(10) ** -18
    lo = Fraction(int((e.lower() / arb(q.numerator) * q.denominator).floor().unique_fmpz())) * q
    hi = Fraction(int((e.upper() / arb(q.numerator) * q.denominator).ceil().unique_fmpz())) * q
    cert = exp_enclosure_certificate(sp.Rational(x.numerator, x.denominator), sp.Rational(lo.numerator, lo.denominator),
                                     sp.Rational(hi.numerator, hi.denominator))
    out.append(_exp_lemma(f"exp_{tag}", f"{x.numerator} / {x.denominator}", cert.n, f"{lo.numerator} / {lo.denominator}",
                          f"{hi.numerator} / {hi.denominator}", neg=False) + "\n")
    print(tag, L, float(x), cert.n, float(lo), float(hi))
out.append("end RK2.T4\n")
open(os.path.join(PKG, "lean", "T4_exp.lean"), "w").write("".join(out))
