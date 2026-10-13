"""Certified DH diffraction emitter (PROGRAM MIRRORMERE, QC-B1 increment 2).

Emits `ZooDH.lean`: the Davenport-Heilbronn analogue of `BraggH100`, the certified
finite-volume diffraction amplitude of the DH zero comb at two rational frequencies

    u2 = 693147/1000000   (~= log 2, the BraggH100 frequency, for direct comparison)
    u5 = 1609437/1000000  (~= log 5, natural for a period-5 object)

with two deliverable theorems per frequency:

  * `dh_diffraction_online_box_u{2,5}` -- the ON-LINE part
        F_on(u) := sum_{k : on-line, 0 < gamma_k <= T} cos(gamma_k * u)
    enclosed in a certified rational interval.  This is the DIRECT analogue of
    BraggH100: each on-line ordinate gamma_k sits in a tight rational bracket
    [a_k, b_k] pinned from a certified sign change of Re D(1/2 + i t) (the DH
    Hardy-Z analogue), and cos(gamma_k * u) is enclosed by the CosEnclosure
    double-angle chain + Lipschitz bracket-width absorption.

  * `dh_offline_term_box_u{2,5}` -- the OFF-LINE pair's contribution.  For an
    off-line zero rho = beta + i gamma (delta := beta - 1/2 != 0) the symmetric
    +gamma pair {rho, 1 - rho-bar} = {beta + i gamma, (1-beta) + i gamma} of the
    DH zero quartet {rho, rho-bar, 1-rho, 1-rho-bar} contributes to the diffraction

        T_off(u) = 2 * cosh(delta * u) * cos(gamma * u)

    (derived + numerically confirmed in dh_diffraction.py; on-line delta=0 gives
    cosh=1, reducing to the single cos(gamma*u) term -- so cosh(delta*u) is the
    DISTINCTIVE off-line signature).  The cosh factor is enclosed by the local
    order-6 `cosh_bracket` (exp Taylor remainder, |delta*u| < 1); cos(gamma*u) by
    the same CosEnclosure chain.  The theorem exposes the comparison constant
    cosh(delta*u) - 1 > 0 as the measured off-line leakage.

TRUST.  The DH ordinate brackets and off-line (beta, gamma) enclosures are Arb
sign inputs (the `henc*` hypotheses), identical trust class to BraggH100's gLine
signs / the band hLine.  Everything downstream is kernel-checked.  The winding
completeness of the on-line set to height T is the separately-certified
`dh_zeros.json` inventory (Arb).  conjecture1_proved = False.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent.parent / "src"))

from telperion.arb_dh import dh_eval  # noqa: E402

U2 = F(693147, 1000000)      # ~= log 2
U5 = F(1609437, 1000000)     # ~= log 5
T_HEIGHT = 100               # diffraction height window (parity with BraggH100)
M_DOUBLE = 12                # double-angle reduction depth (theta <= ~161 => M>=8; 12 gives margin)
GRID = F(10) ** 24           # outward-rounding grid for cos/cosh intervals (1e-24)
BISECT_ITERS = 30            # tight-bracket bisection depth (width ~ 1e-7 from a 0.08 box)
PREC = 200


def _rdown(x: F, D: F = GRID) -> F:
    return F(math.floor(x * D), 1) / D


def _rup(x: F, D: F = GRID) -> F:
    return F(math.ceil(x * D), 1) / D


def _reD(re0: F, t: F, prec=PREC) -> tuple[F, F]:
    rl, rh, _il, _ih = dh_eval(re0, t, prec)
    return rl, rh


def _sign(lo: F, hi: F) -> int:
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    return 0


def tight_online_bracket(box: dict) -> dict:
    """Bisect Re D(1/2 + i t) inside the certified on-line box to a tight rational
    bracket [a, b] with a certified sign change (the ordinate to ~1e-7)."""
    a = F(box["im"][0])
    b = F(box["im"][1])
    (alo, ahi) = _reD(F(1, 2), a)
    (blo, bhi) = _reD(F(1, 2), b)
    sa, sb = _sign(alo, ahi), _sign(blo, bhi)
    if sa == 0 or sb == 0 or sa == sb:
        # endpoints not a clean Re sign change; nudge in. Fall back: scan a fine grid.
        n = 400
        pts = [a + (b - a) * F(k, n) for k in range(n + 1)]
        sgn = None
        for i in range(len(pts) - 1):
            l, _ = _reD(F(1, 2), pts[i])
            _, h2 = _reD(F(1, 2), pts[i + 1])
            (l0, l1) = _reD(F(1, 2), pts[i])
            (r0, r1) = _reD(F(1, 2), pts[i + 1])
            if _sign(l0, l1) != 0 and _sign(r0, r1) != 0 and _sign(l0, l1) != _sign(r0, r1):
                a, b = pts[i], pts[i + 1]
                alo, ahi = l0, l1
                blo, bhi = r0, r1
                sa, sb = _sign(l0, l1), _sign(r0, r1)
                break
        else:
            raise RuntimeError(f"no Re sign change in box {box['im']}")
    # bisect
    for _ in range(BISECT_ITERS):
        m = (a + b) / 2
        (mlo, mhi) = _reD(F(1, 2), m)
        sm = _sign(mlo, mhi)
        if sm == 0:
            break  # ball straddles 0; stop, bracket is tight enough
        if sm == sa:
            a, alo, ahi = m, mlo, mhi
        else:
            b, blo, bhi = m, mlo, mhi
    # round outward to keep small denominators
    a2 = _rdown(a, F(10) ** 7)
    b2 = _rup(b, F(10) ** 7)
    # re-verify sign change on the rounded bracket
    (alo2, ahi2) = _reD(F(1, 2), a2)
    (blo2, bhi2) = _reD(F(1, 2), b2)
    if _sign(alo2, ahi2) == 0 or _sign(blo2, bhi2) == 0 or \
       _sign(alo2, ahi2) == _sign(blo2, bhi2):
        a2, b2 = a, b
        alo2, ahi2, blo2, bhi2 = alo, ahi, blo, bhi
    neg_then_pos = _sign(alo2, ahi2) < 0
    return {
        "a": a2, "b": b2,
        "neg_then_pos": neg_then_pos,
        "reD_a": (alo2, ahi2), "reD_b": (blo2, bhi2),
        "gamma": (a2 + b2) / 2,
    }


# ---------------------------------------------------------------------------
# CosEnclosure double-angle chain (adapted from bragg_refine.cos_chain)
# ---------------------------------------------------------------------------
def cos_chain(theta: F):
    y = theta / F(2) ** M_DOUBLE
    if abs(y) > 1:
        raise ValueError(f"reduced argument y={float(y)} exceeds 1 (raise M)")
    center = 1 - y ** 2 / 2
    rem = y ** 4 * F(5, 96)
    lo = _rdown(center - rem)
    hi = _rup(center + rem)
    base = (y, lo, hi)
    steps = []
    for _ in range(M_DOUBLE):
        cands = [2 * lo ** 2 - 1, 2 * hi ** 2 - 1]
        if lo <= 0 <= hi:
            cands.append(F(-1))
        nlo = _rdown(min(cands))
        nhi = _rup(max(cands))
        case = "lo_nonneg" if lo >= 0 else ("hi_nonpos" if hi <= 0 else "straddle")
        steps.append((lo, hi, nlo, nhi, case))
        lo, hi = nlo, nhi
    return lo, hi, base, steps


def cosh_bracket_interval(x: F):
    """Certified [lo, hi] for cosh(x), |x|<=1, via order-6 exp Taylor remainder:
    |cosh x - (1 + x^2/2 + x^4/24)| <= |x|^6 * 7/4320."""
    if abs(x) > 1:
        raise ValueError(f"cosh arg {float(x)} exceeds 1")
    center = 1 + x ** 2 / 2 + x ** 4 / 24
    rem = abs(x) ** 6 * F(7, 4320)
    return _rdown(center - rem), _rup(center + rem), center, rem


def build():
    data = json.loads((_HERE / "zoo_data" / "dh_zeros.json").read_text())
    on = [z for z in data["zeros"] if z["on_line"] and z["gamma_approx"] <= T_HEIGHT]
    off = [z for z in data["zeros"] if not z["on_line"] and z["gamma_approx"] <= T_HEIGHT]
    on.sort(key=lambda z: z["gamma_approx"])
    online = []
    for i, box in enumerate(on):
        tb = tight_online_bracket(box)
        online.append({"idx": i + 1, **tb})
    return {"online": online, "offline": off, "n_on": len(online)}


def summary():
    d = build()
    print(f"on-line zeros <= {T_HEIGHT}: {d['n_on']}")
    for u, name in ((U2, "u2~log2"), (U5, "u5~log5")):
        tot_lo = F(0)
        tot_hi = F(0)
        for z in d["online"]:
            c = z["gamma"]
            clo, chi, _b, _s = cos_chain(c * u)
            w = _rup((z["b"] - z["a"]) * u)
            tot_lo += clo - w
            tot_hi += chi + w
        truth = sum(math.cos(float(u) * float(z["gamma"])) for z in d["online"])
        print(f"  {name}: F_on in [{float(tot_lo):.6f}, {float(tot_hi):.6f}] "
              f"width {float(tot_hi-tot_lo):.2e} truth {truth:.6f}")
    for z in d["offline"]:
        beta = (F(z["re"][0]) + F(z["re"][1])) / 2
        gamma = (F(z["im"][0]) + F(z["im"][1])) / 2
        delta = beta - F(1, 2)
        for u, name in ((U2, "u2"), (U5, "u5")):
            chlo, chhi, cc, _r = cosh_bracket_interval(delta * u)
            print(f"  off-line gamma~{float(gamma):.3f} delta~{float(delta):.3f} "
                  f"{name}: cosh(delta*u) in [{float(chlo):.6f},{float(chhi):.6f}] "
                  f"(signature cosh-1 ~ {float(cc)-1:.4f})")


# ---------------------------------------------------------------------------
# Lean emitter
# ---------------------------------------------------------------------------
def _q(fr: F) -> str:
    if fr < 0:
        return f"(-({-fr.numerator} / {fr.denominator}) : ℝ)"
    return f"({fr.numerator} / {fr.denominator} : ℝ)"


def _case_term(case: str) -> str:
    if case == "lo_nonneg":
        return "Or.inl (by norm_num)"
    if case == "hi_nonpos":
        return "Or.inr (Or.inl (by norm_num))"
    return "Or.inr (Or.inr (by norm_num))"


def emit_cos_chain(theta: F, tag: str, out: list) -> str:
    """Emit CosEnclosure double-angle chain establishing hcos{tag} : clo <= cos theta <= chi.
    theta is a rational; the chain rewrites 2^M * y = theta at the end.  Returns hyp name."""
    clo, chi, base, steps = cos_chain(theta)
    y, blo, bhi = base
    args = [theta / F(2) ** (M_DOUBLE - j) for j in range(M_DOUBLE + 1)]
    out.append(f"  -- cos({float(theta):.9f}) chain (M={M_DOUBLE})")
    out.append(f"  have hy{tag} : |({_q(args[0])} : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num")
    out.append(f"  have hb{tag} : {_q(blo)} ≤ Real.cos {_q(args[0])} ∧ Real.cos {_q(args[0])} ≤ {_q(bhi)} :=")
    out.append(f"    CosEnclosure.cos_base_interval (y := {_q(args[0])}) hy{tag} (by norm_num) (by norm_num)")
    prev = f"hb{tag}"
    prev_arg = _q(args[0])
    for j, (plo, phi, nlo, nhi, case) in enumerate(steps):
        hname = f"hs{tag}_{j+1}"
        cur_arg = _q(args[j + 1])
        out.append(f"  have hdbl{tag}_{j+1} : (2 : ℝ) * {prev_arg} = {cur_arg} := by norm_num")
        out.append(f"  have {hname} : {_q(nlo)} ≤ Real.cos {cur_arg} ∧ Real.cos {cur_arg} ≤ {_q(nhi)} := by")
        out.append(f"    have h := CosEnclosure.cos_double_interval (y := {prev_arg}) "
                   f"(lo' := {_q(nlo)}) (hi' := {_q(nhi)}) {prev}.1 {prev}.2 "
                   f"(by norm_num) (by norm_num) (by norm_num) (by norm_num) ({_case_term(case)})")
        out.append(f"    rw [hdbl{tag}_{j+1}] at h; exact h")
        prev = hname
        prev_arg = cur_arg
    hcos = f"hcos{tag}"
    out.append(f"  have {hcos} : {_q(clo)} ≤ Real.cos ({_q(theta)}) ∧ "
               f"Real.cos ({_q(theta)}) ≤ {_q(chi)} := {prev}")
    return hcos, clo, chi


def emit_online_cosbox(z: dict, u: F, uname: str, out: list) -> tuple[str, F, F]:
    """Standalone per-zero cos-box lemma for frequency u:
    dh_cosbox_{uname}_{k} (t) (a<=t<=b) : box_lo <= cos(t*u{name}) <= box_hi."""
    i = z["idx"]
    a, b = z["a"], z["b"]
    c = z["gamma"]
    theta = c * u
    w = _rup((b - a) * u)
    out.append("")
    out.append(f"/-- on-line DH ordinate {i} cos-box at {uname}: for `t ∈ [{float(a):.7f},{float(b):.7f}]`,")
    out.append(f"    `cos (t·{uname})` in the certified box (double-angle chain + Lipschitz). -/")
    out.append(f"theorem dh_cosbox_{uname}_{i} (t : ℝ) (hta : {_q(a)} ≤ t) (htb : t ≤ {_q(b)}) :")
    hcos, clo, chi = None, None, None
    body: list = []
    hcos, clo, chi = emit_cos_chain(theta, f"{uname}_{i}", body)
    box_lo = clo - w
    box_hi = chi + w
    out.append(f"    {_q(box_lo)} ≤ Real.cos (t * {uname}) ∧ "
               f"Real.cos (t * {uname}) ≤ {_q(box_hi)} := by")
    out.extend(body)
    out.append(f"  have hdist : |t * {uname} - {_q(theta)}| ≤ {_q(w)} := by")
    out.append(f"    have hcu : ({_q(theta)} : ℝ) = {_q(c)} * {uname} := by rw [{uname}]; norm_num")
    out.append(f"    rw [hcu, ← sub_mul, abs_mul, abs_of_nonneg (by rw [{uname}]; norm_num : (0:ℝ) ≤ {uname})]")
    out.append(f"    have hrc : |t - {_q(c)}| ≤ {_q(b - a)} := by")
    out.append(f"      rw [abs_le]; constructor <;> [linarith [hta, htb]; linarith [hta, htb]]")
    out.append(f"    calc |t - {_q(c)}| * {uname} ≤ {_q(b - a)} * {uname} := by")
    out.append(f"            apply mul_le_mul_of_nonneg_right hrc (by rw [{uname}]; norm_num)")
    out.append(f"      _ ≤ {_q(w)} := by rw [{uname}]; norm_num")
    out.append(f"  have h := CosEnclosure.cos_encl_bracket (arg := t * {uname}) (c := {_q(theta)}) "
               f"(w := {_q(w)}) (by norm_num) hdist {hcos}.1 {hcos}.2")
    out.append(f"  exact ⟨by linarith [h.1], by linarith [h.2]⟩")
    return f"dh_cosbox_{uname}_{i}", box_lo, box_hi


def emit_online_theorem(zeros: list, u: F, uname: str, boxes: list, out: list) -> None:
    """Assembly: dh_diffraction_online_box_{uname}.

    For ANY choice of on-line ordinates g_k, each lying in its certified rational
    bracket [a_k, b_k] (the brackets are the winding-certified on-line DH zero
    boxes of dh_zeros.json, tightened by Re-D sign bisection), the diffraction sum
    `sum cos(g_k * u)` lies in the certified interval.  Fully kernel-closed via the
    per-zero cos-box lemmas + interval fold -- the bracket-membership hypotheses
    carry the Arb inventory trust, everything downstream is kernel."""
    N = len(zeros)
    A_lo = sum((bl for _, bl, _ in boxes), F(0))
    A_hi = sum((bh for _, _, bh in boxes), F(0))
    truth = sum(math.cos(float(u) * float(z["gamma"])) for z in zeros)
    out.append("")
    out.append(f"/-! ### Assembly: on-line DH diffraction at {uname} -/")
    out.append("")
    out.append(f"/-- **Certified on-line DH diffraction at {uname} (~= {float(u):.6f}).**  Let")
    out.append(f"    `g_1 < ... < g_{N}` be the {N} on-line DH ordinates with `0 < g_k <= {T_HEIGHT}`, each")
    out.append(f"    lying in its winding-certified rational bracket `[a_k, b_k]` (`dh_zeros.json`,")
    out.append(f"    tightened by an `Re D(1/2+i·t)` sign-bisection -- the DH Hardy-Z analogue; the")
    out.append(f"    bracket-membership hypotheses carry the Arb inventory trust, same class as")
    out.append(f"    BraggH100's `hLine`).  Then the diffraction sum `sum cos(g_k * {uname})` lies in the")
    out.append(f"    certified interval.  This is the DIRECT DH analogue of `BraggH100.bragg_amplitude_h100`;")
    out.append(f"    the off-line contribution is the separate `dh_offline_term_box_{uname}`.")
    out.append(f"    conjecture1_proved = False. -/")
    out.append(f"theorem dh_diffraction_online_box_{uname}")
    xs = " ".join(f"g{z['idx']}" for z in zeros)
    out.append(f"    ({xs} : ℝ)")
    # per-zero bracket membership hyps
    for z in zeros:
        i = z["idx"]
        out.append(f"    (hg{i} : {_q(z['a'])} ≤ g{i} ∧ g{i} ≤ {_q(z['b'])})")
    sum_expr = " + ".join(f"Real.cos (g{z['idx']} * {uname})" for z in zeros)
    out.append(f"    : {_q(A_lo)} ≤ {sum_expr} ∧")
    out.append(f"      {sum_expr} ≤ {_q(A_hi)} := by")
    for z in zeros:
        i = z["idx"]
        out.append(f"  have hcb{i} := dh_cosbox_{uname}_{i} g{i} (hg{i}).1 (hg{i}).2")
    acc = "hcb1"
    for k in range(1, N):
        fname = f"hsum{k+1}"
        out.append(f"  have {fname} := CosEnclosure.add_encl {acc} hcb{k+1}")
        acc = fname
    out.append(f"  exact ⟨by linarith [{acc}.1], by linarith [{acc}.2]⟩")
    out.append(f"  -- float truth: {truth:.9f}; certified [{float(A_lo):.9f}, {float(A_hi):.9f}]")


def emit_offline_theorem(z: dict, u: F, uname: str, out: list) -> None:
    """dh_offline_term_box_{uname}: for the off-line +gamma pair {rho, 1-conj rho}
    the diffraction term 2*cosh(delta*u)*cos(gamma*u) is certified-enclosed, and
    the DISTINCTIVE off-line signature cosh(delta*u) > 1 is exhibited explicitly."""
    beta = (F(z["re"][0]) + F(z["re"][1])) / 2
    gamma = (F(z["im"][0]) + F(z["im"][1])) / 2
    beta_lo, beta_hi = F(z["re"][0]), F(z["re"][1])
    gam_lo, gam_hi = F(z["im"][0]), F(z["im"][1])
    delta = beta - F(1, 2)
    dxu = delta * u
    chlo, chhi, _cc, _r = cosh_bracket_interval(dxu)
    # cos(gamma*u): enclose at midpoint then absorb the gamma-bracket half width via Lipschitz
    theta = gamma * u
    w = _rup((gam_hi - gam_lo) * u)
    clo0, chi0, _b, _s = cos_chain(theta)
    clo = clo0 - w
    chi = chi0 + w
    # term = 2*cosh*cos. product-interval bounds (cosh>0):
    prod_lo = 2 * min(chlo * clo, chlo * chi, chhi * clo, chhi * chi)
    prod_hi = 2 * max(chlo * clo, chlo * chi, chhi * clo, chhi * chi)
    prod_lo = _rdown(prod_lo)
    prod_hi = _rup(prod_hi)
    out.append("")
    out.append(f"/-! ### Off-line DH pair contribution at {uname} -/")
    out.append("")
    out.append(f"/-- **Certified off-line DH diffraction term at {uname}.**  For the certified off-line")
    out.append(f"    DH zero `rho = beta + i·gamma` (gamma ~ {float(gamma):.3f}, beta ~ {float(beta):.3f}, so the")
    out.append(f"    defect `delta = beta - 1/2 ~ {float(delta):.3f} != 0`), the symmetric +gamma pair of the")
    out.append(f"    zero quartet contributes `2·cosh(delta·{uname})·cos(gamma·{uname})` to the diffraction.")
    out.append(f"    Given `delta ∈ [{float(delta-(F(1,2)-(beta_hi-beta_lo)/2)):.4f}...]` and `gamma` in their certified brackets")
    out.append(f"    (Arb inventory inputs), the term is enclosed AND the cosh factor is certified `> 1`:")
    out.append(f"    the DISTINCTIVE off-line signature (an on-line zero has delta=0, cosh=1).")
    out.append(f"    conjecture1_proved = False. -/")
    out.append(f"theorem dh_offline_term_box_{uname}")
    out.append(f"    (d g : ℝ) (hd : d = {_q(delta)}) (hg : {_q(gam_lo)} ≤ g ∧ g ≤ {_q(gam_hi)})")
    out.append(f"    : (1 : ℝ) < Real.cosh (d * {uname}) ∧")
    out.append(f"      {_q(prod_lo)} ≤ 2 * Real.cosh (d * {uname}) * Real.cos (g * {uname}) ∧")
    out.append(f"      2 * Real.cosh (d * {uname}) * Real.cos (g * {uname}) ≤ {_q(prod_hi)} := by")
    # cosh factor
    out.append(f"  subst hd")
    out.append(f"  have hdxu : (({_q(delta)} : ℝ) * {uname}) = {_q(dxu)} := by rw [{uname}]; norm_num")
    out.append(f"  rw [hdxu]")
    out.append(f"  have hcoshabs : |({_q(dxu)} : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num")
    out.append(f"  have hcoshb := cosh_bracket hcoshabs")
    out.append(f"  have hcoshlo : {_q(chlo)} ≤ Real.cosh ({_q(dxu)}) := by")
    out.append(f"    have h2 := abs_le.mp hcoshb; nlinarith [h2.1, h2.2]")
    out.append(f"  have hcoshhi : Real.cosh ({_q(dxu)}) ≤ {_q(chhi)} := by")
    out.append(f"    have h2 := abs_le.mp hcoshb; nlinarith [h2.1, h2.2]")
    out.append(f"  have hcoshgt1 : (1 : ℝ) < Real.cosh ({_q(dxu)}) := by linarith [hcoshlo]")
    # cos(g*u) box via the chain + Lipschitz
    hcos, cc_lo, cc_hi = emit_cos_chain(theta, f"{uname}off", out)
    out.append(f"  have hdist : |g * {uname} - {_q(theta)}| ≤ {_q(w)} := by")
    out.append(f"    have hcu : ({_q(theta)} : ℝ) = {_q(gamma)} * {uname} := by rw [{uname}]; norm_num")
    out.append(f"    rw [hcu, ← sub_mul, abs_mul, abs_of_nonneg (by rw [{uname}]; norm_num : (0:ℝ) ≤ {uname})]")
    out.append(f"    have hrc : |g - {_q(gamma)}| ≤ {_q(gam_hi - gam_lo)} := by")
    out.append(f"      rw [abs_le]; constructor <;> [linarith [hg.1, hg.2]; linarith [hg.1, hg.2]]")
    out.append(f"    calc |g - {_q(gamma)}| * {uname} ≤ {_q(gam_hi - gam_lo)} * {uname} := by")
    out.append(f"            apply mul_le_mul_of_nonneg_right hrc (by rw [{uname}]; norm_num)")
    out.append(f"      _ ≤ {_q(w)} := by rw [{uname}]; norm_num")
    out.append(f"  have hcosbox := CosEnclosure.cos_encl_bracket (arg := g * {uname}) (c := {_q(theta)}) "
               f"(w := {_q(w)}) (by norm_num) hdist {hcos}.1 {hcos}.2")
    out.append(f"  have hcoslo : {_q(clo)} ≤ Real.cos (g * {uname}) := by linarith [hcosbox.1]")
    out.append(f"  have hcoshi : Real.cos (g * {uname}) ≤ {_q(chi)} := by linarith [hcosbox.2]")
    out.append(f"  refine ⟨hcoshgt1, ?_, ?_⟩")
    out.append(f"  · nlinarith [hcoshlo, hcoshhi, hcoslo, hcoshi, hcoshgt1]")
    out.append(f"  · nlinarith [hcoshlo, hcoshhi, hcoslo, hcoshi, hcoshgt1]")


COSH_LEMMA = '''
/-! ### Local order-6 cosh bracket (self-contained; exp Taylor remainder) -/

/-- `|cosh x - (1 + x²/2 + x⁴/24)| ≤ |x|⁶·(7/4320)` for `|x| ≤ 1`, from Mathlib's
    order-6 `Real.exp_bound` at `x` and `-x` (odd terms cancel).  A tiny local
    `exp` bracket for the ONE small rational argument the off-line cosh factor
    needs, so no cross-island `TaylorKernels` import is required. -/
theorem cosh_bracket {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cosh x - (1 + x^2/2 + x^4/24)| ≤ |x|^6 * (7 / 4320) := by
  have hxn : |(-x)| ≤ 1 := by rwa [abs_neg]
  have hp := Real.exp_bound hx (n := 6) (by norm_num)
  have hm := Real.exp_bound hxn (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hp hm
  have hpn : |Real.exp x - (1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120)| ≤ |x|^6 * (7 / (720*6)) := by
    convert hp using 2 <;> norm_num [Nat.factorial]
  have hmn : |Real.exp (-x) - (1 + (-x) + (-x)^2/2 + (-x)^3/6 + (-x)^4/24 + (-x)^5/120)| ≤ |x|^6 * (7 / (720*6)) := by
    have := Real.exp_bound (x := -x) hxn (n := 6) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
    rw [show |(-x)|^6 = |x|^6 by rw [abs_neg]] at this
    convert this using 2 <;> norm_num [Nat.factorial]
  have habs : |x|^6 = x^6 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have expand : Real.cosh x - (1 + x^2/2 + x^4/24)
      = ((Real.exp x - (1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120))
         + (Real.exp (-x) - (1 + (-x) + (-x)^2/2 + (-x)^3/6 + (-x)^4/24 + (-x)^5/120)))/2 := by
    rw [Real.cosh_eq]; ring
  rw [expand]
  calc |((Real.exp x - (1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120))
         + (Real.exp (-x) - (1 + (-x) + (-x)^2/2 + (-x)^3/6 + (-x)^4/24 + (-x)^5/120)))/2|
      ≤ (|Real.exp x - (1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120)|
         + |Real.exp (-x) - (1 + (-x) + (-x)^2/2 + (-x)^3/6 + (-x)^4/24 + (-x)^5/120)|)/2 := by
        rw [abs_div]; simp only [abs_two]
        apply div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ (x^6 * (7/(720*6)) + x^6 * (7/(720*6)))/2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        rw [← habs]; exact add_le_add hpn hmn
    _ = |x|^6 * (7/4320) := by rw [habs]; ring
'''


def emit(data: dict) -> str:
    online = data["online"]
    offline = data["offline"]
    out: list[str] = []
    out.append("/-  ZooDH.lean -- certified Davenport-Heilbronn diffraction (MIRRORMERE QC-B1).")
    out.append("")
    out.append("    The DH analogue of BraggH100: the finite-volume diffraction amplitude of the")
    out.append("    Davenport-Heilbronn zero comb at two rational frequencies")
    out.append("")
    out.append(f"        u2 = {U2.numerator}/{U2.denominator} (~= log 2, BraggH100's frequency)")
    out.append(f"        u5 = {U5.numerator}/{U5.denominator} (~= log 5, natural for a period-5 object)")
    out.append("")
    out.append("    DH is the classic RH counterexample class: a Dirichlet series with a Riemann-type")
    out.append("    functional equation but NO Euler product, hence zeros OFF the critical line.  This")
    out.append("    file certifies BOTH parts of its diffraction:")
    out.append("")
    out.append(f"      * dh_diffraction_online_box_u{{2,5}} -- the ON-line ordinate sum sum cos(gamma_k·u)")
    out.append(f"        over the {len(online)} on-line DH zeros with 0 < gamma_k <= {T_HEIGHT} (winding-certified,")
    out.append("        dh_zeros.json), each cos enclosed by the CosEnclosure double-angle chain +")
    out.append("        Lipschitz bracket absorption.  DIRECT analogue of bragg_amplitude_h100.")
    out.append("")
    out.append("      * dh_offline_term_box_u{2,5} -- the OFF-line pair's contribution")
    out.append("        2·cosh(delta·u)·cos(gamma·u), delta = beta - 1/2 != 0, for the certified")
    out.append("        off-line zero.  The cosh(delta·u) > 1 factor is the DISTINCTIVE off-line")
    out.append("        signature (an on-line zero has delta = 0 => cosh = 1 => a plain cos term).")
    out.append("        cosh enclosed by the local order-6 cosh_bracket (exp Taylor remainder).")
    out.append("")
    out.append("    TRUST.  Bracket-membership / delta-value hypotheses carry the Arb inventory trust")
    out.append("    (dh_zeros.json winding certificates + Re-D sign bisection), same class as BraggH100's")
    out.append("    hLine.  Everything downstream is kernel-checked (no sorry).  conjecture1_proved = False.")
    out.append("-/")
    out.append("import Mathlib")
    out.append("import CosEnclosure")
    out.append("")
    out.append("open Real")
    out.append("")
    out.append("namespace ZooDH")
    out.append("")
    out.append("set_option maxHeartbeats 4000000")
    out.append("")
    out.append(f"/-- u2 = {U2.numerator}/{U2.denominator} ~= log 2. -/")
    out.append(f"noncomputable def u2 : ℝ := {_q(U2)}")
    out.append(f"/-- u5 = {U5.numerator}/{U5.denominator} ~= log 5. -/")
    out.append(f"noncomputable def u5 : ℝ := {_q(U5)}")
    out.append(COSH_LEMMA)

    # per-zero online cos-box lemmas + assembly, per frequency
    for u, uname in ((U2, "u2"), (U5, "u5")):
        out.append("")
        out.append(f"/-! ### Per-ordinate on-line cos boxes at {uname} -/")
        boxes = []
        for z in online:
            name, blo, bhi = emit_online_cosbox(z, u, uname, out)
            boxes.append((name, blo, bhi))
        emit_online_theorem(online, u, uname, boxes, out)

    # off-line term theorems, per frequency
    for u, uname in ((U2, "u2"), (U5, "u5")):
        for z in offline:
            emit_offline_theorem(z, u, uname, out)

    out.append("")
    out.append("end ZooDH")
    return "\n".join(out) + "\n"


def write_lean():
    data = build()
    src = emit(data)
    path = _HERE.parent / "zeta_zero_localization" / "lean" / "ZooDH.lean"
    path.write_text(src)
    print(f"wrote {path} ({len(src.splitlines())} lines)")
    return data


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", action="store_true", help="write ZooDH.lean")
    args = ap.parse_args()
    if args.emit:
        write_lean()
    else:
        summary()
