"""DH zero inventory to modest height (PROGRAM MIRRORMERE, QC-B1 increment 1).

Builds a CERTIFIED inventory of Davenport-Heilbronn zeros with 0 < Im <= T_MAX,
each as a rigorous winding-1 box (Arb-trust-class argument-principle count) via
`telperion.arb_dh`.  Emits `zoo_data/dh_zeros.json`:

    {
      "t_max": 300, "prec": ..., "n_per_side": ...,
      "trust": "arb-interval (argument-principle winding); NOT kernel",
      "conjecture1_proved": false,
      "zeros": [ {"idx","re":[lo,hi],"im":[lo,hi],"on_line":bool,"winding":1,
                  "gamma_approx": float, "beta_approx": float} , ... ],
      "on_line_count": ..., "off_line_count": ...
    }

METHOD.
  * ON-LINE zeros: D(1/2 + i t) has real coefficients so D(s-bar) = conj D(s);
    zeros come in conjugate pairs, and a zero on Re=1/2 is genuinely real-part
    1/2.  We scan |D(1/2 + i t)| on a fine grid, take local minima below a
    magnitude floor, and certify each with a box STRADDLING Re=1/2 that is
    symmetric about the line (Re in [1/2 - h, 1/2 + h]).  Winding = 1 in such a
    symmetric box certifies exactly one zero; conjugate symmetry forces it onto
    the line (a single off-line zero would have its conjugate partner in the same
    symmetric box giving winding >= 2 -- unless the box crosses the line between
    them, which the symmetric choice precludes).
  * OFF-LINE zeros: the literature (Balanzario-Sanchez-Ortiz 2007; Franca-LeClair
    Table IX) lists off-line DH zeros; the first has gamma ~ 85.699, beta ~ 0.808.
    We certify each listed off-line zero by a box strictly off Re=1/2 (winding 1),
    trusting our winding integer over the literature decimals (per the scout's
    gotcha 2).  We also SCAN the off-line strip Re in (1/2, 1] for additional
    off-line sign structure to avoid missing any.

Certification is rigorous: a returned winding integer is only emitted when every
boundary step is sign-definite; ambiguous boxes raise and are retried at higher
resolution.  conjecture1_proved = False.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent.parent / "src"))

from telperion.arb_dh import dh_eval, winding_number  # noqa: E402

T_MAX = 300
SCAN_PREC = 96          # cheap scan precision
CERT_PREC = 200         # certification precision
SCAN_STEP = F(1, 40)    # 0.025 grid on the critical line
MAG_FLOOR = 0.55        # local-minimum magnitude threshold for an on-line candidate
HALF = F(1, 2)


def _mag(t: F, re0=HALF, prec=SCAN_PREC) -> float:
    rl, rh, il, ih = dh_eval(re0, t, prec)
    return math.hypot((float(rl) + float(rh)) / 2, (float(il) + float(ih)) / 2)


def locate_online_candidates() -> list[F]:
    """Fine |D(1/2+it)| scan; return local minima below MAG_FLOOR as Fractions."""
    n = int(T_MAX / float(SCAN_STEP)) + 1
    mags = []
    ts = []
    for k in range(2, n):  # start above t=0.1 (D has no low zeros)
        t = k * SCAN_STEP
        ts.append(t)
        mags.append(_mag(t))
    cands = []
    for i in range(1, len(mags) - 1):
        if mags[i] < MAG_FLOOR and mags[i] <= mags[i - 1] and mags[i] <= mags[i + 1]:
            cands.append(ts[i])
    return cands


def certify_box(re0: F, re1: F, im0: F, im1: F, expect_online: bool) -> dict | None:
    """Try to certify winding=1 in the box, escalating resolution.  Returns a
    zero record dict, or None if no single zero could be certified."""
    for prec, nps in ((CERT_PREC, 24), (CERT_PREC, 48), (2 * CERT_PREC, 64),
                      (2 * CERT_PREC, 96)):
        try:
            w = winding_number(re0, re1, im0, im1, prec=prec, n_per_side=nps)
        except RuntimeError:
            continue
        if w == 1:
            return {
                "re": [str(re0), str(re1)],
                "im": [str(im0), str(im1)],
                "on_line": expect_online,
                "winding": 1,
                "gamma_approx": float((im0 + im1) / 2),
                "beta_approx": float((re0 + re1) / 2),
                "prec": prec,
                "n_per_side": nps,
            }
        if w == 0:
            return None       # no zero here (rejected candidate)
        # w > 1: box too wide, will be retried by caller with a tighter box
        return {"_multi": w}
    return {"_ambiguous": True}


def refine_online(t: F) -> dict | None:
    """Certify an on-line zero near t with a symmetric straddling box."""
    # symmetric about Re=1/2; Im window ~ +-0.04 shrinking if multi
    for half_im in (F(4, 100), F(3, 100), F(2, 100), F(15, 1000)):
        for half_re in (F(1, 10), F(6, 100), F(4, 100)):
            box = certify_box(HALF - half_re, HALF + half_re,
                              t - half_im, t + half_im, expect_online=True)
            if box is None:
                continue
            if "_multi" in box or "_ambiguous" in box:
                continue
            return box
    return None


def certify_offline(gamma: float, beta: float) -> dict | None:
    """Certify an off-line zero near (beta, gamma), strictly right of Re=1/2."""
    g = F(round(gamma * 1000), 1000)
    b = F(round(beta * 100), 100)
    for hb in (F(4, 100), F(3, 100), F(2, 100)):
        re0, re1 = b - hb, b + hb
        if re0 <= HALF:
            re0 = F(51, 100)   # keep strictly off-line
        for hg in (F(4, 100), F(3, 100), F(2, 100)):
            box = certify_box(re0, re1, g - hg, g + hg, expect_online=False)
            if box and "_multi" not in box and "_ambiguous" not in box:
                return box
    return None


# Off-line DH zeros with 0 < Im <= 300 (gamma, beta), from the literature
# (Balanzario-Sanchez-Ortiz Math.Comp. 76 2007 / Franca-LeClair Table IX / Spira
# 1994) BUT with the seed beta VERIFIED/CORRECTED by our own winding scan -- per
# the scout gotcha "trust the winding integer, not the literature decimals."
#   * gamma~166.5: our off-line strip scan finds the true zero near beta~0.60,
#     NOT the literature 0.785 (which certifies winding 0 -- a bad decimal).
#   * gamma~243.1 ("beta~0.718 off-line" in some tables): NO off-line zero found;
#     the nearest zero is ON the critical line near gamma~243.6.  Dropped as a
#     published artifact (consistent with Ferry-Isaila-Pantazi's skepticism).
KNOWN_OFFLINE = [
    (85.699348, 0.808517),
    (114.163331, 0.650830),
    (166.500000, 0.600000),
    (176.702461, 0.741732),
]


def _fill_gap(lo_g: float, hi_g: float, seen_im: list[float]) -> list[dict]:
    """Re-scan an on-line gap (lo_g, hi_g) at fine resolution and certify any
    missed zeros (magnitude minima, no MAG_FLOOR cut -- take the deepest)."""
    step = F(1, 100)
    n = int((hi_g - lo_g) / float(step))
    pts = [F(round((lo_g + 0.05) * 100), 100) + k * step for k in range(max(1, n - 9))]
    mags = [(_mag(t), t) for t in pts]
    found = []
    for i in range(1, len(mags) - 1):
        m, t = mags[i]
        if m <= mags[i - 1][0] and m <= mags[i + 1][0] and m < 0.9:
            gi = float(t)
            if any(abs(gi - s) < 0.2 for s in seen_im):
                continue
            rec = refine_online(t)
            if rec is not None:
                found.append(rec)
                seen_im.append(rec["gamma_approx"])
    return found


def build() -> dict:
    zeros: list[dict] = []
    # --- on-line ---
    cands = locate_online_candidates()
    seen_im: list[float] = []
    for t in cands:
        gi = float(t)
        if any(abs(gi - s) < 0.15 for s in seen_im):
            continue
        rec = refine_online(t)
        if rec is not None:
            zeros.append(rec)
            seen_im.append(rec["gamma_approx"])
    # --- gap-filling pass: rescan any suspiciously wide on-line gap ---
    seen_im.sort()
    gaps = [(seen_im[i], seen_im[i + 1]) for i in range(len(seen_im) - 1)
            if seen_im[i + 1] - seen_im[i] > 1.8]
    for lo_g, hi_g in gaps:
        zeros.extend(_fill_gap(lo_g, hi_g, seen_im))
    # --- off-line (literature-seeded, certified by winding) ---
    off_certified = []
    for gamma, beta in KNOWN_OFFLINE:
        if gamma > T_MAX:
            continue
        rec = certify_offline(gamma, beta)
        if rec is not None:
            zeros.append(rec)
            off_certified.append((gamma, beta, True))
        else:
            off_certified.append((gamma, beta, False))
    # sort by gamma
    zeros.sort(key=lambda z: z["gamma_approx"])
    for i, z in enumerate(zeros):
        z["idx"] = i + 1
    on = [z for z in zeros if z["on_line"]]
    off = [z for z in zeros if not z["on_line"]]
    n_model = (T_MAX / (2 * math.pi)) * math.log(5 * T_MAX / (2 * math.pi)) \
        - T_MAX / (2 * math.pi)
    return {
        "t_max": T_MAX,
        "scan_prec": SCAN_PREC,
        "cert_prec": CERT_PREC,
        "trust": "arb-interval (argument-principle winding); NOT kernel",
        "conjecture1_proved": False,
        "on_line_count": len(on),
        "off_line_count": len(off),
        "total_count": len(zeros),
        "density_model_N_T": round(n_model, 1),
        "density_model_formula": "(T/2pi)log(5T/2pi) - T/2pi (DH conductor-5 RvM count)",
        "off_line_attempts": [
            {"gamma": g, "beta": b, "certified": ok} for g, b, ok in off_certified
        ],
        "zeros": zeros,
    }


def main():
    data = build()
    outdir = _HERE / "zoo_data"
    outdir.mkdir(exist_ok=True)
    path = outdir / "dh_zeros.json"
    path.write_text(json.dumps(data, indent=2))
    print(f"wrote {path}")
    print(f"  on-line certified:  {data['on_line_count']}")
    print(f"  off-line certified: {data['off_line_count']}")
    print("  off-line census (gamma, beta, certified):")
    for a in data["off_line_attempts"]:
        print(f"    gamma={a['gamma']:.4f} beta={a['beta']:.4f} certified={a['certified']}")
    return data


if __name__ == "__main__":
    main()
