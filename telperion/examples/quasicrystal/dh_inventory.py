"""DH zero inventory to modest height (PROGRAM MIRRORMERE, QC-B1 increment 1).

Builds a CERTIFIED inventory of Davenport-Heilbronn zeros with 0 < Im <= T_MAX,
each as a winding-1 box (Arb-trust-class argument-principle count) via
`telperion.arb_dh.winding_number_rigorous`, and PROVES it complete to T_MAX.
Emits `zoo_data/dh_zeros.json`:

    {
      "t_max": 300, "method": ..., "trust": "...; NOT kernel",
      "conjecture1_proved": false,
      "zeros": [ {"idx","re":[lo,hi],"im":[lo,hi],"on_line":bool,"winding":1,
                  "gamma_approx","beta_approx","prec","recheck_prec","n_per_side",
                  "source"} , ... ],
      "on_line_count", "off_line_count", "total_count",
      "off_line_scan": {...}, "completeness": {...}
    }

METHOD.
  * COUNTS.  Every winding integer comes from the segment-enclosure argument
    principle of `telperion.arb_winding` (D and D' enclosed on every boundary
    segment), computed twice (prec 96 with 8 initial segments per side, prec 144
    with 13); both must agree.  Arb trust class, not kernel.
  * ON-LINE zeros: D has real coefficients, so D(s-bar) = conj D(s), and the FE
    gives rho -> 1 - rho; together rho -> 1 - conj(rho), a reflection in Re = 1/2
    at the same height.  We scan |D(1/2 + i t)| on a fine grid, take local minima
    below a magnitude floor, and certify each with a box symmetric about Re = 1/2.
    Winding = 1 in such a box puts the zero ON the line: an off-line zero there
    would bring its reflection into the same box, giving winding >= 2.
  * OFF-LINE zeros, literature-seeded: the published off-line DH zeros
    (Balanzario-Sanchez-Ortiz 2007; Franca-LeClair Table IX) seed boxes strictly
    right of Re = 1/2, certified by winding 1, trusting our integer over the
    literature decimals (per the scout's gotcha 2).
  * OFF-LINE SCAN (`scan_offline`): Re >= 2 is zero-free by the dominant-term
    bound (`arb_dh.dh_right_halfplane_nonvanishing`).  The strip
    [51/100, 2] x [1/20, T_MAX] is counted rigorously in height-10 slices; a
    slice with more zeros than certified off-line boxes is bisected to find the
    missing zero, which is then certified like the seeded ones.
  * COMPLETENESS (`completeness_check`): the rigorous total over
    [-1, 2] x [1/20, T_MAX] must equal on_line + 2 * off_line.  Re <= -1 holds
    only the real trivial zeros (FE mirror of the dominant-term bound), and
    0 < Im < 1/20 holds no zero (a conjugation-symmetric low box has winding 1:
    just the trivial zero s = -1).  The listed boxes are pairwise disjoint, lie in
    that rectangle, and hold one zero each; every off-line zero rho (all right
    of Re = 1/2) has the reflection 1 - conj(rho) in no listed box.  So the
    equality leaves no room for an unlisted zero.

HISTORY.  The first issue of this file (commit 5f7cf159c) counted with the
node-sampling `arb_dh.winding_number`, now `winding_number_sampled_heuristic`:
its ball values were rigorous but its COUNT WAS A HEURISTIC, and its docstring
called it rigorous.  It also promised an off-line SCAN that had no code, and it
missed the off-line zero rho ~ 0.86953 + 240.40467i (found by an independent AI
audit, 2026-10-14).  The 2026-10-14 re-issue re-certifies every
box rigorously (all 208 old brackets unchanged), adds that fifth off-line zero
from the scan, and adds the completeness check.  conjecture1_proved = False.
"""
from __future__ import annotations

import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent.parent / "src"))

from telperion.arb_dh import (  # noqa: E402
    certify_offline_zero, dh_analytic, dh_eval, dh_right_halfplane_nonvanishing, winding_number_rigorous,
)
from telperion.arb_winding import METHOD, _cut, count_strips, localise_zero  # noqa: E402

T_MAX = 300
SCAN_PREC = 96          # cheap scan precision (|D| on the line; locating only)
CERT_PREC = 96          # certification precision (rigorous winding); recheck at 1.5x
IM_FLOOR = F(1, 20)     # bottom of the counted region (0 < Im < 1/20 is checked zero-free separately)
OFFLINE_RE0 = F(51, 100)
OFFLINE_RE1 = F(2)      # Re >= 2 is zero-free by the dominant term
STRIP = 10              # height of the scan / completeness slices

# Independent localisations of scan-found zeros, re-certified here as given.  An independent AI audit
# (2026-10-14) localised the zero the literature seed missed to this box.  rho sits only ~8.5e-6 above the box's lower Im edge, so it is checked to lie strictly
# inside every box recorded for it.
AUDIT_BOXES = [
    {"re": ["35610821/40960000", "1782031077/2048000000"],
     "im": ["19693950062217/81920000000", "2461750006093/10240000000"],
     "source": "independent AI audit, 2026-10-14"},
]
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


def _winding_twice(re0: F, re1: F, im0: F, im1: F, prec: int) -> int:
    """Rigorous winding at ``prec`` (8 initial segments per side) and at 1.5x
    ``prec`` (13 per side); RuntimeError unless both runs give the same integer."""
    w1 = winding_number_rigorous(re0, re1, im0, im1, prec=prec, init_per_side=8)
    w2 = winding_number_rigorous(re0, re1, im0, im1, prec=prec + prec // 2,
                                 init_per_side=13)
    if w1 != w2:
        raise RuntimeError(f"winding {w1} vs recheck {w2} on [{re0},{re1}]x[{im0},{im1}]")
    return w1


def certify_box(re0: F, re1: F, im0: F, im1: F, expect_online: bool) -> dict | None:
    """Try to certify winding=1 in the box (rigorous segment method, escalating
    precision on refusal).  Returns a zero record dict, or None if the box holds
    no zero."""
    for prec in (CERT_PREC, 2 * CERT_PREC):
        try:
            w = _winding_twice(re0, re1, im0, im1, prec)
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
                "recheck_prec": prec + prec // 2,
                "n_per_side": 8,
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


# Off-line DH zeros with 0 < Im <= 300 (gamma, beta), SEEDED from the literature
# (Balanzario-Sanchez-Ortiz Math.Comp. 76 2007 / Franca-LeClair Table IX / Spira
# 1994) with the seed beta checked by our own winding count -- per the scout
# gotcha "trust the winding integer, not the literature decimals."
#   * gamma~166.5: the true zero is near beta~0.60, NOT the literature 0.785
#     (a box around 0.785 has rigorous winding 0 -- a bad decimal).
#   * gamma~243.1 ("beta~0.718 off-line" in some tables): there is no off-line
#     zero near gamma~243.1; the nearest zero there is ON the line near 243.6.
#     But the off-line SCAN finds an off-line zero rho ~ 0.86953 + 240.40467i that
#     this literature list never had.  The tabulated 243.1 entry MAY be a garbled
#     version of that zero; that is UNVERIFIED.
# This list is only a seed: completeness comes from scan_offline and
# completeness_check, not from the literature.
KNOWN_OFFLINE = [
    (85.699348, 0.808517),
    (114.163331, 0.650830),
    (166.500000, 0.600000),
    (176.702461, 0.741732),
]


def _box(z: dict) -> tuple[F, F, F, F]:
    return F(z["re"][0]), F(z["re"][1]), F(z["im"][0]), F(z["im"][1])


def _inside(z: dict, re0: F, re1: F, im0: F, im1: F) -> bool:
    return _contains((re0, re1, im0, im1), _box(z))


def _contains(outer: tuple, inner: tuple) -> bool:
    return outer[0] <= inner[0] and inner[1] <= outer[1] and outer[2] <= inner[2] and inner[3] <= outer[3]


def _overlap(a: tuple, b: tuple) -> bool:
    return a[0] < b[1] and b[0] < a[1] and a[2] < b[3] and b[2] < a[3]


def scan_offline(off: list[dict], log=print) -> tuple[list[dict], dict]:
    """Rigorous off-line census of [OFFLINE_RE0, OFFLINE_RE1] x [IM_FLOOR, T_MAX].

    Counts every height-STRIP slice rigorously and compares it with the
    certified off-line boxes ``off`` lying in that slice.  A slice with more
    zeros is searched: its zeros are isolated by bisection, those not inside a
    known box are localised and certified with an inventory-style box.  Returns
    (new records, scan summary)."""
    dom = dh_right_halfplane_nonvanishing(OFFLINE_RE1)
    if not dom["certified"]:
        raise RuntimeError(f"dominant-term bound failed at Re = {OFFLINE_RE1}")
    cuts = list(range(STRIP, T_MAX, STRIP))
    census = count_strips(dh_analytic(), OFFLINE_RE0, OFFLINE_RE1, IM_FLOOR, T_MAX,
                          cuts=cuts, prec=CERT_PREC)
    found: list[dict] = []
    for st in census["strips"]:
        a, b = F(st["im0"]), F(st["im1"])
        known = [z for z in off + found if _inside(z, OFFLINE_RE0, OFFLINE_RE1, a, b)]
        if st["winding"] == len(known):
            continue
        if st["winding"] < len(known):
            raise RuntimeError(f"off-line slice [{a},{b}] counts {st['winding']} < {len(known)} certified boxes")
        log(f"  scan: slice Im [{float(a)},{float(b)}] has {st['winding']} off-line zero(s), "
            f"{len(known)} known -- searching")
        for iso in _isolate(OFFLINE_RE0, OFFLINE_RE1, a, b, st["winding"]):
            # a known box inside this one-zero box: its zero IS the known one
            if any(_contains(iso, _box(z)) for z in known):
                continue
            tight = tuple(localise_zero(dh_analytic(), *iso, width=F(1, 1000), prec=CERT_PREC))
            if any(_contains(_box(z), tight) for z in known):
                continue
            if any(_overlap(_box(z), tight) for z in known):
                raise RuntimeError(f"scan: localised box {tight} overlaps a known box partially")
            g = float((tight[2] + tight[3]) / 2)
            bt = float((tight[0] + tight[1]) / 2)
            rec = certify_offline(g, bt)
            if rec is None:
                raise RuntimeError(f"scan found an off-line zero near {bt} + {g}i but could not box it")
            if not _contains(_box(rec), tight):   # the winding-1 box must hold THIS zero
                raise RuntimeError(f"scan: inventory box {rec['re']}x{rec['im']} misses the localised zero")
            rec["source"] = "off-line scan (2026-10-14)"
            rec["localised_box"] = {"re": [str(tight[0]), str(tight[1])], "im": [str(tight[2]), str(tight[3])]}
            za = _zero_approx(tight)
            pt = za.pop("_exact")
            if not _strictly_inside(pt, _box(rec)):
                raise RuntimeError(f"scan: zero {pt} not strictly inside the inventory box")
            rec["zero_approx"] = za
            rec["beta"] = _decimal(pt[0], 10)    # the zero itself (10 digits); the box is the certificate
            rec["gamma"] = _decimal(pt[1], 10)
            rec["beta_gamma_kind"] = ("float estimate (mpmath findroot, dps 30), NOT certified digits; "
                                      "certified only to the boxes")
            for ab in AUDIT_BOXES:
                abox = _box(ab)
                if not _strictly_inside(pt, abox):
                    continue
                cert = certify_offline_zero(*abox)   # rigorous, prec 96 + recheck 144
                rec["audit_box"] = {"re": ab["re"], "im": ab["im"], "source": ab["source"],
                                    "winding": cert["winding"], "method": cert["method"],
                                    "prec": cert["prec"], "recheck_prec": cert["recheck_prec"]}
            log(f"  scan: NEW off-line zero rho ~ {za['beta']} + {za['gamma']}i, "
                f"box Re {rec['re']} Im {rec['im']}")
            found.append(rec)
    summary = {
        "region": {"re0": str(OFFLINE_RE0), "re1": str(OFFLINE_RE1), "im0": str(IM_FLOOR), "im1": str(T_MAX)},
        "right_of_re1_zero_free": {"sigma": dom["sigma"], "tail_upper_float": dom["tail_upper_float"],
                                   "claim": dom["claim"]},
        "strips": [{"im0": s_["im0"], "im1": s_["im1"], "winding": s_["winding"]} for s_ in census["strips"]],
        "total": census["total"],
        "method": METHOD,
        "prec": CERT_PREC,
    }
    return found, summary


def _zero_approx(tight: tuple) -> dict:
    """The zero itself, by mpmath findroot (dps 30) seeded at the centre of the rigorous winding-1 box
    ``tight`` (a FLOAT locator, not a certificate: the box is the certificate).  Refuses unless the root
    lies strictly inside ``tight`` and |D| there is tiny."""
    import mpmath as mp
    with mp.workdps(30):
        k = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)

        def D(s):
            z = [mp.zeta(s, mp.mpf(a) / 5) for a in (1, 2, 3, 4)]
            return 5 ** (-s) * (z[0] - z[3] + k * (z[1] - z[2]))
        c = mp.mpc(float((tight[0] + tight[1]) / 2), float((tight[2] + tight[3]) / 2))
        r = mp.findroot(D, c)
        res = abs(D(r))
        beta, gamma = F(mp.nstr(r.real, 25)), F(mp.nstr(r.imag, 25))
    if not (tight[0] < beta < tight[1] and tight[2] < gamma < tight[3]) or res > 1e-20:
        raise RuntimeError(f"zero_approx: findroot left the certified box or |D| = {res}")
    return {"beta": mp.nstr(r.real, 12), "gamma": mp.nstr(r.imag, 14), "abs_D": mp.nstr(res, 3),
            "how": "mpmath findroot at dps 30 (float locator; lies strictly inside every recorded box)",
            "_exact": (beta, gamma)}


def _decimal(x: F, digits: int) -> str:
    """x rounded to ``digits`` decimals, as an exact decimal string."""
    n = round(x * 10 ** digits)
    sign, n = ("-" if n < 0 else ""), abs(n)
    return f"{sign}{n // 10 ** digits}.{n % 10 ** digits:0{digits}d}"


def _strictly_inside(pt: tuple, box: tuple) -> bool:
    return box[0] < pt[0] < box[1] and box[2] < pt[1] < box[3]


def _isolate(re0: F, re1: F, im0: F, im1: F, count: int, depth: int = 0) -> list[tuple]:
    """Split [re0,re1] x [im0,im1] (holding ``count`` zeros) into boxes holding one
    zero each, by rigorous counts of halves (cuts nudged off the dyadic grid)."""
    if count == 0:
        return []
    if count == 1:
        return [(re0, re1, im0, im1)]
    if depth > 40:
        raise RuntimeError("isolate: could not separate zeros")
    if re1 - re0 >= im1 - im0:
        m = _cut(re0, re1, F(1, 10**7))
        halves = [(re0, m, im0, im1), (m, re1, im0, im1)]
    else:
        m = _cut(im0, im1, F(1, 10**7))
        halves = [(re0, re1, im0, m), (re0, re1, m, im1)]
    w0 = winding_number_rigorous(*halves[0], prec=CERT_PREC)
    return (_isolate(*halves[0], w0, depth + 1)
            + _isolate(*halves[1], count - w0, depth + 1))


def _disjoint(boxes: list[tuple]) -> bool:
    bs = sorted(boxes, key=lambda b: b[2])
    for i, a in enumerate(bs):
        for b in bs[i + 1:]:
            if b[2] >= a[3]:
                break
            if _overlap(a, b):
                return False
    return True


def completeness_check(zeros: list[dict]) -> dict:
    """Prove the inventory complete to T_MAX: rigorous total over
    [-1, 2] x [IM_FLOOR, T_MAX] == on_line + 2 * off_line (see the module doc)."""
    on = [z for z in zeros if z["on_line"]]
    off = [z for z in zeros if not z["on_line"]]
    half = F(1, 2)
    boxes = [_box(z) for z in zeros]
    region = (F(-1), F(2), IM_FLOOR, F(T_MAX))
    if not all(_inside(z, *region) for z in zeros):
        raise RuntimeError("completeness: a listed box leaves the counted region")
    if not _disjoint(boxes):
        raise RuntimeError("completeness: listed boxes overlap")
    if not all(_box(z)[0] + _box(z)[1] == 1 for z in on):
        raise RuntimeError("completeness: an on-line box is not symmetric about Re = 1/2")
    if not all(_box(z)[0] > half for z in off):
        raise RuntimeError("completeness: an off-line box is not strictly right of Re = 1/2")
    total = count_strips(dh_analytic(), region[0], region[1], region[2], region[3],
                         cuts=list(range(STRIP, T_MAX, STRIP)), prec=CERT_PREC)
    expected = len(on) + 2 * len(off)
    ok = total["total"] == expected
    if not ok:
        raise RuntimeError(f"completeness FAILED: total {total['total']} != {len(on)} + 2*{len(off)}")
    # Below IM_FLOOR: the conjugation-symmetric box LOW holds exactly the trivial zero s = -1, so no
    # non-real zero (those come in conjugate pairs) has 0 < |Im| < IM_FLOOR.
    low = (F(-101, 100), F(2), -IM_FLOOR, IM_FLOOR)
    w_low = _winding_twice(*low, CERT_PREC)
    if w_low != 1:
        raise RuntimeError(f"completeness: low box {low} has winding {w_low}, expected 1 (the zero s = -1)")
    return {
        "region": {"re0": "-1", "re1": "2", "im0": str(IM_FLOOR), "im1": str(T_MAX)},
        "total_winding": total["total"],
        "on_line": len(on),
        "off_line": len(off),
        "equation": f"{total['total']} = {len(on)} + 2*{len(off)}",
        "low_box": {"re0": str(low[0]), "re1": str(low[1]), "im0": str(low[2]), "im1": str(low[3]),
                    "winding": w_low, "meaning": "only the trivial zero s = -1: no zero with 0 < Im < 1/20"},
        "complete": ok,
        "claim": f"the listed zeros are ALL zeros of D with 0 < Im <= {T_MAX}",
        "argument": ("Re >= 2 zero-free (dominant term); Re <= -1 only real trivial zeros (FE mirror); "
                     "0 < Im < 1/20 zero-free (low box); listed boxes disjoint, inside the region, "
                     "winding 1 each; on-line boxes symmetric about Re = 1/2; each off-line zero rho "
                     "(Re > 1/2) has the reflection 1 - conj(rho) in no listed box.  So total = on + 2*off "
                     "leaves no unlisted zero."),
        "method": METHOD,
        "prec": CERT_PREC,
    }


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
    off_recs: list[dict] = []
    for gamma, beta in KNOWN_OFFLINE:
        if gamma > T_MAX:
            continue
        rec = certify_offline(gamma, beta)
        if rec is not None:
            rec["source"] = "literature seed"
            off_recs.append(rec)
            off_certified.append({"gamma": gamma, "beta": beta, "certified": True,
                                  "source": "literature seed"})
        else:
            off_certified.append({"gamma": gamma, "beta": beta, "certified": False,
                                  "source": "literature seed"})
    # --- off-line SCAN (finds what the literature seed missed) ---
    new_off, scan = scan_offline(off_recs)
    for rec in new_off:
        off_certified.append({"gamma": rec["gamma_approx"], "beta": rec["beta_approx"],
                              "certified": True, "source": rec["source"]})
    for rec in off_recs + new_off:
        rec.setdefault("source", "literature seed")
    zeros.extend(off_recs + new_off)
    for z in zeros:
        z.setdefault("source", "on-line scan")
    # sort by gamma
    zeros.sort(key=lambda z: z["gamma_approx"])
    for i, z in enumerate(zeros):
        z["idx"] = i + 1
    on = [z for z in zeros if z["on_line"]]
    off = [z for z in zeros if not z["on_line"]]
    n_model = (T_MAX / (2 * math.pi)) * math.log(5 * T_MAX / (2 * math.pi)) \
        - T_MAX / (2 * math.pi)
    completeness = completeness_check(zeros)
    return {
        "t_max": T_MAX,
        "scan_prec": SCAN_PREC,
        "cert_prec": CERT_PREC,
        "method": METHOD,
        "trust": "arb-interval (segment-enclosure argument principle); NOT kernel",
        "issued": ("2026-10-14 re-issue: every count by the rigorous segment method; supersedes the "
                   "node-sampling issue of commit 5f7cf159c (heuristic counts, 4 off-line zeros, "
                   "incomplete)"),
        "conjecture1_proved": False,
        "on_line_count": len(on),
        "off_line_count": len(off),
        "total_count": len(zeros),
        "density_model_N_T": round(n_model, 1),
        "density_model_formula": "(T/2pi)log(5T/2pi) - T/2pi (DH conductor-5 RvM count)",
        "off_line_attempts": off_certified,
        "off_line_scan": scan,
        "completeness": completeness,
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
    print("  off-line census (gamma, beta, certified, source):")
    for a in data["off_line_attempts"]:
        print(f"    gamma={a['gamma']:.4f} beta={a['beta']:.4f} certified={a['certified']} ({a['source']})")
    print(f"  completeness: {data['completeness']['equation']} -> {data['completeness']['complete']}")
    return data


if __name__ == "__main__":
    main()
