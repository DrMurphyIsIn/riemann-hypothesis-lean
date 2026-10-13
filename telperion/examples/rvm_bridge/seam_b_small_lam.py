#!/usr/bin/env python3
"""seam_b_small_lam.py -- numerics for the Wall's small-width seam (seam B, 2026-09-21).

The two-parameter Wall functional (zero side)

    F(c, lam) = Re sum_rho m(rho) (gamma_rho - c)^2 exp(-2 lam (gamma_rho - c)^2),
    gamma_rho = (rho - 1/2)/i,

equals, by the explicit formula for the Gaussian-derivative test phi(u) = K u e^{-u^2/(4 lam)} e^{-icu}
with f = phi * phi~ (E6Bridge5 autocorr),

    F(c, lam) = arch(c, lam) - prime(c, lam),

    f(u)          = A (1 - u^2/(4 lam)) exp(-u^2/(8 lam)) exp(-i c u),   A = 1/(8 sqrt(2 pi) lam^{3/2}),
    prime(c, lam) = sum_{n >= 2} Lambda(n) n^{-1/2} (f(log n) + f(-log n)),
    arch(c, lam)  = G(i/2) + G(-i/2) - f(0) log pi + (1/2pi) int B(r) Re psi(1/4 + i r/2) dr,
    G(z)          = (z - c)^2 exp(-2 lam (z - c)^2),   B(r) = G(r) = (r - c)^2 exp(-2 lam (r - c)^2).

This script tabulates arch, prime and F over a grid of centres c and widths lam through the prime
side (mpmath quadrature for the archimedean integral, the Lambda-sum cut at the Gaussian tail), and
cross-checks against the zero side using the first N zeros (mpmath.zetazero) plus a density tail
estimate for the mass of B beyond the last computed zero.  It also reports the c-uniform lower
bound of the paper analysis.  Nothing here proves anything; conjecture1_proved = False.

Usage:  PYTHONPATH=telperion/src python3 seam_b_small_lam.py [--zeros N] [--cache FILE]
"""
import argparse
import json
import math
import os
import sys
import tempfile
import time

import mpmath as mp

mp.mp.dps = 20


def A_of(lam):
    return 1 / (8 * mp.sqrt(2 * mp.pi) * lam ** mp.mpf(1.5))


def f_pair(u, c, lam):
    """f(u) + f(-u), real: 2 A (1 - u^2/(4 lam)) exp(-u^2/(8 lam)) cos(c u)."""
    return 2 * A_of(lam) * (1 - u * u / (4 * lam)) * mp.exp(-u * u / (8 * lam)) * mp.cos(c * u)


def von_mangoldt_table(N):
    """Lambda(n) for 2 <= n <= N by a sieve of smallest prime factors."""
    spf = list(range(N + 1))
    for i in range(2, int(N ** 0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
    lam_tab = {}
    for n in range(2, N + 1):
        p = spf[n]
        m = n
        while m % p == 0:
            m //= p
        if m == 1:
            lam_tab[n] = mp.log(p)
    return lam_tab


def prime_side(c, lam, table):
    """sum_{n>=2} Lambda(n)/sqrt(n) (f(log n) + f(-log n)); the Gaussian factor is
    exp(-(log n)^2/(8 lam)) so n beyond exp(sqrt(8 lam * 80)) contributes < e^{-80} relative."""
    total = mp.mpf(0)
    for n, L in table.items():
        u = mp.log(n)
        if u * u / (8 * lam) > 80:
            continue
        total += L / mp.sqrt(n) * f_pair(u, c, lam)
    return total


def prime_tail_estimate(c, lam, N):
    """Heuristic size of the prime sum beyond n = N: with Lambda(n) of mean 1 (PNT) the tail is
    ~ int_N^inf f_pair(log x) x^{-1/2} dx = int_{log N}^inf f_pair(u) e^{u/2} du, taken in absolute
    value of the integrand (no cancellation credited).  This is an ERROR BAR on the prime column,
    not a bound: for lam >= 0.5 and c near 0 it exceeds the true |F| (which is ~ 2 gamma_1^2
    exp(-2 lam gamma_1^2) ~ 0), so those rows read as 0 within the bar."""
    A = A_of(lam)
    return mp.quad(lambda u: 2 * A * abs(1 - u * u / (4 * lam)) * mp.exp(-u * u / (8 * lam)) * mp.exp(u / 2),
                   [mp.log(N), mp.log(N) + 20 * mp.sqrt(lam) + 5])


def G(z, c, lam):
    return (z - c) ** 2 * mp.exp(-2 * lam * (z - c) ** 2)


def arch_side(c, lam):
    A = A_of(lam)
    poles = 2 * mp.re(G(mp.mpc(0, 0.5), c, lam))
    log_pi_term = -A * mp.log(mp.pi)

    def integrand(r):
        return G(r, c, lam) * mp.re(mp.digamma(mp.mpc(0.25, r / 2)))

    w = 1 / mp.sqrt(2 * lam)          # bump width in r
    L = 7 * w                         # Gaussian tail e^{-49} beyond
    pts = sorted({c - L, c - 3 * w, c - w, c, c + w, c + 3 * w, c + L, mp.mpf(-5), mp.mpf(0), mp.mpf(5)})
    pts = [p for p in pts if c - L <= p <= c + L]
    integ = mp.quad(integrand, pts)
    return poles + log_pi_term + integ / (2 * mp.pi), poles, log_pi_term, integ / (2 * mp.pi)


def load_zeros(N, cache):
    zeros = []
    if cache and os.path.exists(cache):
        with open(cache) as fh:
            zeros = [mp.mpf(x) for x in json.load(fh)]
    if len(zeros) < N:
        t0 = time.time()
        for k in range(len(zeros) + 1, N + 1):
            zeros.append(mp.im(mp.zetazero(k)))
            if k % 100 == 0:
                print(f"  zero {k}: {zeros[-1]}  ({time.time() - t0:.0f}s)", file=sys.stderr)
                if cache:
                    with open(cache, "w") as fh:
                        json.dump([str(z) for z in zeros], fh)
        if cache:
            with open(cache, "w") as fh:
                json.dump([str(z) for z in zeros], fh)
    return zeros[:N]


def zero_side(c, lam, zeros):
    """Zero side with the first len(zeros) zeros (both conjugate pairs +-gamma, all simple, on the
    line as verified numerically) plus a smooth tail estimate: mass of B beyond gamma_N via the
    Riemann--von Mangoldt density (1/2pi) log(r/2pi) dr, and its mirror at -gamma_N."""
    s = mp.mpf(0)
    for g in zeros:
        s += G(g, c, lam) + G(-g, c, lam)
    T = zeros[-1]

    def dens(r):
        return G(r, c, lam) * mp.log(abs(r) / (2 * mp.pi)) / (2 * mp.pi)

    w = 1 / mp.sqrt(2 * lam)
    tail = mp.mpf(0)
    if c + 7 * w > T:
        tail += mp.quad(dens, [T, max(T, c + 7 * w)])
    if c - 7 * w < -T:
        tail += mp.quad(dens, [min(-T, c - 7 * w), -T])
    return mp.re(s), tail


def lower_bound_constants():
    """The c-uniform lower bound of the memo (threshold 2 on Re psi beyond R0 = 2 e^3):
    F/A >= (2 - log pi) - 4 e^{2 lam} sqrt(32 pi lam) - 32 e^{-(log 2)^2/(16 lam)}
           - 7 R0 * 8 sqrt(2 pi) sqrt(lam) / (2 pi).
    Returns the largest lam on a fine grid at which the bound is nonnegative."""
    R0 = mp.mpf(41)   # E6Bridge11.R₀: Re psi(1/4 + i r/2) >= 2 for |r| >= 41 (Stirling)

    def rhs(lam):
        return (2 - mp.log(mp.pi)) - 4 * mp.exp(2 * lam) * mp.sqrt(32 * mp.pi * lam) \
            - 64 * mp.exp(-(mp.log(2)) ** 2 / (16 * lam)) - 7 * R0 * 8 * mp.sqrt(2 * mp.pi) * mp.sqrt(lam) / (2 * mp.pi)

    lo, hi = mp.mpf('1e-12'), mp.mpf(1)
    for _ in range(80):
        mid = mp.sqrt(lo * hi)
        if rhs(mid) >= 0:
            lo = mid
        else:
            hi = mid
    return lo, rhs


def prime_abs(lam, table, N):
    """P_abs(lam) := 2 sum_{n>=2} Lambda(n) n^{-1/2} |1 - (log n)^2/(4 lam)| exp(-(log n)^2/(8 lam))
    (= E6Bridge16.primeAbs lam), the c-uniform size of the prime side in units of A, and the PNT
    tail estimate beyond n = N (integrand in absolute value: an error bar)."""
    s = mp.mpf(0)
    for n, L in table.items():
        u = mp.log(n)
        s += L / mp.sqrt(n) * abs(1 - u * u / (4 * lam)) * mp.exp(-u * u / (8 * lam))
    tail = mp.quad(lambda u: 2 * abs(1 - u * u / (4 * lam)) * mp.exp(-u * u / (8 * lam)) * mp.exp(u / 2),
                   [mp.log(N), mp.log(N) + 20 * mp.sqrt(lam) + 5])
    return 2 * s, tail


def envelope_sharp(lam, pabs):
    """E6Bridge16.envelopeCsharp: 2 pi e^{P_abs + 1/2} + sqrt((16 + 2 P_abs)/lam) + 3/sqrt(lam) + 1."""
    return 2 * mp.pi * mp.exp(pabs + mp.mpf(1) / 2) + mp.sqrt((16 + 2 * pabs) / lam) + 3 / mp.sqrt(lam) + 1


def envelope_crude(lam):
    """E6Bridge11.envelopeC: 2 e^{9 + 2 X} + 2/sqrt lam, X = 4 e^{2 lam} sqrt(32 pi lam) + 16 e^{16 lam}."""
    X = 4 * mp.exp(2 * lam) * mp.sqrt(32 * mp.pi * lam) + 16 * mp.exp(16 * lam)
    return 2 * mp.exp(9 + 2 * X) + 2 / mp.sqrt(lam)


def band_edge_table(table, N, T=mp.mpf(640000)):
    """The band-edge table for docs/WALL_SHARP_ENVELOPE_2026-09-21.md.  Ladder side (E6Bridge12):
    constB(c) = sum_rho m(rho) e^{1/2} (2 c^2 + 13/4)/(1 + gamma^2) ~ 0.04619 e^{1/2} (2 c^2 + 13/4)
    (sum_rho 1/(1 + gamma_rho^2) = 2 sum_{gamma > 0} 1/(1 + gamma^2) = 0.04619, from the first 2000
    zeros + Riemann-von Mangoldt tail; PROXY).  lamThreshold(c, 2, 1, delta) = max 1 (constB
    e^{15/2} / (11 delta^2 / 2)); the dominance form needs lam >= 1 and tailEnvelope = e^{-15 (lam - 1)/2}
    constB <= windowSum ~ (4/2pi) log(c/2pi) * mean(x^2 e^{-2 lam x^2} on |x| <= 2) (PROXY)."""
    print("# band edge: P_abs(lam), sharp envelope c1'(lam) = 2 pi e^{P_abs + 1/2} + sqrt((16 + 2 P_abs)/lam) + 3/sqrt lam + 1 (E6Bridge16.envelopeCsharp), crude envelopeC(lam) (E6Bridge11)")
    print(f"{'lam':>5} {'P_abs':>10} {'tail-bar':>9} {'c1sharp':>12} {'2pi e^Pabs':>12} {'envelopeC(crude)':>18}")
    rows = {}
    for lam in ['0.1', '0.2', '0.3', '0.4', '0.5', '0.6', '0.7', '0.8', '1', '1.1', '1.2', '1.3', '1.5', '2']:
        lam = mp.mpf(lam)
        pa, tl = prime_abs(lam, table, N)
        rows[lam] = pa
        print(f"{mp.nstr(lam, 3):>5} {mp.nstr(pa, 5):>10} {mp.nstr(tl, 2):>9} {mp.nstr(envelope_sharp(lam, pa), 4):>12} {mp.nstr(2 * mp.pi * mp.exp(pa), 4):>12} {mp.nstr(envelope_crude(lam), 4):>18}")
    # lam_* : c1sharp(lam_*) = T by bisection on a log-linear interpolation of P_abs
    lams = sorted(rows)
    def pa_interp(l):
        for a, b in zip(lams, lams[1:]):
            if a <= l <= b:
                t = (l - a) / (b - a)
                return rows[a] + t * (rows[b] - rows[a])
        return rows[lams[-1]]
    for Tv in [T, mp.mpf('3e12')]:
        lo, hi = lams[0], lams[-1]
        for _ in range(60):
            mid = (lo + hi) / 2
            if envelope_sharp(mid, pa_interp(mid)) <= Tv:
                lo = mid
            else:
                hi = mid
        print(f"# lam_* with c1sharp(lam_*) = T = {mp.nstr(Tv, 6)}: lam_* ~ {mp.nstr(lo, 4)} (P_abs ~ {mp.nstr(pa_interp(lo), 4)}, log(T/2pi) = {mp.nstr(mp.log(Tv/(2*mp.pi)), 4)}); for lam <= lam_* Gaussian positivity holds for ALL |c| >= T (E6Bridge16.gaussian_positivity_above_height)")
    print("# ladder side (PROXY constants): single-near-zero threshold lamThreshold(c,2,1,delta) and dominance-form lam_dom(c)")
    print(f"{'c':>10} {'constB~':>12} {'lamThr(d=.25)':>14} {'lamThr(d=.5)':>13} {'lam_dom~':>9}")
    S = mp.mpf('0.04619')
    for c in [mp.mpf(x) for x in ['100', '1000', '10000', '100000', '640000']]:
        constB = S * mp.exp(mp.mpf(1) / 2) * (2 * c * c + mp.mpf(13) / 4)
        thr = lambda d: max(1, constB * mp.exp(mp.mpf(15) / 2) / (mp.mpf(11) * d * d / 2))
        # dominance: lam >= 1 with e^{-7.5 (lam-1)} constB <= W(lam); W = (4/2pi) log(c/2pi) * mean_{|x|<=2} x^2 e^{-2 lam x^2}
        lam = mp.mpf(1)
        for _ in range(50):
            W = (4 / (2 * mp.pi)) * mp.log(c / (2 * mp.pi)) * mp.quad(lambda x: x * x * mp.exp(-2 * lam * x * x), [-2, 2]) / 4
            lam = max(1, 1 + (mp.log(constB) - mp.log(W)) / mp.mpf('7.5'))
        print(f"{mp.nstr(c, 6):>10} {mp.nstr(constB, 4):>12} {mp.nstr(thr(mp.mpf('0.25')), 4):>14} {mp.nstr(thr(mp.mpf('0.5')), 4):>13} {mp.nstr(lam, 4):>9}")
    print("# overlap test: the dominance form needs lam >= 1 (hlam : 1 <= lam in E6Bridge12); at lam = 1 the sharp envelope needs |c| >= c1sharp(1) ~ 2 pi e^{P_abs(1)}")
    pa1 = rows[mp.mpf(1)]
    print(f"#   c1sharp(1) = {mp.nstr(envelope_sharp(mp.mpf(1), pa1), 4)} vs T = {mp.nstr(T, 6)}: ratio {mp.nstr(envelope_sharp(mp.mpf(1), pa1) / T, 3)} -> NO OVERLAP; and lam_dom(T) ~ 4.3 > 1 makes it worse (P_abs(4.3) ~ 1e3).")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--zeros", type=int, default=2000)
    ap.add_argument("--cache", default=os.path.join(tempfile.gettempdir(), "seam_b_zeros.json"))
    ap.add_argument("--centers", default="0,1,14.134725,50,1000,10000,100000")
    ap.add_argument("--lams", default="0.005,0.01,0.02,0.05,0.1,0.2,0.5,1")
    ap.add_argument("--no-zero-side", action="store_true")
    ap.add_argument("--dps", type=int, default=20, help="mpmath working precision (digits)")
    ap.add_argument("--band-edge", action="store_true", help="print the band-edge table (E6Bridge16) and exit")
    ap.add_argument("--sieve", type=int, default=10 ** 6, help="Lambda sieve limit")
    args = ap.parse_args()
    mp.mp.dps = args.dps
    if args.band_edge:
        N = args.sieve
        print(f"# sieving Lambda(n), n <= {N}", file=sys.stderr)
        band_edge_table(von_mangoldt_table(N), N)
        return

    centers = [mp.mpf(x) for x in args.centers.split(",")]
    lams = [mp.mpf(x) for x in args.lams.split(",")]

    # Lambda table: n up to exp(sqrt(80 * 8 * lam_max)) = exp(sqrt(640)) ~ e^25 is far too big for
    # lam = 1; the prime sum is only needed where the Gaussian factor is non-negligible, and for
    # lam <= 1 the relative size at n = N is exp(-(log N)^2/8).  N = 10^6 gives e^{-23.9}.
    N = 10 ** 6
    print(f"# sieving Lambda(n), n <= {N}", file=sys.stderr)
    table = von_mangoldt_table(N)

    zeros = None
    if not args.no_zero_side:
        print(f"# loading {args.zeros} zeros", file=sys.stderr)
        zeros = load_zeros(args.zeros, args.cache)
        print(f"# last zero gamma_{len(zeros)} = {zeros[-1]}", file=sys.stderr)

    lam0, rhs = lower_bound_constants()
    print(f"# Lean lower bound (E6Bridge11.re_weilForm_gauss_nonneg): F/A >= (2 - log pi) - 4 e^{{2 lam}} sqrt(32 pi lam) - 64 e^{{-(log 2)^2/(16 lam)}} - 7 R0 8 sqrt(2 pi) sqrt(lam)/(2 pi), R0 = 41")
    print(f"# nonnegative for lam <= {mp.nstr(lam0, 6)} (absolute, c-uniform); the Lean file certifies lam0 = 1e-7 with cruder numerics")
    print()
    hdr = f"{'c':>10} {'lam':>7} {'A':>12} {'arch':>14} {'poles':>12} {'-f0logpi':>12} {'psi-int':>14} {'prime':>14} {'ptail-bar':>10} {'F=arch-prime':>14} {'F/A':>10}"
    if zeros is not None:
        hdr += f" {'zeroside(N)':>14} {'tail':>12} {'zs+tail':>14} {'rel.diff':>10}"
    print(hdr)
    for c in centers:
        for lam in lams:
            A = A_of(lam)
            arch, poles, lp, psi = arch_side(c, lam)
            prime = prime_side(c, lam, table)
            ptail = prime_tail_estimate(c, lam, N)
            F = arch - prime
            if abs(poles) < mp.mpf('1e-300'):
                poles = mp.mpf(0)
            row = f"{mp.nstr(c, 8):>10} {mp.nstr(lam, 4):>7} {mp.nstr(A, 6):>12} {mp.nstr(arch, 8):>14} {mp.nstr(poles, 6):>12} {mp.nstr(lp, 6):>12} {mp.nstr(psi, 8):>14} {mp.nstr(prime, 8):>14} {mp.nstr(ptail, 3):>10} {mp.nstr(F, 8):>14} {mp.nstr(F / A, 6):>10}"
            if zeros is not None:
                zs, tail = zero_side(c, lam, zeros)
                tot = zs + tail
                rel = (tot - F) / F if F != 0 else mp.mpf('nan')
                row += f" {mp.nstr(zs, 8):>14} {mp.nstr(tail, 6):>12} {mp.nstr(tot, 8):>14} {mp.nstr(rel, 4):>10}"
            print(row)
            sys.stdout.flush()


if __name__ == "__main__":
    main()
