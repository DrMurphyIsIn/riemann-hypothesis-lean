"""hodge1_gen.py -- exact-rational mirror of KWin2_Data (KPar) and of Hodge1_KPen (HPar), HODGE-1 Phase 1b-A.

Every function here mirrors a Lean definition of the same name (KWin_Data / KWin2_Data / KWin2_Round /
Hodge1_KPen) in exact Fractions, with Lean's conventions: x / 0 = 0 in Q, Nat division floors, floorR/ceilR
at 10^-R.  The Lean kernel re-evaluates every checker (decide +kernel), so nothing here is trusted; this file
chooses the untrusted inputs (the leakage matrices D, the head levels) and pre-checks that the kernel will
return true (and false on the negative controls).

Usage:
  python3 hodge1_gen.py validate     # reproduce KWin2_Cert25 (certE25 true at 45e-6, false at 5e-5)
  python3 hodge1_gen.py h45          # instance H45: head eigenvalues, tail checks, certificates, controls;
                                     # writes h45_data.lean.txt (the D matrices, pasted into Hodge1_Par45.lean)
conjecture1_proved = False.  Nothing here is a proof.
"""
import sys, math, time, os
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))


def div(a, b):
    return F(0) if b == 0 else F(a) / F(b)


def floorR(q, R):
    q = F(q)
    return F((q.numerator * 10 ** R) // q.denominator, 10 ** R)


def ceilR(q, R):
    q = F(q)
    return F(-((-q.numerator * 10 ** R) // q.denominator), 10 ** R)


fact = math.factorial

# ---- KWin_Data constants ----
piLoQ = F(314159265358979323846, 10 ** 20)
piHiQ = F(314159265358979323847, 10 ** 20)
gammaUpQ = sum(F(1, k + 1) for k in range(16)) - 4 * F(6931471803, 10 ** 10) - F(1, 32) + F(1, 3072)
logPiUpQ = F(11447298859, 10 ** 10)
Rk = 30


def bS(j):
    return 2 * F(j) + F(1, 2)


def smax(b, c):
    return max(max(b, c), F(7, 10) * (b + c))


def gpow(x, y, n):
    p, q = F(1), F(0)
    for _ in range(n):
        p, q = p * x - q * y, p * y + q * x
    return p, q


def kap(b, c, k):
    D = b * b + c * c
    x, y = div(b, D), div(c, D)
    p, q = gpow(x, y, k + 1)
    r = k % 4
    v = p if r == 0 else (-q if r == 1 else (-p if r == 2 else q))
    return 2 * v


def kapR(b, c, k):
    return floorR(kap(b, c, k), Rk)


def remB(b, c, h, d):
    s = smax(b, c)
    return div(2 * div(h, s) ** (d + 1), (1 - div(h, s)) * s)


class KPar:
    def __init__(self, **kw):
        self.__dict__.update(kw)
        self._cache = {}

    def memo(self, key, fn):
        if key not in self._cache:
            self._cache[key] = fn()
        return self._cache[key]

    # B. minorant
    def nPc(self):
        return len(self.brks) - 1

    def brk(self, i):
        return self.brks[i] if i < len(self.brks) else self.T

    def pcen(self, i):
        return (self.brk(i) + self.brk(i + 1)) / 2

    def phw(self, i):
        return (self.brk(i + 1) - self.brk(i)) / 2

    def deg(self, i, j):
        row = self.degTab[i] if i < len(self.degTab) else []
        return row[j] if j < len(row) else 0

    def uCoef(self, i, k):
        return sum((kapR(bS(j), self.pcen(i), k) if k <= self.deg(i, j) else F(0)) for j in range(self.nS))

    def rhoRaw(self, i):
        return sum(remB(bS(j), self.pcen(i), self.phw(i), self.deg(i, j))
                   + div(sum(self.phw(i) ** k for k in range(self.deg(i, j) + 1)), 10 ** Rk)
                   for j in range(self.nS))

    def rhoR(self, i):
        return ceilR(self.rhoRaw(i), Rk)

    def HNr(self):
        return F(sum(10 ** 30 // (n + 1) for n in range(self.Nser)), 10 ** 30)

    def C0(self):
        N, M = F(self.Nser), F(self.Mser)
        return (-self.gamUp - self.logPiUp + self.HNr() + div(F(1, 4), N + F(5, 4))
                - F(1, 2) * div((N + M + F(5, 4)) ** 2 - (N + M + 1) ** 2, (N + M + 1) ** 2))

    def C1(self):
        N, M = F(self.Nser), F(self.Mser)
        return div(1, 8 * (N + F(5, 4)) ** 2) - div(1, 8 * (N + M + 1) ** 2)

    def C2(self):
        N = F(self.Nser)
        return div(-1, 32 * (N + F(5, 4)) ** 4)

    def gAlt(self, k):
        if k % 2 == 0:
            s = sum((4 ** (k + 1) * 10 ** (30 + 3 * k) + (4 * j + 1) ** (2 * k + 1) - 1) // (4 * j + 1) ** (2 * k + 1)
                    for j in range(self.nS, self.Nser + 1))
            return F(s, 10 ** (30 + 3 * k))
        s = sum((4 ** (k + 1) * 10 ** (30 + 3 * k)) // (4 * j + 1) ** (2 * k + 1) for j in range(self.nS, self.Nser + 1))
        return -F(s, 10 ** (30 + 3 * k))

    def globRaw(self, p):
        a = self.C0() if p == 0 else (self.C1() if p == 2 else (self.C2() if p == 4 else F(0)))
        b = self.gAlt(p // 2) if (p % 2 == 0 and p // 2 < 2 * self.Kalt + 1) else F(0)
        return a - b

    def globList(self):
        return self.memo("glob", lambda: [floorR(self.globRaw(p), 30 + 3 * (p // 2)) for p in range(self.Dmax + 1)])

    def uList(self, i):
        return self.memo(("u", i), lambda: [self.uCoef(i, k) for k in range(self.Dmax + 1)])

    def wpCoef(self, i, p):
        g = self.globList()
        u = self.uList(i)
        s = sum((u[k] * math.comb(k, p) * (-self.pcen(i)) ** (k - p)) for k in range(self.Dmax + 1) if p <= k)
        return g[p] - s - (self.rhoR(i) if p == 0 else F(0))

    def wpList(self, i):
        return self.memo(("wp", i), lambda: [self.wpCoef(i, p) for p in range(self.Dmax + 1)])

    # C. comb
    def combC(self, p):
        v = F(0)
        if p % 2 == 0 and p // 2 < self.Mc:
            v += ceilR(self.c0 * (-1) ** (p // 2) * self.a0 ** p / fact(p), self.Rc + 2 * p)
        if p == 0:
            v += self.combK
        return v

    def combList(self):
        return self.memo("comb", lambda: [self.combC(p) for p in range(2 * self.Mc + 1)])

    # D. moments and head
    def momPiece(self, i, q):
        wp = self.wpList(i)
        a, b = self.brk(i), self.brk(i + 1)
        s = sum(wp[p] * (b ** (p + q + 1) - a ** (p + q + 1)) / (p + q + 1) for p in range(self.Dmax + 1))
        return s - self.beta0 * (b ** (q + 1) - a ** (q + 1)) / (q + 1)

    def momComb(self, q):
        c = self.combList()
        return sum(c[p] * self.T ** (p + q + 1) / (p + q + 1) for p in range(2 * self.Mc + 1))

    def mom(self, q):
        return sum(self.momPiece(i, q) for i in range(self.nPc())) - self.momComb(q)

    def momList(self, par):
        return self.memo(("mom", par), lambda: [self.mom(2 * s + 2 * par) for s in range(2 * self.Mt)])

    def Gm(self, par, j, k):
        return 2 * self.ell / (2 * j + 2 * k + 2 * par + 1)

    def Bm(self, par, m, k):
        return F((-1) ** m) * self.ell ** (2 * m + par) / fact(2 * m + par) * self.Gm(par, m, k)

    def pv(self, par, k):
        return sum((self.ell / 2) ** (2 * m + par) / fact(2 * m + par) * self.Gm(par, m, k) for m in range(self.Mp))

    def WBmat(self, par, N):
        def mk():
            ml = self.momList(par)
            return [[sum(ml[m + mp] * self.Bm(par, mp, k) for mp in range(self.Mt)) for k in range(N)]
                    for m in range(self.Mt)]
        return self.memo(("WB", par, N), mk)

    def diagc(self, lam):
        return piLoQ * (self.beta0 - lam) - 2 * self.ell * self.Econst

    def headEntry(self, par, N, lam, j, k):
        WB = self.WBmat(par, N)
        piE = piLoQ if par == 0 else piHiQ
        eps = 1 if par == 0 else -1
        return (2 * piE * eps * self.pv(par, j) * self.pv(par, k) + self.diagc(lam) * self.Gm(par, j, k)
                + sum(self.Bm(par, m, j) * WB[m][k] for m in range(self.Mt)))

    def headMat(self, par, N, lam):
        return [[self.headEntry(par, N, lam, j, k) for k in range(N)] for j in range(N)]

    # F. tail constants
    def dPT(self, par, N):
        return 2 * (self.ell / 2) ** (2 * N + par) / fact(2 * N + par)

    def I1T(self, par, N):
        n = 2 * N + par
        return 2 * self.ell ** n * self.T ** (n + 1) / ((n + 1) * fact(n))

    def I2T(self, par, N):
        n = 2 * N + par
        return 4 * self.ell ** (2 * n) * self.T ** (2 * n + 1) / ((2 * n + 1) * fact(n) ** 2)

    def EheadS0(self, par):
        n = 2 * self.Mt + par
        return self.S0 * (2 * (2 * self.ell ** n * self.T ** (n + 1) / ((n + 1) * fact(n)))
                          + 4 * self.ell ** (2 * n) * self.T ** (2 * n + 1) / ((2 * n + 1) * fact(n) ** 2))

    def dPh(self, par):
        return 2 * (self.ell / 2) ** (2 * self.Mp + par) / fact(2 * self.Mp + par)


# ---- KWin_Data / KWin2_Round certificates ----

def ldlAux(f, A, s):
    out = []
    while f > 0 and A:
        r, rs = A[0], A[1:]
        if not r:
            break
        d, a = r[0], r[1:]
        out.append((d, [F(0)] * s + [F(1)] + [div(x, d) for x in a]))
        A = [([] if not row else [y - div(row[0] * aj, d) for y, aj in zip(row[1:], a)]) for row in rs]
        f -= 1
        s += 1
    return out


def mget(A, j, k):
    row = A[j] if j < len(A) else []
    return row[k] if k < len(row) else F(0)


def psdCert(A, n):
    L = ldlAux(n, A, 0)
    if not all(p[0] >= 0 for p in L):
        return False
    for j in range(n):
        for k in range(n):
            s = sum(p[0] * (p[1][j] if j < len(p[1]) else 0) * (p[1][k] if k < len(p[1]) else 0) for p in L)
            if mget(A, j, k) != s:
                return False
    return True


def roundShift(A, n, R):
    return [[floorR(mget(A, j, k), R) - (F(n, 10 ** R) if j == k else F(0)) for k in range(n)] for j in range(n)]


def psdCertR(A, n, R):
    return psdCert(roundShift(A, n, R), n)


# ---- Hodge1_KPen ----

class HPar:
    def __init__(self, K, pc, s0, w2up):
        self.K, self.pc, self.s0, self.w2up = K, pc, s0, w2up

    def Pim(self, par, j, k):
        K = self.K
        n = 2 * j + 2 * k + 2 * par
        return 2 * K.ell / (n + 1) * (1 - (self.s0 / K.ell) ** (n + 1))

    def PDmat(self, par, N, D):
        return [[sum(self.Pim(par, j, i) * mget(D, i, k) for i in range(N)) for k in range(N)] for j in range(N)]

    def DGDmat(self, par, N, D):
        K = self.K
        GD = [[sum(K.Gm(par, i, ip) * mget(D, ip, k) for ip in range(N)) for k in range(N)] for i in range(N)]
        return [[sum(mget(D, i, j) * GD[i][k] for i in range(N)) for k in range(N)] for j in range(N)]

    def leakMat(self, par, N, D):
        PD = self.PDmat(par, N, D)
        DGD = self.DGDmat(par, N, D)
        return [[self.Pim(par, j, k) - PD[j][k] - PD[k][j] + DGD[j][k] for k in range(N)] for j in range(N)]

    def headMatP(self, par, N, lam, eta, D):
        K = self.K
        WB = K.WBmat(par, N)
        Q = self.leakMat(par, N, D)
        pv = [K.pv(par, j) for j in range(N)]
        return [[piLoQ * self.pc * pv[j] * pv[k] + K.diagc(lam) * K.Gm(par, j, k)
                 + sum(K.Bm(par, m, j) * WB[m][k] for m in range(K.Mt))
                 - piHiQ * self.w2up * (self.Pim(par, j, k) + eta * Q[j][k]) for k in range(N)] for j in range(N)]

    def EheadP(self, par):
        K = self.K
        d = K.dPh(par)
        return self.pc * piHiQ * d * (2 * K.Cp + d) + K.EheadS0(par)

    def kapTP(self, par, N):
        K = self.K
        return self.pc * K.Cp * K.dPT(par, N) + K.S0 / 3 * K.I1T(par, N)

    def dTP(self, par, N, eta):
        K = self.K
        return K.beta0 - 2 * K.ell * (K.S0 / 3 * K.I2T(par, N)) - self.w2up * (1 + 1 / eta)

    def tailCondP(self, par, N, lam, eta):
        K = self.K
        dT, kp = self.dTP(par, N, eta), self.kapTP(par, N)
        checks = [K.lamFloor <= lam, K.lamFloor <= dT,
                  4 * kp ** 2 * K.ell ** 2 <= (lam - K.lamFloor) * (dT - K.lamFloor),
                  self.EheadP(par) <= K.Econst, lam < K.beta0,
                  K.T * K.ell <= F(2 * N + par + 1, 2), K.T * K.ell <= F(2 * K.Mt + par + 1, 2), 1 <= N,
                  0 <= self.pc, 0 < eta, 0 <= self.w2up, 0 <= self.s0, self.s0 <= K.ell]
        return all(checks), checks


# ---- exact linear algebra helpers (untrusted design layer) ----

def solve(A, B):
    """A^{-1} B by Gauss-Jordan in Fractions."""
    n = len(A)
    M = [list(A[i]) + list(B[i]) for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [row[n:] for row in M]


def head_eig(A0, K, par, N, dps=80):
    """largest lam with A0 - piLoQ lam G PSD: lambda_min of the pencil (A0, piLo G)."""
    import mpmath as mp
    mp.mp.dps = dps
    A = mp.matrix([[mp.mpf(x.numerator) / x.denominator for x in row] for row in A0])
    G = mp.matrix([[mp.mpf(K.Gm(par, j, k).numerator) / K.Gm(par, j, k).denominator * mp.mpf(piLoQ.numerator) / piLoQ.denominator
                    for k in range(N)] for j in range(N)])
    Lc = mp.cholesky(G)
    Li = mp.inverse(Lc)
    S = Li * A * Li.T
    S = (S + S.T) / 2
    return min(mp.eigsy(S)[0])


def mp_str(x):
    import mpmath as mp
    return mp.nstr(x, 8)


# ---- instances ----

PAR25_MINORANT = dict(
    brks=[F(0), F(3, 10), F(4, 5), F(8, 5), F(16, 5), F(32, 5), F(64, 5), F(20), F(24)],
    degTab=[[20, 8, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
            [22, 9, 7, 6, 6, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3],
            [21, 12, 9, 7, 7, 6, 6, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
            [21, 15, 12, 10, 9, 8, 7, 7, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 4],
            [20, 19, 15, 13, 12, 11, 10, 9, 9, 8, 8, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 5],
            [19, 19, 19, 17, 15, 14, 13, 12, 12, 11, 11, 10, 10, 9, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7],
            [13, 13, 13, 13, 13, 12, 12, 11, 11, 10, 10, 10, 9, 9, 9, 9, 9, 8, 8, 8, 8, 8, 7, 7],
            [8, 8, 8, 8, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6]],
    nS=24, Kalt=5, Dmax=22, Nser=400, Mser=10 ** 9, gamUp=gammaUpQ, logPiUp=logPiUpQ)


def P25():
    return KPar(ell=F(2, 5), T=F(24), beta0=F(318, 1000), S0=F(668, 100), Cp=F(10203, 10000), **PAR25_MINORANT,
                Mt=20, Mp=8, a0=F(6931471805599453, 10 ** 16), da=F(1, 10 ** 16), c0=F(9802581434685472, 10 ** 16),
                dc=F(1, 10 ** 16), Mc=32, combK=F(2164470881, 10 ** 20), Rc=16, Econst=F(1, 10 ** 6),
                lamFloor=F(4, 10 ** 5))


def validate():
    K = P25()
    t = time.time()
    A = K.headMat(0, 16, F(45, 10 ** 6))
    print("P25 even head matrix built in %.1fs" % (time.time() - t), flush=True)
    A0 = K.headMat(0, 16, F(0))
    print("P25 even head eigenvalue (pencil, piLo G): %s  (KWin2_Par25 header: 4.70e-5)" % mp_str(head_eig(A0, K, 0, 16)),
          flush=True)
    t = time.time()
    print("psdCert(headMat P25 0 16 45e-6) = %s  [kernel: certE25 true]  (%.1fs)" % (psdCert(A, 16), time.time() - t),
          flush=True)
    t = time.time()
    print("psdCert(headMat P25 0 16 5e-5)  = %s  [kernel: certE25_negative_control false]  (%.1fs)" % (
        psdCert(K.headMat(0, 16, F(5, 10 ** 5)), 16), time.time() - t), flush=True)


def P45():
    return KPar(ell=F(9, 20), T=F(24), beta0=F(649, 500), S0=F(167, 25), Cp=F(10257, 10000), **PAR25_MINORANT,
                Mt=21, Mp=8, a0=F(0), da=F(0), c0=F(0), dc=F(0), Mc=1, combK=F(0), Rc=16, Econst=F(1, 10 ** 6),
                lamFloor=F(3, 100))


H45 = dict(pc=F(1000), s0=F(6, 25), w2up=F(49013, 100000))
SECTORS = {0: dict(N=16, lam=F(33, 1000), eta=F(2)), 1: dict(N=15, lam=F(31, 100), eta=F(3, 2))}
RD = 25    # leakage matrix D rounded to 10^-RD
RCERT = 40  # psdCertR level


def Dmat(H, par, N):
    K = H.K
    G = [[K.Gm(par, j, k) for k in range(N)] for j in range(N)]
    Pm = [[H.Pim(par, j, k) for k in range(N)] for j in range(N)]
    Dx = solve(G, Pm)
    return [[F(round(x * 10 ** RD), 10 ** RD) for x in row] for row in Dx]


def emit_D(name, D):
    """D as integer rows (numerators over 10^RD): integer literals elaborate fast."""
    rows = []
    for row in D:
        rows.append("    [" + ", ".join("%d" % (x.numerator * (10 ** RD // x.denominator)) for x in row) + "]")
    return ("def %sz : List (List ℤ) :=\n  [" % name + ",\n".join(rows).lstrip() + "]\n\n"
            + "def %s : List (List ℚ) := %sz.map (·.map (fun z : ℤ => (z : ℚ) / 10 ^ %d))\n" % (name, name, RD))


def h45(write=True):
    import mpmath as mp
    K = P45()
    H = HPar(K, **H45)
    out = {}
    for par in (0, 1):
        sec = SECTORS[par]
        N, lam, eta = sec["N"], sec["lam"], sec["eta"]
        t = time.time()
        D = Dmat(H, par, N)
        A0 = H.headMatP(par, N, F(0), eta, D)
        e = head_eig(A0, K, par, N)
        ok, checks = H.tailCondP(par, N, lam, eta)
        print("H45 %s N=%d: head eigenvalue %s (lam = %s), dT' = %.6f, kapT = %.3e, EheadP = %.3e, tailCondP = %s %s  (%.1fs)" % (
            ("even", "odd")[par], N, mp_str(e), float(lam), float(H.dTP(par, N, eta)), float(H.kapTP(par, N)),
            float(H.EheadP(par)), ok, "" if ok else checks, time.time() - t), flush=True)
        A = H.headMatP(par, N, lam, eta, D)
        t = time.time()
        cR = psdCertR(A, N, RCERT)
        print("   psdCertR(headMatP, N, %d) = %s  (%.1fs)" % (RCERT, cR, time.time() - t), flush=True)
        lamNC = F(int(mp.ceil(e * 10 ** 4)) + 1, 10 ** 4)
        t = time.time()
        nc1 = psdCertR(H.headMatP(par, N, lamNC, eta, D), N, RCERT)
        print("   NEGATIVE CONTROL lam = %s > head eigenvalue: psdCertR = %s  (%.1fs)" % (lamNC, nc1, time.time() - t), flush=True)
        out[par] = dict(D=D, lamNC=lamNC, e=e)
    H13 = HPar(K, pc=H45["pc"], s0=H45["s0"], w2up=H45["w2up"] * F(13, 10))
    sec = SECTORS[0]
    A = H13.headMatP(0, sec["N"], sec["lam"], sec["eta"], out[0]["D"])
    e13 = head_eig(H13.headMatP(0, sec["N"], F(0), sec["eta"], out[0]["D"]), K, 0, sec["N"])
    print("NEGATIVE CONTROL w2up * 13/10, even: head eigenvalue %s; psdCertR at lam = %s: %s" % (
        mp_str(e13), sec["lam"], psdCertR(A, sec["N"], RCERT)), flush=True)
    if write:
        with open(os.path.join(HERE, "h45_data.lean.txt"), "w") as f:
            f.write(emit_D("DE45", out[0]["D"]) + "\n" + emit_D("DO45", out[1]["D"]))
        print("negative-control levels: even %s, odd %s" % (out[0]["lamNC"], out[1]["lamNC"]))
    return out




# ---- Phase 1b-B: the direct pole-free certificate at l = 5493/10000 (comb kept in the symbol) ----

PAR12_MINORANT = dict(
    brks=[F(0), F(3, 10), F(4, 5), F(8, 5), F(16, 5), F(32, 5), F(64, 5), F(20), F(25), F(30), F(35), F(40)],
    nS=44, Kalt=5, Dmax=24, Mser=10 ** 9, logPiUp=logPiUpQ)

log2S = sum(F(1, 2) ** (i + 1) / (i + 1) for i in range(60))
H32 = sum(F(1, k + 1) for k in range(32))
gamUp32 = ceilR(H32 - 5 * (log2S - F(1, 2) ** 60) - F(1, 64) + F(1, 12288), 20)


def par12_degtab():
    """KWin2_Par12's degTab, read from the Lean file (single source of truth)."""
    import re
    src = open(os.path.join(HERE, "..", "lean", "KWin2_Par12.lean")).read()
    body = src[src.index("degTab :="):src.index("nS :=")]
    return [[int(x) for x in row.split(",")] for row in re.findall(r"\[([0-9, ]+)\]", body)]


def P5493(Nser=1200, a0=F(6931471805599453, 10 ** 16), c0=F(9802581434685472, 10 ** 16), combK=F(650536633, 10 ** 20),
          Mt=37, Econst=F(1, 10 ** 6)):
    return KPar(ell=F(5493, 10000), T=F(40), beta0=F(1057, 1250), S0=F(723, 100), Cp=F(10385, 10000),
                degTab=par12_degtab(), Nser=Nser, gamUp=gamUp32, **PAR12_MINORANT,
                Mt=Mt, Mp=8, a0=a0, da=F(1, 10 ** 16), c0=c0, dc=F(1, 10 ** 16), Mc=48, combK=combK, Rc=16,
                Econst=Econst, lamFloor=F(5, 10 ** 4))


def h5493(Nser=1200, R=65, lams=None, controls=True):
    import mpmath as mp
    K = P5493(Nser=Nser)
    H = HPar(K, pc=F(1000), s0=F(0), w2up=F(0))
    eta, D = F(1), []
    lams = lams or {0: F(55, 10 ** 5), 1: F(13, 1000)}
    Ns = {0: 32, 1: 31}
    out = {}
    for par in (0, 1):
        N, lam = Ns[par], lams[par]
        t = time.time()
        A0 = H.headMatP(par, N, F(0), eta, D)
        e = head_eig(A0, K, par, N, dps=120)
        ok, checks = H.tailCondP(par, N, lam, eta)
        print("P5493 Nser=%d %s N=%d: head eigenvalue %s (lam %s) dT %.4f kapT %.3e EheadP %.2e tailCondP %s %s (%.0fs)" % (
            Nser, ("even", "odd")[par], N, mp_str(e), float(lam), float(H.dTP(par, N, eta)), float(H.kapTP(par, N)),
            float(H.EheadP(par)), ok, "" if ok else checks, time.time() - t), flush=True)
        t = time.time()
        c = psdCertR(H.headMatP(par, N, lam, eta, D), N, R)
        print("   psdCertR(R=%d) at lam = %s: %s (%.0fs)" % (R, lam, c, time.time() - t), flush=True)
        out[par] = e
        if controls and par == 0:
            lamNC = F(int(mp.ceil(e * 10 ** 6)) + 1, 10 ** 6)
            print("   NEGATIVE CONTROL lam = %s: psdCertR = %s" % (lamNC, psdCertR(H.headMatP(0, N, lamNC, eta, D), N, R)),
                  flush=True)
    if controls:
        import mpmath as mp
        mp.mp.dps = 40
        for name, q, wf in (("q = 2.1", 2.1, 1), ("1.05 c2", 2, F(105, 100))):
            a = mp.log(mp.mpf(q) if q != 2.1 else mp.mpf(21) / 10)
            c = 2 * a / mp.sqrt(mp.mpf(21) / 10 if q == 2.1 else 2) * (mp.mpf(wf.numerator) / wf.denominator if isinstance(wf, F) else 1)
            a0 = F(int(mp.nint(a * 10 ** 16)), 10 ** 16)
            c0 = F(int(mp.nint(c * 10 ** 16)), 10 ** 16)
            Kf = P5493(Nser=Nser, a0=a0, c0=c0)
            Hf = HPar(Kf, pc=F(1000), s0=F(0), w2up=F(0))
            ef = head_eig(Hf.headMatP(0, 32, F(0), eta, D), Kf, 0, 32, dps=120)
            cf = psdCertR(Hf.headMatP(0, 32, lams[0], eta, D), 32, R)
            print("NEGATIVE CONTROL %s (a0 = %s, c0 = %s): even head eigenvalue %s; psdCertR at lam %s: %s" % (
                name, a0, c0, mp_str(ef), lams[0], cf), flush=True)
    return out


if __name__ == "__main__":
    if sys.argv[1] == "h5493":
        h5493(Nser=int(sys.argv[2]) if len(sys.argv) > 2 else 1200, R=int(sys.argv[3]) if len(sys.argv) > 3 else 65)
    else:
        {"validate": validate, "h45": h45}[sys.argv[1]]()


def emit_mom5493(path=None):
    """momList P5493 par as literal (numerator, denominator) pairs, for the staged certificate."""
    K = P5493(Nser=400)
    out = []
    for par, name in ((0, "momE5493"), (1, "momO5493")):
        ml = K.momList(par)
        rows = ",\n    ".join("(%d, %d)" % (q.numerator, q.denominator) for q in ml)
        out.append("def %sz : List (ℤ × ℕ) :=\n  [%s]\n\ndef %s : List ℚ := %sz.map (fun p => (p.1 : ℚ) / (p.2 : ℚ))\n"
                   % (name, rows, name, name))
        print(name, len(ml), "entries, max digits", max(len(str(abs(q.numerator))) + len(str(q.denominator)) for q in ml))
    open(path or os.path.join(HERE, "mom5493.lean.txt"), "w").write("\n".join(out))


def emit_rows5493(path=None):
    """Per-piece moment rows [momPiece P i (2s + 2par) for s < 2 Mt] of P5493, as literal (num, den) pairs."""
    K = P5493(Nser=400)
    out = []
    for par, name in ((0, "rowsE5493"), (1, "rowsO5493")):
        rows = []
        for i in range(K.nPc()):
            row = [K.momPiece(i, 2 * s + 2 * par) for s in range(2 * K.Mt)]
            rows.append("    [" + ", ".join("(%d, %d)" % (q.numerator, q.denominator) for q in row) + "]")
        # sanity: rows reproduce momList
        ml = K.momList(par)
        for s in range(2 * K.Mt):
            assert sum(K.momPiece(i, 2 * s + 2 * par) for i in range(K.nPc())) - K.momComb(2 * s + 2 * par) == ml[s]
        out.append("def %sz : List (List (ℤ × ℕ)) :=\n  [%s]\n\ndef %s : List (List ℚ) :=\n  %sz.map (·.map (fun p => (p.1 : ℚ) / (p.2 : ℚ)))\n"
                   % (name, ",\n".join(rows).lstrip(), name, name))
    open(path or os.path.join(HERE, "rows5493.lean.txt"), "w").write("\n".join(out))
    print("rows written", K.nPc(), "pieces x", 2 * K.Mt)


def emit_B5493(path=None, R=60):
    """The rounded, shifted head matrices roundShift (headMatP ...) N R (numerators over 10^R) for the
    certificate (E, O) and the three negative controls (N: lam above the even eigenvalue; Q: q = 2.1;
    W: 1.05 c2); also reports psdCert on each (must be True, True, False, False, False)."""
    K = P5493(Nser=400)
    H = HPar(K, pc=F(1000), s0=F(0), w2up=F(0))
    Kq = P5493(Nser=400, a0=F(7419373447293773, 10 ** 16), c0=F(10239708175753177, 10 ** 16))
    Kw = P5493(Nser=400, c0=F(5146355253209873, 5000000000000000))
    cases = [("BE5493", H, 0, 32, F(55, 10 ** 5)), ("BO5493", H, 1, 31, F(13, 1000)),
             ("BN5493", H, 0, 32, F(631, 10 ** 6)),
             ("BQ5493", HPar(Kq, pc=F(1000), s0=F(0), w2up=F(0)), 0, 32, F(55, 10 ** 5)),
             ("BW5493", HPar(Kw, pc=F(1000), s0=F(0), w2up=F(0)), 0, 32, F(55, 10 ** 5))]
    out = []
    for name, HH, par, N, lam in cases:
        B = roundShift(HH.headMatP(par, N, lam, F(1), []), N, R)
        assert all(x.denominator <= 10 ** R and (10 ** R) % x.denominator == 0 for row in B for x in row)
        print(name, "psdCert", psdCert(B, N), flush=True)
        rows = ",\n    ".join("[" + ", ".join("%d" % (x * 10 ** R) for x in row) + "]" for row in B)
        out.append("def %sz : List (List ℤ) :=\n  [%s]\n\ndef %s : List (List ℚ) := %sz.map (·.map (fun z : ℤ => (z : ℚ) / 10 ^ %d))\n"
                   % (name, rows, name, name, R))
    open(path or os.path.join(HERE, "B5493.lean.txt"), "w").write("\n".join(out))


def emit_WB5493(path=None):
    """The moment-transform matrices WBmat (Mt x N) of the certificate (E, O) and of the fake-comb controls
    (Q: q = 2.1, W: 1.05 c2), as literal (num, den) pairs.  Untrusted: re-derived by the kernel row by row."""
    Kq = P5493(Nser=400, a0=F(7419373447293773, 10 ** 16), c0=F(10239708175753177, 10 ** 16))
    Kw = P5493(Nser=400, c0=F(5146355253209873, 5000000000000000))
    K = P5493(Nser=400)
    out = []
    for name, KK, par, N in (("WBE5493", K, 0, 32), ("WBO5493", K, 1, 31), ("WBQ5493", Kq, 0, 32), ("WBW5493", Kw, 0, 32)):
        WB = KK.WBmat(par, N)
        rows = ",\n    ".join("[" + ", ".join("(%d, %d)" % (x.numerator, x.denominator) for x in r) + "]" for r in WB)
        out.append("def %sz : List (List (ℤ × ℕ)) :=\n  [%s]\n\ndef %s : List (List ℚ) :=\n  %sz.map (·.map (fun p => (p.1 : ℚ) / (p.2 : ℚ)))\n"
                   % (name, rows, name, name))
        print(name, len(WB), "x", len(WB[0]), flush=True)
    open(path or os.path.join(HERE, "WB5493.lean.txt"), "w").write("\n".join(out))
