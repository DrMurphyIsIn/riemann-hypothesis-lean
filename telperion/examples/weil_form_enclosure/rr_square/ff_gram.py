"""Exact Frobenius-graph Gram on span{f1, f2, Gamma_0..Gamma_r} for a genus-g curve over F_q, with
Gamma_m.Gamma_n = q^min(m,n) N_|m-n| (N_0 := 2 - 2g), Gamma_n.f1 = 1, Gamma_n.f2 = q^n, f1^2 = f2^2 = 0, f1.f2 = 1
(g6_ff_dictionary.md). Hodge index certificate: -(h^2 G - (Gh)(Gh)^T) = sum_i d_i l_i l_i^T with d_i >= 0 rational,
h = f1 + f2. conjecture1_proved = False."""
import sys, json, itertools
from fractions import Fraction as Fr
import sympy

def count_points(p, k, f):
    # y^2 = f(x) over F_{p^k}, odd degree: one point at infinity; brute force via sympy GF(p^k)
    if k == 1:
        n = 1
        for x in range(p):
            v = sum(c * pow(x, i, p) for i, c in enumerate(f)) % p
            n += 1 if v == 0 else (2 if pow(v, (p - 1) // 2, p) == 1 else 0)
        return n
    raise NotImplementedError

def lpoly_g2(p, f):
    # N_1 by counting over F_p, N_2 by counting over F_{p^2} via explicit field arithmetic
    N1 = count_points(p, 1, f)
    # F_{p^2} = F_p[t]/(t^2 - nr), nr a non-residue
    nr = next(a for a in range(2, p) if pow(a, (p - 1) // 2, p) == p - 1)
    def mul(a, b): return ((a[0]*b[0] + nr*a[1]*b[1]) % p, (a[0]*b[1] + a[1]*b[0]) % p)
    def powe(a, e):
        r = (1, 0)
        while e:
            if e & 1: r = mul(r, a)
            a = mul(a, a); e >>= 1
        return r
    N2 = 1; q2 = p * p
    for x0 in range(p):
        for x1 in range(p):
            x = (x0, x1); v = (0, 0); xp = (1, 0)
            for c in f:
                v = ((v[0] + c * xp[0]) % p, (v[1] + c * xp[1]) % p); xp = mul(xp, x)
            if v == (0, 0): N2 += 1
            else: N2 += 2 if powe(v, (q2 - 1) // 2) == (1, 0) else 0
    a1 = N1 - p - 1                      # P(T) = 1 + a1 T + a2 T^2 + p a1 T^3 + p^2 T^4, with N_k = q^k + 1 - sum alpha^k
    s1 = -a1                             # sum alpha = q + 1 - N1
    s2 = p * p + 1 - N2                  # sum alpha^2
    a2 = (s1 * s1 - s2) // 2             # e2
    return [1, -s1, a2, -p * s1, p * p]

def N_from_P(P, q, kmax):
    T = sympy.Symbol('T')
    poly = sum(c * T ** i for i, c in enumerate(P))
    # sum alpha^k from log-derivative: P(T) = prod (1 - alpha T)
    roots_sum = []
    e = [P[1] * -1, P[2], -P[3], P[4]]  # elementary symmetric e1..e4 with signs: P = 1 - e1 T + e2 T^2 - e3 T^3 + e4 T^4
    e1, e2, e3, e4 = -P[1], P[2], -P[3], P[4]
    pk = [4, e1]
    for k in range(2, kmax + 1):
        # Newton: p_k = e1 p_{k-1} - e2 p_{k-2} + e3 p_{k-3} - e4 p_{k-4}
        val = e1 * pk[k-1] - e2 * pk[k-2] + (e3 * pk[k-3] if k >= 3 else 0) - (e4 * pk[k-4] if k >= 4 else 0)
        if k == 2: val = e1 * pk[1] - 2 * e2
        if k == 3: val = e1 * pk[2] - e2 * pk[1] + 3 * e3
        if k == 4: val = e1 * pk[3] - e2 * pk[2] + e3 * pk[1] - 4 * e4
        pk.append(val)
    return [q ** k + 1 - pk[k] for k in range(0, kmax + 1)]

def gram(q, g, N, r):
    n = 2 + r + 1
    G = [[Fr(0)] * n for _ in range(n)]
    G[0][1] = G[1][0] = Fr(1)
    for i in range(r + 1):
        G[0][2 + i] = G[2 + i][0] = Fr(1)
        G[1][2 + i] = G[2 + i][1] = Fr(q ** i)
        for j in range(r + 1):
            G[2 + i][2 + j] = Fr(q ** min(i, j) * (2 - 2 * g if i == j else N[abs(i - j)]))
    return G

def ldl_psd(A):
    """A = sum d_i l_i l_i^T with exact rationals; returns (ds, ls) or None if A not PSD (pivoting by symmetric order)."""
    n = len(A); A = [row[:] for row in A]; ds = []; ls = []
    for k in range(n):
        piv = A[k][k]
        if piv < 0: return None
        if piv == 0:
            if any(A[k][j] != 0 for j in range(n)): return None
            continue
        l = [A[k][j] / piv for j in range(n)]
        ds.append(piv); ls.append(l)
        for i in range(n):
            for j in range(n):
                A[i][j] -= piv * l[i] * l[j]
    assert all(A[i][j] == 0 for i in range(n) for j in range(n))
    return ds, ls

def hodge_matrix(G):
    n = len(G); h = [1, 1] + [0] * (n - 2)
    Gh = [sum(G[i][j] * h[j] for j in range(n)) for i in range(n)]
    hh = sum(h[i] * Gh[i] for i in range(n))
    return [[-(hh * G[i][j] - Gh[i] * Gh[j]) for j in range(n)] for i in range(n)], hh

if __name__ == '__main__':
    out = {}
    q, g = 5, 2
    P = lpoly_g2(5, [2, 3, 0, 1, 0, 1])
    r = 4
    N = N_from_P(P, q, r)
    import numpy as np
    al = np.roots(P[::-1]); al = 1 / al
    print("G2_F5: P =", P, " N_0..N_4 =", N, " max||alpha|/sqrt5-1| =", float(max(abs(abs(al) / 5 ** 0.5 - 1))))
    G = gram(q, g, N, r); M, hh = hodge_matrix(G)
    cert = ldl_psd(M)
    print("  Hodge certificate (curve):", "FOUND" if cert else "NONE", " h^2 =", hh, " rank", len(cert[0]) if cert else None)
    out["G2_F5"] = dict(q=q, g=g, P=P, N=N, G=[[str(x) for x in row] for row in G],
                        d=[str(x) for x in cert[0]], l=[[str(x) for x in li] for li in cert[1]])
    # on-circle fake with N1 < 0 (FK3 search, q = 2)
    for a, b in itertools.product(range(-6, 0), range(0, 20)):
        PF = [1, a, b, 2 * a, 4]
        z = 1 / np.roots(PF[::-1]) / np.sqrt(2)
        if max(abs(abs(z) - 1)) < 1e-6 and 2 + 1 + a < 0:
            break
    NF = N_from_P(PF, 2, r)
    GF = gram(2, 2, NF, r); MF, _ = hodge_matrix(GF); certF = ldl_psd(MF)
    print("FK3 (q=2, on circle, N1<0): P =", PF, " N =", NF, " Hodge certificate:", "FOUND" if certF else "NONE",
          " Gamma_0.Gamma_1 =", GF[2][3])
    out["FK3"] = dict(q=2, g=2, P=PF, N=NF, G=[[str(x) for x in row] for row in GF],
                      d=[str(x) for x in certF[0]] if certF else None, l=[[str(x) for x in li] for li in certF[1]] if certF else None)
    # off-circle fake (FK2 search, q = 3)
    for a, b in itertools.product(range(-8, 9), range(-20, 21)):
        PO = [1, a, b, 3 * a, 9]
        z = 1 / np.roots(PO[::-1]) / np.sqrt(3)
        if max(abs(abs(z) - 1)) > 0.05 and min(abs(z.imag)) > 1e-6: break
    NO = N_from_P(PO, 3, r)
    GO = gram(3, 2, NO, r); MO, _ = hodge_matrix(GO)
    print("FK2 (q=3, off circle): P =", PO, " N =", NO, " Hodge certificate:", "FOUND" if ldl_psd(MO) else "NONE (Hodge index fails)")
    json.dump(out, open(__import__("os").path.join(__import__("os").path.dirname(__file__), "ff_gram_out.json"), "w"), indent=1)
