"""Prime-free window numerics (2026-09-23), companion to E6Bridge31.lean and
telperion/docs/PRIME_FREE_WINDOW_PLAN_2026-09-23.md.  conjecture1_proved = False.

Three independent evaluations of the archimedean Weil form
    Q(g) = 2 Re[G(1/2) conj G(-1/2)] - log(pi) ||g||^2 + (1/2pi) int |ghat(r)|^2 Re psi(1/4 + i r/2) dr
on tests g supported in [-L, L] (the goal node's class, autocorrelation support |u| <= 2L):
  (1) r-space: Gram matrix from the Fourier side with scipy's complex digamma;
  (2) u-space: the exact identity
        Q(g) = poles + (psi(1/4) - log pi) ||g||^2 + (1/2) intint |g(v) - g(w)|^2 k(v - w),
        k(u) = e^{3|u|/2} / (e^{2|u|} - 1),
      via the vertical-line digamma series (this file checks (1) == (2) to 1e-7);
  (3) the zero sum sum_rho |ghat(gamma_rho)|^2 for the minimiser (explicit formula check).
Also the elementary lower-bound thresholds of the Lean proof (r-space layer cake, E6Bridge31)
and of the two u-space routes.  Run: python3 prime_free_window_numerics.py
"""
import numpy as np
import mpmath as mp
from numpy.polynomial.legendre import leggauss, legvander
from scipy.linalg import eigh
from scipy.special import digamma
from scipy.optimize import brentq

GAMMA = float(mp.euler)
LOGPI = float(np.log(np.pi))
L0 = float(np.log(2) / 2)


def gram_rspace(L, K=14, nu=300, R=600.0, dr=0.02):
    """Q and the L2 Gram on the basis (1-x^2)^2 x^k, x = u/L, from the Fourier side."""
    x, w = leggauss(nu)
    u, wu = L * x, L * w
    B = np.array([(1 - (u / L) ** 2) ** 2 * (u / L) ** k for k in range(K)])
    r = np.arange(-R, R + dr / 2, dr)
    Ghat = np.exp(1j * np.outer(r, u)) @ (B * wu).T
    psi = digamma(0.25 + 0.5j * r).real
    M = (B * wu) @ B.T
    Aarch = (Ghat.conj().T @ (Ghat * psi[:, None])) * dr / (2 * np.pi)
    Gp, Gm = (B * wu) @ np.exp(u / 2), (B * wu) @ np.exp(-u / 2)
    P = np.outer(Gm.conj(), Gp)
    P = P + P.conj().T
    A = Aarch - LOGPI * M + P
    return (A + A.conj().T) / 2, M, Gp, Gm


def gram_uspace(L, K=24, nv=200, nu=1500, vanish_order=0):
    """Q and the L2 Gram on (1-x^2)^vanish_order P_k(x) (Legendre) from the u-space identity."""
    x, w = leggauss(nv)

    def basis(uu):
        xx = np.clip(uu / L, -1, 1)
        V = legvander(xx, K - 1).T * (1 - xx ** 2) ** vanish_order
        V[:, np.abs(uu) > L] = 0.0
        return V

    u, wu = L * x, L * w
    B = basis(u)
    M = (B * wu) @ B.T
    Gp, Gm = (B * wu) @ np.exp(u / 2), (B * wu) @ np.exp(-u / 2)
    P = np.outer(Gm, Gp)
    P = P + P.T
    tx, tw = leggauss(nu)
    t, tw = L * (tx + 1), L * tw
    acc = np.zeros((K, K))
    for ti, wi in zip(t, tw):
        a, b = ti - L, L
        vv = (b - a) / 2 * x + (a + b) / 2
        wv = (b - a) / 2 * w
        F = (basis(vv - ti) * wv) @ basis(vv).T
        acc += wi * (2 * M - (F + F.T) * np.exp(1.5 * ti)) / (np.exp(2 * ti) - 1)
    tail = M * (-np.log1p(-np.exp(-4 * L)))
    return P - (LOGPI + GAMMA) * M + acc + tail, M, Gp, Gm


def mineig(A, M, k=3):
    return eigh(A, M, eigvals_only=True)[:k]


def mineig_vanishing(A, M, Gp, Gm):
    """Restrict to G(1/2) = G(-1/2) = 0 (the Yoshida / Connes-Consani class)."""
    C = np.vstack([Gp, Gm])
    _, _, Vh = np.linalg.svd(C)
    N = Vh[2:].conj().T
    return mineig(N.conj().T @ A @ N, N.conj().T @ M @ N)


def zero_sum_of_minimiser(L, K=30, nzeros=200):
    A, M, _, _ = gram_uspace(L, K=K)
    w, V = eigh(A, M)
    c = V[:, 0]
    x, wq = leggauss(400)
    u, wu = L * x, L * wq
    g = c @ legvander(x, K - 1).T
    tot = 0.0
    for n in range(1, nzeros + 1):
        gz = float(mp.zetazero(n).imag)
        tot += 2 * abs(np.sum(wu * g * np.exp(1j * gz * u))) ** 2
    return w[0], tot / (c @ M @ c)


# The nineteen E6Bridge30 floors used by E6Bridge31 (radius, floor), base psiR(0) >= -4.2315.
FLOORS = [(0, -4.2315), (0.5, -2.1913), (0.6, -1.8138), (0.9, -1.0532), (1.4, -0.4233),
          (1.5, -0.3405), (2.4, 0.1691), (2.9, 0.3621), (3.6, 0.5804), (5.1, 0.9303),
          (6.9, 1.2333), (8, 1.3814), (8.9, 1.4881), (11.1, 1.709), (11.6, 1.753),
          (13.5, 1.9046), (16, 2.0742), (16.1, 2.0804), (18.9, 2.2403), (21.1, 2.3499)]


def lean_bound(L):
    """The E6Bridge31 lower bound of Q / ||g||^2: |ghat|^2 <= 2 L f(0), pole terms
    >= -(e^{L/2} - e^{-L/2})^2 L f(0), 19-band layer cake."""
    band = sum((FLOORS[i][1] - FLOORS[i - 1][1]) * FLOORS[i][0] for i in range(1, len(FLOORS)))
    d = np.exp(L / 2) - np.exp(-L / 2)
    return FLOORS[-1][1] - LOGPI - (2 * L / np.pi) * band - d ** 2 * L


def crude_u_bound(L, N=2000):
    """u-space series with |f(u)| <= f(0) only."""
    b = 2 * np.arange(N) + 2.5
    s = np.sum(1 / (np.arange(N) + 1) - (2 / b) * (1 - np.exp(-2 * b * L)))
    return -8 * (np.exp(L) - 1) - LOGPI - GAMMA - 4 * (1 - np.exp(-L)) + s


def dirichlet_u_bound(L, N=2000):
    """u-space with the Dirichlet form kept (inside-outside part only), poles by Cauchy-Schwarz."""
    b = 2 * np.arange(N) + 2.5
    s = np.sum(1 / (np.arange(N) + 1) - 2 / b + 2 * np.exp(-b * L) / b)
    return -4 * np.sinh(L) - LOGPI - GAMMA - 4 + 4 * np.exp(-L / 2) + s


if __name__ == "__main__":
    A, M, Gp, Gm = gram_rspace(L0)
    A2, M2, Gp2, Gm2 = gram_uspace(L0, K=14, vanish_order=2)
    print("r-space vs u-space (same basis) min eig:", mineig(A, M)[0], mineig(A2, M2)[0])
    for L in [0.05, 0.1, 0.2, 0.3, L0, 0.36, 0.38, 0.5]:
        A, M, Gp, Gm = gram_uspace(L, K=30)
        print(f"L={L:.4f} 2L={2 * L:.4f} min eig full={mineig(A, M)[0]:+.6f} "
              f"pole-free class={mineig_vanishing(A, M, Gp, Gm)[0]:+.6f}")
    ev, zs = zero_sum_of_minimiser(L0)
    print(f"at 2L = log 2: min eig {ev:.6f}; zero sum over first 200 zero pairs {zs:.6f}")
    print("Lean bound threshold L =", brentq(lean_bound, 1e-4, 0.5), "value at 1/14:", lean_bound(1 / 14))
    print("crude-u threshold L =", brentq(crude_u_bound, 1e-4, 0.5))
    print("Dirichlet-u threshold L =", brentq(dirichlet_u_bound, 1e-4, 0.5))
