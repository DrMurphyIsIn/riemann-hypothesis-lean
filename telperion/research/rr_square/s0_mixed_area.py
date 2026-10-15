"""Lemma S, step 0: the mixed-area (cone-point excess) pairing vs the disjoint pairing of g8 §2(e).
Classes: xi0 <-> (1,0), xi1 <-> (0,1), Gamma_mu <-> (mu,-1)  (jump vectors / Newton segments).
Mixed area of segments: B(u,v) = |det(u,v)|, B(u,u) = 0. Then Gamma_mu.xi0 = 1, Gamma_mu.xi1 = mu (CC's real degrees),
Gamma_mu.Gamma_nu = |mu - nu|. g8 assumed Gamma_mu.Gamma_nu = 0 (disjoint away from the cone point).
conjecture1_proved = False."""
from fractions import Fraction as Fr
import numpy as np, itertools, random
def gram(vecs, disjoint=False):
    n = len(vecs); G = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j: continue
            if disjoint and i >= 2 and j >= 2: G[i][j] = Fr(0); continue
            u, v = vecs[i], vecs[j]; G[i][j] = abs(u[0] * v[1] - u[1] * v[0])
    return G
def npos(G):
    w = np.linalg.eigvalsh(np.array([[float(x) for x in r] for r in G])); return int((w > 1e-12).sum()), int((w < -1e-12).sum())
mus = [Fr(1), Fr(3, 2), Fr(13, 10), Fr(17, 10), Fr(11, 10)]
vecs = [(Fr(1), Fr(0)), (Fr(0), Fr(1))] + [(m, Fr(-1)) for m in mus]
print("mixed-area pairing  (+,-):", npos(gram(vecs)), "   g8 disjoint pairing (+,-):", npos(gram(vecs, True)))
# g8's violating vector v = P_1 - (5/6) P_{3/2}, P_mu = Gamma_mu - mu xi0 - xi1, f = xi0 + xi1
def B(x, y, G):
    return sum(x[i] * G[i][j] * y[j] for i in range(len(x)) for j in range(len(y)))
V = [(Fr(1), Fr(0)), (Fr(0), Fr(1)), (Fr(1), Fr(-1)), (Fr(3, 2), Fr(-1))]
for name, G in [("mixed-area", gram(V)), ("disjoint", gram(V, True))]:
    P1 = [-Fr(1), -Fr(1), Fr(1), Fr(0)]; P32 = [-Fr(3, 2), -Fr(1), Fr(0), Fr(1)]
    v = [a - Fr(5, 6) * b for a, b in zip(P1, P32)]; f = [Fr(1), Fr(1), Fr(0), Fr(0)]
    print(f"{name}: B(v,f) = {B(v, f, G)}, B(v,v) = {B(v, v, G)}, B(f,f) = {B(f, f, G)}")
# random stress: Lorentzian signature of |det| Gram for random lattice/rational vectors in a half-plane
random.seed(1); bad = 0
for trial in range(2000):
    k = random.randint(2, 9)
    vs = [(Fr(random.randint(1, 20)), Fr(-random.randint(1, 20))) for _ in range(k)] + [(Fr(1), Fr(0)), (Fr(0), Fr(1))]
    if npos(gram(vs))[0] != 1: bad += 1
print("random half-plane families with != 1 positive direction:", bad, "/ 2000")
