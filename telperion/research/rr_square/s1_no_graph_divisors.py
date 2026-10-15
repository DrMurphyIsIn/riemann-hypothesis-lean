"""Lemma S step 1 sanity checks (the proof is in LEMMA_S_STEP1).
(a) Monodromy: phi(x) = max(0, <J,x>) for a ray crease, transported by the diagonal dilation delta(x) = p x,
    becomes phi(x/p) = phi(x)/p: the jump J becomes J/p (not equal modulo affine functions unless J = 0).
(b) Balancing at a ray/fibre crossing: for a continuous PL function with creases on the ray (direction (1,mu))
    and the vertical fibre through a point, the ray-jump coefficient is the same on both sides of the fibre.
    We verify by brute force: build PL functions from 4 sector gradients, impose continuity, and solve.
conjecture1_proved = False."""
import numpy as np, itertools
p, mu = 2.0, 1.5
J = np.array([mu, -1.0])
phi = lambda x: max(0.0, J @ x)
x = np.array([0.7, 0.9])
print("(a) phi(x/p) =", phi(x / p), " phi(x)/p =", phi(x) / p, " -> jump J/p after one diagonal loop")
# (b) vertex at origin; rays: ray-out d1=(1,mu), fibre-up d2=(0,1), ray-in d3=(-1,-mu), fibre-down d4=(0,-1)
# sectors S1 between d1,d2; S2 between d2,d3; S3 between d3,d4; S4 between d4,d1 with gradients g1..g4 (8 unknowns).
# continuity across each boundary ray d: (g_after - g_before) . d = 0.
dirs = [np.array([1, mu]), np.array([0, 1.0]), np.array([-1, -mu]), np.array([0, -1.0])]
# boundary k separates sector k-1 (before) and sector k (after); sector order S4|d1|S1|d2|S2|d3|S3|d4|S4
A = []
pairs = [(3, 0, 0), (0, 1, 1), (1, 2, 2), (2, 3, 3)]   # (before, after, dir index)
for b, a_, k in pairs:
    row = np.zeros(8); row[2*a_:2*a_+2] = dirs[k]; row[2*b:2*b+2] = -dirs[k]; A.append(row)
A = np.array(A)
null = np.linalg.svd(A)[2][np.linalg.matrix_rank(A):]
n_ray = np.array([mu, -1.0])
for v in null:
    g = v.reshape(4, 2)
    c_out = (g[0] - g[3]) @ n_ray / (n_ray @ n_ray)    # jump across ray-out, along its normal
    c_in = (g[1] - g[2]) @ n_ray / (n_ray @ n_ray)     # jump across ray-in (same orientation)
    print(f"(b) solution: ray-out jump {c_out:+.6f}, ray-in jump {c_in:+.6f}")
