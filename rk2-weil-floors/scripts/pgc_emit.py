"""RK-2 C: emit a PGC (packed Gram certificate) Lean instance for one Arb head (rk1 rk_fz head_par{p}.pkl).

Box (exact integers, from the Arb balls of the UPPER triangle, mirrored; the true head is symmetric so each upper ball also encloses
its mirror):  M_ij = round(mid_ij * S),  w = 1 + max_ij (ceil(rad_ij * S) + ceil|mid_ij * S - M_ij|),  S = 2^(2s);
then |A_ij - M_ij/S| <= w/S.
Factor: L = rk1 rk_bchol.factor (blocked midpoint Cholesky, C-level arb_mat work, at the head's precision) of A - c'I with
c' = lambda_A_lower(chol_par{p}.json) * (1 - SHIFT), rounded to integers at scale 2^s.  cS = floor(c' S).
Residual R = M - cS I - L L^T exactly (fmpz_mat); bK, bE = bit lengths of max|L|, max|R| plus one (so every L entry is in
[-2^(bK-1), 2^(bK-1)) and every R entry in [-2^(bE-1), 2^(bE-1))); rho = m (w + 2^(bE-1)); floor = (cS - rho)/S.
Packing (base X = 2^B, offset H = 2^(B-1)): row_i = sum_j (M_ij + H) X^j;  col_k = sum_{j < m} (L_jk + H) X^j (full length,
L_jk = 0 for j < k); numerals above CHUNK bits are emitted as a balanced (hi <<< k) ||| lo tree.
Nothing here is trusted: the Lean kernel re-derives the per-entry bound |R_ij| <= 2^(bE-1) from the packed data (RK2.paramsOK,
RK2.blk; RK2.rowOK_spec) and RK2.pgc_floor does the rest.
Usage: pgc_emit.py HEAD.pkl NAME OUT.lean OUT.json [--forge F] [--rowsblk N]          conjecture1_proved = False."""
import os, sys, json, pickle, math, time, resource, argparse
os.environ["OPENBLAS_NUM_THREADS"] = "1"
PKG = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RK1 = os.environ.get("RK1_SCRIPTS", os.path.join(PKG, "..", "..", "..", "rk1", "scripts"))   # rh-team/rk1/scripts
sys.path.insert(0, RK1)
sys.path.insert(0, os.path.join(RK1, "y1copy"))
from flint import arb, ctx, arb_mat, fmpz_mat
import rk_bchol                                   # read-only import of rk1's blocked factor (unmodified)
sys.set_int_max_str_digits(0)

SHIFT = "5e-5"         # c' = lambda_A_lower * (1 - SHIFT)
RHO_BUDGET = 4e-5      # target rho/S <= RHO_BUDGET * c'


def teamrel(p):
    """a path relative to the rh-team root (no absolute paths in generated files)"""
    p = os.path.abspath(p)
    i = p.find("/rk1/")
    return p[i + 1:] if i >= 0 else os.path.relpath(p)


def ceil_shift(x, k):
    """ceil(x * 2^k) for integers x, k (k may be negative)."""
    return x << k if k >= 0 else -((-x) >> (-k))


CHUNK = 16384      # bits per literal chunk (Lean decodes a numeral in time quadratic in its length)


def natlit(v, lo=0, n=None):
    """a Lean ℕ term for v: one hex numeral if short, else a balanced tree (hi <<< k) ||| lo of CHUNK-bit numerals."""
    if n is None:
        n = max(1, -(-v.bit_length() // CHUNK))
    if n == 1:
        return f"0x{v:x}"
    h = n // 2
    k = h * CHUNK
    return f"(({natlit(v >> k, n=n - h)}) <<< {k} ||| {natlit(v & ((1 << k) - 1), n=h)})"


def round_shift(x, k):
    if k >= 0:
        return x << k
    q, r = divmod(x, 1 << (-k))
    return q + (1 if 2 * r >= (1 << (-k)) else 0)


def load_box(d, s2):
    m, bl = d["m"], d["blocks"]
    M = [[0] * m for _ in range(m)]
    wmax = 0
    for (I, J), ents in d["head"].items():
        (a, b), (c, e) = bl[I], bl[J]
        for r in range(a, b):
            for q in range(c, e):
                if r > q:
                    continue
                mm, me, rm, re_ = ents[(r - a) * (e - c) + (q - c)]
                mm, me, rm, re_ = int(mm), int(me), int(rm), int(re_)
                v = round_shift(mm, me + s2)
                # |mid*S - v| <= ceil(|mm*2^(me+s2) - v|)
                if me + s2 >= 0:
                    err = 0
                else:
                    k = -(me + s2)
                    err = ceil_shift(abs(mm - (v << k)), -k)
                wv = ceil_shift(rm, re_ + s2) + err
                M[r][q] = M[q][r] = v
                wmax = max(wmax, wv)
    return M, 1 + wmax


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("head"); ap.add_argument("name"); ap.add_argument("out_lean"); ap.add_argument("out_json")
    ap.add_argument("--forge", default=None, help="raise cS by this relative amount (forged-certificate control)")
    ap.add_argument("--rowsblk", type=int, default=0)
    ap.add_argument("--s", type=int, default=0)
    a = ap.parse_args()
    t0 = time.time()
    D = os.path.dirname(a.head); par = a.head.split("head_par")[1][0]
    ch = json.load(open(os.path.join(D, f"chol_par{par}.json")))
    d = pickle.load(open(a.head, "rb"))
    m, prec = d["m"], d["prec"]
    ctx.prec = prec
    lamA = arb(ch["lambda_A_lower"].split(" ")[0].strip("["))
    cp = (lamA * (1 - arb(SHIFT))).mid()
    cpf = float(cp)
    s = a.s or int(math.ceil(math.log2(m ** 1.5 / (RHO_BUDGET * cpf)))) + 4
    s2 = 2 * s
    S = 1 << s2
    M, w = load_box(d, s2)
    # factor of A - c'I on midpoints (rk1 rk_bchol, unmodified)
    A, bl, _, _ = rk_bchol.load(a.head)
    Lb = rk_bchol.factor(A, bl, cp)
    assert Lb is not None, "pivot failure"
    L = [[0] * m for _ in range(m)]
    for (I, K), blkm in Lb.items():
        (i0, i1), (k0, k1) = bl[I], bl[K]
        E = blkm.entries()
        nc = k1 - k0
        for i in range(i0, i1):
            for k in range(k0, k1):
                if k <= i:
                    mm, me = E[(i - i0) * nc + (k - k0)].mid().man_exp()
                    L[i][k] = round_shift(int(mm), int(me) + s)
    del A, Lb
    cm, ce = cp.man_exp()
    cS = int(cm) << (int(ce) + s2) if int(ce) + s2 >= 0 else int(cm) >> (-(int(ce) + s2))
    if a.forge:
        cS = int(cS * (1 + float(a.forge)))
    Mm = fmpz_mat(m, m, [M[i][j] for i in range(m) for j in range(m)])
    Lm = fmpz_mat(m, m, [L[i][k] for i in range(m) for k in range(m)])
    P = Lm * Lm.transpose()
    Rm = Mm - P
    Rl = Rm.entries()
    Emax = 0
    for i in range(m):
        for j in range(m):
            v = int(Rl[i * m + j]) - (cS if i == j else 0)
            if abs(v) > Emax:
                Emax = abs(v)
    Kmax = max(abs(L[i][k]) for i in range(m) for k in range(i + 1))
    Mmax = max(abs(M[i][j]) for i in range(m) for j in range(m))
    bK = Kmax.bit_length() + 1          # every L entry in [-2^(bK-1), 2^(bK-1))
    bE = Emax.bit_length() + 1          # every residual entry in [-2^(bE-1), 2^(bE-1))
    K, E = 1 << (bK - 1), 1 << (bE - 1)
    B = max(Mmax.bit_length(), (cS + m * K * K + E).bit_length()) + 2
    H = 1 << (B - 1)
    assert Mmax < H and cS + m * K * K + E < H and bK < B and bE < B
    rho = m * (w + E)
    floor_num = cS - rho
    rows = []
    for i in range(m):
        v = 0
        for j in reversed(range(m)):
            v = (v << B) + (M[i][j] + H)
        rows.append(v)
    cols = []
    for k in range(m):
        v = 0
        for j in reversed(range(m)):
            v = (v << B) + ((L[j][k] if j >= k else 0) + H)
        cols.append(v)
    # blocks of rows (bound the kernel cache: about 2 m (m B / 8) bytes retained per row)
    rowbytes = 2 * m * (m * B / 8)
    nb = a.rowsblk or 10
    blocks = []
    i = 0
    while i < m:
        n = min(nb, m - i)
        blocks.append((i, n))
        i += n
    flo = floor_num / S
    pub = None
    if floor_num > 0:
        e10 = math.floor(math.log10(flo))
        pn = (floor_num * 10 ** (5 - e10)) // S if 5 - e10 >= 0 else floor_num // (S * 10 ** (e10 - 5))
        pub = (pn, e10 - 5)          # published = pn * 10^(e10-5), rounded down, 6 significant digits
    rep = dict(name=a.name, head=teamrel(a.head), m=m, prec=prec, s=s, S_log2=s2, B=B, w=w, cS=str(cS), rho=str(rho),
               bK=bK, bE=bE, Kmax=str(Kmax), Emax=str(Emax), floor=flo, floor_rel_to_arb=flo / float(lamA),
               arb_lambda_A=ch["lambda_A_lower"], forge=a.forge, blocks=len(blocks), rows_per_block=nb, pub=pub)
    # ---- Lean
    out = []
    out.append("import RK2PGC\n\n")
    out.append(f"/-! RK-2 C PGC instance `{a.name}` (generated by rk2/C/scripts/pgc_emit.py; m = {m}, S = 2^{s2}, B = {B}).\n"
               f"Head: {teamrel(a.head)}.  Arb lambda_A (rk1 chol_par{par}.json) = {ch['lambda_A_lower'].replace('+/-', '±')}.\n"
               f"The box hypothesis `hbox` (the head lies within w/S of Mz/S entrywise) is the ARB trust seam, never asserted here.\n"
               f"conjecture1_proved = False. -/\n\n")
    out.append("set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 2048\n\n")
    out.append(f"namespace RK2.{a.name}\n\nopen RK2\n\n")
    for i, v in enumerate(rows):
        out.append(f"def r{i} : ℕ := {natlit(v)}\n")
    out.append("def rows : List ℕ := [" + ", ".join(f"r{i}" for i in range(m)) + "]\n\n")
    for k, v in enumerate(cols):
        out.append(f"def c{k} : ℕ := {natlit(v)}\n")
    out.append("def cols : List ℕ := [" + ", ".join(f"c{k}" for k in range(m)) + "]\n\n")
    out.append(f"def D : Dat := {{ B := {B}, m := {m}, cS := {cS}, bK := {bK}, bE := {bE}, rows := rows, cols := cols }}\n\n")
    out.append("theorem hp : paramsOK D = true := by decide +kernel\n\n")
    for t, (i0, n) in enumerate(blocks):
        out.append(f"theorem b{t} : blk D {i0} {n} = true := by decide +kernel\n")
    out.append("\n")
    acc = blocks[0][1]
    prev = "b0"
    for t in range(1, len(blocks)):
        i0, n = blocks[t]
        out.append(f"theorem h{t} : blk D 0 {acc + n} = true := blk_append D 0 {acc} {n} {prev} b{t}\n")
        acc += n; prev = f"h{t}"
    assert acc == m
    out.append(f"\ntheorem hall : blk D 0 {m} = true := {prev}\n\n")
    out.append(f"/-- Every real matrix in the box has the quadratic floor (cS - ρ)/S, ρ = m (w + 2^(bE-1)). -/\n"
               f"theorem floor (G : Fin {m} → Fin {m} → ℝ)\n"
               f"    (hbox : ∀ i j : Fin {m}, |G i j - (Mz D i j : ℝ) / (2 : ℝ) ^ {s2}| ≤ (({w} : ℕ) : ℝ) / (2 : ℝ) ^ {s2}) (x : Fin {m} → ℝ) :\n"
               f"    ((({cS} : ℤ) - {rho} : ℤ) : ℝ) / (2 : ℝ) ^ {s2} * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * G i j * x j :=\n"
               f"  pgc_floor D hp hall {w} {rho} (by decide +kernel) _ (by positivity) G hbox x\n\n")
    if pub is not None:
        pn, pe = pub
        if pe >= 0:
            pubn, pubd = pn * 10 ** pe, 1
        else:
            pubn, pubd = pn, 10 ** (-pe)
        rep["pub_num"], rep["pub_den"] = str(pubn), str(pubd)
        out.append(f"/-- The published floor {pn}e{pe} (rounded down). -/\n"
                   f"theorem floor_pub (G : Fin {m} → Fin {m} → ℝ)\n"
                   f"    (hbox : ∀ i j : Fin {m}, |G i j - (Mz D i j : ℝ) / (2 : ℝ) ^ {s2}| ≤ (({w} : ℕ) : ℝ) / (2 : ℝ) ^ {s2}) (x : Fin {m} → ℝ) :\n"
                   f"    (({pubn} : ℝ) / {pubd}) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * G i j * x j := by\n"
                   f"  refine le_trans ?_ (floor G hbox x)\n"
                   f"  have hx : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (x i))\n"
                   f"  have hc : ({pubn} : ℝ) / {pubd} ≤ ((({cS} : ℤ) - {rho} : ℤ) : ℝ) / (2 : ℝ) ^ {s2} := by norm_num\n"
                   f"  exact mul_le_mul_of_nonneg_right hc hx\n\n")
    out.append(f"end RK2.{a.name}\n")
    txt = "".join(out)
    open(a.out_lean, "w").write(txt)
    ru = resource.getrusage(resource.RUSAGE_SELF)
    rep.update(bytes=len(txt), cpu_seconds=ru.ru_utime + ru.ru_stime, wall_seconds=round(time.time() - t0, 1),
               maxrss_MB=ru.ru_maxrss / 1e6)
    json.dump(rep, open(a.out_json, "w"), indent=1)
    print(json.dumps({k: rep[k] for k in ("name", "m", "s", "B", "floor", "floor_rel_to_arb", "blocks", "bytes", "cpu_seconds")}))


if __name__ == "__main__":
    main()
