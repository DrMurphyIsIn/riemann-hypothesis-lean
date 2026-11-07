"""collect per-cell numbers for the trust table (re-runs asm_emit into work/, does not touch inst/)"""
import json, subprocess
import os
C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # the package root
RK1OUT = os.environ.get("RK1_OUT", os.path.join(C, "..", "..", "..", "rk1", "out"))
cells = [("K4_L1","R_K-4_L1.0","kernel"),("K3_L1","R_K-3_L1.0","kernel"),("K20_L1","R_K-20_L1.0","kernel"),("K23_L1","R_K-23_L1.0","kernel"),
 ("K20_L145","R_K-20_L1.45","kernel"),("EP5_L145","R_EP5_L1.45","kernel"),("K20_L1494","R_K-20_L1.493945","kernel"),
 ("K20_L2","R_K-20_L2.0","kernel"),("K23_L2","R_K-23_L2.0","kernel"),("K4_L2","R_K-4_L2.0","kernel"),("K3_L2","R_K-3_L2.0","kernel"),
 ("K20_L225","R_K-20_L2.25","arb"),("K23_L225","R_K-23_L2.25","arb"),("K4_L225","R_K-4_L2.25","arb"),("K3_L225","R_K-3_L2.25","arb"),
 ("K20_L24","R_K-20_L2.4","arb"),("K23_L24","R_K-23_L2.4","arb"),("K4_L24","R_K-4_L2.4","arb")]
rows = []
for n, d, mode in cells:
    args = ["python3", f"{C}/scripts/asm_emit.py", f"Asm_{n}", os.path.join(RK1OUT, d), f"{C}/work/Asm_{n}.lean", mode]
    if mode == "kernel":
        args += [f"{C}/json/{n}_even.json", f"{C}/json/{n}_odd.json"]
    r = json.loads(subprocess.check_output(args))
    r["dir"] = d
    if mode == "kernel":
        for par in ("even", "odd"):
            j = json.load(open(f"{C}/json/{n}_{par}.json"))
            r[f"m_{par}"] = j["m"]; r[f"S_{par}"] = j["S_log2"]; r[f"B_{par}"] = j["B"]; r[f"blocks_{par}"] = j["blocks"]
            r[f"floor_{par}"] = j["floor"]; r[f"rel_{par}"] = j["floor_rel_to_arb"]
    rows.append(r)
json.dump(rows, open(f"{C}/work/summary.json", "w"), indent=1)
for r in rows:
    print(f"{r['cell']:16s} {r['mode']:6s} pub {r['published']:.6g}  rel_to_cert {r['published_rel_to_cert']:.7f}")
