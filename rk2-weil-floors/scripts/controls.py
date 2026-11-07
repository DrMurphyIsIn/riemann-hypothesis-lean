"""RK-2 C controls (PREREG §3).
forge NAME     : write controls/CTRL_forged_NAME.lean = the honest instance with cS raised by 1e-3 relative, so the claimed floor
                 (cS' - rho)/S exceeds the Arb lambda_A of the head; every row check must then fail (`decide` proves it false).
plant TAG NAME : in exp/TAG.ndjson, change the leading digit of the Nat literal of row r_{m//2} of instance NAME (a literal that
                 occurs ONCE in the export) so that the planted value is ABSENT from the export; write exp/TAG_planted.ndjson.
                 nanoda must then fail at the type checker (def_eq), not at the parser.
conjecture1_proved = False."""
import sys, json, re
sys.set_int_max_str_digits(0)
import os
C = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # the package root


def forge(name):
    j = json.load(open(f"{C}/json/{name}.json"))
    txt = open(f"{C}/lean/{name}.lean").read()
    cS = j["cS"]
    cS2 = str(int(cS) + int(cS) // 1000)
    n = txt.count(cS)
    txt = txt.replace(cS, cS2).replace(f"namespace RK2.{name}", f"namespace RK2.CTRL_forged_{name}").replace(
        f"end RK2.{name}", f"end RK2.CTRL_forged_{name}")
    open(f"{C}/lean/CTRL_forged_{name}.lean", "w").write(txt)
    flo = (int(cS2) - int(j["rho"])) / 2 ** j["S_log2"]
    print(json.dumps(dict(name=name, cS=cS, cS_forged=cS2, occurrences=n, claimed_floor=flo, arb=j["arb_lambda_A"])))


def plant(tag, name):
    j = json.load(open(f"{C}/json/{name}.json"))
    i = j["m"] // 2
    src = open(f"{C}/lean/{name}.lean").read()
    mt = re.search(rf"^def r{i} : ℕ := 0x([0-9a-f]+)$", src, re.M)
    v = int(mt.group(1), 16)
    sv = str(v)
    exp = open(f"{C}/exp/{tag}.ndjson").read()
    occ = exp.count(sv)
    assert occ == 1, ("literal occurrences", occ)
    lead = int(sv[0])
    new = str((lead % 9) + 1) + sv[1:]
    assert new != sv and exp.count(new) == 0
    open(f"{C}/exp/{tag}_planted.ndjson", "w").write(exp.replace(sv, new))
    cfg = json.load(open(f"{C}/exp/{tag}_cfg.json"))
    cfg["export_file_path"] = f"{C}/exp/{tag}_planted.ndjson"
    json.dump(cfg, open(f"{C}/exp/{tag}_planted_cfg.json", "w"))
    print(json.dumps(dict(tag=tag, name=name, row=i, digits=len(sv), occurrences_before=occ, planted_absent=True,
                          old_lead=sv[0], new_lead=new[0])))


if __name__ == "__main__":
    if sys.argv[1] == "forge":
        forge(sys.argv[2])
    else:
        plant(sys.argv[2], sys.argv[3])
