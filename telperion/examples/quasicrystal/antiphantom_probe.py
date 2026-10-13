"""ANTI-PHANTOM PROBE for the zoo's Ramanujan-tau re-derivation (ROUTE A, A1b).

`zoo._delta_tau_upto` computes tau from the definition Delta = q prod (1-q^m)^24 and
cross-checks the result against two arithmetic laws structurally independent of the
q-expansion recursion (the Hecke recursion tau(p^2) = tau(p)^2 - p^11 and coprime
multiplicativity).  A gate nobody has ever seen fire is not a gate, so this probe
CORRUPTS the eta exponent 24 -> 23 and asserts that the cross-checks REFUSE.

Exit 0 = the gate fired (good).  Exit 1 = the gate is inert (a finding).

Run:  python antiphantom_probe.py

conjecture1_proved = False.
"""
from __future__ import annotations

import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent


def _corrupted_tau_fn(exponent: int = 23):
    """Re-exec zoo's `_delta_tau_upto` source with the eta exponent corrupted."""
    src = (_HERE / "zoo.py").read_text(encoding="utf-8")
    start = src.index("def _delta_tau_upto")
    end = src.index("def _load_delta")
    body = src[start:end].replace("range(24)", f"range({exponent})")
    if f"range({exponent})" not in body:
        raise SystemExit("PROBE BROKEN: could not corrupt the eta exponent")
    ns: dict = {}
    exec("import math\n" + body, ns)  # noqa: S102 - probing our own source by design
    return ns["_delta_tau_upto"]


def main() -> int:
    sys.path.insert(0, str(_HERE))
    import zoo  # noqa: E402

    genuine = zoo._delta_tau_upto(30)
    if genuine[2] != -24 or genuine[4] != -1472:
        print(f"PROBE FAILED: genuine tau disagrees with the literature: "
              f"tau(2)={genuine[2]}, tau(4)={genuine[4]}")
        return 1
    print(f"genuine eta product OK: tau(2)={genuine[2]}, tau(4)={genuine[4]}")

    for exponent in (23, 25, 12):
        try:
            _corrupted_tau_fn(exponent)(30)
        except AssertionError as exc:
            print(f"exponent 24 -> {exponent}: REFUSED as designed -- {exc}")
        else:
            print(f"*** ANTI-PHANTOM GATE IS INERT at exponent {exponent}: a wrong "
                  f"eta product produced a tau the cross-checks accepted ***")
            return 1
    print("anti-phantom gate OK: every corrupted eta exponent was refused")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
