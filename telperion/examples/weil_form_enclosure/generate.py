"""Generate the E8 Weil-form enclosure ladder: enclose -> certify -> emit -> write.

    python examples/weil_form_enclosure/generate.py            # write lean/WeilFormEnclosure.lean
    python examples/weil_form_enclosure/generate.py --check     # drift check (no write)
    python examples/weil_form_enclosure/generate.py --cross-check   # the memo's section-4 run

The registry node `RH_limit_explicit_formula` (E8, `WeilExplicit`, proved in
examples/rvm_bridge/lean/E6Bridge4.lean against Anthropic's zeta-23-lean) identifies the sum
over the zeros with `archSide g - primeSide g`.  This example EVALUATES that right-hand side --
the two pole terms, the `-g(0) log pi` term, the digamma integral and the finite prime sum --
for concrete members of the registered test class, with rigorous Arb ball arithmetic
(`telperion.weil_form_eval`), and emits the kernel CONSEQUENCE of the resulting rational
enclosure: positivity of a certified autocorrelation pairing, and Sylvester positive-
definiteness of the 2x2 Weil-Gram block of a test pair.

Test functions (both in the E8 class: smooth, compactly supported, real):

    g_w(u) = exp(-1 / (1 - (u/w)^2))   for |u| < w,   0 otherwise,     w in {1, 3/2}.

HONEST SCOPE.  A positive pairing is what RH PREDICTS for an autocorrelation; observing it
confirms NOTHING (Weil positivity over every admissible test function is RH-equivalent, and a
finite family does not approach "every").  The falsifiable direction is emitted alongside as
`weil_negative_refutes_rh`, whose RH content sits entirely in an undischarged hypothesis.
The Arb enclosures are the documented non-kernel trust seam; the emitted theorems carry them
as NAMED HYPOTHESES and the kernel proves only what follows from them.
conjecture1_proved = False.

Dependency: python-flint (see the `flint` manifest group in telperion.toml).  The archimedean
quadrature runs to |r| <= 1024 with a 5-fold integration-by-parts tail; the whole run takes a
couple of minutes.
"""
import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import ValidationReport, certify, emit  # noqa: E402
from telperion.emit_weil_form_enclosure import (  # noqa: E402
    GRAM_MINOR,
    POSITIVITY,
    WeilBox,
    WeilFormEnclosureData,
    WeilFormEnclosureEmitter,
    weil_form_enclosure_family,
    weil_form_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.weil_form_eval import (  # noqa: E402
    GaussianSpec,
    WeilTestSpec,
    enclose_weil_gram,
    gaussian_cross_check,
    round_outward,
)

PREC_BITS = 56
ARCH_T = 1024
N_BYPARTS = 5
SIG = 12
MAX_WIDTH = Fraction(1, 100000)          # 1e-5: a box wider than this carries no consequence
_HERE = Path(__file__).resolve().parent
_OUT = _HERE / "lean" / "WeilFormEnclosure.lean"
_DEFS = _HERE / "lean" / "WeilFormDefs.lean"
_MIRROR_SOURCE = _HERE.parent / "rvm_bridge" / "lean" / "E6Bridge4.lean"
_CROSSCHECK = _HERE / "crosscheck.json"

SPECS = (
    WeilTestSpec("bump_w1", width=Fraction(1)),
    WeilTestSpec("bump_w3o2", width=Fraction(3, 2)),
)


def _extract_weilexplicit(text: str) -> str:
    """The `namespace WeilExplicit ... end WeilExplicit` block, for the mirror drift gate."""
    # anchor on the line-initial forms: the E6Bridge4 docstring mentions the namespace in prose.
    start = text.index("\nnamespace WeilExplicit\n") + 1
    end = text.index("\nend WeilExplicit\n") + len("\nend WeilExplicit")
    return text[start:end]


def check_vocabulary_mirror() -> int:
    """Gate: this island's `WeilExplicit` block must match the proved node's, byte for byte.

    If `E6Bridge4.lean` is absent from a checkout the gate is a no-op (reported), exactly as
    the rvm_bridge drift check handles a missing registry file."""
    if not _MIRROR_SOURCE.exists():
        print(f"mirror: SKIPPED ({_MIRROR_SOURCE} not in this checkout)")
        return 0
    ours = _extract_weilexplicit(_DEFS.read_text(encoding="utf-8"))
    theirs = _extract_weilexplicit(_MIRROR_SOURCE.read_text(encoding="utf-8"))
    if ours != theirs:
        print("DRIFT: WeilFormDefs.lean's WeilExplicit block no longer matches "
              "examples/rvm_bridge/lean/E6Bridge4.lean")
        return 1
    print("mirror: OK (WeilExplicit block matches the proved E8 node byte-for-byte)")
    return 0


def build() -> str:
    gram = enclose_weil_gram(
        SPECS, prec_bits=PREC_BITS, arch_T=ARCH_T, n_byparts=N_BYPARTS)
    boxes = {}
    for (i, j), b in gram.items():
        lo, hi = round_outward(b.lo, b.hi, SIG)
        boxes[(i, j)] = WeilBox(i=i, j=j, label_i=b.label_i, label_j=b.label_j, lo=lo, hi=hi)

    radius = {i: s.width for i, s in enumerate(SPECS)}

    data_by_name = {}
    for i, s in enumerate(SPECS):
        data_by_name[f"weil_autocorr_pos_{s.label}"] = WeilFormEnclosureData(
            shape=POSITIVITY, boxes=(boxes[(i, i)],), max_width=MAX_WIDTH,
            support_radius=2 * radius[i],     # supp (autocorr g) = [-2w, 2w]
            arch_T=ARCH_T, n_byparts=N_BYPARTS)
    data_by_name["weil_gram_minor_0_1"] = WeilFormEnclosureData(
        shape=GRAM_MINOR,
        boxes=(boxes[(0, 0)], boxes[(1, 1)], boxes[(0, 1)]),
        max_width=MAX_WIDTH,
        support_radius=radius[0] + radius[1],
        arch_T=ARCH_T, n_byparts=N_BYPARTS)

    names = sorted(data_by_name)
    fam = weil_form_enclosure_family(
        "WeilFormEnclosure",
        GridSpec([("k", list(range(len(names))))]),
        lambda pt: names[pt["k"]],
        spec=lambda pt: data_by_name[names[pt["k"]]],
    )
    report = emit(
        certify(fam),
        LeanProfile(
            namespace=("WeilFormEnclosure",),
            imports=("WeilFormDefs",),
            prelude="open Complex\n\n" + weil_form_prelude_lean(),
        ),
        [WeilFormEnclosureEmitter()],
        ValidationReport(checks=(("weil_form_enclosure", True),)),
    )
    return next(iter(report.files.values()))


def cross_check() -> int:
    """The E8 design memo section-4 numerical run, reproduced with rigorous Arb zeta zeros.

    NOT a certificate and NOT Lean: the Gaussian is outside the registered (compactly
    supported) class, so `weil_form_enclosure_certificate` refuses it.  It exists to catch a
    sign or factor error in the normalisation, which would show at the 1e-1 level."""
    rows = [
        gaussian_cross_check(GaussianSpec("a02_c10", a=Fraction(1, 5), center=Fraction(1))),
        gaussian_cross_check(GaussianSpec("a025_c03", a=Fraction(1, 4), center=Fraction(3, 10))),
    ]
    _CROSSCHECK.write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
    for r in rows:
        print(f"{r['label']}: zero side {r['zero_side']} vs rhs {r['rhs']} "
              f"|diff| {r['abs_difference']}")
    print(f"wrote {_CROSSCHECK}")
    return 0


def main(*, check: bool = False, xcheck: bool = False) -> int:
    if xcheck:
        return cross_check()
    rc = check_vocabulary_mirror()
    if check:
        text = build()
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: WeilFormEnclosure.lean does not match regeneration")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return rc
    if rc:
        return rc
    text = build()
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="drift check; never writes")
    ap.add_argument("--cross-check", dest="xcheck", action="store_true",
                    help="run the memo's Gaussian zero-side/prime-side agreement report")
    args = ap.parse_args()
    raise SystemExit(main(check=args.check, xcheck=args.xcheck))
