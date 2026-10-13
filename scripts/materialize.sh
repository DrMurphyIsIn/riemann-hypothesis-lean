#!/bin/bash
# Clone the Arda development repository at the commit recorded in formalization/ARDA_SOURCE into work/arda and
# check that this repository's telperion/ copy matches it: every file byte-identical, except the files listed in
# CENSORING.md, which may differ only in comments, docstrings and prose (scripts/check_telperion_copy.py checks
# Python files by syntax tree and Lean files with comments stripped). Needs git and python3 (3.9 or later).
#
#   scripts/materialize.sh            # network: clone + check
#
# The Lean islands build from either tree; their code is the same. From this repository:
#   cd telperion/examples/weil_form_enclosure/lean && lake exe cache get && lake build && lake env lean AxiomGuardRRSquare.lean
#   cd telperion/examples/dbn/lean                 && lake exe cache get && lake build && lake env lean AxiomGuardDBN.lean
#   cd telperion/examples/rvm_bridge/lean          && lake exe cache get && lake build && lake env lean AxiomGuardRvMBridge.lean
#     # HODGE-1: then `lake build <m>` for each m in hodge1_heavy_modules.txt, one at a time, and
#     #          lake env lean Hodge1_Guard.lean
#   telperion/examples/oai_qrh_bridge/materialize.sh     # fetches openai/math at its pin (hash-checked)
#   telperion/examples/liu_dbn_bridge/liu_materialize.sh # fetches openai/math and Baiying Liu's Lean at their pins
# .github/workflows/verify.yml runs all of this; formalization/README.md lists what each guard must print.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
eval "$(grep -E '^(source_repo|source_commit)=' "$HERE/formalization/ARDA_SOURCE")"
[ "$(cat "$HERE/telperion/SYNC")" = "$source_commit" ] || { echo "telperion/SYNC and formalization/ARDA_SOURCE disagree"; exit 1; }
ARDA="$HERE/work/arda"
mkdir -p "$HERE/work"; rm -rf "$ARDA"
git clone --filter=blob:none --no-checkout "$source_repo" "$ARDA"
git -C "$ARDA" checkout --detach "$source_commit"
python3 "$HERE/scripts/check_telperion_copy.py" "$ARDA"
echo "Materialized $source_repo @ $source_commit at $ARDA; telperion/ matches it up to the comment rewording listed in CENSORING.md."
