#!/bin/bash
# Materialize the oai_qrh_bridge workspace: an UNMODIFIED checkout of openai/math (pinned in
# OAI_PIN) with the three Arda bridge files and one appended lean_lib stanza.  OpenAI's lakefile
# applies its own compatibility patches to its dependencies and requires OAI to be the WORKSPACE
# ROOT (its post_update hook rejects a checkout under a downstream .lake/packages), so a Lake
# git dependency on openai/math does not work; this script is the supported way in.
#
# Usage: materialize.sh [--from-local DIR]
#   default        clone openai/math at the pinned commit into work/oai (network; then
#                  `lake exe cache get` fetches Mathlib oleans, and OAI's closure is compiled).
#   --from-local   reflink-copy (cp -c, APFS) an existing built copy of openai/math's lean/
#                  directory whose sources equal the pinned commit (checked file by file
#                  against a pinned git checkout given by $OAI_GIT, default ~/oai-math).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
. "$HERE/OAI_PIN"
WORK="$HERE/work/oai"
mkdir -p "$HERE/work"
if [ "${1:-}" = "--from-local" ]; then
  SRC="$2"; GIT="${OAI_GIT:-$HOME/oai-math}"
  [ "$(git -C "$GIT" rev-parse HEAD)" = "$commit" ] || { echo "OAI_GIT is not at $commit"; exit 1; }
  # Abort unless every source file equals the pinned commit (build outputs and replay
  # scratch excluded; the lakefile must be OpenAI's unmodified one).
  diff -rq "$GIT/$subdir" "$SRC" -x .lake -x .git -x replay_configs -x replay_logs \
       -x REPLAY_REPORT.md -x ReplayChecks || { echo "source tree differs from $commit"; exit 1; }
  rm -rf "$WORK"; cp -c -R "$SRC" "$WORK" 2>/dev/null || cp -R "$SRC" "$WORK"
else
  rm -rf "$HERE/work/math"
  git clone --no-checkout "$repo" "$HERE/work/math"
  git -C "$HERE/work/math" checkout --detach "$commit"
  rm -rf "$WORK"; mv "$HERE/work/math/$subdir" "$WORK"
fi
cp "$HERE/lean/"*.lean "$WORK/"; rm -f "$WORK/lakefile-stanza.lean"
# Single-pin port: the 19 dbn modules, copied byte-identically from the dbn island, then the
# recorded patches (dbn_port/patches/*.patch, each with its reason in the doc), then the
# LiCriterion shim (dbn_port/Lc).
DBN="$HERE/../dbn/lean"
for m in DBNZeroFreeHalfplane DBNRealZerosIffFinal DBNRealZerosIff DBNDefs DBNXi DBNXiIBP \
         DBNGKernel DBNXiCos DBNXiRiemann DBNM1Parametric DBNM1Approx DBNHadamard \
         DBNHadamardLinear DBNHadamardMean DBNHadamardProduct DBNHadamardCount DBNStep \
         DBNHeatApprox DBNHurwitz; do
  cp "$DBN/$m.lean" "$WORK/$m.lean"
done
for pf in "$HERE"/dbn_port/patches/*.patch; do
  [ -e "$pf" ] || continue
  (cd "$WORK" && patch -p1 --no-backup-if-mismatch < "$pf")
done
mkdir -p "$WORK/Lc/LiCriterion"
cp "$HERE/dbn_port/Lc/XiZeros.lean" "$WORK/Lc/XiZeros.lean"
cp "$HERE/dbn_port/Lc/LiCriterion/Basic.lean" "$WORK/Lc/LiCriterion/Basic.lean"
cp "$HERE/lean/"*.comparator.json "$WORK/"
cp "$HERE/lean/negative_control/"*.lean "$HERE/lean/negative_control/"*.json "$WORK/"
cat "$HERE/lean/lakefile-stanza.lean" >> "$WORK/lakefile.lean"
[ "$(cat "$WORK/lean-toolchain")" = "$toolchain" ] || { echo "toolchain mismatch"; exit 1; }
grep -q "\"rev\": \"$mathlib\"" "$WORK/lake-manifest.json" || { echo "mathlib pin mismatch"; exit 1; }
cat <<MSG
Materialized at $WORK (openai/math $commit, $toolchain, Mathlib $mathlib).
Next, from $WORK:
  lake update            # only on a fresh clone: OAI's hooks clone + patch its dependencies
  lake exe cache get     # Mathlib oleans
  lake build ArdaQRHBridge AxiomGuardQRHBridge ArdaDBNUnconditional ArdaDBNChallenge
  lake env lean AxiomGuardQRHBridge.lean
  lake env comparator qrh_seven_eighths.comparator.json
MSG
