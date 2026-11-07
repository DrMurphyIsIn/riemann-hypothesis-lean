#!/bin/bash
# usage: check_export.sh STAGE EXPORT [EXPORT_RC | NANODA_OUT NANODA_RC]
#   STAGE=export : FAIL unless the lean4export rc is 0 and the export is >= 1 MB
#   STAGE=nanoda : FAIL unless nanoda rc is 0 and it reports "Checked N declarations with no errors" with N > 0
# Exit 0 = OK, exit 1 = FAIL (and prints FAIL).  Guards the vacuous pass (an empty export is "Checked 0").  bb REVIEW_RK2_C R-1.
STAGE=$1; EXP=$2
if [ "$STAGE" = export ]; then
  RC=$3; SZ=$(stat -f %z "$EXP" 2>/dev/null || echo 0)
  if [ "$RC" != 0 ]; then echo "FAIL export rc $RC ($(basename "$EXP"))"; exit 1; fi
  if [ "$SZ" -lt 1000000 ]; then echo "FAIL export $(basename "$EXP") has $SZ bytes (< 1 MB)"; exit 1; fi
  echo "OK export $SZ bytes"; exit 0
else
  OUT=$3; RC=$4
  N=$(grep -o "Checked [0-9]* declarations with no errors" "$OUT" | grep -o "[0-9]*" | head -1)
  if [ "$RC" != 0 ]; then echo "FAIL nanoda rc $RC ($(basename "$EXP"))"; exit 1; fi
  if [ -z "$N" ] || [ "$N" -le 0 ]; then echo "FAIL nanoda checked ${N:-no} declarations ($(basename "$EXP"))"; exit 1; fi
  echo "OK nanoda checked $N declarations"; exit 0
fi
