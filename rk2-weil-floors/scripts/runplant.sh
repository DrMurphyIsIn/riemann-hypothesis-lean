#!/bin/bash
# usage: runplant.sh TAG...  -- nanoda on exp/TAG_planted_cfg.json (made by controls.py plant); each MUST FAIL (rc != 0 at def_eq)
source "$(dirname "$0")/env.sh"
for t in "$@"; do
  echo "=== planted $t (MUST FAIL) $(date +%T)" >> "$PKG/logs/controls.log"
  ( /usr/bin/time -p $LOCK "$NANODA" "$PKG/exp/${t}_planted_cfg.json" ) > "$PKG/exp/${t}_planted.nanoda" 2>&1
  rc=$?
  grep -v "^\s*$" "$PKG/exp/${t}_planted.nanoda" | egrep -i "assert|panick|error|Checked|real|tc.rs|duplicate" | head -6 >> "$PKG/logs/controls.log"
  echo "=== rc $rc $(date +%T)" >> "$PKG/logs/controls.log"
done
