#!/bin/bash
# usage: run_export.sh MODULE TAG DECL...  -- lean4export MODULE (from build/) then nanoda; log to logs/nanoda.log; md5 kept.
# ABORTS (exit 1, FAIL in the log) on a failed or < 1 MB export, or on nanoda rc != 0 / "Checked 0" (scripts/check_export.sh; bb R-1).
source "$(dirname "$0")/env.sh"
G="$PKG/scripts/check_export.sh"; E=$PKG/exp; LOG=$PKG/logs/nanoda.log
MOD=$1; TAG=$2; shift 2
cd "$PKG/build"
echo "=== export $TAG ($MOD: $*) $(date +%T)" >> "$LOG"
( /usr/bin/time -p env LEAN_ABORT_ON_PANIC=1 $LOCK "$PKG/scripts/leanrun.sh" "$LEAN4EXPORT" $MOD -- "$@" > "$E/$TAG.ndjson" ) 2> "$E/$TAG.err"
erc=$?
echo "export rc $erc bytes $(stat -f %z "$E/$TAG.ndjson") md5 $(md5 -q "$E/$TAG.ndjson")" >> "$LOG"
grep real "$E/$TAG.err" >> "$LOG"
if ! "$G" export "$E/$TAG.ndjson" $erc >> "$LOG"; then echo "nanoda $TAG NOT RUN: export guard FAIL $(date +%T)" >> "$LOG"; echo FAIL > "$PKG/logs/$TAG.XDONE"; exit 1; fi
printf '{"export_file_path": "%s", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true, "print_success_message": true, "print_axioms": false}' "$E/$TAG.ndjson" > "$E/${TAG}_cfg.json"
( /usr/bin/time -l $LOCK "$NANODA" "$E/${TAG}_cfg.json" ) > "$E/$TAG.nanoda" 2>&1
rc=$?
egrep "Checked|error|panick|real|maximum resident" "$E/$TAG.nanoda" | head -8 >> "$LOG"
echo "nanoda $TAG rc $rc $(date +%T)" >> "$LOG"
if ! "$G" nanoda "$E/$TAG.ndjson" "$E/$TAG.nanoda" $rc >> "$LOG"; then echo FAIL > "$PKG/logs/$TAG.XDONE"; exit 1; fi
echo $rc > "$PKG/logs/$TAG.XDONE"
