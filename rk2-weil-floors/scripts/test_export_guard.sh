#!/bin/bash
# bb REVIEW_RK2_C R-1 test: the export guard must FAIL on an empty or failed export and on "Checked 0"; must pass a good case.
# Run from anywhere; uses only package-relative paths (work/guardtest) and $NANODA.
source "$(dirname "$0")/env.sh"
G="$PKG/scripts/check_export.sh"; T=$PKG/work/guardtest; mkdir -p "$T"; P=0; F=0
rel() { sed "s#$PKG/##g"; }
expect() { want=$1; shift; "$@" > "$T/out.txt" 2>&1; got=$?; if { [ $want = fail ] && [ $got != 0 ]; } || { [ $want = ok ] && [ $got = 0 ]; }; then echo "PASS ($want): $* -> $(cat "$T/out.txt")" | rel; P=$((P+1)); else echo "TEST FAILED ($want, got rc $got): $*" | rel; F=$((F+1)); fi; }
: > "$T/empty.ndjson"
expect fail "$G" export "$T/empty.ndjson" 0                   # empty export, rc 0
expect fail "$G" export "$T/empty.ndjson" 1                   # failed export
head -c 2000000 /dev/zero > "$T/big.ndjson"
expect fail "$G" export "$T/big.ndjson" 1                     # big but failed
expect ok   "$G" export "$T/big.ndjson" 0                     # positive control (size + rc only)
# nanoda itself on the empty export reports "Checked 0 declarations" with rc 0: the guard must FAIL it
printf '{"export_file_path": "%s", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true, "print_success_message": true, "print_axioms": false}' "$T/empty.ndjson" > "$T/empty_cfg.json"
$LOCK "$NANODA" "$T/empty_cfg.json" > "$T/empty.nanoda" 2>&1; nrc=$?
echo "nanoda on the empty export: rc $nrc, $(grep -o 'Checked [0-9]* declarations[a-z ]*' "$T/empty.nanoda")"
expect fail "$G" nanoda "$T/empty.ndjson" "$T/empty.nanoda" $nrc
echo "Checked 5 declarations with no errors" > "$T/good.nanoda"
expect ok   "$G" nanoda "$T/big.ndjson" "$T/good.nanoda" 0    # positive control
expect fail "$G" nanoda "$T/big.ndjson" "$T/good.nanoda" 101  # nanoda rejection
# end to end: a module that fails to export must make run_export.sh exit 1 without running nanoda
expect fail "$PKG/scripts/run_export.sh" NoSuchModule guardtest_e2e RK2.nothing
grep -q "nanoda guardtest_e2e NOT RUN: export guard FAIL" "$PKG/logs/nanoda.log" && { echo "PASS: e2e logged NOT RUN"; P=$((P+1)); } || { echo "TEST FAILED: e2e log"; F=$((F+1)); }
rm -f "$PKG"/exp/guardtest_e2e.* "$PKG/logs/guardtest_e2e.XDONE"; rm -rf "$T"
echo "guard tests: $P passed, $F failed"; [ $F = 0 ]
