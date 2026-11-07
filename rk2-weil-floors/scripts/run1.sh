#!/bin/bash
# usage: run1.sh NAME  -- compile lean/NAME.lean to build/NAME.olean, log time/RSS to logs/kernel.log
source "$(dirname "$0")/env.sh"
N=$1; cd "$PKG/lean"
echo "=== $N $(date +%T)" >> "$PKG/logs/kernel.log"
( /usr/bin/time -l $LOCK "$PKG/scripts/leanrun.sh" lean -o "$PKG/build/$N.olean" $N.lean ) > "$PKG/logs/$N.out" 2>&1
rc=$?
egrep "error|real|maximum resident" "$PKG/logs/$N.out" | head -20 >> "$PKG/logs/kernel.log"
echo "=== exit $rc $(date +%T)" >> "$PKG/logs/kernel.log"
echo $rc > "$PKG/logs/$N.DONE"
