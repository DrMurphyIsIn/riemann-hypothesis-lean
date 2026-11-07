#!/bin/bash
# usage: run_queue.sh TAG NAME...  -- compile sequentially (one lean at a time); writes logs/TAG.QDONE at the end
source "$(dirname "$0")/env.sh"
TAG=$1; shift
for N in "$@"; do rm -f "$PKG/logs/$N.DONE"; "$PKG/scripts/run1.sh" $N; done
echo done > "$PKG/logs/$TAG.QDONE"
