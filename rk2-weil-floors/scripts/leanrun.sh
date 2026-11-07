#!/bin/bash
# plain lean (no lake) against $LEAN_ENV plus the package build dir; usage: leanrun.sh <lean args...>
source "$(dirname "$0")/env.sh"
[ -n "$LEAN_ENV" ] || { echo "set LEAN_ENV to a built Lean v4.34.1 + Mathlib d13f23b project" >&2; exit 2; }
LP=$PKG/build:$LEAN_ENV/.lake/build/lib/lean
for d in "$LEAN_ENV"/.lake/packages/*/.lake/build/lib/lean; do LP=$LP:$d; done
TC=$(dirname "$(dirname "$(command -v lean)")")
export LEAN_PATH=$TC/lib/lean:$LP
exec "$@"
