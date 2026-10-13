#!/bin/bash
# Check the output of a Lean axiom guard (`lake env lean AxiomGuard*.lean > out`).
#   scripts/axiom_check.sh OUT FLOOR [NAME...]
# Fails unless: OUT has at least FLOOR "depends on axioms" / "does not depend on any axioms" lines (so a guard
# that elaborated to nothing cannot pass); no sorryAx appears; every listed axiom is one of propext,
# Classical.choice, Quot.sound; and each NAME (a fully qualified theorem name) is printed. Adapted from the axiom
# guards of the development repository's CI. Lean wraps long axiom lists, so lines are joined before parsing.
set -euo pipefail
out="$1"; floor="$2"; shift 2
n=$(grep -cE "depends on axioms|does not depend on any axioms" "$out" || true)
if [ "$n" -lt "$floor" ]; then echo "::error::$out: $n axiom lines, expected at least $floor"; exit 1; fi
if grep -q sorryAx "$out"; then echo "::error::$out: sorryAx present"; exit 1; fi
if tr "\n" " " < "$out" | grep -oE "depends on axioms: \[[^]]*\]" \
     | sed -E "s/depends on axioms: \[|\]//g" | tr "," "\n" | tr -d " " \
     | grep -vE "^$|^propext$|^Classical\.choice$|^Quot\.sound$"; then
  echo "::error::$out: an axiom outside [propext, Classical.choice, Quot.sound] is listed above"; exit 1; fi
for name in "$@"; do
  if ! grep -qE "'$name' (depends on axioms|does not depend on any axioms)" "$out"; then
    echo "::error::$out: no axiom line for $name"; exit 1; fi
  echo "ok: $name"
done
echo "$out: $n axiom lines, all within [propext, Classical.choice, Quot.sound]"
