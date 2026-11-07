# sourced by the package scripts.  All paths are relative to the package root PKG; external tools come from the environment:
#   LEAN_ENV     a built Lean v4.34.1 + Mathlib d13f23b project with its own .lake (e.g. an APFS clone of rec1/kr_build)
#   LEAN4EXPORT  lean4export binary for v4.34.1 (default: lean4export on PATH)
#   NANODA       nanoda 37cb87b7 binary (default: nanoda_bin on PATH)
#   LEANLOCK     optional wrapper that serialises heavy Lean jobs (empty: run directly)
PKG=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
LEAN4EXPORT=${LEAN4EXPORT:-lean4export}
NANODA=${NANODA:-nanoda_bin}
if [ -n "$LEANLOCK" ]; then LOCK="env ARDA_LEAN_SLOTS=1 $LEANLOCK"; else LOCK=""; fi
mkdir -p "$PKG/build" "$PKG/exp" "$PKG/logs" "$PKG/work"
