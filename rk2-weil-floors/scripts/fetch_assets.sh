#!/bin/bash
# usage: fetch_assets.sh [--local DIR]
#   Download the four L = 2 certificates that are too large for git (RELEASE_ASSETS.md) from the GitHub release v1.1.0,
#   decompress them into lean/, and verify the sha256 of every .xz and of every decompressed file, plus the md5 that
#   MANIFEST.md records.  --local DIR takes the .xz files from DIR instead of downloading them.
#   Any mismatch, failed download or missing tool is fatal: the script prints FAIL, removes what it wrote and exits 1.
#   A file already in lean/ with the right sha256 is kept.
set -u
PKG=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
URL=${RK2_ASSET_URL:-https://github.com/DrMurphyIsIn/riemann-hypothesis-lean/releases/download/v1.1.0}
LOCAL=""
if [ "${1:-}" = --local ]; then LOCAL=${2:?"--local needs a directory"}; fi

# name  sha256(.lean.xz)  sha256(.lean)  bytes(.lean)  md5(.lean, as in MANIFEST.md)
ASSETS="
K3_L2_even 6acfebef2e18012f7a8f10275213b6cab4b7b0a72876d25c3edb661067d92a76 2cf6f69a8ae6a93591d1df426ef98f2dd99ba430db704f30d64b5a75d01cf4a8 149800511 52b05fafa090e67de347afb473fc5c5d
K3_L2_odd 0b25459ff3211e93fb7c030fb47263d0be9c33133be75600ae01d63c14fdf14f 2f825a3dc547abf23769cc35849815b66fda7bd4a45ee78de7004a5c91bb669a 139066135 f114394d102207b7259fc59feeccbd74
K4_L2_even fb8ea245675eb513b7ec4d2f5cc5fbe0e724fab521628faba462b64b48c00a47 f89ebde373119dcec2a2ced2f3d24a7547961eb89b0dbce5b87ee6537bf7e460 87291881 7db3db13eac934137b633e0ada2ef667
K4_L2_odd 993018b69b06547dd2e332d0b2260c3b66b8775d8f103f4c8873cf31b912238f 6988ecc4b821aeec670027a2352c656232a7824851727f3959d5c37f7564ae14 79726895 50b67595663f69addede45b8ce48c96d
"

fail() { echo "FAIL: $*" >&2; rm -f "$TMP"/* 2>/dev/null; exit 1; }
if command -v sha256sum >/dev/null; then sha() { sha256sum "$1" | cut -c1-64; }
elif command -v shasum >/dev/null; then sha() { shasum -a 256 "$1" | cut -c1-64; }
else echo "FAIL: need sha256sum or shasum" >&2; exit 1; fi
if command -v md5sum >/dev/null; then md5of() { md5sum "$1" | cut -c1-32; }
elif command -v md5 >/dev/null; then md5of() { md5 -q "$1"; }
else echo "FAIL: need md5sum or md5" >&2; exit 1; fi
command -v xz >/dev/null || { echo "FAIL: need xz" >&2; exit 1; }
[ -n "$LOCAL" ] || command -v curl >/dev/null || { echo "FAIL: need curl" >&2; exit 1; }

TMP=$(mktemp -d "${TMPDIR:-/tmp}/rk2assets.XXXXXX") || { echo "FAIL: mktemp" >&2; exit 1; }
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$PKG/lean"
n=0
while read -r NAME XZSHA SHA BYTES MD5; do
  [ -n "$NAME" ] || continue
  OUT=$PKG/lean/$NAME.lean
  if [ -f "$OUT" ] && [ "$(sha "$OUT")" = "$SHA" ]; then echo "ok (present)  lean/$NAME.lean"; n=$((n+1)); continue; fi
  [ -f "$OUT" ] && echo "lean/$NAME.lean is present but its sha256 is wrong; replacing it"
  if [ -n "$LOCAL" ]; then cp "$LOCAL/$NAME.lean.xz" "$TMP/$NAME.lean.xz" || fail "no $LOCAL/$NAME.lean.xz"
  else curl -fsSL --retry 3 -o "$TMP/$NAME.lean.xz" "$URL/$NAME.lean.xz" || fail "download of $URL/$NAME.lean.xz"; fi
  got=$(sha "$TMP/$NAME.lean.xz")
  [ "$got" = "$XZSHA" ] || fail "$NAME.lean.xz sha256 is $got, expected $XZSHA"
  xz -dc "$TMP/$NAME.lean.xz" > "$TMP/$NAME.lean" || fail "xz could not decompress $NAME.lean.xz"
  got=$(sha "$TMP/$NAME.lean")
  [ "$got" = "$SHA" ] || fail "$NAME.lean sha256 is $got, expected $SHA"
  got=$(wc -c < "$TMP/$NAME.lean" | tr -d ' ')
  [ "$got" = "$BYTES" ] || fail "$NAME.lean has $got bytes, expected $BYTES"
  got=$(md5of "$TMP/$NAME.lean")
  [ "$got" = "$MD5" ] || fail "$NAME.lean md5 is $got, expected $MD5 (MANIFEST.md)"
  mv "$TMP/$NAME.lean" "$OUT" || fail "could not write lean/$NAME.lean"
  rm -f "$TMP/$NAME.lean.xz"
  echo "ok (verified) lean/$NAME.lean  sha256 $SHA"
  n=$((n+1))
done <<< "$ASSETS"
[ "$n" = 4 ] || fail "only $n of 4 assets in place"
echo "all 4 release assets in place and verified"
