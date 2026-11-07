# Release assets and differences from the reviewed package

## The four certificates kept out of git

GitHub refuses files over 100 MB and warns above 50 MB. Every file of the package over 50 MB is therefore attached to the
GitHub release [v1.1.0](https://github.com/DrMurphyIsIn/riemann-hypothesis-lean/releases/tag/v1.1.0) as an `.xz` file
(`xz -9`) instead of being committed. There are four, the L = 2 heads of ℚ(√−3) and ℚ(i). The other four L = 2 instances,
for ℚ(√−5) and ℚ(√−23), are 20–25 MB and are in git.

```sh
scripts/fetch_assets.sh                 # download, decompress into lean/, verify every sha256 and the MANIFEST md5
scripts/fetch_assets.sh --local DIR     # the same, from .xz files already in DIR
```

| file | bytes | sha256 | release asset | asset bytes | asset sha256 |
|---|---:|---|---|---:|---|
| `lean/K3_L2_even.lean` | 149800511 | `2cf6f69a8ae6a93591d1df426ef98f2dd99ba430db704f30d64b5a75d01cf4a8` | `K3_L2_even.lean.xz` | 24959284 | `6acfebef2e18012f7a8f10275213b6cab4b7b0a72876d25c3edb661067d92a76` |
| `lean/K3_L2_odd.lean` | 139066135 | `2f825a3dc547abf23769cc35849815b66fda7bd4a45ee78de7004a5c91bb669a` | `K3_L2_odd.lean.xz` | 16758012 | `0b25459ff3211e93fb7c030fb47263d0be9c33133be75600ae01d63c14fdf14f` |
| `lean/K4_L2_even.lean` | 87291881 | `f89ebde373119dcec2a2ced2f3d24a7547961eb89b0dbce5b87ee6537bf7e460` | `K4_L2_even.lean.xz` | 14336520 | `fb8ea245675eb513b7ec4d2f5cc5fbe0e724fab521628faba462b64b48c00a47` |
| `lean/K4_L2_odd.lean` | 79726895 | `6988ecc4b821aeec670027a2352c656232a7824851727f3959d5c37f7564ae14` | `K4_L2_odd.lean.xz` | 12622416 | `993018b69b06547dd2e332d0b2260c3b66b8775d8f103f4c8873cf31b912238f` |

Their md5s are the ones `MANIFEST.md` records: 52b05fafa090e67de347afb473fc5c5d, f114394d102207b7259fc59feeccbd74,
7db3db13eac934137b633e0ada2ef667 and 50b67595663f69addede45b8ce48c96d. `fetch_assets.sh` checks those as well.

The instances can also be regenerated from the Arb heads with `scripts/pgc_emit.py`. The heads are not published.

## Differences from the reviewed package

`MANIFEST.md` (md5 34c179102921e9ddf35408dbea335279) is the manifest of the package as reviewed, and it is unchanged here.
Every file it lists is in this directory byte for byte, except for the following:

| file | status | md5 here | why |
|---|---|---|---|
| `lean/K3_L2_{even,odd}.lean`, `lean/K4_L2_{even,odd}.lean` | release assets (above) | as in MANIFEST | over 50 MB |
| `scripts/run_export.sh` | changed | 999f104a260589603f2bda46ffea747d | it logs the basename and md5 of the lean4export and nanoda binaries it runs (review nit of 2026-11-07); no other change |
| `README.md` | changed | 122a61b6a19f9be6c47cbce281aab552 | the added section "About this copy" |
| `scripts/exp_emit.py` | docstring reworded | 82a011268d0a71e06f84a18f7bb55264 | the module docstring no longer names a local directory; the syntax tree without docstrings is identical |
| `RELEASE_ASSETS.md` | added | | this file |
| `scripts/fetch_assets.sh` | added | | the downloader and checker |
| `.gitignore` | added | | keeps the fetched certificates and build products out of git |

No Lean file, JSON file, control or log changed.
