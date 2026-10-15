# Changelog

## v1.0.2 (2026-10-14)

This release corrects the vendored copy of Telperion. Two defects in the engine were found after v1.0.1 by an independent
AI audit, run in a different session from the one that wrote the code. No human review found them. Both are fixed in the
development repository, Arda, by pull requests #740 and #739. `telperion/` is now copied from Arda commit
`5d1c8c579be7c3a1fdf43a2a5aeef37f1d8bb4fa` (2026-10-14), which contains both fixes. v1.0.0 and v1.0.1 used
`50b1000254c6bb74bf12d21fa66483bd9fc14aeb` (2026-10-13).

**None of the repository's own claims depended on either defect.** The three papers and `docs/PROGRESS.md` make no claim
about how many zeros the Davenport–Heilbronn function has, and they do not use the Báez-Duarte emitter. Every theorem they
state is unchanged, and so is every Lean file they cite. The papers are unchanged in this release.

### The winding-number zero counts were not rigorous

Telperion counts the zeros of an analytic function in a box with the argument principle: it adds up how far the function's
argument turns around the box's boundary. In v1.0.0 and v1.0.1 the default backend for this, `arb_dh.winding_number`, used
by the `winding_box_zero` emitter, evaluated the function with Arb balls only at a finite set of points on the boundary.
Each value was rigorous, but nothing controlled what the function did between two sample points. A pair of zeros just
inside an edge, between two sample points, adds a full turn to the argument without changing any sampled value's
quadrant, and the count misses both. The audit built such a case, and doubling the sampling density does not help. So
those counts were heuristic, not certified. The engine's documentation called them rigorous, and they were not.

The default backend is now the segment-enclosure method of the new module `telperion/src/telperion/arb_winding.py`. It
encloses the function on whole boundary segments, not just at their endpoints, using a bound on its derivative there. A
segment is accepted only when the enclosure proves the function's values stay in a small disc away from zero, so the
argument change along it is known exactly. A segment that fails is split, and past a depth limit the routine refuses
instead of guessing. These counts are rigorous in Arb's interval arithmetic. They are not kernel-checked.

The Davenport–Heilbronn inventory, `telperion/examples/quasicrystal/zoo_data/dh_zeros.json`, was built with those
counts, and it was also incomplete. It listed 4 off-line zeros up to height 300, taken from published tables. There are 5.
The one it missed, ρ ≈ 0.8695305796 + 240.4046723514i, is not in those tables, and the off-line scan the inventory's
documentation promised had never been written. The inventory has been re-issued with every count done by the rigorous
method, and with the scan, which finds the fifth zero. It now also proves itself complete to height 300: the rigorous
total over the region is 214, and that equals the 204 zeros on the line plus the 5 off-line zeros counted with their
mirror images, 214 = 204 + 2·5.
`dh_inventory.py` and `zoo_verdicts.json`, which said "certification is rigorous" and "4 off-line pairs certified", now say
what is true.

### The Báez-Duarte family label was false

The `BaezDuarte` emitter certifies upper bounds on the distance d²_N in the Nyman–Beurling–Báez-Duarte criterion, where RH
holds exactly when d²_N → 0. Up to v1.0.1 it used the family {1/(kx)}, k ≥ 2, in L²(0, 1), and labelled it with "RH ⟺
d²_N → 0". For that family the label is false. On (1/2, 1) the whole span of the family is the multiples of 1/x, so d²_N ≥
1/2 − (ln 2)² ≈ 0.0195 for every N, whether RH is true or not. Its bounds therefore could never have approached 0.

The emitter now uses Bagchi's functions g_k(x) = {1/(kx)} − {1/x}/k (Báez-Duarte 2003; Bagchi 2006, Theorem 7), for which
the equivalence does hold. Only the upper bounds are certified; for N ≥ 3 their closeness to the true d²_N is computed, not
certified. At N = 2 the bound is certified on both sides, since d²_2 = 1 − ln 2 exactly. The theorem names in the emitted
Lean are unchanged.

### Also in the re-sync

The new source commit also brings in Lean work that was merged into Arda between the two commits. It is vendored because the
islands' build files and axiom guards at the new commit name it:

- `dbn`: `DBNEulerModelRH.lean` and `RegEulerModel.lean`, the Euler-model strip (PR #725). This is a statement about the
  finite Euler-product model, not about ζ.
- `rvm_bridge`: `PFSemibounded.lean`, `RegSemibounded.lean`, `SemilocalWeil.lean` and `RegRRConverse.lean`. These are
  equivalences with RH, not progress on it.
- `weil_form_enclosure`: `LemmaSCore.lean`, with the two Lemma S research memos and their check scripts in
  `telperion/research/rr_square/`.

`docs/PROGRESS.md` is still the record as of the old commit, and it has not been extended to this work. It now says so.

### Censoring

Every file that is new or changed since the old commit was scanned again for the five kinds of material listed in
[`CENSORING.md`](CENSORING.md). The earlier rewordings were re-applied where their files changed. The scan found two more
private paths, one in a Lean comment and one in a research memo. Both were reworded and are listed in `CENSORING.md`.
`scripts/check_telperion_copy.py` passes against the new commit: no code, definition, statement or proof differs from Arda.

### Documentation corrections

- `README.md` and `docs/PROGRESS.md` called the Euler-model strip an open, unmerged pull request (#725). It was merged on
  2026-10-14.
- `docs/PROGRESS.md` said `telperion/` was copied from the commit it was checked against. That was true until this release.
- The source commit is updated in `formalization/ARDA_SOURCE`, `formalization/README.md`, `NOTICE.md`, `README.md`,
  `telperion/README.md` and `.zenodo.json`.

### arXiv packages

The three papers did not change, so their arXiv packages did not either. Each package was rebuilt from this release with
its `make_arxiv.sh`; all three compiled without errors, at the same page counts (18, 15 and 13), and the rebuilt
`paper.tex` is identical to the one already in each `arxiv.tar.gz`. The committed packages are kept as they are. They are
still staged and not submitted.

## v1.0.1 (2026-10-14)

The RR-chain nodes were judged and recorded (Arda #731), and their status updated in the paper, `docs/PROGRESS.md` and the
formalization README. Zenodo version DOI 10.5281/zenodo.23365216.

## v1.0.0 (2026-10-13)

First release. Zenodo version DOI 10.5281/zenodo.23352051 (concept DOI 10.5281/zenodo.23352050).
