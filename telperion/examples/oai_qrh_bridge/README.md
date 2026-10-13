# oai_qrh_bridge: OpenAI's quasi-Riemann hypothesis for zeta, as an Arda island

This island exists for one theorem:

```lean
theorem qrh_seven_eighths : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0
```

That statement, word for word, is the hypothesis `hqrh` of `dbn_real_zeros_of_qrh` on the dbn
island (`telperion/examples/dbn/lean/DBNZeroFreeHalfplane.lean`). Feeding one into the other gives
"every zero of the de Bruijn-Newman function H_t is real for t >= 9/32", which is the
classical bound Λ ≤ 9/32. The proof is not ours. It is OpenAI's.

## Credit and license

The proof of the 7/8 zero-free half-plane is OpenAI's work. It comes from family 003, "The
quasi-Riemann hypothesis", in https://github.com/openai/math, released on 2026-10-06 under the
Apache License, Version 2.0. The theorem we re-export is
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, in `lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean`
at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Our file `lean/ArdaQRHBridge.lean` adds
one line: it closes the implicit binder `{s}` into `∀ s`. We do not copy or modify any OpenAI
source file. The Apache-2.0 license text is `lean/LICENSE` in OpenAI's repository and comes with
every materialized checkout.

## Why this island looks different from the others

Every other island is a Lake package that CI builds in place. This one cannot be, for two reasons.

1. **OpenAI's lakefile has to be the workspace root.** It pins about 25 dependency packages and
   applies a compatibility patch to 23 of them (`lean/patches/*-lean4341.patch`). The patching
   runs in a `run_cmd` during lakefile elaboration and in a `post_update` hook. Both locate the
   dependencies under OpenAI's own `.lake/packages`. We tried the obvious thing, a
   `require OAI from git "https://github.com/openai/math.git" @ "adc7f124…" / "lean"` in a
   downstream package. `lake update` cloned everything for six minutes and then stopped with
   `error: iut: Lake resolved an unexpected checkout at …/.lake/packages/iut`. That is the hook
   refusing a non-root workspace, as designed.
2. **Size.** The import closure of the QRH theorem is about 2,924 OpenAI modules and 486k lines,
   plus PrimeNumberTheoremAnd's Wiener files and one Rellich-Kondrachov file. Vendoring that into
   Arda would make us maintainers of half a million lines we did not write.

So the island is a recipe, not a package. `materialize.sh` produces an unmodified checkout of
OpenAI's `lean/` directory at the pinned commit, under `work/oai` (gitignored). It copies in our
two `.lean` files and the Comparator configs, and appends two `lean_lib` lines to the lakefile.
OpenAI stays the root, its patches apply as intended, and the bridge builds inside it.

```
OAI_PIN                          repo, commit, toolchain v4.34.1, Mathlib d13f23b
materialize.sh                   clone (default) or reflink a local built copy (--from-local DIR)
lean/ArdaQRHBridge.lean          the re-export (one theorem)
lean/AxiomGuardQRHBridge.lean    #print axioms for it and for OpenAI's theorem
lean/lakefile-stanza.lean        the two lean_lib lines appended to OpenAI's lakefile
lean/*.comparator.json           Comparator configs, nanoda ON
lean/ArdaDBNUnconditional.lean   the unconditional 9/32 theorem (single pin)
lean/ArdaDBNChallenge.lean       its Comparator challenge (Mathlib + transcribed DBN.H only)
lean/negative_control/           tampered challenge that Comparator must reject
dbn_port/                        patches + LiCriterion modules for the single-pin port
logs/                            trimmed Comparator logs
fidelity/                        the cross-pin check of riemannZeta (see below)
```

## Building it

```sh
cd telperion/examples/oai_qrh_bridge
./materialize.sh                 # or: ./materialize.sh --from-local <openai-replay-dir>
cd work/oai
lake update                      # fresh clone only: OpenAI's hooks clone and patch deps
lake exe cache get               # Mathlib oleans
lake build ArdaQRHBridge AxiomGuardQRHBridge
```

On a fresh clone the last step compiles OpenAI's whole QRH closure. The local replay measured
11,873 jobs for the four family-003 solution modules, and the `.lake` directory came to 19 GB. On
this Mac, starting from the already-built replay copy (`--from-local`, an APFS reflink that costs
no extra disk), the bridge itself took 45 seconds: 7,065 jobs, of which only the two new modules
were compiled.

## What was checked locally (2026-10-07)

| Check | Result |
|---|---|
| `lake build ArdaQRHBridge AxiomGuardQRHBridge` | green, 7,065 jobs |
| `#print axioms qrh_seven_eighths` | `[propext, Classical.choice, Quot.sound]` |
| Comparator on `qrh_seven_eighths`, nanoda on, local and not sandboxed | see `telperion/docs/QRH_DBN_BRIDGE_2026-10-07.md` |
| Cross-pin identity of `riemannZeta` (Mathlib d13f23b here, de5ce8a9 on the dbn island) | see the same doc |

The independent replay of OpenAI's four family-003 Comparator challenges, with nanoda on, was
done earlier the same day. Lean's kernel and nanoda accepted all four.

## The single-pin port: Λ ≤ 9/32 in one environment

The island also builds the dbn island's corollary at OpenAI's pin and closes it:

```lean
theorem dbn_real_zeros_of_qrh_unconditional :
    ∀ t : ℝ, 9 / 32 ≤ t → ∀ z : ℂ, DBN.H t z = 0 → z.im = 0 :=
  dbn_real_zeros_of_qrh qrh_seven_eighths
```

`materialize.sh` copies the 19 dbn modules straight from `../dbn/lean`, so nothing is duplicated
in git. It applies the two one-line patches in `dbn_port/patches`, which Mathlib renames forced.
It adds `dbn_port/Lc`: LiCriterion's `XiZeros.lean` unchanged, and a three-declaration trim of
its `Basic.lean`. Everything else is byte-identical.

Comparator, run locally with nanoda on, accepts the theorem against `lean/ArdaDBNChallenge.lean`.
That challenge imports only Mathlib plus a verbatim transcription of `DBN.H`. A tampered copy in
`lean/negative_control/` is rejected. The full record, including every change and why, is
section 6 of `telperion/docs/QRH_DBN_BRIDGE_2026-10-07.md`.

## The seam this island cannot close (for the rc1 artifacts)

The kernel checks `qrh_seven_eighths` against Mathlib d13f23b. It checks `dbn_real_zeros_of_qrh`
against Mathlib de5ce8a9. No single kernel run sees both, so "plug one into the other" is a
claim about two environments. `fidelity/` addresses it directly. It exports the statement from
both environments with lean4export and compares every definition and theorem statement that the
statement's meaning depends on. The verdict and its limits are in the doc above.

## Scope

A zero-free half-plane `Re s > 7/8` is not the Riemann hypothesis, which is `Re s > 1/2`. Λ ≤ 9/32
is weaker than the numerical bounds Λ ≤ 0.22 (Polymath15) and Λ ≤ 0.2 (Platt-Trudgian), and RH is
Λ ≤ 0. Nothing here proves RH. conjecture1_proved = False.
