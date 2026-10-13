# What was changed in the Telperion copy, and why

`telperion/` is copied from the Arda development repository at commit
`b17b3c68fe67e314e1051f4dab46f7d527a7b62a` (2026-10-13). Before publishing, the copy was scanned for five
kinds of material that do not belong in a public repository, and the hits were reworded:

- **(i) private project**: references to an unrelated private software project of the author's;
- **(ii) private paths**: paths into the author's home directory, private working directories, scratch
  directories and temporary directories, and pointers to unpublished working notes;
- **(iii) secrets**: tokens, keys, passwords, environment files and private e-mail addresses;
- **(iv) session identifiers**: internal session IDs and session links;
- **(v) personal information**: personal or medical information of any kind.

The scan found nothing in categories (iii), (iv) and (v). (The only e-mail address is the author's public
commit address, in a design note; the strings that look like credentials are the field names and dummy
values of the API client's tests.) Everything below is category (i) or (ii).

Only comments, docstrings and prose were changed. No code, definition, statement or proof was touched.
`scripts/check_telperion_copy.py` checks this against a checkout of the source commit, and
`scripts/materialize.sh` makes that checkout and runs the check. It compares every file: Python by syntax tree
with docstrings removed, Lean with comments removed. Any other difference must be listed here. The removed
text is not quoted in this file; anyone with access to the source commit can see it with the checker.

## Reworded files

### Engine source (Python comments and docstrings)

| file | category | change |
|---|---|---|
| `telperion/src/telperion/bg/counterexample_hunt.py` | (i) | module docstring describes the search method without naming the private project |
| `telperion/src/telperion/bg/parallel_map.py` | (i) | same, for the island model |
| `telperion/src/telperion/certify.py` | (i) | one comment describes two certificate shapes by their mathematics |
| `telperion/src/telperion/emit_concave_stationary_max.py` | (i) | docstring and one comment cite the textbook Kelly fraction instead of a private source file |
| `telperion/src/telperion/emit_scale_invariance.py` | (i) | docstrings describe the two textbook examples (parameter cancellation, the squared Sharpe ratio) instead of a private codebase |
| `telperion/src/telperion/hunt.py` | (i) | one comment line, as in the Brualdi–Goldwasser copy |
| `telperion/src/telperion/emit_lfunction_product.py` | (ii) | a self-test comment no longer names a temporary directory |

The first six use the same wording as the Brualdi–Goldwasser repository's copy (its commit 2df89ad).

### Lean islands (comments only)

| file | category | change |
|---|---|---|
| `telperion/examples/rvm_bridge/lean/Hodge1_KPen.lean` | (ii) | header comment cites "design notes, unpublished" instead of a private path |
| `telperion/examples/rvm_bridge/lean/Hodge1_Par45.lean` | (ii) | same |
| `telperion/examples/rvm_bridge/lean/Hodge1_Par5493.lean` | (ii) | same |
| `telperion/examples/rvm_bridge/lean/Hodge1_PoleFreeWindow.lean` | (ii) | same |
| `telperion/examples/rvm_bridge/lean/Hodge1_Reduction.lean` | (ii) | same, for the plan document |
| `telperion/examples/rvm_bridge/lean/Hodge1_Strip.lean` | (ii) | same |
| `telperion/examples/rvm_bridge/lean/Hodge1_RHReduction.lean` | (ii) | a session name containing the local user name becomes "an independent session" |
| `telperion/examples/weil_form_enclosure/lean/RRSquare.lean` | (ii) | header comment names the unpublished note by file name only |
| `telperion/examples/weil_form_enclosure/lean/RRSquareFF.lean` | (ii) | same (generated file; see the next entry) |
| `telperion/examples/quasicrystal/lean/Probes/AuditTorusDict_Source.lean` | (ii) | a comment says "an old local checkout" instead of naming a private directory |

### Generator (string literal that becomes an emitted Lean comment)

| file | category | change |
|---|---|---|
| `telperion/examples/weil_form_enclosure/rr_square/gen_lean.py` | (ii) | emitted-comment exception: the same one-line change as in `RRSquareFF.lean`, inside the string the generator writes as that file's header comment. The checker allows this file to differ only in string constants. Running the generator reproduces the published `RRSquareFF.lean` byte for byte. |

### Prose, logs and READMEs

| file | category | change |
|---|---|---|
| `telperion/README.md` | (i) | one table row describes the scale-invariance emitter by its mathematics; plus the added "About this copy" section |
| `telperion/docs/NEW_EMITTERS_SUMMARY.md` | (i) | a section heading and two table rows, as in the Brualdi–Goldwasser copy |
| `telperion/NS_EULER_EMITTER_CATALOG.md` | (ii) | a worktree path becomes "a separate worktree" |
| `telperion/docs/QRH_DBN_BRIDGE_2026-10-07.md` | (ii) | three local paths (a worktree, a replay checkout, a `cd` line) made generic |
| `telperion/docs/LIU_DBN_BRIDGE_2026-10-11.md` | (ii) | local tool paths, private note paths and session names containing the local user name made generic |
| `telperion/docs/SECOND_PASS_EMITTER_CATALOG.md` | (ii) | a private plan file becomes "the build plan, not published" |
| `telperion/research/rr_square/RR_SQUARE_STATEMENT_2026-10-12.md` | (ii) | a private note path becomes the note's file name, marked unpublished |
| `telperion/examples/liu_dbn_bridge/README.md` | (ii) | a private note path and two command lines with local directories made generic |
| `telperion/examples/oai_qrh_bridge/README.md` | (ii) | one command line with a local directory made generic |
| `telperion/examples/liu_dbn_bridge/logs/comparator_2026-10-11.txt` | (ii) | the two header lines of a run log no longer name local tool directories; the recorded output is unchanged |
| `telperion/examples/liu_dbn_bridge/logs/materialize_2026-10-11.txt` | (ii) | the home directory in one path of a run log is replaced by `<checkout>`; the recorded output is otherwise unchanged |

## Added files

| file | why |
|---|---|
| `telperion/SYNC` | the source commit, one line |
| `telperion/tests/conftest.py` | skips 131 tests that need files only the development repository has; see its docstring |

## Left out

These are absent from the copy and are not counted as changes:

- the development repository's missions registry, scratch and research folders (except `research/rr_square/`),
  explorer, tools, prototypes and most of its documents and examples (only a selection is published, as in the
  Brualdi–Goldwasser copy);
- eleven test modules that cannot be imported without the development repository, and the test fixtures only
  they use (`tests/fixtures/compose/`);
- three numerics scripts in `examples/rvm_bridge/` (`phase0_gaussian_obligations.py`, `wall_landscape.py`,
  `fixed_width_band.py`), because their code hard-codes a machine-specific scratch directory as the default
  output location. Changing that would be a code change, so they were left out instead;
- compiled Python caches (`__pycache__`) that the development repository had committed.
