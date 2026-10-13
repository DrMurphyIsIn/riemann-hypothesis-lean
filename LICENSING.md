# Licensing

This repository uses a split licensing model, the same one as the Brualdi–Goldwasser repository.

## The mathematics: Apache-2.0 / CC-BY-4.0

Everything outside `telperion/` (`formalization/`, `scripts/`, `.github/`) is licensed under the
[Apache License 2.0](LICENSE). So are the Lean islands, generators and emitted certificates under
`telperion/examples/` (see the next section). The papers (`papers/`) and the prose documents (`README.md`,
`NOTICE.md`, `CENSORING.md`, `formalization/README.md`) are licensed under
[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).

## The Telperion engine: Business Source License 1.1

`telperion/` is a vendored copy of the Telperion certificate engine, licensed under the
[Business Source License 1.1](telperion/LICENSE):

- **Free for research.** Academic research, teaching, scholarly work, peer review and evaluation are
  permitted outright by the Additional Use Grant.
- **Commercial production use** requires a license from the Licensor.
- **Change License:** each release converts to Apache-2.0 three years after its release date.
- Contributions to the engine require the individual CLA in [`telperion/CLA.md`](telperion/CLA.md).
  Contributions to the mathematics do not.

Emitted certificates are excluded from the Licensed Work. Every Lean file a generator writes is part of the
open mathematical record and is Apache-2.0, not BSL. The same goes for the hand-written Lean islands in
`telperion/examples/` (`dbn`, `oai_qrh_bridge`, `liu_dbn_bridge`, `rvm_bridge`, `weil_form_enclosure`,
`quasicrystal`), which the development repository licenses as mathematics under Apache-2.0. Reviewers need no
license beyond the Additional Use Grant to rebuild and check every theorem here.

## Third-party code that is not in this repository

- **OpenAI's quasi-Riemann hypothesis** (openai/math, Apache-2.0) is fetched at a pinned commit by
  `telperion/examples/oai_qrh_bridge/materialize.sh` and `liu_dbn_bridge/liu_materialize.sh`, and is never
  redistributed here.
- **Baiying Liu's Lean** (arXiv:2610.12234) is fetched at a pinned commit by `liu_materialize.sh`, and every
  file is checked by hash. Liu's repository carries no licence file. The Arda owner decided on 2026-10-11 to
  treat it as Apache-2.0, but Liu has granted nothing in writing. That is why none of Liu's code is stored
  here, only its commit hash, the sha256 of each file, and the names of the declarations it adds. Attribution
  to Liu is kept everywhere.
- **Zeta23** (anthropics/formal-math, Apache-2.0), **LiCriterion** (Apache-2.0) and **Mathlib** (Apache-2.0)
  are fetched by Lake at pinned commits.
- `telperion/examples/oai_qrh_bridge/dbn_port/Lc/` is a trimmed copy of LiCriterion (Apache-2.0, see its
  `NOTICE`), as in the qrh-debruijn-newman repository.
