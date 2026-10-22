# v32: source-bound Fourier inputs and exact spectral pairing

Scope: frozen PR110–112 plus author commits3fb0ba0ede60a785bc7ad448756140df868c20f1 and32fefb4c537f96071ff576db76f268e1bb9d3b4c. Baseline main1c760e35eb3cf96fb14a6fd4f2d468cadb4f64c9 (v31). Normal Git merges preserve every frozen author commit; all five mathematical source files are byte-identical to their reviewed versions.

The actual bounded-energy MGF test and compact source energy geometry supply the next finite-cover far-tail probability step in OQ3. OQ4 now has the exact signed reflected-mode pairing and principal-mode normalization including the central zero mode at n=0 and empty-tail m=1/m=2 cases. The common source scale bridge derives gamma, actual remaining length and bias/variance inputs from the original truncated law. The chord module constructs the genuine triangular biased-pair noise law, its exact characteristic function and closed-cone comparison.

Added5 production modules /80 public theorems: OQ3 2/5; OQ4 1/69; Common2/6. Total215 modules /1548 public theorems /2550 namespace theorem declarations including generated /3943 module-owned constants. Counts do not represent root completion percentages. No new original root is claimed closed.

## Validation

Three fresh never-author acceptance reports: docs/integration-v32/oq3-review.md, docs/integration-v32/oq4-review.md and docs/integration-v32/c12-review.md. Exact source-to-statement scope, boundary cases and existing target evidence are independently reviewed. Root compiles all five new modules then Shao sequentially with pinned Lean4.36.0-rc1 / mathlib807d3836b165983210ee2ecf3cd28f239436949c, autoImplicit=false, -M8192 -j4. All6 compile invocations pass, all new target logs empty. Full public-theorem audit, all-owned-constant transitive axiom audit and module coverage pass. Only propext,Classical.choice,Quot.sound permitted. Baseline210 sources and987 object-family files are hash-verified unchanged before/after the gate; exact v31 artifacts reused, not rebuilt. Source/manifest/pin hashes remain stable throughout validation. Final receipt: verification/receipt-v32.json; baseline evidence and raw logs stay on server logs/integration-v32/.

Resources: root gate CPU10–13, one heavyLean at a time. User's separate10-core/80GiB CPU0–9 process family untouched. Other lanes retain ownership and worktree; no branch resets or cache upgrades.

## Remaining bearing obligations

OQ3: finite exponential cover and actual global far-layer probability bound, complete mixed LLT/Levy, later source layers/cusp/phase steps remain separate. OQ4: uniform actual spectral remainder bounds, complete S2–S5/Brownian/general roots remain open. Common: whole Xi construction, derivatives and damping, Fourier comparison/inversion/desmoothing and C1/C2 roots remain open. p35 closure is preserved; other original roots remain open. New work must name the original obligation and direct consumer, rather than count standalone auxiliaries as root progress.

C12 evidence in docs/c12-v32/ is the original source/scope/author/independent review record. Its historical PENDING labels and pre-reservation command affinities are retained as history, superseded by final proof reviews and the current root gate; no old command was rerun. Published text copies normalize CRLF to LF only, with both hashes in publication-format.json. Local originals remain unchanged.

Declaration accounting: the five target modules own223 constants in their unit reviews. Full-library owned count grows by224 because import use additionally materializes Shao.OQ3.binaryRelativeEntropy.eq_1 for an unchanged upstream definition. No old owned name disappears; this equation theorem passes the same transitive axiom gate and is not counted as a new public source theorem or bearing obligation. See docs/integration-v32-declaration-delta.json.

The first staged diff check rejected extra terminal blank lines in three fresh review copies. Local original reports are preserved; publication copies only collapse the terminal newline run to one LF, with before/after hashes in docs/integration-v32/review-publication-format.json. No mathematical source, gate script or checked input changed; no Lean repeat was required.
