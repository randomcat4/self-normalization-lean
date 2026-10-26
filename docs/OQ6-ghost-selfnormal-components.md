# Exact ghost-sample components for the original self-normalized tail

This milestone supplies three components for the p51 S11 upper-tail argument. It preserves arbitrary measurable sample spaces and the original assumptions. The original S11 event, W/V normalization and G_y complement union are still open.

* `PairedSelfNormalizedTail` proves the swap specification, strict paired-event measurability, the finite-sign integral bridge and the paired tail bound `2 * exp(-t^2/2)` for `t >= 0`. It assumes only a probability law and measurable real-valued g; no moment assumptions are added.
* `OriginalGhostGoodEvent` proves the sample sum/energy moments, the ghost good-event lower mass `1/2`, and its use on the original sample law under the exact L2, mean-zero and unit-second-moment assumptions. It includes n=0 and atomic laws.
* `OriginalGhostComparison` proves the Euclidean energy comparison and the deterministic implication from the original strict threshold and the ghost good event to the paired strict threshold, for every n and t>=1. It adds no positivity assumption on energy or n.

The exact accepted source hashes are respectively `23d5e22f5bd8669f8e7d41afec78cf1b5bcf8150052ec666fc2bfbac507a7d8b`, `fc4127fadfab83ff08605b50b0cfa0525084201b7a5b78293d42d9826d82e83a` and `45119bf03fae2df0fac15f380b6283b131dafd6cb00646de55e30c0bf4e5ed35`.

Each exact source has complete independent source-to-statement/proof coverage, with exact reuse of unchanged reviewed bytes after frozen repairs. Every new complete helper and its scope/data composition was independently reviewed. Old failed sources and receipts remain preserved. The sum-body scope judgments invalidated by the 201 repair are explicitly excluded from reused evidence.

Server native02 and same-first-original-object all-owner audits returned actual Lean RC0 for all three modules. All-owned discovery uses the module index and all environment constants without a namespace filter. Actual counts are 10/21/2 owned constants, with 123/447/80 complete TYPE lines and 15/26/0 non-theorem FULLVALUE lines. Complete name components, universes, body presence and recursive axiom sets are reviewed; only propext, Classical.choice and Quot.sound occur.

The first objects are `da3d2658aabde869760cf289534d016fe65529a3e5ad43293e22a5e11aac92e2`, `399266357b6bb5c62696d2b2c0f45284f4ac415f477115066592e18f49926541` and `07f7f83e68a4bbc1976521fe7e0a7d7cc3be651848742e38a1d94be70352fd7b`. No producer recompilation or warning cleanup follows these objects. Five/7/0 source warnings, the same 134-byte standing mathlib path warning, strict wrapper false and FIRSTEMPTY=false are preserved and classified. These wrapper results are distinct from actual kernel/audit RC0.

Sources and evidence use leanprover/lean4:v4.36.0-rc1 and mathlib 807d3836b165983210ee2ecf3cd28f239436949c. All checks ran on the designated server under CPU52-55, the original lane lock, -M8192 -j4 and the active two-command global phase limit. No local Lean or old producer/leaf audit replay occurred.

The source route retains attribution to Shao-Zhou (2016), formula (92), and Jing-Shao-Wang (2003), Lemma 6.4; this milestone makes no novelty claim or claim of reading the latter full text. The p54 repairs and 124 non-prerequisite scope remain. Original C1 immutablev85 is complete; S11/C2/C12/OQ56 are OPEN, and OQ3 is PAUSED_BY_USER. Shared imports, cache and integration remain owned by Root.
