# p35 residual operator and rare-event lower bound: independent review

Status: all five source units independently CORRECT and LEAN_FULLY_CHECKED at the immutable hashes below; the import-only aggregate also compiles on the designated server. All full OQ5/OQ6 roots remain OPEN.

Pinned Lean4.36.0-rc1(c9afcddf514a6772bd4d649f7cfc04eff0b9f15e), mathlib807d3836b165983210ee2ecf3cd28f239436949c. All Lean runs use the assigned lead-oq56 server worktree after activate.sh then cd. No local Lean, lane cache fetch/write or shared integration edit.

| Module under Shao/OQ5/P35 | Accepted SHA256 | Public declarations |
| --- | --- | --- |
| CategoryTails.lean | 58d04c1b7cb0640f5e92d41724795d5d2ac744569d5559d0d7268023c50eca38 | 6:1def,5theorems |
| RareEvents.lean | 152e198f01c79b34fd3a88ab4b49740fd027980bb0909b31bae2d74a5d074f53 | 18:6defs,12theorems |
| ResidualOperator.lean | f6de6c3e08a74f73f87c265a5d962ba8a34e5c52515c793ede27d751b353feec | 16:3defs/abbrev,13theorems |
| BinomialBound.lean | 3ede275bad942643b1cf6799cd823fa98f1f16960891ccfd50d4a3751c81f5a9 | 1theorem |
| RareLowerBound.lean | 447010c5b9305adeea249e289aaa831b85f7c1b553fcf41ef524e673597b3bb5 | 5theorems |

Total46 new public declarations, including36 public theorems. Each had a frozen exact interface, blind source/statement translation review before implementation, author server check and independent fresh proof/source-to-Lean review. Reviewers read original p35 and elaborated declarations, authored/repaired none of these proofs, and reported CORRECT. Every public definition/abbreviation/theorem was transitively audited with #print axioms from the exact source prefix; all axiom sets are subsets of propext,Classical.choice,Quot.sound. Private dependencies were included transitively. Comment/string-aware source scans found zero proof placeholders, new axioms or bypass tokens. All targeted final Lean checks passed without diagnostics. Aggregate/source-byte/encoding/diff checks are recorded in the lane packaging receipt.

Review details: units12/13 verify actual category mass, strict below/above tails, positivity and zero boundary; measurable fixed-J/count events, disjoint powersetCard decomposition, exact sampleLaw probability and source specialization. Unit14 checks full infinite-dimensional L2 construction, actual universal kernel sections, AE action and output MemLp, nonzero feature, exact range/rank/eigenvalue arguments using only second feature moments. Unit15 checks the sharp binomial inequality with both natural-domain premises and positivity before division. Unit16 checks the real event behind the probability, exact geometric tail error, Bernoulli squeeze on the full atTop sequence, sharp binomial coefficient substitution, eventual half bound, positivity/logarithm directions and final exp bound. No guessed numeric cutoff replaces the eventual statements.

Compact independent reports: shared drafts/oq56/unit12 through unit16, semantic-review.md and proof-review.md. Raw server evidence: work/oq56/fresh-review12 through fresh-review16, exact-source Audit.lean, target/axiom logs, coverage/scan/hash manifests and receipts. Authors are separate coefficient/event, measure/operator and lower-bound contexts. Independent source translators and final proof reviewers used fresh gpt-6.1-sol xhigh contexts and did not implement proofs. No novelty claim or external source substitution is made.

This receipt is for the exact five new source files. Construction prerequisite is in PR12. Root remains responsible for its integrated build/import/public-theorem manifest/whole-library axiom gate; this lane does not alter those shared files or merge PRs. None of Q1 through Q6, domination failure, true Studentizer positivity or full tail/root completion is asserted here.
