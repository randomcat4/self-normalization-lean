# Shao C1/C2 Lean foundations

Private formalization of the shared finite-path and event interfaces of C1 and C2. This milestone provides genuine square-sum energy, nonempty-prefix maxima, weak multiplication crossings, strict survival, zero-energy normalization, and two-sided event identities. It does not claim the quantitative C1/C2 probability theorems or a unified 124 proof mechanism.

## Modules

- Shao/Basic/FinitePath.lean: actual finite paths, prefixes, energy, extrema, negation and scaling.
- Shao/Basic/Events.lean: weak crossing and strict complement semantics.
- Shao/C1/Normalization.lean: zero-energy conventions and positive-threshold strict event comparisons.
- Shao/C2/TwoSided.lean: double-hit intersection, absolute-event union and complements.
- Shao/Checks/Boundaries.lean: zero paths, singleton paths, threshold equality and the time-zero distinction.

See [frozen scope](docs/scope-v1.md), [delivery plan](docs/plan.md) and [independent review](docs/review-v1.md). Source: [randomcat4/shao at 35d4580](https://github.com/randomcat4/shao/tree/35d4580b61e22e7145f47730045a09874ef93259); exact manuscript hashes and source anchors are in the scope contract.

## Reproducibility

Lean is pinned in lean-toolchain; mathlib and transitive dependencies are pinned in lake-manifest.json. On the designated server, populate the required fixed-version mathlib cache, run lake build, then lake env lean scripts/Audit.lean. Audit prints every exported project theorem's actual type and transitive axioms and rejects axioms outside propext, Classical.choice and Quot.sound. Receipt details are stored under verification/. No local Lean checks or duplicate preparation tests are part of this workflow.

All computations, dependency caches and raw logs stay on the server. The repository contains curated source and evidence only. Independent statement review complements kernel checks; it does not replace them.

## Probability milestone

49 additional public theorems establish path/event measurability, the finite iid product law and fixed-permutation probability invariance. The library now contains 132 public theorems; the kernel audit covers 168 theorem declarations including generated declarations. See [scope](docs/scope-v2.md), [independent review](docs/review-v2.md), [verification receipt](verification/receipt-v2.json), and [whole-corpus roadmap](docs/whole-corpus-plan.md). No complete root probability theorem is claimed.

## OQ5 p35 finite algebra milestone

11 further public theorems prove the unordered-pair double counting, centered-row studentizer identity and exact target-category cancellation, for arbitrary deterministic vectors with n>=3. Target sets may be empty, singleton or full. The complete library has 143 public theorems and 223 audited theorem declarations including generated declarations. See [scope](docs/oq5-row-scope.md), [independent review](docs/oq5-row-review.md) and [receipt](verification/receipt-v3.json). The fixed-law counterexample and all four root groups remain open.

## Shared deletion, survival and Lindley milestone

43 additional public theorems establish ordered sample compression, the source weak crossing deletion implication, closed-wall survival and coordinate bounds, the actual Lindley recursion, and its finite-iid joint law with the true square-sum energy. There are now 186 public theorems and 295 audited theorem declarations including generated ones. See [scope](docs/scope-v4.md), [independent review](docs/review-v4.md) and [server receipt](verification/receipt-v4.json). All complete root groups remain open.

## OQ4 foundation milestone

15 additional public theorems cover finite recurrence, overshoot sums and moments, and variance scaling. The integrated library has 201 public theorems and 327 audited theorem declarations. See [scope and review](docs/integration-v5.md) and [server receipt](verification/receipt-v5.json). K/Kv and the complete OQ4 root remain formally unclosed.

## OQ5 fixed-law milestone

43 additional public theorems construct the fixed probability law, Borel observation encoding and exact feature moments. The integrated library has 244 public theorems and 395 audited theorem declarations. See [scope and review](docs/integration-v6.md) and [server receipt](verification/receipt-v6.json). The full counterexample remains formally unclosed.

## Conditioning and truncation milestone

43 additional public theorems establish genuine fixed-pattern conditional iid laws, exact retained-set events, and the original truncation budget with integral estimates, continuity, strict growth and its normalized limit. The library has 287 public theorems and 443 audited theorem declarations. See [scope and independent reviews](docs/integration-v7.md) and [server receipt](verification/receipt-v7.json). Full root theorems remain formally unclosed.
