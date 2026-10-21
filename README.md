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
