# Shao Lean formalization

Source-faithful Lean formalization of the C1/C2 and OQ3–OQ6 result packages. The original C1 theorem and the five assigned original C2 conclusions have been accepted. OQ56 and broader shared extensions remain open. Acceptance always refers to an exact frozen statement and source version, including its explicit domain, repairs and external-result attribution.

The accepted mathematical snapshot, exact inventory and remaining work are recorded in the [current scope](docs/CURRENT-STATUS.md) and [evidence index](docs/EVIDENCE.md). Inventory counts are not completion percentages.

## Accepted scope and current state

| Package | Accepted result and current boundary |
| --- | --- |
| C1 | Original signed half-line theorem on the full nonnegative original I_n, both signs, accepted at immutable v85. [Scope and receipt](docs/EVIDENCE.md#c1) |
| C2 / assigned C12 | All five original labels g:double, g:absolute, m:B, m:A and m:C accepted by v112. Assigned C1/C2 work is complete; broader common extensions remain separate. [Evidence](docs/EVIDENCE.md#c2) |
| OQ3 | Paused by the human. The accepted fixed jointly nonlattice counterexample remains in Lean; paused B/D directions are not declared complete. [Counterexample](Shao/OQ3/SourceCounterexampleRoot.lean) |
| OQ4 | The assigned original fixed-law weak-window result and universal sharp sixth-root criterion are accepted. The human has resumed autonomous source-bound extensions; this does not accept every historical OQ4 extension. [Boundary](docs/CURRENT-STATUS.md#oq4) |
| OQ5/OQ6 | Original S10/S12 comparison, S13 deletion support and full-tilt rho moments have accepted components. The rho-sensitive capped partial-law deletion producer and original-window four S14 expectation fees are accepted; compact fees, general S15 and full S11/OQ56 remain open. [Current frontier](docs/CURRENT-STATUS.md#oq56) |

## Selected accepted OQ56 components

- v113: original low-energy and normalized upper-tail components.
- v114: literal good-event probability and conditional finite clipping construction.
- v115: all-n/all-real-y event identity, literal constant-512 studentizer domination with its window, and bounded-product/polylog-envelope four-payment bound.
- v116: literal clipped comparison without an external domination premise, and comparison-exception/payment composition in that bounded class.
- v117: original-length deterministic/measurable deletion envelopes and genuine rho/rho-squared moments under the full quadratic tilt, including rho = 0.
- v118: original-length rho-sensitive capped deletion bounds under the actual partial weight, with full integrability and rho = 0; this supplies S13 absolute-D/J ingredients within the original explicit window.
- v119: all four original S14 expectation fees and their combined polynomial budget, preserving the original law/window/n and rho = 0; this is not a general probability-payment or full-root theorem.
- v120: original untilted compact continuous-cap combined expectation fees, retaining the original (n-2)^2 budget via an explicit parameter transform. The actual projection cost remains separate; its L2 bound of at most 4 is not a decay rate.
- v121: the actual projection p-moment rate and combined compact analytic cost, for 2<p<=3 and a finite genuine projection p-moment. Probability/CDF and root closure remain separate.

The bounded-class exponential payment bound retains the three terms exp(-cn) + 4 exp(-y sqrt(n)/2) + 9 exp(-k_n). It is not a theorem for the unrestricted original S15 class. Symmetry, normalization, original sample-length denominators, threshold windows, zero-denominator guards and genuine remainder fees remain where the exact statements require them.

## Verification and reproduction

Lean is pinned to `leanprover/lean4:v4.36.0-rc1`; mathlib is pinned to `807d3836b165983210ee2ecf3cd28f239436949c`. Complete independent source-to-statement/proof review complements server kernel checks and recursive axiom audits of every actual module owner, including private/generated declarations and required full non-theorem values. The axiom whitelist is `propext`, `Classical.choice`, `Quot.sound`.

All Lean compilation and heavy computation run on the designated server, using the existing pinned package view and lane lock. Reuse qualified exact-source evidence and first original objects; do not update packages, rebuild mathlib or repeat accepted producers to refresh documentation. See the [execution and delivery rules](docs/plan.md). Curated sources and receipts are committed; caches, binaries, raw logs, environments and credentials remain outside Git.

Versioned scope/review/receipt files are immutable historical evidence. Their old inventory counts or planning comments are not the current project status. Documentation-only commits may advance main while the mathematical snapshot and its receipt remain at the accepted proof version.

Source baseline: [shao@35d4580](https://github.com/randomcat4/shao/tree/35d4580b61e22e7145f47730045a09874ef93259). The separate unified-124 research objective is not a prerequisite for the accepted original scopes.

- v122: one common countably generated sub-sigma algebra preserving the same original jointly measurable kernel and all countable scalar observables, including empty spaces. Law/integral/moment/CDF transport remains open.

- v123: bounded changing-row positive-boundary/studentized limits and deterministic-strip energy Laplace ratios; conditional same-kernel/coarser-law integral, moment and sample-law transport. Full changing-row shrinking windows and literal CDF/root applications remain open.
