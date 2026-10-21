# OQ5 fixed-law integration acceptance

PR #6 constructs the fixed category probability law, its exact first and second moments, a Borel real observation encoding with Uniform[-1,1] noise, the actual pushforward probability law, and the centered category feature with mean zero and variance 1/15 - 1/511^2 > 0. The distribution is independent of the current sample size. These six modules add 43 public theorems (61 public declarations including definitions and instances).

All mathematical source bytes match the frozen ff2ee3834d2a04b477632f99d2ccd9db42c56fcd PR head and the accepted normalization hashes. See oq5-fixed-law-frozen.md, oq5-fixed-law-review.md and oq5-fixed-law-scope.md. The independent normalization acceptance preserved original reviews and verified byte equivalence after line-ending normalization, with fresh server checks at the current source hashes.

This integration includes the latest common and OQ4 foundations, adds Shao.OQ5.P35.FixedLaw to the root import and updates the public theorem inventory. The server build and transitive axiom audit cover 244 public source theorems and 395 theorem declarations including generated declarations. Only propext, Classical.choice and Quot.sound are permitted. Exact receipts are verification/receipt-v6.json and verification/declarations-v6.json. Unchanged dependency artifacts were reused after source byte identity checks; no local Lean validation ran.

The infinite sample, population kernel integrability, projection, rank, Studentizer positivity and tail estimates remain subsequent units. No fourth moment is assumed. This milestone does not close OQ5/OQ6 or any other complete root theorem and does not revise the source mathematical verdicts.
