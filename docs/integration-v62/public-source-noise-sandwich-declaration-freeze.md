# Actual source-noise strict-CDF sandwich — declaration freeze

Root author/coordinator freeze, 2026-10-24. The exact selected declarations
are the two complete heads in
`drafts/c12-source-noise-sandwich/candidate-declarations.lean.txt`.
All literal let-bindings are part of these frozen heads. The proof is
`drafts/c12-source-noise-sandwich/candidate-proof.md`.

Selected public heads:

1. `Shao.sourceFourierTest_noise_sandwich_pointwise`.
2. `Shao.sourceTruncation_actual_noise_cdf_sandwich`.

Zero new global/private definitions. Additional private helper THEOREMS are
authorized, with every actual private/generated declaration included in the
final complete actual-owned-type/transitive-axiom review. No change to the
selected assumptions, constants, quantifier order, product law or let-values
is authorized without a separate explicit root revision.

Only two actual source products are selected. The first proves the genuine
strict-indicator comparison on the actual cutoff plateau; the second proves
the true integral sandwich under the actual fixed-cutoff law and full noise.
Measurability of the arbitrary real sample statistic is a structural input,
not a desired comparison premise. No integrability of that statistic or
no-atom hypothesis is added. Negative CDF arguments and zero clock remain
literal in the frozen statement. The same fixed-x noise is used for all y.

The explicit epsilon≤1/800 is selected before implementation to pay the
accepted actual full-noise support constant 100 and |Y|≤1/8. It narrows only
this new auxiliary interface and does not change any accepted old result.
Actual bad-clock numerical payment, weighted Gaussian cost, weighted-sup
contraction, endpoint approximation and C1/C2 closure remain downstream.

Root may author the implementation; acceptance then requires a fresh
independent complete reviewer. All Lean checking remains on the server,
CPU10–13/root-heavy.lock/-M8192/-j4, fixed toolchain/package cache. Original
accepted source/object/review receipts are reused, with no old recompilation.
New implementation write authority is limited to
`drafts/c12-source-noise-sandwich/SourceNoiseSandwich.lean` locally and a
separately activated remote `Shao/Probability/SourceNoiseSandwich.lean`.
This freeze alone grants no remote worktree write authority.
