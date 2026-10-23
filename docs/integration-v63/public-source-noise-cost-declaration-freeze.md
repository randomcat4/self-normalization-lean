# Actual noise and bad-clock Gaussian-weighted payment: declaration freeze

Root selected and frozen before implementation, 2026-10-24.
The exact complete public head, including all literal let-values, is in
`drafts/c12-source-noise-cost/candidate-declarations.lean.txt`.
Proof plan: `drafts/c12-source-noise-cost/proof-candidate.md`.

Selected: `Shao.sourceTruncation_noise_badClock_weighted_cost`,
module `Shao.Probability.SourceNoiseCost`. One public theorem, zero new
global/private definitions. Additional private helper THEOREMS are authorized;
all actual private/generated types and every local value must be included in
the final fresh complete review. No selected assumptions, constants, objects,
let-values or quantifier order may change without explicit root revision.

Original raw-law finite second moment, mean zero, n raw-second normalization
and original cutoff budget are retained. No raw third-moment finiteness,
conditional-mean zero or no-atom assumption is introduced. This producer pays
the actual bad-clock event and actual same-noise expected displacement against
the genuine Gaussian tail, using already accepted clock/Mills/moment interfaces.
It does not pay weighted-sup contraction, original-CDF pullback or C1/C2 roots.

SourceNoiseSandwich is now exact-hash root-qualified after complete fresh review.
Its original source/object and all old successful receipts are immutable and
reused; no successful producer is recompiled for this unit. Source writing is
limited to `drafts/c12-source-noise-cost/SourceNoiseCost.lean` locally and
`Shao/Probability/SourceNoiseCost.lean` in separately activated root worktree.
Remote activation requires old-writer release; the SNS author/reviewer have
both explicitly released and have no in-flight commands. Use the existing root
CPU10-13/root-heavy.lock/-M8192/-j4 and pinned cache/toolchain. First successful
whole-source check must produce the retained same-invocation -o. One full
actual-owner type/transitive-axiom audit follows; then writer release and a
fresh independent complete review are mandatory for acceptance.
