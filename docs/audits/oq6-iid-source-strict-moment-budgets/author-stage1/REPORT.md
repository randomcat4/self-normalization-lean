# Unit 230 Stage 1 author report

Status: READY_FOR_LEAD_DECLARATION_FREEZE; LEAN_TRANSLATION_UNAUDITED.

The new substantive proposed result is the single generic IID theorem in
`CANDIDATE.md`, with full preamble, binders, ordinary typed lets and right-hand
sides. It handles the actual source-z truncated budget, its genuine scalar and
product integrability, equal marginal integrals, `L=n*δ_i`, the p-moment rate,
and strict individual/total original margins. A complete source map and
implementation route are in `SOURCE-AND-ROUTE.md`.

The proposed constant is explicit:

`c = Real.rpow (min (1/2) cBudget / 2) (1/p)`.

Thus `c^p=min(1/2,cBudget)/2`, and c depends only on `p,cBudget`, before all
`n,z`. For positive beta the rate and the printed S19 window give `L≤c^p`.
For beta zero the unconditional rate forces all budgets to vanish; this is
handled in an explicit branch. No beta positivity or standardized second
moment is silently assumed. Generic `cBudget>0` is not identified with a
published Shao-Zhou constant. Both `p=3` and the excluded lower endpoint `p=2`
are discussed explicitly. No sufficiently-large-n threshold is part of the
candidate; for positive beta its positive window exponent gives eventual
nonemptiness without modifying the all-n conditional claim.

The entire primary p51 source was read, including S4, as was the complete
qualified scalar public declaration and the full TruncationIntegrals source.
The qualified scalar API is instantiated at `y=z-1`; no `1+z` compact bound
is substituted. The old producer's exact source/qualified-evidence bytes are
bound in `INPUT-BINDINGS.json`. Its existing independent qualification is
reused rather than re-reviewed. The source's own repair-candidate status and
external attribution are preserved.

The finite-product transport is standard `measurePreserving_eval` plus its
integrability transport and `integral_map`; no arbitrary-space encoding or
new shared Probability implementation is needed. The positive-beta power
cancellation is fully specified in the route using actual qualified local
mathlib API names. No mathematical blocker was found. That is a Stage 1
assessment, not an elaboration result or independent correctness verdict.

The assignment activation and brief hashes matched their supplied values.
Actual runtime ACK was sent to the lead after reading them. No source file was
written outside `drafts/oq56/unit230/author-stage1-01/**`. No unit228 or unit229
source was opened or used. The read-only curated snapshot was not changed.

Actions performed: local read-only source and exact-evidence inspection,
bounded source-name searches, local SHA256/byte binding, and creation of this
Stage 1 proposal packet. No Lean implementation, local/server Lean execution,
server request, network request, transfer, Git/API publication, or child
delegation occurred. No mathematical source bytes were changed.

Requested model: `gpt-6.1-sol`; requested effort: `xhigh`; fresh context: true.
The actual model/effort and token counters are not exposed to this author and
are recorded as null. No estimated subscription allocation or fabricated
token usage is reported.

The lead may now accept/reject or edit the candidate, then freeze exact
declarations before a separate implementation authorization. The next
mathematical task after that freeze is the implementation of this one new
source-bound generic budget theorem, followed by independent complete review
and exact-source server kernel/transitive-axiom evidence. This Stage 1 author
releases its writer slot with zero ongoing or pending execution.
