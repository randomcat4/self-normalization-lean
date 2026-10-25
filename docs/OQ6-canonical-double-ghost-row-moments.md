# Canonical double-ghost row moments

The module `Shao.OQ6.CanonicalDoubleGhostRowMoments` proves the actual original-sample row bound in p44 equations (1)–(4). For the original Euclidean row vector R_i(x) = Σ_{j≠i} r(x_i,x_j), and paired energy S(z) = Σ_i (w(z_i.1)+w(z_i.2))², its final theorem gives actual integrability and

    (∫ ‖R‖₂^q dν^n)^(1/q) ≤ 2√q · (∫ S^q d(ν⊗ν)^n)^(1/q).

The inputs are a probability measure, a product-measurable and product-L1 kernel, both almost-everywhere canonical marginals, real q at least two, an almost-everywhere nonnegative product envelope, and actual paired-energy q-power integrability. The sample space has only a measurable structure. The statement permits nonmeasurable w when the stated energy integrability and almost-everywhere envelope hold. Both canonical marginals are explicit, so the row result also covers nonsymmetric kernels satisfying them.

## Mathematical interfaces

The five definitions use the genuine finite product laws and `EuclideanSpace` with exponent two. The five theorems establish:

- The actual measure-preserving map from two independent original sample vectors to the vector of coordinate pairs.
- Original and ghost Bochner L1, almost-everywhere ghost-section L1, and the complete vector ghost mean equal to the original row vector.
- Vector q-power Jensen with all scalar concavity, closed-set, continuity and integrability conditions paid.
- Actual ghost q-power integrability and its dimension-free outer integral bound, using qualified 187 norm invariance and 186 finite sign moments.
- Actual original-row q-power integrability and the displayed final moment-root estimate.

Four-corner L1 and product-envelope pullbacks always carry distinct-index evidence. The diagonal is defined to be zero; no property of r(a,a) is assumed. Energy measurability is recovered from the given S^q integrability by a continuous reciprocal-power map. A crude square-root-of-n bound serves only to prove Lq integrability. The final constant is exactly two times square-root-of-q. Empty and singleton index sets, zero weights and zero energy require no division by n or energy.

## Exact evidence

The final source is `0b7f38c8840ffefb15fc9185c8f54c2c6907da96cc49bd5e7ee3c5ed512250fc` (38651 bytes, 569 LF). Its original successful object is `039bdc5ca03a7505762d852b8e6464c7f88de90c5b68914e6aaf6e6cb3a50d85` (834464 bytes).

Native02 returned actual Lean RC0 in 7.268890615552664 seconds. The same-object metadata and recursive-axiom audit returned actual Lean RC0 in 5.461736064404249 seconds. Source warnings number thirteen, with no error; the audit has only the existing 134-byte Lake environment warning. Both strict wrapper results remain false, FIRSTEMPTY remains false, and manual AUTHOR-STOP prevents recompilation to clean warnings.

The whole imported-module-index inventory has 28 actual owners: 23 theorem constants and five definitions, with 761 complete TYPE lines and 27 complete non-theorem VALUE lines. All recursive axioms are within propext, Classical.choice and Quot.sound. Eighteen generated declarations include two outside this module's namespace, `FiniteHilbertSignMoments.energy.eq_1` and `DoubleGhostSignInvariance.pairedLaw.eq_1`; neither is omitted or treated as a changed producer definition. The audit output is exactly reconstructible in memory as 68243 bytes with SHA256 `e59c801389591823d57ffd5962be5f3cbc70fe4521c9d8388526c20efa4af577`.

The original source `1ac13836...` failed native01 with nineteen errors and twelve warnings and produced no object. Its bytes, failure receipt and full source review remain archived. The repair changes four proof bodies, preserving all ten declaration heads, five global values, fifty-three local data types and values, and mathematical assumptions. The linked original review, complete changed-proof review, final independent review, coverage and parent/independent qualification records jointly document the final exact source. Qualified 185/186/187 producer proofs and objects are reused without replay.

## Remaining source scope

This unit supplies the original row-vector moment step. Scalar F, the outer scalar chaos moment, tails, DC and the C2/C12/OQ56 roots remain open. The p54 repairs and Shao–Zhou Lemma 6.1 attribution retain their original scope. The 124 mechanism is not a prerequisite. OQ3 remains paused by the user.
