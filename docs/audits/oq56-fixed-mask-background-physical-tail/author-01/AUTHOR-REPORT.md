# Unit281 complete frozen implementation author report

STATUS: COMPLETE_IMPLEMENTATION_TEXT; INDEPENDENT_SOURCE_REVIEW_AND_SERVER_GATES_PENDING.

The complete source FixedMaskConditionalBackgroundPhysicalTail.lean implements all18 frozen declarations: three fixed definitions and fifteen public theorem proofs. The exact parent freeze is 6cda9b8cd087cd9b29b8b4275a8f385d7c6dfaab1feb1aa7a4249e18c0a72712 /13617B. No frozen HEAD, fixed RHS, PRE or CLOSE was changed. No extra top-level helper, premise, import or option was added. All helper reasoning and probability-measure instances are local to their theorem.

The activation a480a6177a2e7187e7a97b803732df510731fd2f61eddbabe03e08222da5c590 /22616B and all88 immutable input bindings were verified before the first author-01 write. This same canonical author communicated an observed runtime ACK before writing. Its earlier proposal LAST remains sealed and read-only; the new implementation activation supplies the present authority.

## Mathematical work completed

T01 proves that the actual mixed membership intersection is measurable. T02 rewrites it to an actual finite rectangle, applies the pinned finite product measure formula, and splits the coordinate product by B and its finite complement. Its exponents are B.card and n-B.card. T03 takes ENNReal.toReal and uses the measurable complement probability to obtain d^m(1-d)^K. No combinatorial factor is inserted because the retained set B is fixed.

T04 proves the all-good, no-good, d=0 and d=1 endpoint statements from the same exact mass formula. In particular K=0 gives the anomalous factor a zeroth power even when d=1; m=0 gives the retained factor a zeroth power even when d=0. At n=0 the empty finite product has mass1. The proof never changes the standard 0^0=1 convention.

T05 proves measurable backgroundSample for the actual Ω-valued sample and arbitrary equivalence e, using typed coordinate-evaluation measurability. Its order is unrestricted.

T06 uses the accepted generic indep_cond_joint_map_eq_pi with the complete Fin n evaluation family and the actual mixed coordinate events. It first identifies cond P E_B with the heterogeneous product of conditional coordinate marginals. A full-mask nonzero premise then gives nonzero mass for every actually indexed coordinate event by monotonicity and the original evaluation marginal. Each such conditional coordinate measure receives a probability instance. The selected evaluation family is obtained by injective precomposition with j↦(e j).val, and its joint map is the product of the selected conditional marginals. Retained membership makes each selected conditional marginal exactly (μ C)⁻¹ • μ.restrict C.

This proof never asserts μ C≠0 merely because the full mask is nonzero. For B empty there is no retained index. The family of required selected identities is empty, so the empty product law is retained without such an assertion. No real-valued retained samplePath corollary, ordering assumption, StandardBorel structure or RCD construction is used.

T07 performs its P E_B=0 split before any normalization or inverse cancellation. In the zero branch, every measurable evaluation of P.restrict E_B is zero by monotonicity; its pushforward and the zero-weight right side are zero. In the nonzero branch only, finiteness of the original product probability permits inverse cancellation and recovers P.restrict E_B=(P E_B)•cond P E_B. The measurable map commutes with this scalar multiplication and T06 completes the identity. There is no common-background probability instance in the zero branch.

T08 proves measurable scaledResidual as constant multiplication of the original measurable uncurry r, with explicit typed functions. T09 uses only the first component of the accepted public physical_clipped_globally_measurable theorem, at auxiliary C0=rho=y=0. Its guarded projection ratio equals actual279 physicalStatistic pointwise by the qualified projection-ratio bridge and total real division at zero. Pointwise r symmetry and dimension≥4 remain explicit. The old finite-sum measurability proof is not copied.

T10 obtains a measurable actual physical closed upper tail for the λ-scaled residual. T11 derives ambient n≥4 from B.card≥4 and B.card≤n, then uses the exact279 guarded background bridge to identify the original-row tail with the actual backgroundSample preimage. D03 fixes the original backgroundNumerator/backgroundStudentizer coefficients and the explicit zero guard. T12 obtains the original-row event's measurability from this preimage identity.

T13 evaluates the genuine conditional pushforward at the measurable closed-tail event and takes toReal. T14 evaluates the zero-safe restricted pushforward from T07, rewrites the actual preimage to D03 and applies restrict evaluation. Taking toReal and T03 gives the required weighted original P intersection identity. T14 does not divide by a mask mass and is valid for masks of weight0. T15 derives cutoff measurability from w and specializes the exact law, conditional tail and weighted original tail identities to C={o | w o≤R}.

## Source fidelity and boundary scope

All generic statements keep arbitrary measurable Ω, every n, every fixed B and arbitrary fixed e. No distinctness of observed values is assumed. Repeated observations and atoms are allowed.

Only the physical corollaries carry pointwise r symmetry and m≥4. The accepted279 ratio identity requires them; they have not been silently discarded. The actual λ=(m-2)/(n-2) remains the frozen scaledResidual, with the original n denominator. No conditional canonicality, true projection or variance statement is inferred for the original g/r.

All physical events are closed z≤T at every real z. The Studentizer-zero guard sets the statistic to0 on both sides of T11. Such points belong exactly for z≤0, including at the atom z=0. No closed-to-strict replacement, continuity assumption or atomless law is used.

The p41 background algebra may start at m≥3, but the supplied actual physical interface and this freeze require m≥4. No m=3 physical extension is claimed. Generic T01-T07 remain valid at m=0 and all other cardinalities.

## Exact supplier and API evidence

The exact qualified279 source and first original object are reused unchanged. Full six actual TYPEs, full three non-theorem VALUEs and six public HEAD/RHS contexts are included in the author bundle; one total-ratio interface is read-only context, while the projection-ratio and guarded background interfaces are the actual theorem calls. Their exact evidence was already independently qualified and is not replayed.

The full generic ConditionalIID producer source, full public physical measurability HEAD and complete pinned Pi rectangle declaration/context were read. Additional authorized curated reads bind exact accepted call-site contexts for heterogeneous product evaluation, injective retained precomposition, cond_isProbabilityMeasure, complement probabilities, finite product splitting, normalized restriction and finite ENNReal cancellation. The report records source HEADs separately from actually printed TYPEs. No new Mathlib #print or server fetch is claimed.

USED-SUPPLIER-AND-API-COVERAGE.json records all these uses and their local evidence. It also states the local imported-API coverage limit: some general Mathlib independence/conditional methods have accepted exact call sites here rather than a newly printed full declaration. That does not constitute a compiler result for the new source.

## Deliverables and checks

The directory includes every exact copied HEAD/RHS/PRE/CLOSE, all fifteen individual PROOF components, ALLHEAD.txt, ALLPROOF.txt, complete source, per-declaration byte/line assembly map, supplier full interface copies, API bindings, this report, MFT.md, static guard, manifest and unique final LAST.

The proof components begin literally with := by followed by LF. Definition HEADs own the outer := exactly once; the following RHS is bare. A deterministic byte reconstruction checks the source against these exact components and separately checks both concatenated streams. UTF-8 without BOM, LF-only and a single final LF are required. Source declaration counts and line/byte spans are derived from these actual files.

Only local text/hash/format/static-guard checks are authorized. No Lean, axiom audit, compiler/environment probe, SSH, network, upload, Git/API publication, child, Goal or schedule was run. All original proposal/freeze/library/shared/source/other-owner files were read-only. SourceAccepted=false, KernelChecked=false and Qualified=false for281. Actual compiled owner counts, TYPE/VALUE output and transitive axioms are null until the later server gates; no successful proof or machine result is invented.

## Next source-bound work and open scope

Next282 may compose this actual fixed-mask law/event transport with the already qualified276 full-window conditional theorem. It must preserve the SAME original model and physical statistic, true conditional mean/projection/variance, common N before λ,m,z, n≤2m≤2n, λ∈[0,1], z≥1 window and the original external hSZ/hSZC contracts. This implementation does not reconstruct those276 producers or perform that quantitative composition.

Conditioning on complete anomalous values, interaction concentration, Δ/threshold loss, quantitative low-s_B costs, anomaly exponential integration, discarded large-K/Q probability and unconditional PE-R/PE-L/NR/DC/full OQ56/root conclusions remain OPEN.

## Provenance, independent review and release

This is the same author as the sealed declaration proposal, explicitly reactivated after parent substantive freeze. The author supplies complete proofs but does not perform or claim the required independent SOURCE/proof review. Parent independent SOURCE and exact-source server kernel/all-owned-transitive-axiom gates follow.

Requested settings are gpt-6.1-sol/xhigh. Actual model, backend, effort and separate input/cached-input/output/reasoning-subset token counts are null because they are not exposed. Requested settings are not presented as measured usage or subscription allocation.

After the manifest and unique LAST are sealed, all active and dormant authority of this implementation role is released with six work counters zero, child0, no queued continuation and no active wait. No further writes are authorized from the sealed role without a new explicit parent activation.
