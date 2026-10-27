# Unit234 original independent reviewer: eight-limit target repair

STATUS: CORRECT — AFFECTED SOURCE REPAIR ACCEPTED FOR NEW NATIVE003 ONLY

The same original never-author reviewer `/root/oq56_single_witness234_source_review` was reactivated by activation SHA256 `c3c31c3daa5383a445d527b5daecab0c60519bf897474fb5611350d52e68fecb`, 3680B. Runtime ACK was written first. Ownership is restricted to this `source-review-repair-02/**` directory. The same author has released the new candidate with zero writer/execution/child authority. Requested model/effort are gpt-6.1-sol/xhigh; actual unexposed model/effort and four usage counts remain null.

Reviewed current source: SHA256 `8cc15a8f79707bc6ff88896cef3125030284e309907966e9eabeb7d4b3a1ca90`, **36755B / 594LF / zero CR / UTF-8 without BOM**. The complete current-source compatibility and all eight affected Prop targets are CORRECT. `sourceAcceptedForNewNativeOnly=true`, `qualified=false`, `kernelPending=true`; native003 and its downstream all-owned machine join remain pending.

## Exact edit and retained evidence

The predecessor is exact source `62069177484ab575f8090ac6e3950990add45afc428b8e45e35548258c397b77`, 35522B/581LF, accepted by the previous affected review for native002 only. I independently compared the full old and new source bytes. Exactly1233 bytes containing13LF were inserted at zero-based byte offset29299, immediately after the unchanged `intro τ hτ`. These bytes are eight `change ... at` commands and occupy current lines470–482. There are zero deleted bytes and zero other byte changes. Removing that block reproduces the entire predecessor source and its exact hash; prefix and suffix are identical separately. Predecessor lines1–469 map to current1–469, and predecessor470–581 map to current483–594. The earlier old-line330 deletion remains exactly as independently reviewed before.

The complete frozen preamble/head and closing are unchanged. Thus all87 ordinary types/RHSs, all46 literal retained analytic clauses, source hypotheses, instances, callback inventory, sole228 witness, canonical normalization and approved aliases/cutoffs remain exact. No new ordinary helper, assumption, callback, witness or observable was added. The first complete independent review and first affected review are reused through the exact source-byte chain. This is not a duplicate full old-proof review or a fresh literal reading of all594 unchanged/new source lines. The new affected context433–571 and all eight new command targets were read completely; the full eight actual native002 target errors, without elision, were read and compared to the needed complete frozen definitions and qualified228 heads.

All55 original immutable mathematical input bindings and all28 first-affected direct bindings were rehashed unchanged. The previous manifests'8+6 payloads, the new author's6 payloads and its11 input bindings were independently verified. Qualified228/229/230 proofs and machine evidence remain exact reusable inputs. No accepted old producer/proof/full review/kernel/leaf-AX check was replayed. The API-MAP artifact binds the unchanged prior complete API evidence and records every actual error block, new full target and exact frozen-clause correspondence.

## Why the eight conversions are mathematically exact

The diagnostic mismatch is at the input neighborhood to `.eventually`: a proof obtained from the retained228 conclusion has its limit value expanded through the original kernel/iid definitions, while the subtraction argument is expressed using local frozen aliases. The existing `simp only [sub_self, abs_zero]` cancels a literally identical expression minus itself; it does not normalize these differently presented let-expression chains. The printed targets have the form `nhds |expandedOriginalValue - frozenAlias|`. Their unresolved predicate metavariables do not supply additional mathematical data.

The repair first gives each existing Tendsto proof the exact public frozen type. Every target is identical to its corresponding retained clause39–46 after whitespace normalization, and that clause has an unchanged qualified228 source head. `change ... at` acts on an already-derived proof and can succeed only when the old and new propositions are definitionally equal; it does not assume an arbitrary limit equality or create a new convergence hypothesis. Actual acceptance of these commands by Lean remains native003's job.

| Existing proof | Retained clause | Native002 error line | Current command lines | Exact limit value after folding |
|---|---:|---:|---:|---|
| hIlim |39|493|470|I0 = original-P integral of exp(S0)|
| hFullLim |40|500|471–472|original-P integral of fullTest0 * exp(S0)|
| hDelLim |41|510|473–474|for each i, original-P integral of deletedTest0 i * exp(S0minus i)|
| hFullRatio |42|517|475–476|full weighted original integral divided by the same full I0|
| hDelRatio |43|527|477–478|each deleted weighted original integral divided by the same full I0|
| hCompactLim |44|537|479–480|for each i, original-P integral of compactDeletedTest0 i|
| hSourceLim |45|541|481|sourceCost0, the full plus sum of deleted weighted integrals over full I0|
| hCostLim |46|545|482|compactCost0 with Lcompact0, original A0/B0 integrals and compact deleted sum|

For hIlim, unfolding I0→S0→ℓ0→ξ0→g/N gives exactly the printed original integral: the exponential of the full sum of z*g(ζ i)/sqrt(n) minus its square/2, with P equal to the original mΩ iid product of μ. Iη and the new-side sequence are the same already-retained objects. No product-law transport or new moment identity is used by this conversion.

For hFullLim, unfolding fullTest0 gives z*A0+z²*B0, A0=|D1|, D1=residualStatisticD n r and B0=studentizerClipBudget n r C0 rho 1. The frozen r=h−g−g and rho=sqrt(original product residual-square integral) match the complete expanded original-kernel error type. The multiplication by exp(S0) and original P remain literal. The new-side fullTestη and Sη are unchanged.

For hDelLim, deletedTest0 is the capped source-z weight `min |z*ξ0 i| 1` times `|A0−A0delete i| + z*|B0−B0delete i|`. Substituting the absolute residual statistics and original-length deletion budgets explains the nested absolute bars printed by Lean. S0minus erases i only from the exponential sum; the finite sample length n and original n−1/n−2 coefficient conventions do not change. This is the exact original-law deleted cost, without an added independence assumption.

For hFullRatio and hDelRatio, the numerators are exactly those just checked. Both denominator targets are I0, the full original partition integral. In particular, no deleted partition denominator or fresh normalizer is substituted. The expanded full exponential integrals in the two printed denominators are exactly I0 by its frozen RHS; the augmented denominators remain the same Iη k. Existing positivity/integrability is untouched.

For hCompactLim, compactDeletedTest0 has the distinct cap `min |ξ0 i| (1+z)⁻¹`, multiplied by the same absolute deletion differences. It has no exponential factor. The complete printed error type has precisely that cap and original P, so the change does not confuse the source-z and compact1+z regimes.

For hSourceLim, sourceCost0 expands to the full weighted integral plus the finite sum of deleted weighted integrals, all divided by I0. The complete printed expression contains the same addition, sum, caps, original kernel/rho/clipping1 definitions, exponentials and full denominator. It is a folding of a frozen ordinary value, not an additional source-cost limit assumption.

For hCostLim, compactCost0 expands to Lcompact0 + integral A0 + z*integral B0 + sum of compact deleted integrals. Lcompact0 has the separate literal scale1+z inside the squared capped projection moments. Each term and its original P in the full printed error type matches that RHS. No source-z replacement, weighted-product L1 claim, rate, uniformity or additional moment is introduced.

All eight type annotations occur after τ>0 is introduced, but none of their target types contains τ. Thus they do not condition convergence on a tolerance or alter its quantifiers. Once folded, subtraction is by the exact displayed limiting value and absolute value converges to |c−c|=0; the existing strict-neighborhood proof applies. Every subsequent event proof, finite-coordinate conjunction and single common cutoff is unchanged. The source230 and generic229 premises, true original-P/P₀/ν integrability and transports, and the analytic packet outside the source-window guard are also unchanged.

## Failed native002 and remaining qualification

The hash-bound saved diagnostics report natural RC1 after16.82541251182556 seconds, timed_out=false, all owned group members ended, preservation equality true, and object_after=null. The complete diagnostic text contains eight source type errors at493/500/510/517/527/537/541/545, six warning-only letI messages at313/314/316/338/339/354, and the separately preserved mathlib-local-changes stderr warning. All eight errors and their full expanded expected types are retained in the new API map and input record. Native001 and native002 remain failed attempts without objects; neither is a pass, an AX result or an uncertain in-flight operation to replay.

This source review authorizes only new native003 on exact8cc15a8f source. It does not guarantee that every new annotation or unchanged downstream tactic elaborates. Success must be followed by a same-first-original-object audit of all actual module-index TYPE/VALUE/recursive axioms and this same independent context's final semantic join. Actual private/generated owner counts remain pending; the whitelist remains propext, Classical.choice and Quot.sound.

The original same-witness interface scope is unchanged; broader OQ56 remains OPEN. No actual-goodset/SZ/CDF/atom/zero-event/root completion follows. This affected turn opened no233/235 unqualified proof/review material. No Lean, server, network/upload, Git/API, child, source/freeze or other-owner write occurred. The final release sets writer/heavy/inflight/pendingExternal/pendingWrites/children to zero.
