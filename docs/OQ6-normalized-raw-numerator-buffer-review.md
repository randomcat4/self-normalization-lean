# Independent final review — unit159

STATUS: CORRECT

The exact repaired source proves the frozen one-theorem, 13-let, 30-clause contract. It closes the fixed-law, fixed-n, fixed-threshold strict-buffer raw-numerator probability-limsup step of p37 Section 5, equation (16). It does not close an original OQ56 root or invoke the external Shao–Zhou probability theorem.

Reviewer: `/root/oq56_buffer159_final_review`, a fresh independent review context, never an author of this source. The prescribed configuration is gpt-6.1-sol / xhigh. Runtime model, effort, and token telemetry are not exposed and are recorded as null rather than inferred.

## Exact reviewed version and method

The entire repaired `author-01/stage2/repair-01/NormalizedRawNumeratorBuffer.lean` was read, including every proof line: 12075 UTF-8 bytes, 231 LF-terminated lines, SHA256 `76bb9359913e6734026e09ada5890767207b0a2fa0c89e44ccc0db8403fce7cb`. Its entire freeze is `f531c79692ad13d93ea080cfa6f6482f38a6f7ce01e420409b083869586f9d29`. The raw theorem header is `41e9689b435fe7d430c643de1cc17cca89114bb5927e856e4d1dd8f6575ff5c5`, 3562 UTF-8 bytes. The raw prefix, suffix, four imports, two options, all binders, all 13 literal let values, and all 30 conclusions were checked against that freeze. The source adds no other global declaration.

I independently read the complete original `scope01.md`, `p37.md`, `p38.md`, `p39.md`, and `p54.md`; the complete stage1 proposal and mathematical derivation; the complete original author proof note; the complete repair note, exact three-site delta, repair input bindings and DONE; and the stage1, initial-candidate, repair, direct-kernel and metadata-producer intake records. The old failed source is retained and the exact delta reconstructs the new bytes forwards and the old bytes backwards.

I also read every field of the actual-owned metadata and literally every line of both actual FULLTYPE payloads: 457 source-theorem lines plus 7 generated-theorem lines, 464 lines / 36157 payload bytes in total. There are no non-theorem VALUE payloads. Whole-payload hashes, bytes and line counts were recomputed. `coverage.json` contains individual source-line and FULLTYPE-line hashes, with no uncovered line. This is a source/proof/type/axiom and original-source fidelity review, not merely a declaration-header comparison.

Only local read-only inspection and deterministic hashing were used. I ran no Lean, toolchain probe, build, server/network/Git/cache operation, old-proof check, child, thread, Goal or automation. Existing exact server evidence is reused through its recorded source/object/receipt bindings. Remote raw receipts, stdout and object bytes were not independently fetched or rehashed in this review; their exact original records are preserved in the parent projection.

## Original-source fidelity and the actual mathematical objects

p37 (8) normalizes the actual approximation by its true means and total centered L2 scale. The four qualified150 definitions have exactly that meaning: `actualCoordinateMean` is the integral of Y; `actualCenteredFamily` is Y minus that mean; `actualNormalizationScale` is the square root of the sum of its actual centered square integrals; and `actualNormalizedFamily` uses `(Y-a)/s` through `deterministicAffineObservation`. These are not free normalization parameters.

The genuine-integral issue is covered by the unchanged qualified150 contract. Under a probability law, a measurable bounded-error perturbation of each measurable L2 ξ_i is L2 and L1; its square is integrable, as is the centered square. The full copied hypotheses include centering of ξ and total actual second moment one. The strict smallness condition gives s_k > 1/2, so the normalized family is not relying on a totalized division by zero. I inspected the four actual definition values, the two complete150 normalization interfaces and the complete156 normalization-sequence interface; I verified their exact source/freeze/qualification bindings and reused their qualified proofs without rereviewing or rerunning them.

The invocation at source95–97 passes exactly ν,n,hn,ξ,hξ,hξ2,hξmean,hξenergy,Y,hY,ε,hε,hεsmall,hεlim,herr to qualified156. Its twelve conclusions place η measurability/L2 in position6 and the all-sample Wη/Vη limits in positions9/10. The destructuring matches those positions. The ν, n, ξ and x are fixed; k changes only the approximation. The error bound is for every k,i,ω, so the derived limits are pointwise for every ω. No almost-everywhere input is silently upgraded here.

The 13 frozen values are all literal and correctly preserved:

| Let | Meaning checked |
| --- | --- |
| η | Actual150 normalized family of Y_k under the same ν. |
| W | Sum of the original ξ_i. |
| Wη | Sum of those actual normalized coordinates. |
| V | Square root of the sum of original coordinate squares. |
| Vη | Square root of the sum of actual normalized coordinate squares. |
| b | The real square root of the literal signed `1 + D2`. |
| Dη | `D1 + W - Wη + x*b*(Vη - V)`, with the p37(11) signs and order. |
| E | Strict encoded numerator bad event `x*abs(Dη) > Vη/4`. |
| Eorig | Strict original buffered event `x*abs(D1) > V/8`. |
| Z | Original projection-zero event `V = 0`. |
| p0 | `ν.real Z`, without coded or physical zero-mass substitution. |
| U | Countable union of E_k over k ≥ N. |
| L | Countable intersection of those tail unions. |

The equality atoms and signed correction are the exact p37(11)/(16) mechanism. The theorem proves an isolated raw consequence with fewer unnecessary premises than the whole original scalar-theorem application: independence, positivity of `1+D2`, integrable remainder envelopes, and atomlessness are not needed for this multiplicative step. Their absence is valid here and does not remove them from separate quotient or external-theorem consumers. No integral or moment of D1/D2 is taken.

## Complete proof check and all 30 conclusions

For each fixed sample, b(ω) is a finite real constant. The actual limits Wη_k→W and Vη_k→V imply Dη_k→D1 by addition, subtraction and multiplication by that constant. Taking absolute values and subtracting Vη_k/4 gives convergence of the actual gap to `x*abs(D1)-V/4`. On V>0 and `x*abs(D1)≤V/8`, this limit is at most `-V/8<0`. Convergence to that open negative halfline supplies eventual safety. The original equality boundary at V/8 is included; no event-probability continuity assertion is used.

Outside Eorig∪Z, nonnegative V and V≠0 imply V>0 and nonmembership in Eorig supplies the nonstrict smallness inequality. Eventual safety gives N=N(ω). If such an ω were in L, its membership in U_N would yield a k≥N with the strict bad-event inequality, contradicting safety. This proves L⊆Eorig∪Z with a sample-dependent index. The proof never substitutes a common deterministic index across samples.

| Clause | Source proof | Independent check |
| --- | --- | --- |
| 1 | hDηm,112–114 | Measurable signed sum/difference/product of the literal measurable functions. |
| 2 | hEm,115–117 | Strict comparison of measurable Vη/4 and x·abs(Dη); repaired composition is the actual absolute-value function. |
| 3 | hEorigm,118–119 | Same measurable strict comparison for original V/8 and D1. |
| 4 | hZm,120 | Measurable equality of V and zero. |
| 5 | hUm,121–123 | Countable k union and the proposition-indexed union for N≤k. |
| 6 | hLm,124 | Countable intersection of the measurable U_N. |
| 7 | hVnonneg,125 | Real square-root nonnegativity at every sample. |
| 8 | hVηnonneg,126 | Same for every k and sample. |
| 9 | hWpoint,95–97 | Exact qualified156 all-sample actual-sum limit. |
| 10 | hVpoint,95–97 | Exact qualified156 all-sample actual-energy limit. |
| 11 | hDpoint,127–135 | Explicit local aliases align the same156 limits; cancellation is W−W and V−V, with no new premise. |
| 12 | hgaplim,136–140 | Absolute-value continuity and multiplication by x, then subtraction of Vη/4. |
| 13 | hstrict,141–143 | The limiting gap is ≤−V/8 and −V/8<0 under the exact two premises. |
| 14 | hsafe,144–150 | Eventual membership in the open negative halfline gives the required nonstrict safe inequality. |
| 15 | hLcover,151–165 | Contradiction using a sample-dependent eventual index and actual tail-union membership. |
| 16 | hUanti,166–171 | k≥M and N≤M imply k≥N; thus U_M⊆U_N. |
| 17 | hfinite(E k),172 | A genuine probability measure gives finite ENNReal mass to every set. |
| 18 | hfinite Eorig,172 | The same finite-measure fact. |
| 19 | hfinite Z,172 | The same finite-measure fact, without requiring Z to be null. |
| 20 | hfinite(U N),172 | The same fact for every tail union. |
| 21 | hfinite L,172 | The same fact for the limiting event. |
| 22 | hcoverμ,173 | ENNReal measure monotonicity applied to clause15. |
| 23 | hunionμ,174 | ENNReal union upper bound; no disjointness premise. |
| 24 | hUmeasurelim,175–178 | Decreasing measurable sets, null-measurability, and finite U_0 satisfy continuity from above. |
| 25 | hprob,179–180 | Every real probability of E_k lies in [0,1]. |
| 26 | hUprob,181–182 | Every real probability of U_N lies in [0,1]. |
| 27 | hUreallim,183–186 | Compose the genuine ENNReal limit with toReal continuity at the finite νL. |
| 28 | hrealcover,187–191 | Finite-measure real monotonicity and union bound give ν.real L≤ν.real Eorig+p0. |
| 29 | heventual,192–205 | A fixed tail-union probability is <ν.real L+δ; all k≥N satisfy E_k⊆U_N. |
| 30 | hcobounded/hlimupper/hlimsup,206–222 | Nonnegativity supplies explicit lower coboundedness; each eventual δ bound bounds real limsup, and half the positive excess contradicts any strict excess. |

The return expression at223–227 lists these facts in exactly the frozen conjunction order. There is no discarded conclusion or renamed desired-limit premise.

The order of the measure argument is substantive. `hfinite` precedes measure continuity and every toReal conversion. The ν(U_N) limit is established in ENNReal with finite U_0, before applying continuity of toReal at finite νL. This avoids the infinity-to-zero behavior of totalized toReal. Real measure monotonicity and union bounds are legitimate because ν is finite. The proof explicitly states both [0,1] bounds; the chosen pinned limsup rule requires the provided lower coboundedness and an eventual upper bound. The half-excess argument is sound in the real conditionally complete order. It does not assert that ν(E_k) converges.

## Adversarial boundaries and instantiation

At x=0 both numerator bad events are empty because V,Vη≥0. The proof remains valid, while the separately attributed external tail theorem still has its own x≥1 range. At n=1 all finite sums and normalization contracts remain valid; no pair/deletion argument is used. n=0 is excluded by hn. Dependence among ξ coordinates causes no problem because no independence is used in the raw proof.

At V=0, strict negativity can fail, including when D1=0. The proof retains the entire original Z and pays ν.real Z once. It does not use coded atomlessness to erase original zero energy. An equality atom at `x*abs(D1)=V/8` with V>0 has limiting gap −V/8<0 and is safe. No nullity of equality events is assumed. Eorig and Z need not be disjoint and are combined only by a union bound.

D1 and D2 may be unbounded and nonintegrable but are real-valued and measurable. For each fixed sample, b is finite even when 1+D2≤0 under Lean's real-square-root convention. It is only multiplied in this theorem. No quotient is taken, no positivity is inferred, and no division is licensed downstream without the separate original almost-everywhere positivity hypothesis. There is no H2/mixed fourth moment or hidden L1-remainder premise.

ε need not be monotone. All positive ε_k below the bound and tending to zero are covered, with an every-sample error bound. This is an admissible-sequence version of the original ε↓0 raw step, not a new full-filter formulation. It suffices for the concrete canonical sequence. No uniformity in n, x, the law, or the samplewise eventual index is asserted.

Qualified157's inspected semantic interface supplies the explicit `ε_k=1/(8*sqrt(n)*(k+1))`, all its smallness/limit properties, the literal floor-coded Y, the every-point approximation, and the same augmented ν for every k. Its η uses the very same actual150 family. Its independent complete proof is reused as an instantiation interface, not reproved in this review. The full copied156 assumptions on ξ under ν are obtained by the inspected155 genuine moment/L2 transport. The155 event-law equality applies to every measurable tuple event, so Eorig and Z transfer under q to the original law. Its canonical consumer explicitly identifies ν.real Z with the original P.real Z0.

Thus the p0 here is original projection-zero mass. It is distinct from coded Vη-zero mass, already null in the canonical construction, and from physical centered-row Studentizer-zero mass. The later quotient-versus-multiplication comparison may have its own p0 payment; this theorem's one p0 is not silently canceled against that payment. The canonical application remains available without inserting envelopes or atom assumptions into159. No separate canonical159 consumer is claimed to have been implemented.

## Repair, actual owned declarations and server evidence

The failed source `538d4f1682dca6aaf11ab8331453dd701d5e4f5cd8e2e930de953ef8bf29e029` and failed receipt `8c2131310b45b76fb44a9f6ae2ae3e66e64e7b7faec8a4621300c9f614c8bf32` remain evidence of that failure. Its actual diagnostics are the two unavailable Measurable.abs field projections and one mismatch in cancellation of the156 W/V limits. The delta `00d4e0071c963d6ba341562a9f6e5e5782d4cbafeeb58217bde3ee1e239d04fc` changes precisely those three proof sites: two equivalent continuous-absolute-value compositions and two explicitly typed aliases inside hDpoint. Forward/reverse byte reconstruction and unchanged frozen prefix/header/suffix were verified. There is no fourth repair, mathematical change, assumption change, warning cleanup, or deletion of failed evidence.

The actual owner inventory is selected by equality of the imported environment's module index with the source anchor, not by namespace prefix. I inspected the complete audit program, which scans every such constant, prints every actual type, prints non-theorem definition/opaque values when present, and calls recursive `Lean.collectAxioms` for every owned declaration. It rejects any dependency outside the standard whitelist.

| Actual owned declaration | Payload check | Semantic and axiom check |
| --- | --- | --- |
| `actual_normalized_raw_numerator_bad_event_limsup` | 35766 bytes /457 lines, SHA `a1f05226e708363961975d3d85a532620928472a6728afe852de67d6bcc1d162` | Every line read. The expanded type contains exactly the original binders, 13 literal lets and ordered30 conclusions, ending in real limsup≤ν.real Eorig+p0. Axioms: propext, Classical.choice, Quot.sound. |
| `actual_normalized_raw_numerator_bad_event_limsup._simp_1_1` | 391 bytes /7 lines, SHA `06f88dfec3222f59e105999671c37bb2ece7951e322b8aa9903b6ada4b5c5a55` | Every line read. It is the definitional rewrite `(μ s).toReal = μ.real s` for an arbitrary measure/set; it assumes no desired probability bound, atom condition or finiteness result. Same three allowed axioms. |

Both constants have kind thmInfo and present bodies. There is one source-owned and one generated declaration, two actual TYPE payloads, zero non-theorem VALUE payloads and six recursive axiom occurrences, two of each allowed axiom. No sorryAx, new axiom, unsafe/native_decide, admit or sorry is used. The source syntax and the actual owner inventory agree; the generated simplification theorem was included, not missed because the source has one theorem header.

Actual-owned metadata hash: `6910a0d19731bbf9be1c8871606344301da289d8282602d2af1777fb258e5518`,39371 bytes. Compact hash: `febf3d43460747b697345934a56b0667d9a70ff807f2b32201b272d47f956e04`. Origin projection hash: `ccce86e2a89215c652ddc04d7918a5564a45748b41fbe5784c4fa4945619bdb9`. Producer intake hash: `893fd19c2527e06b9844d7ca594aff25781ed4450f3755db57e81ecd58f2b7f4`. Their module/source/object/payload/receipt/name/count bindings agree.

The original successful server kernel receipt is `497b283332257c71e16ae4e142a2cdc9f50aa3a9e4d82c8aee91018977739c85`: direct exit0,5.615912113s, original object `60a05c09edbbcad9b0149b2bd5c34b1f3a3fe1b9fb76cfaa89e508f885ef0416`,641136 bytes;2468 protected records preserved; group ended, no timeout or post-error. It compiles the exact repaired source with CPU22–25, native -M8192/-j4, under the recorded lane lock.

The original all-owned audit receipt is `f9dadc10ff31369220e114d198f39a51d04b78402fd6f8fba4657d4c4f012fca`: direct exit0,5.129577473s, import-only/no -o,2476 protected records preserved, group ended, no timeout or post-error. It binds the exact same source and original object. The printed stdout's recorded digest/length agree between the metadata and the compact parent evidence.

The wrapper success=false flags are preserved honestly: the producer retained the unused frozen hx warning and the134-byte Lake stderr; the audit retains the same known Lake warning. Direct Lean exit0, original output object and the no-error/preservation/ended records supply the successful kernel/audit evidence. This review does not relabel a failed direct check as success. The first metadata parser's source-head-based COUNT1 guard stopped before artifact writes; the actual audit inventory is COUNT2. The corrected parsing includes the generated declaration and reran no Lean command.

## Scope left open

Accepted139–158 proofs and checks were not replayed or commissioned again. Unit158 is neither imported nor assumed. Its status wording in earlier stage1 notes is historical;159 does not depend on it. This qualification is only for the exact159 raw-numerator theorem and its actual generated simplification theorem.

Still unpaid by159: applying/formalizing the named external Shao–Zhou Theorems2.1/2.2/Remark2.2; assembling the complete analytic upper/lower probability bounds; actual statistic/remainder/envelope validity; p54's actual G∩Cn concentration event, strict controls, failure probabilities and Gaussian-tail division; original iid p0 decay; physical centered-row Studentizer conversion and its separate zero-mass payment; complete original root closure; novelty or historical priority. The p54 correction remains a uniform conditional standardized-p-moment bound, without the false arbitrary-polynomial convergence-rate claim. The actual raw D2 bad event is not replaced by an analytic-envelope event.

All original C12/OQ3/OQ4/OQ56 root groups remain OPEN. OQ3 remains PAUSED_BY_USER. No merge or integration authority is claimed. On writing the completed artifacts, this review owner releases its assigned directory with zero in-flight operations; continuing lane work belongs to the parent owner.
