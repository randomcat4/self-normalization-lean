# Unit212 independent complete SOURCE review

STATUS: CORRECT

This is a complete independent source-to-statement and proof review of the exact 294-line candidate `Shao.OQ5.P51.ClippedDeletionEnvelope`. The candidate is accepted for its first source-bound native check. It is **not formally qualified**: no new native kernel receipt, actual-owner TYPE/FULLVALUE enumeration, or recursive-axiom receipt was available to this reviewer at this stage. The same independent reviewer must examine that evidence after the first successful native check.

The reviewed source is `drafts/oq56/unit212/author-01/stage2/ClippedDeletionEnvelope.lean`, SHA256 `ff1dfa393df846344a790f1862c05f48ea66365bb6d0c1fe903eb67d95d06e58`, 13,341 bytes, 294 LF bytes, UTF-8 without BOM or CR, with a single final LF. The reviewer is `/root/oq56_clippeddeletion212_final_review`, separate from the author `/root/oq56_clippeddeletion212_author`. This review wrote only the new `unit212/final-review-01/` directory. It ran no server, Lean, axiom, network, Git, API, or upload operation and changed no mathematical source.

## Frozen statement and original scope

The complete parent freeze `f690fcf4b7aea4c0f323c0863406a66f5de6961d6dee91e306fc99db6ad2f580` and canonical data/Prop-closure contract `5ce280d648183f47942274162c7a0b0de12272d27dba3a4a5b7b91c3f7cf993a` were read. All three complete definition bodies and all five complete public theorem heads occur exactly in the reviewed source, in the frozen sequence. The two imports and `autoImplicit false` agree with the freeze. There is no additional global helper, ambient mathematical variable, imported premise, or weakened surviving condition.

The reviewer read original `C:/game/shao/current/oq56/inputs02/p51.md`, SHA256 `96920f428b8fc09788a6388103cefe398e3ec739129a5922b984babd09e99359`, at L9–26, L43–96 and L128–184. S1 fixes the once-counted pair sum F, off-diagonal rows psi, u=psi/(n-2), J=sum u², and D=F/(sqrt(n)(n-1)). S13 specifies D3=|D| and D4=B_y with deleted |D^(i)| and B_y^(i), containing neither a Good indicator nor the deleted observation. The same original n, n-1 and n-2 coefficients must be retained. The reviewed definitions and conclusions implement this deterministic/measurable S13 support exactly.

The original symmetric-kernel premise is retained where the two deletion identities need it. Broader statements about normalization, nonnegativity, coordinate invariance and measurability legitimately require less. There is no hidden iid law, independence, integrability, moment or Standard Borel assumption. These are pointwise finite or measurable-space statements. No statement claims the rho/rho²-sensitive S14 expectation bounds, a probability bound, general S15, or OQ56/root completion.

## Complete declaration and proof review

**L16–21, residualStatisticDDeleted.** The numerator is the once-counted pair sum of the matrix obtained by zeroing all entries incident to i. Its denominator is the original sqrt(n)(n-1). In particular, this is not a resized sample statistic. With a symmetric kernel, the qualified132 deletion identity gives precisely F-FDeleted=psi_i.

**L23–29, residualEnergyJDeleted.** Every row is the qualified132 off-diagonal row sum of that same erased matrix. Row i is zero and row j≠i loses exactly the incident entry r_ij, using symmetry when matching the source expression. The denominator is the unchanged (n-2)². Arbitrary diagonal kernel values are never used.

**L31–36, studentizerClipBudgetDeleted.** This is the frozen affine expression C0 times ((1+rho)y/sqrt(n) + JDeleted/((1+rho)y sqrt(n))). The base term is shared with full B. There is no Good/V=0 branch, sentinel observation, or disguised clipped-delta replacement.

**L38–46, residualEnergyJ_eq_rowSqSum.** The qualified196 type of `residualU_eq_erased_row` identifies each u_j with the off-diagonal raw row divided by n-2. Unfolding J and rowSum, applying `(a/b)^2=a²/b²`, and distributing a fixed division through a finite sum produces exactly the displayed common denominator. This uses no cancellation and remains a valid identity under Lean's total real division when n=2. No positive denominator is inferred outside the intended range.

**L48–68, clippedDeletion_envelopes_nonneg.** Deleted J is a finite sum of nonnegative squares divided by a square, hence nonnegative even if that square is zero. The signs C0≥0, rho≥0, y≥0 imply every term in deleted B is nonnegative; sqrt(n) is nonnegative. Full B uses the exact qualified208 nonnegativity theorem with matching arguments and signs. Both D envelopes are absolute values. No symmetry or stochastic premise enters this proof.

**L70–111, clippedDeletion_coordinate_invariant.** The proof considers each erased entry j,k. If j=i or k=i both sides are zero. Otherwise hxz supplies both retained-coordinate equalities, so the two erased matrices agree extensionally. Applying the pair-sum and row-square functionals proves DDeleted/JDeleted equality; substituting the latter proves BDeleted equality. This covers every matrix entry and proves actual dependence on retained observations. It does not infer independence from an unstated sample law.

**L113–198, clippedDeletion_measurable_factorization.** Both qualified133 actual existential types were read completely. They give measurable real-valued functions on the exact retained function space `{j : Fin n // j ≠ i} → Ω`, with pointwise factor equations for the erased pair sum and raw erased row-square sum. The source chooses exactly those frozen F and L witnesses and obtains both measurability and factor equations from `Classical.choose_spec`. No element of Ω is selected.

The frozen E maps eta to `(|F eta/denD|, C0*(base+(L eta/denJ)/denB))`. Fixed real division, absolute value, addition, multiplication and product pairing preserve measurability for arbitrary constant denominators, including zero. Rewriting the two qualified133 factor equations proves the exact deleted pair factorization. E only accesses the retained eta; neither its type nor its complete initializer captures a removed observation or any Good/V0 indicator.

For the full envelopes, product measurability of r is composed with the two measurable coordinate evaluations. The full pair sum is a finite sum with a fixed Fin-order conditional, so each branch is measurable. The full raw rows are finite measurable sums; their squares, outer sum and fixed division are measurable. The earlier exact J identity converts this into the actual J, and the actual full B definition is its affine expression. Thus both full-envelope measurability conclusions follow without a law, integrability, sign, nonzero denominator, symmetry or observation-space inhabitance premise.

**L200–290, clippedDeletion_cost_identities.** All four header-let values M, psi, Lambda and LambdaDeleted, the repeated proof-local values and all proposition scopes were read in full. Symmetry of M is exactly hsym applied to sample coordinates. n≥4 gives positive sqrt(n), n-1 and n-2; rho≥0 and y≥1 give the remaining positive factors. C0 need only be nonnegative and may be zero.

The full D is definitionally the qualified190 originalUpper sum divided by denD, equal to the accepted P35 once-counted sum at M. Dividing the exact qualified132 pair deletion identity by the common denominator yields the first conjunct. The second conjunct is the real reverse triangle inequality and correctly asserts only an inequality between the absolute-envelope cost and the raw D cost.

The exact full-J normalization and the deleted-J body give `(J-JDeleted)=(Lambda-LambdaDeleted)/(n-2)²`. The second qualified132 identity supplies the entire signed expansion `psi_i² + sum_{j≠i}(2 M_ij(psi_j-M_ij)+M_ij²)`. The proof neither drops that cross term nor assumes its sign. In particular, it does not assert JDeleted≤J.

Subtracting the two frozen B expressions cancels the unchanged base term, and ordinary distributive algebra gives the exact B difference. Substituting the exact J difference, taking absolute values, and using C0≥0 and positive denJ/denB yields precisely `C0*|Lambda-LambdaDeleted|/(denJ*denB)`. Every final conjunction is explicitly supplied. No desired analytic cost is used as an assumption or unproved intermediate lemma.

## Direct consumed evidence and the old P35 decision

The reviewer read all 13 selected direct actual TYPE records and all seven required non-theorem FULLVALUE expressions from groups196/208/190/132/133. The names and coverage are recorded in `COVERAGE.json`. Every selected expression was independently compared with its exact existing saved metadata. Each group's exact qualification hash/bytes and metadata hash/bytes were verified. Its source hash and first-original-object hash occur in the qualification, and its current local curated source bytes match the bound source. All five groups are already qualified; their old theorem proofs and proof VALUEs were reused rather than reread or reexecuted.

The selected complete primary heads/effective contexts at L1–175 were read. This includes the entire relevant P35 source preamble, implicit `{n : ℕ}`, namespace, and complete `unorderedPairSum` initializer. The original read-only `RowIdentity.lean` L1–34 was also read directly and its entire file hash/size verified. The initializer sums each unordered pair once using `i<j`, exactly as actual190 `originalUpper` FULLVALUE does after sampling. Actual132 and actual133 TYPEs explicitly apply `@Shao.OQ5.P35.unorderedPairSum n`, exposing the n argument that source syntax leaves implicit.

I independently accept the parent's narrowly scoped evidence decision: no mathematical type, data initializer, capture, or normalization information is missing for this source review. A separately saved standalone reflected P35 TYPE/FULLVALUE packet is absent and remains explicitly absent; this report does not fabricate one or call the source body a reflected expression. The new consumer's native check must establish actual elaborated compatibility, followed by review of all new actual owners and recursive axioms. Replaying an accepted old producer or leaf-axiom check solely to change this packet's format is unnecessary.

Old140/141/142 and boundary210 are explanatory downstream context, not direct proof dependencies. Their old proofs are outside this review. In particular the old scale s=1+sqrt(v) is not silently substituted for literal rho or rho² in S14, and the actual quadratic-tilt y-window is not conflated with the sigma*y≤sqrt(n) geometry window. Unit211 is independently owned and is neither consumed nor reviewed here.

## Edge, safety and evidence checks

At n=0 there is no i:Fin n. At n=1 or 2, the broader identities and measurability statements retain total real division and do not assert positive statistical denominators. The cost theorem explicitly imposes n≥4 and y≥1. C0=0 and rho=0 are allowed, and neither is a divisor. y=0 is allowed only in the broader claims where total division suffices. Ω may be empty; no Inhabited or selected sentinel value is needed. No ties, hidden diagonal restriction or sample-law premise occurs.

The exact source contains no `sorry`, `admit`, new `axiom`, `unsafe` or `native_decide`. This static scan is not a transitive-axiom certificate. Allowed transitive axioms remain only `propext`, `Classical.choice`, `Quot.sound`. All new actual owners, including generated/private/imported-definition owners, must be determined by the existing server discovery/audit tooling rather than inferred from source declaration counts.

`binding-validation.json` records 52 independently verified current local bindings, with zero mismatches, all eight exact frozen heads/bodies, all 13 selected actual TYPE and seven FULLVALUE comparisons, and the five direct source/Q/O chains. The 19 stage1 non-instruction inputs remain exact. Historical AGENTS.md's 40,634 bytes remain the exact prefix with SHA256 `6a8569365eb2c4e91303b040f4049d5e89018004f616fa45b9b272413737ed7a`; the current 42,736-byte instruction file SHA256 `8a813e9ec5c5afd05f75609fb74424ee0409f96f7d8c056d952530d523cb19fe` appends the already-read v115 instructions. No mathematical binding changed.

The source-map counts are three definitions, five public theorems, 17 actual proof-local non-Prop data values, and four P05 header-let values repeated in the proof. The 17 values and all derived proposition types/bodies/scopes were reviewed from the complete source and frozen closure plan. They are not claims about generated owner counts. Machine coverage remains pending in full.

## Verdict and next checkpoint

No critical mathematical or source-fidelity gap was found in this exact source. `acceptedForNative=true`, `qualified=false`, and `machineEvidencePending=true` are the only acceptance claims at this stage. The lane lead may run the first new-source native check within its current phase/CPU/lock/memory authority, then the same-original-object all-owner audit if it succeeds. A changed proof invalidates only affected review evidence and needs an explicit delta review. Accepted old source/object evidence remains reusable without old checks.

After this payload is sealed, this reviewer has writer/execution/heavy/inflight/pending/children all zero. It can continue the independent qualification only when the parent supplies the exact successful native/first-object/all-actual evidence. Ending this ordinary turn is not a persistent continuation mechanism.

Requested model/effort are gpt-6.1-sol/xhigh. Actual model/effort and input/cached-input/output/reasoning-subset telemetry are unavailable and recorded as null. No subscription-percentage or purchased-credit inference is made.
