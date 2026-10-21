# OQ56 unit30 blind source-to-root-contract review

STATUS: CORRECT
GATE: source translation and completeness only; no unit30 proof or Lean certification. No unit30 implementation existed at inspection. All full roots remain OPEN pending implementation, fresh proof/axiom review, and separate root integration.

Reviewed the exact forty ordered clauses of frozen v1 against original p35 sections 1-7 and the public root contract. Inspected the bound actual definitions and relevant accepted public theorem types, plus only the frozen declaration types of unit29. Did not read actual unit29 proof, author reports, API notes, chats, drafts, or any unit30 implementation. No Lean, builds, source/cache/git edits, or proof authoring occurred.

## Bound inputs

- Original p35: C:/game/shao/current/oq56/inputs02/p35.md, SHA256 f5308d1bcdbe2c54e075626617572bf264e3148dd4393324a22ac9664e4e2da5.
- Public root contract: library/docs/oq5-counterexample-contract.md, SHA256 552c2239210552f9f4dedb268886697233bae16e0b33dcb2fecb86727ee5e696.
- Unit30 frozen v1: drafts/oq56/unit30/frozen-v1.md, SHA256 17a7ebdfc65ae3794093a0579e60481e2b62d107a37cbf2e53ad1656752b3443.
- Unit29 frozen declaration types: drafts/oq56/unit29/frozen-v1.md, SHA256 4d32aefc64bac991acfd63f0712e0cc403c385de6538f9239f822852afde53c9.

## All forty clauses: source and contract coverage

The numbers below are the exact frozen order, without merging or dropping any conjunct.

| Clause | Meaning and source/contract obligation |
|---:|---|
| 1 | The actual once-fixed real observation law is a probability measure: C0, p35 70-84, contract section 2. |
| 2 | The actual infinite sample law is a probability measure: C0, same fixed real law for all sample sizes. |
| 3 | Every coordinate observation is measurable: C0 infinite iid realization. |
| 4 | Every coordinate has exactly realLaw: identical distribution, with no n-dependent law. |
| 5 | The entire coordinate family is independent under sampleLaw: actual infinite iid, not merely finite replacement variables. |
| 6 | The fixed population kernel is Borel measurable on the real product: p35 11, 80-84. |
| 7 | That same kernel is symmetric: p35 11 and formula (8). |
| 8 | The actual kernel is integrable under the independent two-observation product law: a valid population mean. |
| 9 | Its square is integrable: E h(X1,X2)^2 < infinity, C1, p35 13 and 95-99. |
| 10 | The actual double integral equals populationMean: theta = E h, p35 15 and 88-89. |
| 11 | Every fixed-x kernel section is integrable and its integral minus theta is the actual projection g(x): exact raw Hoeffding projection, not a surrogate. |
| 12 | g is integrable: valid expectation for the centered projection. |
| 13 | E g = 0: C1 and contract section 2. |
| 14 | g^2 is integrable: finite projection second moment. |
| 15 | E g^2 > 0: nondegenerate raw projection variance, p35 13 and 99. |
| 16 | |g|^3 is integrable: the required third absolute projection moment, p35 13 and 99. |
| 17 | The actual decoded feature Z is integrable. |
| 18 | E Z = 0: p35 (1), 75 and 86. |
| 19 | Z^2 is integrable: no fourth-moment assumption. |
| 20 | E Z^2 equals the actual explicit featureVariance = 1/15 - 1/511^2. |
| 21 | That raw feature variance is strictly positive: p35 (1), C1. |
| 22 | The actual residual equals h - theta - g(x) - g(y), pointwise for all real inputs. Its bound definition is exactly -Z(x)Z(y). |
| 23 | Every residual section is integrable and has integral zero: canonical degeneracy. Symmetry is already inherited from the actual negative product. |
| 24 | For every element of the full quotient L2(realLaw), all residual-product sections are integrable and residualOperator agrees almost everywhere with the residual integral action. This identifies the actual integral operator on full L2. |
| 25 | The actual full operator range is exactly span{featureL2}: the nonzero feature direction, not a restriction of the domain to a chosen span. |
| 26 | The actual full operator has rank exactly one. |
| 27 | Its complete set of nonzero real eigenvalues is the singleton {-featureVariance}: correct unscaled negative eigenvalue, p35 17-19 and 99. |
| 28 | For every positive domination constant, the actual product-law violation event has positive mass: domination fails on positive-probability sets, p35 101 and contract section 2. |
| 29 | For every fixed n >= 3, the actual R_n is positive with probability one: Q5, p35 (18), not only along n_j. |
| 30 | The complete deterministic x_n tends to infinity: A0, p35 209-213. |
| 31 | x_n / n^(1/6) tends to zero: the stronger source admissibility scale. |
| 32 | x_n / sqrt(n) tends to zero: the original logarithmic assertion's admissibility scale. |
| 33 | The actual prescribed n_j is strictly increasing. |
| 34 | That actual subsequence tends to infinity: a valid route from full-n limits to subsequence limits. |
| 35 | The actual logarithmic tail ratio tends to zero only along n_j: p35 (2), 215-216. |
| 36 | The actual Gaussian-relative tail ratio tends to positive infinity only along n_j: p35 (2), 218-221. |
| 37 | For the same admissible complete x_n, the full-n logarithmic ratio does not tend to one: explicit witness refuting the first original universal conclusion. |
| 38 | The complete b_n = 2*x_n has b_n / n^(1/6) tending to zero. |
| 39 | For all n >= 1 the witness x_n is nonnegative and lies strictly below b_n; in particular b_n > 0 on the original n >= 3 domain. |
| 40 | The actual relative-tail error fails the necessary epsilon-uniform approximation on 0 <= t < b_n: explicit admissible-window witness refuting the original supremum formulation. It asserts neither failure for every window nor arbitrary user thresholds. |

Clauses 1-28 cover the fixed construction and C1; clause 29 is Q5; clauses 30-34 and 38-39 are A0; clauses 35-37 and 40 give A1 and the two required original-conclusion refutations. The intended unconditional theorem fixedLawCounterexample : FixedLawCounterexample has no hypothesis or free law/kernel/limit parameter. Thus this is a concrete fixed-witness certificate, not an assumption package accepted as a theorem.

## Underlying definitions inspected

The source values are preserved: category mass 16382/16383 at zero and (1/16384)^j above zero; k_j = 4^j, v_0 = 0, v_j = 32^j, mu = 1/511, Z = v_C-mu, d_0 = 0 and d_j = (k_j-1) Z_j^2/(k_j^4-2). categoryMeasure is the countable weighted-Dirac law, not a finite truncation. noiseLaw is normalized Lebesgue restriction to [-1,1]. realLaw is the pushforward of categoryMeasure.prod noiseLaw by (C,A) -> 3*C+A; sampleLaw is its infinite product. None takes the current sample size as a parameter. The Borel decoders recover C and A on the support; their chosen Borel extension outside the support is harmless and is used consistently in kernel and projection.

populationKernel is the raw A(x)+A(y)+d(x)+d(y)-Z(x)Z(y); offsetMean is the actual integral of d, populationMean=2*offsetMean, populationProjection=A+d-offsetMean, and populationResidual=-Z(x)Z(y). Together with clauses 10-11 and 22, these are the actual mean, projection and canonical residual, with no silent recentering or rescaling. The contract allows positive finite raw projection variance. No Eg^2=1 claim is needed or made; the raw eigenvalue remains -(1/15-1/511^2).

ObservationL2 is Lp real 2 realLaw, the full quotient Hilbert space. featureL2 is MemLp.toLp of the actual feature, and residualOperator is rankOne real (-featureL2) featureL2. Its action is therefore f -> -Z*E(Zf), and clause 24 binds this abstract continuous linear operator back to the actual residual integral for every full-L2 input. Clauses 25-27 certify exact full range/rank/eigenvalues. No finite-span substitute is present.

sampleU uses pairCount=n(n-1)/2 and unorderedPairSum summing exactly i<j. sampleRowMean excludes its own coordinate. jackknifeSq is exactly 4(n-1)/(n-2)^2 times the sum over all n centered row squares. sampleStudentizer=sqrt(jackknifeSq); sampleStatistic uses sqrt(n)*(sampleU-populationMean)/R when R>0 and zero otherwise. Clause 29 removes any convention-based counterexample for every fixed n>=3.

The actual x_n is n^(3/20)/16, and rareSampleSize j=(4^j)^4. Its public exact scale identities are x_(n_j)=k_j^(3/5)/16 and x_(n_j)^2/2=k_j^(6/5)/512. standardNormalUpperTail is 1-cdf(gaussianReal 0 1), with accepted public strict positivity for every finite real input and the exp(-x^2/2) upper bound for x>=0. It is not a renamed exponential bound.

The only unit29 definitions used in this review are its frozen types: p35TailProbability n is the actual sampleLaw.real event {T_n >= x_n}, and counterexampleWindow n=2*x_n. No actual unit29 proof was inspected. Its frozen types explicitly provide eventual positive sample tails before logarithmic inequalities. The final root proof review must verify that fact and Gaussian positivity in the real proof chain; this preimplementation review does not claim those unreviewed proofs have passed.

The forty-clause root statement need not repeat every Q0-Q6 intermediate estimate as a conjunct. The public root contract requires their actual proof provenance, which remains a later whole-chain audit obligation. In particular the rare-event cost constant 5 and the stronger source 2*x threshold belong to the imported actual tail-lower-bound chain; the proposed final limits do not replace them with a changed numerical constant. Eventual tail positivity is also not a missing root conclusion: besides its frozen unit29 theorem, it follows from clause 36 and the actual everywhere-positive Gaussian denominator. No log-zero shortcut can be accepted in the subsequent proof review.

The pointwise uniform assertion in clause 40 is the necessary uniform-error consequence of the original supremum-to-zero assertion. Its explicit negation is sufficient to refute that original assertion; a supremum API is unnecessary. Clauses 35-36 assert only subsequence limits. Clauses 37 and 40 are the full-sequence failures actually required. The finite n=0 extension does not change any source statement or atTop limit.

## Hashes of inspected bound source modules

Read-only server worktree: /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56. All paths below are under Shao/OQ5/P35/; source reads included definitions and public declaration types, not author reports.

| File | SHA256 |
|---|---|
| FixedLawCoefficients.lean | 6e78d7a098e466bed295f37700c4a521592602e82e213048eedbea235b1311ee |
| FixedCategoryLaw.lean | fa2a245dcd1db84e72c435835f7ccb43b81e86b2b48a9378ccb8306082d8af17 |
| RealEncoding.lean | e8129c3e46a923c1e336ab4b3cacc8bb26d26060e929180585987a38c3a2523a |
| RealLaw.lean | 87b7ff8d3e2df9b420b5b3e595be412bcb0d53c88f24ed3199f24417b9ef5625 |
| InfiniteSample.lean | cdaa18c8361c59586e04323b523d85b116a830827f84f463bd25d76ebb40987c |
| PopulationKernel.lean | 6709d96689f6a0ee544d1fe32de12c0b8baf69ae1d09cab1189fc6d1f358bba4 |
| KernelMoments.lean | 34c9efb21d34065396aab955464552c42b6ba371ec0a134a8d5fdaad1a4046a6 |
| RealMoments.lean | b254f73230074702afec88c535666f56d1624126f844c035ee670aa2c52dcd62 |
| ProjectionMoments.lean | 68545c519a8ffe968976d3ac4976ce9b4fa7e152120d48a59908717c0c623426 |
| FeatureMoments.lean | b4489379bf8a2b28ce11a76524c8c4b401e5b3c8012f1ef45aae3dcef7d06351 |
| ResidualOperator.lean | f6de6c3e08a74f73f87c265a5d962ba8a34e5c52515c793ede27d751b353feec |
| DominationFailure.lean | 127836b8f83099d67bd6c687037f19ac401e1ca39764167884422052d7fcf239 |
| RowIdentity.lean | 73bb0809bc6d323b31775327e468677d6320b38f8fe87363936860164f17f975 |
| SampleStatistics.lean | 14f5e09f7ddcac10dac43c94cf5a14adf5d44d85896d92cf26e666d496adcf85 |
| RareEvents.lean | 152e198f01c79b34fd3a88ab4b49740fd027980bb0909b31bae2d74a5d074f53 |
| ThresholdScales.lean | a326bf6a3979ae7f1c5f9d5dae597b70c612ba1bb1881d3195ed041f2d00351d |
| GaussianTail.lean | 49ac94290ccedbf6cb7cfe16771702f8a52563fc3e474622305da13d60b3f2a6 |

GAPS: None in the frozen source-to-statement translation or final-bundle coverage. This verdict authorizes only progression past the translation gate. It does not certify the future unit30 proof, unit29 implementation, public import integration, novelty, OQ6, p52/p53 strengthening, RS2, or any other programme root.
