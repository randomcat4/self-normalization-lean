# OQ56 unit30 final whole-p35 source/proof/axiom gate

STATUS: CORRECT
FORMAL COVERAGE: LEAN_FULLY_CHECKED — the complete original p35 fixed-law counterexample root contract, for the exact source snapshot below.

The original p35 root is fully mechanized at these hashes. This is not merely acceptance of a wrapper: all forty root clauses were checked against the frozen contract, the loaded witness definitions were independently checked, the actual probability/positivity/moment/operator/tail chain was traced, and the entire project-source closure was anchored and scanned. Root-global import/manifest integration and its whole-library gate remain separate. OQ6 and every other programme root remain OPEN; p52/p53 strengthenings, RS2 and novelty are not certified.

Reviewer authored/fixed no project proof. Local write ownership was only this report; remote audit files/logs are only in work/oq56/fresh-review30/. No project source, cache, import manifest, build artifact or Git state was rewritten. No local Lean was run.

## Exact source and contract binding

- Root target: Shao/OQ5/P35/FixedLawCounterexample.lean, SHA256 ac851b0ed4182dadc62acbffe4241b855b7299065a64a875a40b21876d6414dd.
- Frozen unit30: drafts/oq56/unit30/frozen-v1.md, SHA256 17a7ebdfc65ae3794093a0579e60481e2b62d107a37cbf2e53ad1656752b3443.
- Original p35 sections 1-7: C:/game/shao/current/oq56/inputs02/p35.md, SHA256 f5308d1bcdbe2c54e075626617572bf264e3148dd4393324a22ac9664e4e2da5.
- Public root contract: library/docs/oq5-counterexample-contract.md, SHA256 552c2239210552f9f4dedb268886697233bae16e0b33dcb2fecb86727ee5e696.
- Unit29 frozen declaration interface: SHA256 4d32aefc64bac991acfd63f0712e0cc403c385de6538f9239f822852afde53c9.
- Worktree: /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56; observed branch feat/oq56-conditional-bounds, HEAD 4c7ffd668885cf4b582464f99fe327fd0db28385. The source manifest, rather than HEAD alone, identifies the full reviewed snapshot including continuation files.
- Complete recursive project-source import closure: 36 files. Exact manifest source-closure.sha256 has SHA256 164cf342b121ea41ec9a61806c7806c569c5cb11d0a6193ba37e9e3c6508237b.

The 36 current source hashes all matched both the original audit manifest and an independent version anchor: 14 exact immutable ledger hashes supplied for the accepted continuation chain/root, plus 22 byte-for-byte Git source comparisons against frozen commit 4c7ffd668885cf4b582464f99fe327fd0db28385. There were zero mismatches. This anchors imported proofs by source bytes and prior frozen versions, not timestamps. Final rehash at 2026-10-21 13:07:59 UTC found every closure source unchanged.

## Independent comparison of all forty clauses

The root file has exactly one public proposition definition (lines 24-72) and one unconditional public theorem (line 75). No variables, law/kernel parameters, assumed tail estimates, or assumed root conclusions enter their signatures. Its proof (lines 77-103) obtains every conjunct from the actual imported proofs, with only elementary reordering at clauses 11/22 and pairing at 23/24.

In addition to the following source/contract comparison, all forty clauses were independently extracted from the numbered frozen document into an audit proposition. Lean proved its definitional equality to the actual FixedLawCounterexample by rfl. Thus conjunct order, grouping, quantifiers, signs, events, domains and thresholds match the freeze exactly.

| Clause | Root lines | Contract coverage verified |
|---:|---:|---|
| 1 | 25 | Actual once-fixed realLaw is a probability measure. |
| 2 | 26 | Actual infinite sampleLaw is a probability measure. |
| 3 | 27 | Every coordinate observation is measurable. |
| 4 | 28 | Every coordinate has precisely the same realLaw. |
| 5 | 29 | Entire coordinate family is independent under that sampleLaw. |
| 6 | 30 | Actual fixed population kernel is Borel measurable. |
| 7 | 31 | Same kernel is symmetric on all real inputs. |
| 8 | 32 | Actual two-observation kernel is integrable. |
| 9 | 33 | Actual kernel square is integrable. |
| 10 | 34 | Its actual product-law integral equals populationMean. |
| 11 | 35-36 | Every fixed-x section is integrable and its centered integral is the actual projection. |
| 12 | 37 | Projection is integrable. |
| 13 | 38 | Its mean is zero. |
| 14 | 39 | Its square is integrable. |
| 15 | 40 | Its raw second moment/variance is strictly positive. |
| 16 | 41 | Its third absolute moment is finite. |
| 17 | 42 | Actual decoded feature Z is integrable. |
| 18 | 43 | E Z = 0. |
| 19 | 44 | Z has finite second moment, without a fourth-moment premise. |
| 20 | 45 | That moment equals actual explicit featureVariance. |
| 21 | 46 | featureVariance is strictly positive. |
| 22 | 47 | Actual residual is h-theta-g(x)-g(y), pointwise. |
| 23 | 48 | Actual residual is sectionwise integrable and canonical. |
| 24 | 49-51 | Correct residual integral action for every element of the full quotient L2(realLaw). |
| 25 | 52 | Full operator range is exactly span{featureL2}. |
| 26 | 53 | Full operator rank is exactly one. |
| 27 | 54 | Complete nonzero real eigenvalue set is {-featureVariance}. |
| 28 | 55 | Actual domination violation has positive product probability for every positive constant. |
| 29 | 56 | Actual R_n is positive almost surely for every fixed n>=3. |
| 30 | 57 | Complete deterministic x_n tends to infinity. |
| 31 | 58 | Complete x_n=o(n^(1/6)). |
| 32 | 59 | Complete x_n=o(sqrt(n)). |
| 33 | 60 | The prescribed sample-size subsequence is strictly increasing. |
| 34 | 61 | That subsequence tends to infinity. |
| 35 | 62-63 | Actual logarithmic ratio tends to zero only along that subsequence. |
| 36 | 64-65 | Actual Gaussian-relative ratio tends to infinity only along that subsequence. |
| 37 | 66-67 | Full-n logarithmic ratio fails to tend to one for the same admissible x_n. |
| 38 | 68 | Complete b_n=2*x_n=o(n^(1/6)). |
| 39 | 69 | The witness x_n belongs to [0,b_n) for every n>=1. |
| 40 | 70-72 | Actual epsilon-uniform relative approximation on this admissible window fails. |

Clauses 1-28 provide C0/C1; 29 provides Q5; 30-34/38-39 provide A0; 35-37/40 provide A1 and the original two conclusion failures. These are concrete fixed witnesses, stronger than postulating an existential law. The actual definitions and complete proof chain, not just theorem names, determine their meanings.

## Semantic and proof-chain findings

Fixed construction and moments. The actual loaded definitions were compared by rfl to the source bodies: the infinite geometric category law has masses 16382/16383 at zero and (1/16384)^j otherwise; k_j=4^j, v_0=0, v_j=32^j, mu=1/511, Z=v_C-mu, and fixed d_j=(k_j-1)Z_j^2/(k_j^4-2) for j>=1, with d_0=0. categoryMeasure is the countable weighted-Dirac sum. noiseLaw is normalized Lebesgue restriction to [-1,1]. realLaw is the pushforward of their independent product by X=3C+A; sampleLaw is its infinite product. There is no current n/j argument to the law or kernel.

The raw kernel is A(x)+A(y)+d(x)+d(y)-Z(x)Z(y); populationMean=2*offsetMean, projection=A+d-offsetMean, residual=-Z(x)Z(y). KernelMoments explicitly proves product-law integrability before integral identities. Its h^2 estimate uses the product of second moments at two distinct observations, not E Z^4. ProjectionMoments proves the third absolute moment and establishes E g^2>=1/3 through independent category/noise mixed moments. Offset and feature are never assumed independent. Positive finite raw variance is exactly the allowed original contract; no variance-one normalization or incorrectly retained scaled eigenvalue appears.

Canonical operator. ObservationL2 is the full Lp real 2 realLaw quotient, and residualOperator is rankOne real (-featureL2) featureL2 on all of that space. ResidualOperator proves product integrability for each full-L2 input, agreement almost everywhere with the actual residual integral, feature norm squared=featureVariance, feature nonzero, exact range/rank, and the unique nonzero eigenvalue -featureVariance=-(1/15-1/511^2). This is not an operator whose ambient domain was replaced by a one-dimensional span.

Domination and true statistics. DominationFailure uses a whole Cartesian same-category support rectangle, whose actual product mass is p_j^2>0, and compares h^2 against c0*(actual E g^2+g(x)^2+g(y)^2). Thus it is neither a point nor a null-diagonal violation. The original unordered-pair U uses exactly i<j and n(n-1)/2. Each row excludes itself. jackknifeSq keeps the exact 4(n-1)/(n-2)^2 coefficient and all centered row coordinates. sampleStatistic uses its true square-root denominator, subtracts populationMean, and explicitly equals zero outside the positive-denominator branch. All these loaded bodies passed separate rfl checks.

SampleStatistics proves a genuine grouped category/noise product-law identity for every fixed n. R_n=0 forces equality of two adjusted rows; after all categories are fixed, the corresponding affine equality of two independent continuous noise coordinates has zero measure, via singleton sections and Fubini. This proves the whole zero event null for every n>=3, not merely for n_j, and makes the statistic's zero convention irrelevant on the original domain.

Conditional probability chain. The actual fixed-position restriction and normalized truncated-category marginal are used first. ConditionalBackground derives the selected complement coordinates' iid laws from the actual joint map. ConditionalMixture then gives the exact finite uniform mixture back to the count event. No iid claim is made after mixing target positions. Nonzero finite event mass and genuine conditional probability instances are proved, with j>=1 explicitly supplied.

BackgroundMoments keeps the actual nonzero negative truncated feature mean and its geometric decay, and the actual offset bias. FiniteIIDMoments supplies the two required second-moment-only leave-own-index/pair identities, with explicit integrability/MemLp and no fourth-moment hypothesis. ConditionalStudentizer's four-energy estimate retains baseline A+e, target t*S_B*I, background K*t*z, and leave-own z_i*(S_B-z_i), with the original denominators. Its actual selected-coordinate L2/moment inputs and integrable dominating energy are discharged before integration and finite-mixture transfer. ConditionalNumerator likewise retains deterministic K*d/(n-1), offset bias, target-background and background-pair mean terms; it proves actual MemLp-2, exact same mean for each J, mean/k->1, and uniform actual variance. Variance mixing uses that same proved mean and centered-square integrals, not independence of dependent terms. No new root premise is introduced by their generic helpers.

Rare tail and positivity. RareTailLowerBound specializes actual numerator Chebyshev, true R^2 Markov, a union bound, and every-fixed-n R positivity transferred through conditional absolute continuity. It never assumes numerator/denominator independence. The original signal N>=k/2 and R<=4*k^(2/5), with R>0, imply actual T>=k^(3/5)/8=2*x_(n_j). The actual count-event mass is eventually at least exp(-5*k*log k); positive finite mass is present before conditional-to-original multiplication. The resulting actual half-exponential tail bound implies eventual strictly positive sample tails.

Complete scales and actual Gaussian comparison. The loaded x_n is exactly n^(3/20)/16, n_j=(4^j)^4, b_n=2*x_n; x_(n_j)^2/2=k_j^(6/5)/512 and 5*k_j*log k_j=o(x_(n_j)^2/2). The loaded Gaussian tail is exactly 1-cdf(gaussianReal 0 1), with strict positive tail for every finite real input, and the exp(-x^2/2) upper bound for x>=0.

TailLimits uses actual eventual sample-tail positivity before its logarithmic inequalities. It rewrites division by the negative denominator as -log(p)/(x^2/2), where x^2/2>0; thus its bound has the correct sign reversal. The upper bound is (5*k*log k+log 2)/(x^2/2)->0. The relative comparison uses the true positive Gaussian denominator and the actual half-exponential tail bound; x^2/2-5*k*log k->infinity gives divergence. The explicit full-n failures follow through the genuine n_j->infinity subsequence. The final window proof chooses the witness x_n in [0,b_n), using an eventual bound <=2 contradicted by divergence >=3. The epsilon-uniform assertion is a necessary consequence of the original supremum formulation, so its refutation suffices without a supremum API. No full-n zero/infinity limit or arbitrary-window claim is substituted.

All positive-j specializations occur inside eventually j>=1 or explicitly quantified j>=1 statements. Finite initial values, including totalized divisions/logarithms, are discarded only by legitimate atTop reasoning. Neither a totalized integral/variance nor log(0) supplies the root conclusion.

## Independent designated-server receipts

Evidence directory:
 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/work/oq56/fresh-review30/

All Lean commands sourced activate.sh before cd to the worktree. Only one Lean process was launched by this reviewer at a time, on CPU affinity 0,1,2,3.

| Check | Actual result | Receipt / server output |
|---|---|---|
| lake env lean Shao/OQ5/P35/FixedLawCounterexample.lean | Exit 0, 4.94 s, stdout/stderr both 0 bytes | target-receipt.json; target.stdout; target.stderr |
| Exact target-byte prefix plus independent frozen-40 equality and public #check/#print axioms | Exit 0, 6.01 s, stderr 0 bytes; 308 declarations checked | SourcePrefixAudit.lean; audit-receipt.json; audit.stdout; audit.stderr; axioms.json; audited-declarations.txt |
| Exact target-byte prefix plus loaded-definition/body equality audit | Exit 0, 7.03 s, stdout/stderr both 0 bytes; 46 rfl checks | LoadedDefinitionsAudit.lean; definitions-receipt.json; definitions.stdout; definitions.stderr |
| Entire recursive project-source forbidden-code scan | 36 files, zero sorry/admit/axiom/unsafe/native_decide code tokens; nested comments and strings stripped; no raw/interpolated-string cases present | scan-receipt.json; source-closure.sha256 |
| Immutable source anchors | 14 accepted-ledger anchors + 22 frozen-commit anchors, zero mismatches | accepted-source-anchors.json |
| Final immutable rehash | Target and all 36 closure sources unchanged | final-integrity-receipt.json |

SourcePrefixAudit.lean SHA256: 441b1c512df96d5a56bca9258bd4c6b555ef53118435c86a6030a6c1d47a8384.
LoadedDefinitionsAudit.lean SHA256: 1aca068c96d28823fe4f3f2f8ed076b079ae5be7b77171c2ae06003d10cc3036.

Both public root declarations, and every one of the 308 audited P35 public declarations in the closure, have transitive axioms contained in {propext, Classical.choice, Quot.sound}. The two root declarations each report exactly these three. There is no sorryAx or other extra axiom.

Actual versions: leanprover/lean4:v4.36.0-rc1; Lean commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e, Lake 5.0.0-src+c9afcdd. Both the manifest and actual shared Mathlib checkout equal 807d3836b165983210ee2ecf3cd28f239436949c.

Critical continuation hashes, all equal to their supplied accepted immutable ledger entries:

| Module | SHA256 |
|---|---|
| ConditionalSample | d39762332c4205a79d8c56bf598d0d7894382ba6139d3ed1724b191a8c6a82b4 |
| BackgroundMoments | 692ea10f63674f37bbf17b7e1d42fbc34ab3f706d3a37e8740a98b9a7488be09 |
| DominationFailure | 127836b8f83099d67bd6c687037f19ac401e1ca39764167884422052d7fcf239 |
| SampleStatistics | 14f5e09f7ddcac10dac43c94cf5a14adf5d44d85896d92cf26e666d496adcf85 |
| FiniteIIDMoments | 4b2c65ec7fb03767b6a469ef5918592c9a76e993ad95262e6a7aae6840c4520b |
| ThresholdScales | a326bf6a3979ae7f1c5f9d5dae597b70c612ba1bb1881d3195ed041f2d00351d |
| ConditionalMixture | 3be0b68edb5435fb6c1136a0d6ab134e23f28dea4494d0d4d35bf93b2bd3a5be |
| ConditionalBackground | bd8fbc670d0c29179994482f93aad25e48587ed423c34884f2f6f60adb7481dc |
| ConditionalStudentizer | 85766d90d01cb9e50e342183a6168a356b5ddd2cea84887c5d7439c7abb8eb62 |
| ConditionalNumerator | a47d906cd619e57594a9eed98a3204c8218a4a8c82f8e1b9eb4ba6725ae08c13 |
| RareTailLowerBound | fa4f66079518d619393af07c29ada8b388bf0236e028a07fb3cbb5631843e1c7 |
| GaussianTail | 49ac94290ccedbf6cb7cfe16771702f8a52563fc3e474622305da13d60b3f2a6 |
| TailLimits | c7e457617aea8e0cea35d01202ea1bbac5e8178a80fda8c5a70e64ca49ab0d11 |

The full manifest also anchors the actual fixed-law, feature/kernel/projection moments, negative full-L2 operator, finite-row/cancellation algebra and shared probability/selection dependencies. Its individual hashes and anchor provenance remain in the server evidence directory; raw audit logs were not copied locally.

## Verdict, attribution and remaining integration

GAPS: None. The complete original p35 fixed-law counterexample contract is formally proved, source-faithful and independently accepted at the recorded 36-file snapshot.

This formalizes the supplied original p35 construction and its stated scope, including its negative canonical rank-one residual and both Studentized-tail failures. It adds no historical-priority or mathematical-novelty claim. Original p35 section 8/RS2 and the p52/p53/OQ6 material are outside this certificate.

The root coordinator still owns publishing the selected source snapshot through the appropriate shared public imports/manifests, running the whole-library integration checks on that integrated version, retaining this review/axiom/source evidence, and updating final programme coverage after its integration gate. This review makes no claim that those repository-wide integration steps have already run.
