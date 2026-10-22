# OQ3-U19a: actual global exponential tests for the source law

Frozen v1 DECLARATION_REVIEW_PENDING; no implementation. Proposed Shao/OQ3/SourceGlobalExponentialTests.lean; exact imports Shao.OQ3.EnergyBernoulliMGF, Shao.OQ3.PositiveRate, Shao.OQ3.RegularCovariance. Namespace Shao.OQ3, open MeasureTheory, open scoped Matrix Topology BigOperators, noncomputable section. Zero public definitions, two complete public targets. Root explicitly authorized OQ3-owned actual finite exponential separators, forbidding a competing public globalRate; canonical domK/extended values/global supremum remain root-owned. Exact consumer type proposal SHA26acfd13db3712335e6dbc6933f5e1a73b2967ab248ffed98fd0be71dca76312 was handed to root. U18c entire265line CORRECT final13ce132b was lead-read before its acceptance/exactPR144 publication and this scope.

Original target -> R1 section3, especially161-237/(7)-(13): the same actual source saddle is the unique global positive-tail rate minimum, not just a local one. Original report SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662; root-contract30 requires an honest extended-real supremum on domK, and D_x has c>0/weak a-bound, not false closedness in all R². Remaining obligation -> numeric binary gap alone and local real logMGF do not prove this global minimum; arbitrary-rho KL plus duality is one possible path but remains unproved. This module instead produces actual admissible finite-real exponential tests and candidate bounds from source moments and the already accepted energy Bernoulli MGF bound. It eliminates the true global separation/candidate-maximum obligation without assuming a rate gap or entropy-duality theorem. Direct consumers -> root's canonical extended-Legendre supremum/candidate attainment/strict offcandidate inequality, then the same C-law rootA assembly. Root itself coordinates exact domK/extended values/offsupport and boundary/supremum bridge; this module defines none of those objects. GeneralKL(9)/(10), saddle derivative/curvature/constant identities and other original roots remain OPEN.

```lean
theorem source_saddle_exponential_value_bound
    (q : ℝ) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    (∀ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      s * (q / 4) + t * q -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ≤
          saddleRate sourceEll q w) ∧
    (8 * sourceEll) * (q / 4) + (-sourceEll) * q -
      Real.log (∫ x : ℝ, Real.exp ((8 * sourceEll) * x + (-sourceEll) * x ^ 2)
        ∂originalMeasure sourceEll w) = saddleRate sourceEll q w

theorem exists_source_tail_exponential_separator
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k))
    (a c : ℝ) (hc0 : 0 < c)
    (htail : (Real.sqrt q / 4) * Real.sqrt c ≤ a)
    (hne : a ≠ q / 4 ∨ c ≠ q) :
    ∃ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      saddleRate sourceEll q w < s * a + t * c -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w)
```

Both targets fix the actual w/q/sourceEll and originalMeasure before any test parameters or mean point. The first returns real Integrable and strictly positive partition at EVERY s/t, then candidate test-value upper bound, plus exact actual theta0=(8sourceEll,-sourceEll) attainment. The second covers EVERY positive-tail mean point c>0,a>=(sqrt(q)/4)*sqrt(c) except(q/4,q), and produces finite real s/t with actual integrability/positive partition and value strictly above the same saddleRate. Finite real means the parameters are real numbers; w may have infinite countable support. There is no KL/finiteness/rate-gap/local-optimizer assumption, no law rechoice at a/c/s/t, no assertion for general unbounded rootB, and no redefining saddleRate as an assumed global rate. Nonnegative w and full4HasSum allow inactive zero weights/finite models as well as C's positive final weights. The first needs no extra qwindow; the complete moment model suffices. The second preserves original strict qwindow. Its c>0 matches original D_x, and it must handle c outside[1,1+H], endpoints p=0/1 and weak tail equality.

Inside each proof derive HasSum w1 from hm0, true atomicMeasure probability, actual bounded/away-zero support, EX=q/4 from atomicMeasure_mean and EX²=q from atomicMeasure_constraints at3; no real tsum/integral totalization shortcut. The same actual originalMeasure is a genuine probability and all quadratic exponential partitions are finite and strictly positive by true bounded support. Public integral_exp_tilted gives exact change of MGF to pi=atomicMeasure w with exponent(s-8ell)X+(t+ell)X² and denominatorZ=inverseNormalizer. Its unconditional API uses totalization, so the producer must establish integrability and positive numerator/denominator BEFORE Real.log_div or Legendre use. Public originalMeasure_forward_normalizer at theta0 gives its actual partition=Z^-1. No new local/global K/domain definition is introduced.

For candidate upper bound center h=(s-8ell)*(X-q/4)+(t+ell)*(X²-q); actual mean0 and exp(h)>=1+h yield true Eexp(h)>=1, then log>=0. Together with exact MGF change this gives all test values <=actual ell*q+log Z, i.e. saddleRate; actual theta0 attains equality. All integral add/sub/multiplication steps require actual integrability from fixed support, not undefined integral0.

For strict separation fix H=25+8sqrt10 (50<H<51) and actual 1<=X²<=1+H. At given c>0 choose R=sqrt(c)/sqrt(q)>0 and delta=a-qR/4>=0; show c=qR² and qR/4=(sqrt(q)/4)*sqrt(c) with positive q/sqrt(q) gates. For test(s,t)=(8ell,-ell+u), theta=uH, p=(c-1)/H, z0=(q-1)/H, accepted bounded_energy_logMGF_le_bernoulli gives its value minus lambda0 at least 8ell*delta-ell*q*(R-1)^2 +theta*p-log(1-z0+z0*exp theta). If1<=c<=1+H and R!=1, SourceBinaryEntropyGap.binaryRelativeEntropy_source_gap plus public sourceEll_lt_one_div_thirty gives binaryD>ell*q*(R-1)^2; accepted exists_binary_exponential_test (including p0/1) produces a genuine finite theta exceeding that threshold. If R=1 then c=q and offcandidate+tail force a>q/4, so theta0 itself strictly exceedslambda0. No arbitrary-rho KL or unproved entropy-Legendre equality is consumed.

For c<1 or c>1+H, do NOT silently restrict to feasible moments. Let B0=8ell*a-ell*c+log Z and T=abs(lambda0-B0)+1>0. Energy support bounds give log Epi exp(uX²)<=u for u<0, and <=u*(1+H) for u>0. Choose actual finite u=T/(c-1)<0 in the first case, or u=T/(c-(1+H))>0 in the second; show denominator sign/nonzero before cancellation. The resulting admissible test value>=B0+T>lambda0. These edge cases are mandatory proof obligations. All Gaussian/Phi/cusp/CLT results are irrelevant here; do not smuggle a manually assumed global minimum or scalar KL interpretation into these inputs.

Actual accepted API sources: EnergyBernoulliMGF has exists_binary_exponential_test13-97 and bounded_energy_logMGF_le_bernoulli99-184; PositiveRate/AtomicMeasure/InverseTilt provide true model moment/probability/tilt/normalizer interfaces; RegularCovariance200 sourceEll_lt_one_div_thirty. Pinned MeasureTheory/Measure/Tilted236 integral_exp_tilted has f/g explicit and actual ratio; Log/Basic138 Real.log_div needs both arguments nonzero. Private helpers allowed only inside the new owned module and all their actual types/generated descendants need full final semantic+axiom review. No shared definition/cache/pin/old source edits.

Direct actual C finalw=limitingMass sourceEll p r supplies both hw and fullhm at the same fixed q; no new p/q/eps/r is chosen. Csource235lines12309B SHAd935445d9a9ba3a524273b35986cbd0e6371faa1cd93295c42c205ec80a55696, PR144 exactheadf69807c8fbae2875e5cb6d6f704e7ca1c63085d7, fullproof265lines32764B SHA13ce132bdc97668cfd077156a7c99fc0309e4b6ff277dc02296e3da02e580e51 accepted. C is a later consumer, not an import dependency. All eleven project dependencies of these three imports are already integrated under rootv35; root is independently accepting A139/B141 and has no public globalRate yet. Current checkout frozen clean Cheadf698; new implementation branch only after whole CORRECT declaration final is lead-read, using newest suitable rootaccepted/main checkpoint since no C-source import is required; preserve all frozenheads/no lane merge/rebase/reset/retarget.

Read-only candidate closure for exactly these three imports completed2026-10-22T17:33:34.721650Z: physical11Shao/2776Mathlib, public2523internal+189external=2712, no source/olean gaps; canonical11project map compactSHA8238b008f0d69333bbd4a891d836c26b6e5d997325d2fe396696bd7017934783. All source inputs were previously accepted; no provisional dependency. This is readiness, not the target's proof. Root also filled unrelated futureKL/Bernoulli15modules and strictly imported those2roots, preserving allprior39871sharedfiles/pin807d3836; rootreceipt e5a25f97 is administrative only and no repeatprobe/wholecache scan is needed. Reviewer independently verifies actual necessary APIs/three-import graph, not author candidate/scanner/future JSON or notes.

Independent declaration gate first extracts BOTH entire types only and persists fresh blind translations, then reads scope/R1/root-contract tail/domain requirements and actual accepted APIs; checks global versus local semantics, allquantifiers/edgecases/real admissibility and mathematical feasibility, mechanical last. Reviewer owns only new u19a-statement-review.md and run/statement-review.md; no source/scope/old reports/shared/cache/pins writes/spawn/Lean/#check/probe/build/rebuild/commit/pub/fullrawlogdownload. No U19a Lean/Audit/probe/newbranch before lead reads the whole complete CORRECT final. All heavy work designatedserver CPU14-17/native-M8192-j4/strict autoImplicitfalse/one lane heavy total; no heartbeat/ulimit-v/settings weakening, no externalCPU0-9/80GiB interference. Standardaxioms only propext/Classical.choice/Quot.sound; forbid sorry/admit/newaxiom/unsafe/native_decide/implemented_by. All OQ3 roots A/B/C/D remain OPEN, no optimality/weakestbeta/novelty claims.
