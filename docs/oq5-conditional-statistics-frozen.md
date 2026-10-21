# Exact frozen conditional/statistical interfaces

Original p35 only; full roots OPEN. Each contract received independent source translation before implementation.

# OQ56 unit17 — actual conditional decoded product law after fixing J, frozen v1

Source p35§4 lines116–130, contract Q1. Condition only on the actual positive fixed-position event fixedCategoryEvent n j J, then derive its genuine normalized restriction law. All original observations still use the one sampleLaw. Root's Shao.Probability.ConditionalIID is the shared generic theorem and must be reused, not copied.

Namespace Shao.OQ5.P35:
sampleDecoded (i : ℕ) (ω : ℕ → ℝ) : ℕ × ℝ := (sampleCategory i ω, decodeNoise (sampleCoordinate i ω))
categoryPatternSet {n : ℕ} (j : ℕ) (J : Finset (Fin n)) (i : Fin n) : Set ℕ := if i ∈ J then {j} else Set.Iio j
backgroundCategoryLaw (j : ℕ) : MeasureTheory.Measure ℕ := ProbabilityTheory.cond categoryMeasure (Set.Iio j)

Exact required conclusions:
measurable_sampleDecoded (i : ℕ) : Measurable (sampleDecoded i)
map_sampleDecoded (i : ℕ) : MeasureTheory.Measure.map (sampleDecoded i) sampleLaw = observationPairLaw
iIndepFun_sampleDecoded : ProbabilityTheory.iIndepFun sampleDecoded sampleLaw
backgroundCategoryLaw_isProbability (j : ℕ) (hj : 1 ≤ j) : MeasureTheory.IsProbabilityMeasure (backgroundCategoryLaw j)
categoryPatternLaw_isProbability {n : ℕ} (j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) (i : Fin n) : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond categoryMeasure (categoryPatternSet j J i))
fixedCategoryEvent_ne_zero (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) : sampleLaw (fixedCategoryEvent n j J) ≠ 0
conditionalPairLaw_factorization (S : Set ℕ) (hS : MeasurableSet S) (hS0 : categoryMeasure S ≠ 0) : ProbabilityTheory.cond observationPairLaw (S ×ˢ (Set.univ : Set ℝ)) = (ProbabilityTheory.cond categoryMeasure S).prod noiseLaw
fixedCategoryEvent_cond_isProbability (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))
decoded_cond_fixed_joint_map (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) : MeasureTheory.Measure.map (fun ω i : Fin n => sampleDecoded i.val ω) (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J)) = MeasureTheory.Measure.pi (fun i : Fin n => (ProbabilityTheory.cond categoryMeasure (categoryPatternSet j J i)).prod noiseLaw)

The final equality is the entire actual decoded finite joint law, with all n coordinates. At target positions it has category conditioned on {j}; at every complement position it has exactly category conditioned on C<j, independently paired with the original continuous noiseLaw. Thus it preserves the full product law and all category/noise independence, rather than just separate marginals. Arbitrary fixed J and n=0 are included, with j≥1 supplying positive coordinate/event probabilities. Empty background is allowed. The indexed background law is only an auxiliary conditional law; it does not replace sampleLaw or introduce a triangular array.

No claim of coordinate/background independence under the mixed count event rareCategoryEvent itself, no conditioning without first fixed J, no zero-mean truncated feature assumption, no feature/offset independence or fourth feature moment. The actual nonzero-event facts must be proved before invoking shared conditional-iid law. hS0 is a helper premise discharged for all actual pattern sets, not a root assumption. Further selected-background iid corollaries or mixing uniform moment bounds back over J are subsequent dependencies. Additional source-specific helpers allowed, no shared code edits or premise changes. Independent source/statement review before proof, assigned-server actual compilation, fresh independent proof/semantic and whitelist axiom audits after. No sorry/admit/new axiom/unsafe/native_decide.

# OQ56 unit18 — actual background category moments, frozen v1

Original source p35 section4, formula(10), contract Q2. Prerequisite unit17 defines backgroundCategoryLaw j := ProbabilityTheory.cond categoryMeasure (Set.Iio j), the actual normalized restriction of the one fixed category law. This scalar unit uses that same definition. No n/J parameter, replacement iid assumption or new observation law. Unit17 connects this marginal to actual complement coordinates after fixing J; finite-sum transport/mixing are subsequent dependencies.

Namespace Shao.OQ5.P35. File Shao/OQ5/P35/BackgroundMoments.lean. Required exact declarations, with direct actual Bochner integrals:

integrable_backgroundCategoryFeature (j : ℕ) (hj : 1 ≤ j) : MeasureTheory.Integrable categoryFeature (backgroundCategoryLaw j)
integrable_backgroundCategoryFeature_sq (j : ℕ) (hj : 1 ≤ j) : MeasureTheory.Integrable (fun c => categoryFeature c ^ 2) (backgroundCategoryLaw j)
integrable_backgroundCategoryOffset (j : ℕ) (hj : 1 ≤ j) : MeasureTheory.Integrable categoryOffset (backgroundCategoryLaw j)
integrable_backgroundCategoryOffset_sq (j : ℕ) (hj : 1 ≤ j) : MeasureTheory.Integrable (fun c => categoryOffset c ^ 2) (backgroundCategoryLaw j)

backgroundCategoryFeature_mean_exact (j : ℕ) (hj : 1 ≤ j) :
  categoryBelowMass j * (∫ c, categoryFeature c ∂backgroundCategoryLaw j) =
    -(512 / 511 : ℝ) * (1 / 512 : ℝ) ^ j +
      (16384 / (511 * 16383) : ℝ) * (1 / 16384 : ℝ) ^ j

backgroundCategoryFeature_mean_neg (j : ℕ) (hj : 1 ≤ j) :
  (∫ c, categoryFeature c ∂backgroundCategoryLaw j) < 0

backgroundCategoryMoments_uniform :
  ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
    (∫ c, categoryFeature c ^ 2 ∂backgroundCategoryLaw j) ≤ C ∧
    (∫ c, categoryOffset c ^ 2 ∂backgroundCategoryLaw j) ≤ C ∧
    |∫ c, categoryFeature c ∂backgroundCategoryLaw j| ≤ C * (1 / 512 : ℝ) ^ j ∧
    |(∫ c, categoryOffset c ∂backgroundCategoryLaw j) - offsetMean| ≤ C * (1 / 1024 : ℝ) ^ j

The feature mean is genuinely negative, including j=1, and must never be silently centered to zero. Ordinary powers give exactly the source k_j^(-9/2) and k_j^(-5) rates since k_j=4^j; no real-power corollary is required in this unit. offsetMean remains the existing actual real-law integral. The one finite positive C is independent of j and has no extra premise. Preserve category zero atom/value/offset. Integrability obligations are explicit; no totalized-integral shortcut. Source-specific restricted-integral/tail helpers are allowed. Do not assume independence of feature and offset, a fourth feature moment, or independence under the mixed rare event. Do not copy the root generic conditional-iid module. Only this scalar Q2 slice is claimed; full roots remain OPEN.

Freeze before implementation; blind independent source translation review; designated-server author compile; fresh independent proof/source review and all-public transitive axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Author owns only BackgroundMoments.lean and unit18 report. Shared files/cache and other owners' source remain untouched.

# OQ56 unit19 — positive actual probability of domination failure, frozen v1

Source original p35 section3 final paragraph, with raw h/g from(8); contract C1 ancillary domination-failure property. The source single fixed law, raw unscaled kernel/projection and actual projection variance integral must be retained. This property alone is not a tail counterexample or root closure.

Namespace Shao.OQ5.P35. File Shao/OQ5/P35/DominationFailure.lean. Exactly these new event definitions:

categorySupportBlock (j : ℕ) : Set ℝ :=
  {x | decodeCategory x = j ∧ decodeNoise x ∈ Set.Icc (-1 : ℝ) 1}

dominationFailureEvent (c0 : ℝ) : Set (ℝ × ℝ) :=
  {xy | c0 * ((∫ x, populationProjection x ^ 2 ∂realLaw) +
      populationProjection xy.1 ^ 2 + populationProjection xy.2 ^ 2) <
    populationKernel xy.1 xy.2 ^ 2}

Required exact conclusions:

measurableSet_categorySupportBlock (j : ℕ) : MeasurableSet (categorySupportBlock j)
measure_categorySupportBlock (j : ℕ) :
  realLaw (categorySupportBlock j) = ENNReal.ofReal (categoryMass j)
measure_categorySupportBlock_prod (j : ℕ) :
  (realLaw.prod realLaw) (categorySupportBlock j ×ˢ categorySupportBlock j) =
    ENNReal.ofReal (categoryMass j) ^ 2
measurableSet_dominationFailureEvent (c0 : ℝ) : MeasurableSet (dominationFailureEvent c0)
exists_categorySupportBlock_violation (c0 : ℝ) (hc0 : 0 < c0) :
  ∃ j : ℕ, 0 < j ∧
    categorySupportBlock j ×ˢ categorySupportBlock j ⊆ dominationFailureEvent c0
measure_dominationFailureEvent_pos (c0 : ℝ) (hc0 : 0 < c0) :
  0 < (realLaw.prod realLaw) (dominationFailureEvent c0)

The mass identities cover every j including zero. A same-category Cartesian rectangle is a positive actual product-measure event; a point or null diagonal is not a substitute. The positive-j witness inclusion is pointwise on the support block, and the final probability is for two independent draws from the actual fixed realLaw. sigma_g^2 is exactly the displayed integral, finite/positive from accepted ProjectionMoments and Eg=0, with no rescaling to1 or replacement by featureVariance. Auxiliary deterministic estimates/growth helpers are allowed. No finite ambient dimension, sample-size-dependent law, fourth feature moment, category-feature/offset independence, or added moment bound is allowed. No novel result claim; retain original source attribution. All full roots remain OPEN.

Freeze before implementation; blind independent source translation review; designated-server author compile; fresh independent proof/source review and all-public transitive axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Author owns only DominationFailure.lean and unit19 report. Shared source/cache and other owners' edits remain untouched.

# OQ56 unit20 — actual statistics and every-fixed-n Studentizer positivity, frozen v1

Source original p35 sections1/2 and section7 first paragraph(18), contract D0/Q5. All n use the existing one fixed infinite sampleLaw, raw populationKernel and populationMean. The true jackknife square retains every q_i-U coordinate and exact source normalization. Only positivity and statistical/law bridges, not Q3/Q4 bounds, are claimed here.

File Shao/OQ5/P35/SampleStatistics.lean, namespace Shao.OQ5.P35. Definitions:
finiteSample (n : ℕ) (ω : ℕ → ℝ) (i : Fin n) : ℝ := sampleCoordinate i.val ω
sampleMatrix (n : ℕ) (ω : ℕ → ℝ) (i j : Fin n) : ℝ := populationKernel (finiteSample n ω i) (finiteSample n ω j)
sampleU (n : ℕ) (ω : ℕ → ℝ) : ℝ := (pairCount n)⁻¹ * unorderedPairSum (sampleMatrix n ω)
sampleRowMean (n : ℕ) (ω : ℕ → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.erase i, sampleMatrix n ω i j
jackknifeSq (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, (sampleRowMean n ω i - sampleU n ω) ^ 2
sampleStudentizer (n : ℕ) (ω : ℕ → ℝ) : ℝ := Real.sqrt (jackknifeSq n ω)
sampleStatistic (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  if 0 < sampleStudentizer n ω then
    Real.sqrt (n : ℝ) * (sampleU n ω - populationMean) / sampleStudentizer n ω
  else 0

Required exact conclusions (all functions are functions of the displayed ω):
measurable_finiteSample (n : ℕ) : Measurable (finiteSample n)
measurable_sampleMatrix (n : ℕ) (i j : Fin n) : Measurable (fun ω => sampleMatrix n ω i j)
measurable_sampleU (n : ℕ) : Measurable (sampleU n)
measurable_sampleRowMean (n : ℕ) (i : Fin n) : Measurable (fun ω => sampleRowMean n ω i)
measurable_jackknifeSq (n : ℕ) : Measurable (jackknifeSq n)
measurable_sampleStudentizer (n : ℕ) : Measurable (sampleStudentizer n)
measurable_sampleStatistic (n : ℕ) : Measurable (sampleStatistic n)

For the next three required bridges use exactly
A := fun i : Fin n => decodeNoise (finiteSample n ω i),
d := fun i : Fin n => observationOffset (finiteSample n ω i),
Z := fun i : Fin n => observationFeature (finiteSample n ω i).
These are shorthands expanded or let-bound in theorem types, not additional parameters.
sampleU_eq_uStatistic (n : ℕ) (ω : ℕ → ℝ) : sampleU n ω = uStatistic A d Z
sampleRowMean_eq_rowMean (n : ℕ) (ω : ℕ → ℝ) (i : Fin n) : sampleRowMean n ω i = rowMean A d Z i
jackknifeSq_eq_studentizerSq (n : ℕ) (ω : ℕ → ℝ) : jackknifeSq n ω = studentizerSq A d Z
jackknifeSq_nonneg (n : ℕ) (hn : 3 ≤ n) (ω : ℕ → ℝ) : 0 ≤ jackknifeSq n ω

map_sampleGroupedDecoded (n : ℕ) :
  MeasureTheory.Measure.map
    (fun ω => ((fun i : Fin n => sampleCategory i.val ω),
      (fun i : Fin n => decodeNoise (sampleCoordinate i.val ω)))) sampleLaw =
    (MeasureTheory.Measure.pi (fun _ : Fin n => categoryMeasure)).prod
      (MeasureTheory.Measure.pi (fun _ : Fin n => noiseLaw))

studentizerSq_eq_zero_imp_adjustedRow_eq {n : ℕ} (A d Z : Fin n → ℝ) (hn : 3 ≤ n)
    (hzero : studentizerSq A d Z = 0) (i j : Fin n) : adjustedRow A d Z i = adjustedRow A d Z j
measure_jackknifeSq_zero (n : ℕ) (hn : 3 ≤ n) : sampleLaw {ω | jackknifeSq n ω = 0} = 0
ae_jackknifeSq_pos (n : ℕ) (hn : 3 ≤ n) : ∀ᵐ ω ∂sampleLaw, 0 < jackknifeSq n ω
ae_sampleStudentizer_pos (n : ℕ) (hn : 3 ≤ n) : ∀ᵐ ω ∂sampleLaw, 0 < sampleStudentizer n ω
measure_sampleStudentizer_pos (n : ℕ) (hn : 3 ≤ n) : sampleLaw {ω | 0 < sampleStudentizer n ω} = 1

The law identity is full grouped category/noise independence, including n0. Statistical definitions/measurability/bridges cover every n with the existing totalized divisions; positivity is asserted for EVERY fixed n>=3, with n quantified before AE. It is not restricted to n_j and cannot be replaced by an uncentered norm or a null-diagonal argument. The zero convention of T is explicitly0 and retained after proving its branch null. A genuine whole zero-event nullity proof must use the actual sample map and continuous independent noises (e.g. fix all categories via product Fubini, then an affine single-noise section is a singleton). No new absolute-continuity/independence premise may be assumed. No fourth moment or Q0 conditioning is needed. Source-specific measurable law/Fubini helpers permitted; no shared generic iid reimplementation or existing source changes.

Freeze then blind independent source translation; designated-server author target and fresh independent proof/source/all-public transitive whitelist axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Author owns only SampleStatistics.lean, unit20 author report and remote scratch. Shared imports/manifests/cache and other owners remain untouched. Full roots OPEN.

# OQ56 unit21 — two finite iid second-moment identities, frozen v1

Source original p35 section5 lines148-153 and section6 formula(16), contract mandatory finite iid identities. This p35-owned helper is generic finite probability algebra and must be applied later through the actual fixed-J law. It does not assert independence after mixing target sets or close Q3/Q4. No fourth feature moment; common mean is arbitrary, including nonzero.

File Shao/OQ5/P35/FiniteIIDMoments.lean, namespace Shao.OQ5.P35. Reuse existing unorderedPairSum from RowIdentity; each unordered pair is counted exactly once. Definitions for any m:ℕ and type Ω:

finiteFeatureSum (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ := ∑ i : Fin m, Z i ω
finiteLeaveOwnSquareSum (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin m, Z i ω ^ 2 * (finiteFeatureSum Z ω - Z i ω) ^ 2
finitePairProductSum (Z : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  unorderedPairSum (fun i l => Z i ω * Z l ω)

All six required theorems take the following exact context/hypotheses (no m>0 restriction):
{m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
{μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
{ν : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure ν]
{Z : Fin m → Ω → ℝ}
(hZ : ∀ i, Measurable (Z i))
(hIndep : ProbabilityTheory.iIndepFun Z μ)
(hLaw : ∀ i, ProbabilityTheory.IdentDistrib (Z i) (id : ℝ → ℝ) μ ν)
(hν2 : MeasureTheory.MemLp (id : ℝ → ℝ) 2 ν)

In the displays below u := ∫ z, z ∂ν; M2 := ∫ z, z^2 ∂ν; v := ProbabilityTheory.variance (id : ℝ → ℝ) ν. These are shorthand for the actual fixed common-law moments and must be expanded or bound by let in the exact theorem type, not treated as extra parameters/assumptions.

finite_iid_leaveOwnSquare_integrable :
  MeasureTheory.Integrable (finiteLeaveOwnSquareSum Z) μ
finite_iid_leaveOwnSquare_integral :
  (∫ ω, finiteLeaveOwnSquareSum Z ω ∂μ) =
    (m : ℝ) * M2 * (((m - 1 : ℕ) : ℝ) * M2 +
      ((m - 1 : ℕ) : ℝ) * ((m - 2 : ℕ) : ℝ) * u ^ 2)
finite_iid_pairProduct_memLp_two :
  MeasureTheory.MemLp (finitePairProductSum Z) 2 μ
finite_iid_pairProduct_variance :
  ProbabilityTheory.variance (finitePairProductSum Z) μ =
    (m.choose 2 : ℝ) * v ^ 2 +
      (m : ℝ) * (((m - 1 : ℕ) : ℝ) ^ 2) * u ^ 2 * v
finite_iid_pairProduct_integral :
  (∫ ω, finitePairProductSum Z ω ∂μ) = (m.choose 2 : ℝ) * u ^ 2
finite_iid_sumSquare_integral :
  (∫ ω, finiteFeatureSum Z ω ^ 2 ∂μ) =
    (m : ℝ) * M2 + (m : ℝ) * ((m - 1 : ℕ) : ℝ) * u ^ 2

The three definitions and six exact public targets include every m, especially0/1/2, arbitrary real mean and degenerate marginals. Natural subtraction in the displayed counts is deliberate; never falsely cast m-1 or m-2 as real subtraction without size hypotheses. At m0 all sums vanish; at m1 leave-own/pair sums vanish; at m2 leave-own integral is2*M2² and pair variance isv²+2*u²*v. Actual L2 and L1 obligations must precede use of totalized variance/integrals. Pair L2 must exploit independence of distinct coordinate squares; generic Holder on two L2 variables alone is not enough. Overlapping pair products need covariance/mixed moment factorization, not an unjustified independence assertion. A centered-variable decomposition inside the proof is allowed after proving its mean zero; the original Z need not be centered.

Supporting generic finite family/private algebraic helpers in this owned file are allowed; do not duplicate root conditional-iid or shared iid-map proofs, invent a competing variance definition or change shared Probability files. No EZ4, extra Lp exponents, finite category support or new source premises. Later actual-background specialization and uniform-J mixing remain OPEN.

Blind independent source/statement review before implementation; actual author target on designated server; fresh independent source/proof/all-public transitive axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Author owns only this new file/unit21 author report and remote scratch; no source/cache/shared imports/manifests/commit changes elsewhere.

# OQ56 unit22 — deterministic threshold and subsequence scales, frozen v1

Original p35 section7, lines209-216; root contract A0. One complete deterministic threshold sequence and the existing fixed category subsequence. This unit is purely deterministic and does not assume tail probability or any later Q3–Q6 result. All full roots remain OPEN.

Namespace Shao.OQ5.P35; file Shao/OQ5/P35/ThresholdScales.lean.
Exactly one definition:
counterexampleThreshold (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 20 : ℝ) / 16

Here a real exponent denotes Real.rpow; ordinary natural powers remain ordinary powers. Existing rareSampleSize j=(4^j)^4 and categoryScale j=(4:ℝ)^j are retained, not redefined.

Required exact conclusions:

counterexampleThreshold_pos (n : ℕ) (hn : 1 ≤ n) : 0 < counterexampleThreshold n
counterexampleThreshold_tendsto : Filter.Tendsto counterexampleThreshold Filter.atTop Filter.atTop
counterexampleThreshold_div_sixth_tendsto_zero :
  Filter.Tendsto (fun n : ℕ => counterexampleThreshold n / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0)
counterexampleThreshold_div_sqrt_tendsto_zero :
  Filter.Tendsto (fun n : ℕ => counterexampleThreshold n / Real.sqrt (n : ℝ)) Filter.atTop (nhds 0)
strictMono_rareSampleSize : StrictMono rareSampleSize
rareSampleSize_tendsto : Filter.Tendsto rareSampleSize Filter.atTop Filter.atTop
counterexampleThreshold_rareSampleSize (j : ℕ) :
  counterexampleThreshold (rareSampleSize j) = categoryScale j ^ (3 / 5 : ℝ) / 16
counterexampleThreshold_sq_half_rareSampleSize (j : ℕ) :
  counterexampleThreshold (rareSampleSize j) ^ 2 / 2 = categoryScale j ^ (6 / 5 : ℝ) / 512
rareLogCost_div_threshold_sq_tendsto_zero :
  Filter.Tendsto (fun j : ℕ => (5 * categoryScale j * Real.log (categoryScale j)) /
    (counterexampleThreshold (rareSampleSize j) ^ 2 / 2)) Filter.atTop (nhds 0)
counterexampleThreshold_window (n : ℕ) (hn : 1 ≤ n) :
  0 ≤ counterexampleThreshold n ∧ counterexampleThreshold n < 2 * counterexampleThreshold n

These are full atTop limits on ℕ, not a finite probe or a subsequence replacing the complete threshold sequence. The exact source exponent3/20 and constant1/16 must remain. Source threshold at n_j is k_j^(3/5)/16; its square divided by2 is k_j^(6/5)/512. The ratio cost limit expresses5*k*log(k)=o(x_nj²/2), with no sign reversal or claim about log probability yet. The window witness will support b_n=2*x_n, whose small-o follows immediately from the sixth-power scale limit. All real-power rewrites must establish needed nonnegativity/positivity. No tail/Gaussian/variance assumption or law change. Supporting deterministic helpers allowed.

Blind independent source/statement review before implementation; all Lean and heavy work designated server; author actual target then fresh independent source/proof and all-public transitive whitelist axiom audits. No sorry/admit/new axiom/unsafe/native_decide. Main lead owns only this new file and unit22 author report; do not modify root/common imports/manifests/cache or other source.
