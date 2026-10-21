# Exact frozen original p35 completion interfaces

Source original p35 only. Each contract was independently source-reviewed before implementation; the final root also has a clause-to-contract completeness gate.

# OQ56 unit23 — mix fixed-position conditional laws back to the exact count event, frozen v1

Source original p35 section4 fixingJ and section5 final sentence removingJ, contract Q1. Existing fixedCategoryEvent/exactCategoryEvent decomposition and the ONE sampleLaw are retained. This unit proves the genuine conditional mixture and transports bounds uniformly inJ. It does not assert independence under the mixed count event, Q3/Q4 numerical bounds or root completion.

File Shao/OQ5/P35/ConditionalMixture.lean, namespace Shao.OQ5.P35. No new event/law definitions. Let F := (Finset.univ : Finset (Fin n)).powersetCard K, a display shorthand expanded in theorem signatures. Hypotheses always n K j:ℕ, hj:1≤j, hK:K≤n. They guarantee every fixed event and the exact event positive and choose(n,K)>0, including n0/K0, K0, K=n.

Required exact declarations:

exactCategoryEvent_ne_zero (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n) :
  sampleLaw (exactCategoryEvent n K j) ≠ 0
exactCategoryEvent_cond_isProbability (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n) :
  MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.cond sampleLaw (exactCategoryEvent n K j))

cond_exactCategoryEvent_eq_uniform_sum (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n) :
  ProbabilityTheory.cond sampleLaw (exactCategoryEvent n K j) =
    ((n.choose K : ℝ≥0∞)⁻¹) •
      ∑ J ∈ F, ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J)

integrable_cond_exactCategoryEvent (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (f : (ℕ → ℝ) → ℝ)
    (hf : ∀ J ∈ F, MeasureTheory.Integrable f (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))) :
  MeasureTheory.Integrable f (ProbabilityTheory.cond sampleLaw (exactCategoryEvent n K j))

integral_cond_exactCategoryEvent (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (f : (ℕ → ℝ) → ℝ)
    (hf : ∀ J ∈ F, MeasureTheory.Integrable f (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))) :
  (∫ ω, f ω ∂ProbabilityTheory.cond sampleLaw (exactCategoryEvent n K j)) =
    (n.choose K : ℝ)⁻¹ *
      ∑ J ∈ F, (∫ ω, f ω ∂ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))

integral_cond_exactCategoryEvent_le (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (f : (ℕ → ℝ) → ℝ) (C : ℝ)
    (hf : ∀ J ∈ F, MeasureTheory.Integrable f (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J)))
    (hbound : ∀ J ∈ F, (∫ ω, f ω ∂ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J)) ≤ C) :
  (∫ ω, f ω ∂ProbabilityTheory.cond sampleLaw (exactCategoryEvent n K j)) ≤ C

measureReal_cond_exactCategoryEvent_le (n K j : ℕ) (hj : 1 ≤ j) (hK : K ≤ n)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) (C : ℝ)
    (hbound : ∀ J ∈ F, (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J)).real B ≤ C) :
  (ProbabilityTheory.cond sampleLaw (exactCategoryEvent n K j)).real B ≤ C

The conditional measure equality is uniform across F because the actual fixed-position probabilities are all exactlyp_j^K*q_j^(n-K), already proved. The coefficient is the inverse cardinalchoose(n,K), not the inverse of its real cast in an ENNReal scalar slot. Integral coefficient is its real inverse, with finite nonzero casts justified. f is arbitrary signed real observable, so actual integrability is explicitly required componentwise and proved for the mixture; helper premises must be discharged for later actual statistics. No f independence, permutation invariance, nonnegative C or meanzero premise is added. Bound transfer uses a uniform-inJ bound, no iid inference aftermixing. For later source specialization n=n_j,K=K_j, existing count_le andhj discharge all helper premises. All full roots remain OPEN.

Supporting source-specific finite restriction/sum/integral helpers allowed. No shared conditional-iid proof copying, source-law changes or new root assumptions. Blind independent source translation before implementation; designated-server author compile and separate fresh proof/source/all-public transitive whitelist axiom audits. No sorry/admit/new axiom/unsafe/native_decide. Author lead owns only this new file/unit23 author report and scratch; sharedsource/cache/imports/manifests and other owners untouched.

# OQ56 unit24 — actual selected-background iid corollaries after fixed J, frozen v1

Original p35 section4 line116 and Q1/Q2, preparing actual conditional use of finite iid moments. All claims are under the genuine cond sampleLaw (fixedCategoryEvent n j J), first fixingJ. Reuse unit17 decoded_cond_fixed_joint_map; do not copy the root generic conditional-iid proof. The conditional marginal and independence corollaries are source-specific consequences of that entire joint-law equality. Background means remain negative as in unit18, not zero.

File Shao/OQ5/P35/ConditionalBackground.lean, namespace Shao.OQ5.P35; no new law/random-variable definitions required. All functions below are explicitly displayed.

map_sampleDecoded_cond_fixed (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) (i : Fin n) :
  MeasureTheory.Measure.map (sampleDecoded i.val) (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J)) =
    (ProbabilityTheory.cond categoryMeasure (categoryPatternSet j J i)).prod noiseLaw

iIndepFun_sampleDecoded_cond_fixed (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) :
  ProbabilityTheory.iIndepFun (fun i : Fin n => sampleDecoded i.val)
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))

For the next five statements take arbitrary m n j:ℕ, hj:1≤j, J:Finset(Fin n),
e:Fin m→Fin n, he:e.Injective, hback:∀r,e r ∉ J.
This is an actual deterministic injective selection of background positions, not a new sample. Empty selections m0 and empty/fullJ are allowed. Later ordered complement enumeration discharges he/hback; no fresh iid premise is permitted.

map_selectedBackgroundDecoded :
  MeasureTheory.Measure.map (fun ω (r : Fin m) => sampleDecoded (e r).val ω)
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J)) =
      MeasureTheory.Measure.pi (fun _ : Fin m => (backgroundCategoryLaw j).prod noiseLaw)

iIndepFun_selectedBackgroundFeature :
  ProbabilityTheory.iIndepFun (fun r : Fin m => fun ω => categoryFeature (sampleCategory (e r).val ω))
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))

identDistrib_selectedBackgroundFeature (r : Fin m) :
  ProbabilityTheory.IdentDistrib (fun ω => categoryFeature (sampleCategory (e r).val ω)) (id : ℝ → ℝ)
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))
    (MeasureTheory.Measure.map categoryFeature (backgroundCategoryLaw j))

iIndepFun_selectedBackgroundOffset :
  ProbabilityTheory.iIndepFun (fun r : Fin m => fun ω => categoryOffset (sampleCategory (e r).val ω))
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))

identDistrib_selectedBackgroundOffset (r : Fin m) :
  ProbabilityTheory.IdentDistrib (fun ω => categoryOffset (sampleCategory (e r).val ω)) (id : ℝ → ℝ)
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent n j J))
    (MeasureTheory.Measure.map categoryOffset (backgroundCategoryLaw j))

memLp_backgroundFeature (j : ℕ) (hj : 1 ≤ j) :
  MeasureTheory.MemLp (id : ℝ → ℝ) 2 (MeasureTheory.Measure.map categoryFeature (backgroundCategoryLaw j))
memLp_backgroundOffset (j : ℕ) (hj : 1 ≤ j) :
  MeasureTheory.MemLp (id : ℝ → ℝ) 2 (MeasureTheory.Measure.map categoryOffset (backgroundCategoryLaw j))

These nine public conclusions provide full decoded-vector laws, genuine full mutual independence and actual one-dimensional common laws, plus the exact L2 inputs from actual background second moments. No offset/feature independence is asserted: both remain functions of the same category. No iid statement under exactCategoryEvent or rareCategoryEvent, no fourth moments, no altered unconditional law, and no unexplained iid copy. Full n-vector may have nonidentical target/background marginals. The selected pair law includes unchanged independent noises. Probability-measure instances required inside proofs must be discharged from accepted fixed-event/background positivity. Supporting source-specific map/selection helpers allowed. If root publishes arbitrary-pattern conditional wrappers, reuse them; otherwise derive these consequences directly from unit17 public joint map and existing Mathlib pi marginal/independence equivalences, not by reproducing generic conditioning proof.

Freeze then independent blind source translation before proof; author actual designated-server target, fresh independent source/proof and all-public transitive whitelist axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Lead owns only this new file/unit24 author report/scratch; no sharedsource/cache/import/manifest or other-owner changes. All full roots OPEN.

# OQ56 unit25 — actual uniform conditional jackknife square bound, frozen v1

Original p35 section5 formulas(11)-(13), contract Q3. This unit proves the TRUE Studentizer square of SampleStatistics under actual normalized restrictions of the one sampleLaw. It must retain all four vectors in TargetCancellation, derive every actual conditional iid/moment input from unit17/18/24, use the second-moment-only finite identities21, then mix fixedJ via unit23. No new root premise or independent-copy substitution.

File Shao/OQ5/P35/ConditionalStudentizer.lean, namespace Shao.OQ5.P35. No new public definition. Required exact three public statements:

integrable_jackknifeSq_cond_fixed (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
  MeasureTheory.Integrable (jackknifeSq (rareSampleSize j))
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J))

integrable_jackknifeSq_cond_rare (j : ℕ) (hj : 1 ≤ j) :
  MeasureTheory.Integrable (jackknifeSq (rareSampleSize j))
    (ProbabilityTheory.cond sampleLaw (rareCategoryEvent j))

jackknifeSq_cond_uniform :
  ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
    (∀ J : Finset (Fin (rareSampleSize j)), J.card = targetCategoryCount j →
      (∫ ω, jackknifeSq (rareSampleSize j) ω
        ∂ProbabilityTheory.cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ C) ∧
    (∫ ω, jackknifeSq (rareSampleSize j) ω
      ∂ProbabilityTheory.cond sampleLaw (rareCategoryEvent j)) ≤ C

The single finite real C is existential before j and J; all j>=1 and every actual target set are included. This uniform-all-j strengthening of source's sufficient eventual bound is justified by k_j>=4 and the fixed scalar Q2 bounds. A specific numeric C is not frozen and must be constructed if used, never assumed. Both actual L1 obligations are explicit so totalized Bochner integrals cannot hide nonintegrability. Original all-row centered jackknifeSq cannot be replaced by a surrogate; the accepted exact identity and projection contraction may dominate it by full adjusted-row energy.

The four energies must include baseline A+e, target t*S_B*I/(n-2), background K*t*z/(n-2), and leave-own z_i*(S_B-z_i)/(n-2). Both target-background interactions remain. After first fixingJ, enumerate actual complement positions injectively and use true conditional iid feature/offset marginal laws. Do not claim feature/offset independence, iid under the mixed event, or truncated feature meanzero. Use actual nonzero u_j fromunit18 with its decay bound. The leave-own term factors independent distinct-index squares via21 and must never introduce E Z^4. Actual integrability of each dominating energy precedes integral comparison. Means, second moments and probability instances must be discharged from accepted actual law results, not passed as fresh assumptions. Finitepartition uniform-J mixing concludes the same bound under rareCategoryEvent.

Source-specific deterministic contraction/four-square estimates, background sum reindexing, elementary fixed coefficient inequalities and private moment/transport helpers are allowed within this file. The frozen coefficient/sample/statistical source files remain immutable. Unit24 provides generic injective background selection with e:Fin m→Fin n; use existing Shao.retainedIndex(univ\J) and its true membership/injection to discharge that helper's premises. Unit23 supplies genuine conditional mixture/bound transfer. Required files may be authored concurrently; wait for actual oleans as needed instead of redeclaring their interfaces or silently adding an iid premise. Source n_j>=256 ensures all original denominators positive. No rpow/asymptotic estimate or Gaussian input is needed for this uniform bound.

Freeze then blind independent source translation before proof; author actual designated-server target; fresh independent source/proof/all-public transitive whitelist axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Author owns only ConditionalStudentizer.lean/unit25 author report/scratch, no root/common/cache/imports/manifests/commits or other-owner source edits. Q4/Q6/A1 and all full roots remain OPEN even if this unit passes.

# OQ56 unit26 — actual centered numerator signal and conditional variance, frozen v1

Original p35 section6 formulas(14)-(17), contract Q4. Use one sampleLaw, exact sampleU/populationMean and true normalized restrictions. Source nonzero truncated feature mean and every cross interaction must remain. No Q3 premise, Gaussian input or new high moment is needed. Earlier frozen modules remain immutable.

File Shao/OQ5/P35/ConditionalNumerator.lean, namespace Shao.OQ5.P35. Exactly two definitions:

sampleCenteredNumerator (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * (sampleU n ω - populationMean)

conditionalNumeratorMean (j : ℕ) : ℝ :=
  let n : ℝ := rareSampleSize j
  let K : ℝ := targetCategoryCount j
  let m : ℝ := (rareSampleSize j - targetCategoryCount j : ℕ)
  let u : ℝ := ∫ c, categoryFeature c ∂backgroundCategoryLaw j
  let dB : ℝ := ∫ c, categoryOffset c ∂backgroundCategoryLaw j
  Real.sqrt n *
    (K * categoryOffset j / (n - 1) + 2 * m * dB / n -
      2 * K * categoryFeature j * m * u / (n * (n - 1)) -
      m * (m - 1) * u ^ 2 / (n * (n - 1)) - populationMean)

All natural quantities in real let slots are explicitly cast. Both definitions cover every n/j using existing totalized divisions; no positive-range identity at j0 is required, and limits are full atTop with any finite exceptional indices justified.

Required exact seven public conclusions:

memLp_sampleCenteredNumerator_cond_fixed (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
  MeasureTheory.MemLp (sampleCenteredNumerator (rareSampleSize j)) 2
    (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J))

memLp_sampleCenteredNumerator_cond_rare (j : ℕ) (hj : 1 ≤ j) :
  MeasureTheory.MemLp (sampleCenteredNumerator (rareSampleSize j)) 2
    (ProbabilityTheory.cond sampleLaw (rareCategoryEvent j))

integral_sampleCenteredNumerator_cond_fixed (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin (rareSampleSize j))) (hJ : J.card = targetCategoryCount j) :
  (∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
    ∂ProbabilityTheory.cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) = conditionalNumeratorMean j

integral_sampleCenteredNumerator_cond_rare (j : ℕ) (hj : 1 ≤ j) :
  (∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
    ∂ProbabilityTheory.cond sampleLaw (rareCategoryEvent j)) = conditionalNumeratorMean j

conditionalNumeratorMean_div_scale_tendsto_one :
  Filter.Tendsto (fun j : ℕ => conditionalNumeratorMean j / categoryScale j) Filter.atTop (nhds 1)

integral_sampleCenteredNumerator_cond_rare_div_scale_tendsto_one :
  Filter.Tendsto (fun j : ℕ =>
    (∫ ω, sampleCenteredNumerator (rareSampleSize j) ω
      ∂ProbabilityTheory.cond sampleLaw (rareCategoryEvent j)) / categoryScale j) Filter.atTop (nhds 1)

variance_sampleCenteredNumerator_cond_uniform :
  ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
    (∀ J : Finset (Fin (rareSampleSize j)), J.card = targetCategoryCount j →
      ProbabilityTheory.variance (sampleCenteredNumerator (rareSampleSize j))
        (ProbabilityTheory.cond sampleLaw (fixedCategoryEvent (rareSampleSize j) j J)) ≤ C) ∧
    ProbabilityTheory.variance (sampleCenteredNumerator (rareSampleSize j))
      (ProbabilityTheory.cond sampleLaw (rareCategoryEvent j)) ≤ C

Actual L2 is explicit before interpreting variance; it supplies both first and square integrability under genuine probability conditional measures. The exact conditional mean is independent ofJ by the proved source identity and actual equal background laws, not by assuming permutation symmetry. The formula has targetsignal K*d/(n-1), backgroundoffset2*m*dB/n, target-backgroundmean -2*K*t*m*u/[n(n-1)], and backgroundpairmean -m(m-1)u²/[n(n-1)], followed by subtracting the original populationMean=2offsetMean. The noise contribution is truly centered under fixedJ. Natural m count is cast after subtraction; m-1 inside real formula is justified in the actual j>=1 range. Neither u nor the offset bias may be erased.

The one finite positive varianceC precedes all j/J, works for every j>=1 and survives actual finite mixture. Uniform-all-j strengthens the sufficient eventual source bound using k>=4/n>=256 and Q2. For mixing variance, use the SAME proved conditional mean for allJ and actual centered-square integrals; no independent numerator/denominator or iid aftermixedcount assumption. Pair variance must use21's only-L2 exact formula, not feature fourth moments or false independence of overlapping pair products. Variance-of-sum can use a fixed multiple bound to accommodate d/Z dependence. Source-specific finite reindexing, scalar fixed-coefficient/limit helpers and moment transport allowed; no separate replacement marginal/copy or extra source hypotheses.

Blind independent source translation before implementation; actual designated-server author compile then separate fresh source/proof/all-public transitive whitelist axiom audit. No sorry/admit/new axiom/unsafe/native_decide. Author owns only ConditionalNumerator.lean/unit26 author report/scratch; no sharedsource/cache/imports/manifests/git/other-owner changes. Q6/A1 and all full roots remain OPEN.

# OQ56 unit27 — actual joint good event and sparse Studentized tail lower bound, frozen v1

Original p35 sections6–7, lines188-207/formula(19); contract Q6. Derive conclusions from actual proved Q3(unit25), Q4(unit26), everyfixedn positivity20, Q0 actualevent lower16 and thresholdscales22. These are imported proved dependencies, never extra root hypotheses. All objects live under the one sampleLaw and true sampleStatistic with its explicit zero convention.

File Shao/OQ5/P35/RareTailLowerBound.lean, namespace Shao.OQ5.P35. Exactly one eventdefinition:

jointGoodEvent (j : ℕ) : Set (ℕ → ℝ) :=
  {ω | categoryScale j / 2 ≤ sampleCenteredNumerator (rareSampleSize j) ω ∧
    0 < sampleStudentizer (rareSampleSize j) ω ∧
    sampleStudentizer (rareSampleSize j) ω ≤ 4 * categoryScale j ^ (2 / 5 : ℝ)}

Required exact public conclusions:

measurableSet_jointGoodEvent (j : ℕ) : MeasurableSet (jointGoodEvent j)

jointGoodEvent_subset_tail (j : ℕ) (hj : 1 ≤ j) :
  jointGoodEvent j ⊆ {ω | 2 * counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω}

jointGoodEvent_cond_probability_tendsto_one :
  Filter.Tendsto (fun j : ℕ =>
    (ProbabilityTheory.cond sampleLaw (rareCategoryEvent j)).real (jointGoodEvent j))
    Filter.atTop (nhds 1)

rare_tail_probability_lower :
  ∃ ε : ℕ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ᶠ j : ℕ in Filter.atTop,
      0 ≤ ε j ∧ ε j < 1 ∧
      (1 - ε j) * Real.exp (-5 * categoryScale j * Real.log (categoryScale j)) ≤
        sampleLaw.real {ω | 2 * counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω}

rare_tail_probability_half_lower :
  ∀ᶠ j : ℕ in Filter.atTop,
    (1 / 2 : ℝ) * Real.exp (-5 * categoryScale j * Real.log (categoryScale j)) ≤
      sampleLaw.real {ω | counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω}

rare_tail_probability_eventually_pos :
  ∀ᶠ j : ℕ in Filter.atTop,
    0 < sampleLaw.real {ω | counterexampleThreshold (rareSampleSize j) ≤ sampleStatistic (rareSampleSize j) ω}

The source good numerator is>=k/2, actualR positive and<=4*k^(2/5), hence T>=k^(3/5)/8=2*x_nj. Preserve factor2 and the complete source x_n. Probability of the JOINT event tends1 by a union bound, never by numerator/denominator independence. Chebyshev applies to actual finite variance with mean eventually>=3k/4; Markov applies to true R². ZeroR is null for each fixed sample size under actual normalized rare-event restriction via absolute continuity, not assumed away. Unknown constants remain existential/proved; no exact cutoff is invented. Nonzero finite rare-event mass precedes any cond-to-original cancellation; final tails are actualsampleLaw events, measurable and eventually strictlypositive before subsequent log use.

The first lower bound retains an actual ε_j→0 and source2*x threshold. The half lower follows eventually, then monotone threshold inclusion weakens to x_nj; no Gaussian comparison or finalratio limit is claimed inthisunit. Undercond at j0 may be degenerate but all fullatTop limits discard finitelymany indices properly. Real powers requirepositive k. Supporting measurable/statistical/event/Markov/Chebyshev transport helpers allowed. No EZ4, independent-copy law, mixed-event iid, rootpremisechange or denominator surrogate.

Blind independent source translation beforeimplementation; author actual designatedserver target; fresh independent source/proof/allpublic transitivewhitelist axiom audit. No sorry/admit/newaxiom/unsafe/native_decide. Lead owns only RareTailLowerBound.lean/unit27 authorreport/scratch; no sharedsource/cache/importmanifest/otherowner edits. A1and allfullrootsremainOPEN.

# OQ56 unit28 — the actual standard Gaussian comparison tail, frozen v1

Original p35 section7 lines215-223, root contract A1/external Gaussian comparison interface. This unit identifies the source Phi/Psi with the actual standard Gaussian probability measure and proves its strict positive upper tail and exponential upper bound. It does not assume a normal approximation or any source sample tail result. P35-local names avoid editing shared common definitions; if a current root public equivalent exists, reuse it and record the equality.

File Shao/OQ5/P35/GaussianTail.lean, namespace Shao.OQ5.P35. Exactly two definitions:
standardNormalCDF (x : ℝ) : ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x
standardNormalUpperTail (x : ℝ) : ℝ := 1 - standardNormalCDF x

Required exact four public conclusions:
standardNormalCDF_eq (x : ℝ) :
  standardNormalCDF x = (ProbabilityTheory.gaussianReal 0 1).real (Set.Iic x)
standardNormalUpperTail_eq (x : ℝ) :
  standardNormalUpperTail x = (ProbabilityTheory.gaussianReal 0 1).real (Set.Ioi x)
standardNormalUpperTail_pos (x : ℝ) : 0 < standardNormalUpperTail x
standardNormalUpperTail_le_exp (x : ℝ) (hx : 0 ≤ x) :
  standardNormalUpperTail x ≤ Real.exp (-(x ^ 2) / 2)

The Gaussian variance parameter1 has its existing NNReal type, with mean0 and probabilitymeasure instance. Psi is1-CDF at x, thus the strict upper intervalIoi; it is positive for EVERY finite realx. The upper bound is forx>=0, with exact exponent-x²/2. It may be proved from pinned Mathlib Gaussian momentgeneratingfunction/Chernoff and tailIoi⊆Ici, or an equivalent already-proved official Gaussian tail theorem. Positive tail must follow actual full-support/positive-density/absolute-continuity structure, not an added positive-tail assumption. All finite/nozero probability side conditions must be discharged before usingreal probabilities. No bespoke replacementPhi, Gaussianratio assumption or new axiom. No finalcounterexamplelimit is claimed here.

Pinned source APIs inspected bylead: Gaussian.Real gaussianReal_absolutelyContinuous' (volume≪gaussian forvariance!=0), mgf_id_gaussianReal, integrable_exp_mul_gaussianReal; Probability.CDF cdf_eq_real; Moments.Basic measure_ge_le_exp_mul_mgf. Required Gaussian.Real and Probability.CDF oleans currentlyabsent; root-onlycachefetch requested, author mustwait forcache ratherthanwritecache or rebuildmathlib.

Freeze then blind independent source translation beforeproof; designatedserver actualauthor target and separate fresh source/proof/allpublic transitivewhitelist axiom audit. No sorry/admit/newaxiom/unsafe/native_decide. Lead owns onlyGaussianTail.lean/unit28authorreport/scratch, no sharedsource/cache/importmanifest/otherowner changes. AllfullrootsOPEN.

# OQ56 unit29 — actual logarithmic and Gaussian-relative tail failures, frozen v1

Original p35 section7 lines209-223, root contract A1. All conclusions concern actualsampleLaw and true sampleStatistic, the complete counterexampleThreshold sequence and fixed rareSampleSize subsequence, plus actual standardGaussianUpperTail. Importedproved Q6/scale/Gaussian dependencies must discharge every input; no tail lower bound/positivity/limit is added as a root premise.

File Shao/OQ5/P35/TailLimits.lean, namespace Shao.OQ5.P35. Exactly two definitions:
p35TailProbability (n : ℕ) : ℝ :=
  sampleLaw.real {ω | counterexampleThreshold n ≤ sampleStatistic n ω}
counterexampleWindow (n : ℕ) : ℝ := 2 * counterexampleThreshold n

Required exact ten public conclusions:
p35TailProbability_nonneg (n : ℕ) : 0 ≤ p35TailProbability n
p35TailProbability_le_one (n : ℕ) : p35TailProbability n ≤ 1
p35TailProbability_eventually_pos :
  ∀ᶠ j : ℕ in Filter.atTop, 0 < p35TailProbability (rareSampleSize j)

p35LogTailRatio_tendsto_zero :
  Filter.Tendsto (fun j : ℕ => Real.log (p35TailProbability (rareSampleSize j)) /
    (-(counterexampleThreshold (rareSampleSize j) ^ 2) / 2)) Filter.atTop (nhds 0)

p35RelativeTailRatio_tendsto_atTop :
  Filter.Tendsto (fun j : ℕ => p35TailProbability (rareSampleSize j) /
    standardNormalUpperTail (counterexampleThreshold (rareSampleSize j))) Filter.atTop Filter.atTop

p35LogTailRatio_not_tendsto_one :
  ¬ Filter.Tendsto (fun n : ℕ => Real.log (p35TailProbability n) /
    (-(counterexampleThreshold n ^ 2) / 2)) Filter.atTop (nhds 1)

p35RelativeTailRatio_not_tendsto_one :
  ¬ Filter.Tendsto (fun n : ℕ => p35TailProbability n /
    standardNormalUpperTail (counterexampleThreshold n)) Filter.atTop (nhds 1)

counterexampleWindow_div_sixth_tendsto_zero :
  Filter.Tendsto (fun n : ℕ => counterexampleWindow n / (n : ℝ) ^ (1 / 6 : ℝ))
    Filter.atTop (nhds 0)

counterexampleThreshold_mem_window (n : ℕ) (hn : 1 ≤ n) :
  0 ≤ counterexampleThreshold n ∧ counterexampleThreshold n < counterexampleWindow n

p35WindowUniformApproximation_false :
  ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    ∀ t : ℝ, 0 ≤ t → t < counterexampleWindow n →
      |sampleLaw.real {ω | t ≤ sampleStatistic n ω} / standardNormalUpperTail t - 1| ≤ ε)

The two actualratios have limits ONLY along the explicit subsequence; the fulln statements are their failure to converge to1, not falsefulln limits0/infinity. The window is the complete deterministic2*x_n, has the required o(n^(1/6)) scale and contains witnessx_n for n>=1. The last concrete uniform-approximation assertion is a necessary consequence of the source supremum formulation and is refuted at the explicitadmissiblewindow, without requiring a supremum API. It does not assert failure at everywindow or for arbitraryuserthresholds.

Eventual strictpositive actualtail fromunit27 precedes log inequalities; actualGaussiantail ispositive forallfinite x fromunit28 and its bound applies because thresholdspositive. The logarithmic denominator is negative: probability<=1 gives log<=0 and ratio>=0, while the sourcehalfexp lower yields upperbound (log2+5*k*logk)/(x_nj²/2)→0. Dividinginequalities must preserve the sign reversal. The relative ratio uses positive denominators, halfexp lower/exp(-x²/2) upper and growth of x²/2-5*klogk. No log0 or totalizeddivision shortcut; finiteinitialvalues may be discarded by fullatTop limits only. Constants1/16,1/512 andcost5 remainexact. No normalapproximation or externalShao-Zhoutheorem used.

Freeze then blind independent source translation beforeproof; actual designatedserver author target and separate fresh source/proof/allpublic transitivewhitelist axiom audit. No sorry/admit/newaxiom/unsafe/native_decide. Lead owns onlyTailLimits.lean/unit29authorreport/scratch; no sharedsource/cache/importmanifest/otherowner changes. ThisunitclosesA1onlyafterallimportedactualdependenciespass; fullrootbundle/source contractgate remainsOPEN until separatelyassembled and independentlyreviewed.

# OQ56 unit30 — full original p35 fixed-law counterexample certificate, frozen v1

This is the FINAL p35 ROOT bundle, not a new analytic result. Source original p35 sections1–7 (only), public root contract docs/oq5-counterexample-contract.md sections2–4/7. It must recover every root obligation from actual previously proved modules, with no added assumption. No p52/p53 strengthening, OQ6 positive theorem, novelty claim or other root closure. Root integration gate remains separate after this source passes.

File Shao/OQ5/P35/FixedLawCounterexample.lean, namespace Shao.OQ5.P35. Define exactly ONE proposition FixedLawCounterexample by the conjunction of the following clauses IN THIS ORDER; display shorthands are expanded in Lean, not free parameters or assumptions. All functions/laws below are the existing once-fixed actual definitions. Write `open MeasureTheory ProbabilityTheory Filter` and topology notation as needed.

1. IsProbabilityMeasure realLaw
2. IsProbabilityMeasure sampleLaw
3. ∀ i : ℕ, Measurable (sampleCoordinate i)
4. ∀ i : ℕ, Measure.map (sampleCoordinate i) sampleLaw = realLaw
5. iIndepFun sampleCoordinate sampleLaw
6. Measurable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2)
7. ∀ x y : ℝ, populationKernel x y = populationKernel y x
8. Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2) (realLaw.prod realLaw)
9. Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2 ^ 2) (realLaw.prod realLaw)
10. (∫ xy : ℝ × ℝ, populationKernel xy.1 xy.2 ∂realLaw.prod realLaw) = populationMean
11. ∀ x : ℝ, Integrable (populationKernel x) realLaw ∧
      ((∫ y, populationKernel x y ∂realLaw) - populationMean = populationProjection x)
12. Integrable populationProjection realLaw
13. (∫ x, populationProjection x ∂realLaw) = 0
14. Integrable (fun x => populationProjection x ^ 2) realLaw
15. 0 < (∫ x, populationProjection x ^ 2 ∂realLaw)
16. Integrable (fun x => |populationProjection x| ^ 3) realLaw
17. Integrable observationFeature realLaw
18. (∫ x, observationFeature x ∂realLaw) = 0
19. Integrable (fun x => observationFeature x ^ 2) realLaw
20. (∫ x, observationFeature x ^ 2 ∂realLaw) = featureVariance
21. 0 < featureVariance
22. ∀ x y : ℝ, populationResidual x y = populationKernel x y - populationMean - populationProjection x - populationProjection y
23. ∀ x : ℝ, Integrable (populationResidual x) realLaw ∧ (∫ y, populationResidual x y ∂realLaw) = 0
24. ∀ f : ObservationL2,
      (∀ x : ℝ, Integrable (fun y => populationResidual x y * f y) realLaw) ∧
      ((residualOperator f : ℝ → ℝ) =ᵐ[realLaw] fun x => ∫ y, populationResidual x y * f y ∂realLaw)
25. LinearMap.range residualOperator.toLinearMap = Submodule.span ℝ ({featureL2} : Set ObservationL2)
26. residualOperator.toLinearMap.rank = 1
27. {lam : ℝ | lam ≠ 0 ∧ Module.End.HasEigenvalue residualOperator.toLinearMap lam} = {(-featureVariance)}
28. ∀ c0 : ℝ, 0 < c0 → 0 < (realLaw.prod realLaw) (dominationFailureEvent c0)
29. ∀ n : ℕ, 3 ≤ n → sampleLaw {ω | 0 < sampleStudentizer n ω} = 1
30. Tendsto counterexampleThreshold atTop atTop
31. Tendsto (fun n : ℕ => counterexampleThreshold n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0)
32. Tendsto (fun n : ℕ => counterexampleThreshold n / Real.sqrt (n : ℝ)) atTop (nhds 0)
33. StrictMono rareSampleSize
34. Tendsto rareSampleSize atTop atTop
35. Tendsto (fun j : ℕ => Real.log (p35TailProbability (rareSampleSize j)) /
      (-(counterexampleThreshold (rareSampleSize j) ^ 2) / 2)) atTop (nhds 0)
36. Tendsto (fun j : ℕ => p35TailProbability (rareSampleSize j) /
      standardNormalUpperTail (counterexampleThreshold (rareSampleSize j))) atTop atTop
37. ¬ Tendsto (fun n : ℕ => Real.log (p35TailProbability n) /
      (-(counterexampleThreshold n ^ 2) / 2)) atTop (nhds 1)
38. Tendsto (fun n : ℕ => counterexampleWindow n / (n : ℝ) ^ (1 / 6 : ℝ)) atTop (nhds 0)
39. ∀ n : ℕ, 1 ≤ n → 0 ≤ counterexampleThreshold n ∧ counterexampleThreshold n < counterexampleWindow n
40. ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, 0 ≤ t → t < counterexampleWindow n →
        |sampleLaw.real {ω | t ≤ sampleStatistic n ω} / standardNormalUpperTail t - 1| ≤ ε)

Then prove exactly ONE public theorem:
fixedLawCounterexample : FixedLawCounterexample

Public surface of this final bundle is1Propdef+1theorem; no new observation/kernel/statistic or measure definition. The concrete actual objects constitute the fixed witnesses, stronger than merely postulating an existential law. Their definitions take no current n/j parameter except the deterministic sample selection/statistics and sparse category coefficient sequences. Root semantic review MUST inspect underlying definitions: actual standardNormalUpperTail=1-CDF of gaussianReal0 1; p35TailProbability=actualsampleLaw{T_n>=x_n}; actual unordered-pair U and original all-centered-row jackknifeSq/T-zero convention; true residual=-Z(x)Z(y) and full quotient L2. This bundle does not rename an assumed theorem into completion.

Clauses11/22 may require algebraic reordering of already proved exact formulas; preserve the displayed raw unscaled projection/residual signs. No Eg²=1 is claimed: actualvariance>0 and finite, source raw eigenvalue-featureVariance preserved. Any future global variance normalization must scale kernel/projection/residual/eigenvalue coherently and prove T invariance; it is not needed by this p35 root contract. Actual both taildenominators are valid: ultimate positive sample tails and positive Gaussian tails are already proved in imported modules before the ratio-limit proofs. The definition uses fullsequence x_n and b_n=2*x_n, onlysubseq ratio limits, and explicit failure of the concrete uniform-window necessary condition.

Freeze then a fresh independent blind source-to-root-contract translation/completeness review BEFORE implementation. Once unit29 actual source compiled, lead assembles the certificate from accepted actual proofs, runs designated-server target, and a separate fresh independent reviewer audits this entire root-to-source dependency chain, actual target, all public root declarations and transitive whitelist axioms. No sorry/admit/newaxiom/unsafe/native_decide. No theorem or bundle marked complete merely because imports/partial identities compile. Root coordinator separately owns shared imports/manifest/whole-library integration and final coverage label. Author owns only FixedLawCounterexample.lean/unit30 author report/scratch; sharedsource/cache/other-owner source remain untouched. OQ6 and all other programme roots remain OPEN.
