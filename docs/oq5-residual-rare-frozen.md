# Frozen residual/rare interfaces

Original p35 only; all roots remain OPEN. Exact lane unit contracts below, independently source-reviewed before implementation.

# OQ56 unit12 — exact fixed category tails, frozen v1

Source p35 §3/4, especially q_j=P(C<j) in (9)/(10). Use the same actual categoryMeasure and categoryMass. No conditioning or new law.

Namespace Shao.OQ5.P35:
categoryBelowMass (j : ℕ) : ℝ := categoryMeasure.real (Set.Iio j)

Exact conclusions:
categoryBelowMass_zero : categoryBelowMass 0 = 0
categoryBelowMass_nonneg (j : ℕ) : 0 ≤ categoryBelowMass j
categoryBelowMass_eq (j : ℕ) (hj : 1 ≤ j) : categoryBelowMass j = 1 - (16384/16383 : ℝ) * (1/16384 : ℝ) ^ j
categoryMeasure_above_eq (j : ℕ) : categoryMeasure.real (Set.Ioi j) = (1/16383 : ℝ) * (1/16384 : ℝ) ^ j
categoryBelowMass_bounds (j : ℕ) (hj : 1 ≤ j) : (16382/16383 : ℝ) ≤ categoryBelowMass j ∧ categoryBelowMass j < 1

The positive-index premise on the CDF formula and bounds is essential; the special atom at zero is unchanged. The strict-upper-tail formula includes j=0. All real probabilities are of the actual finite probability measure. Supporting finite-sum/recurrence helpers may be added. No sample-size dependence, premise changes, Q1 conditionals or generic shared modules. This is a Q0/Q2 category-tail dependency only. Independent statement review before implementation; designated-server compilation and fresh proof/semantic+axiom audits afterwards. No sorry/admit/new axiom/unsafe/native_decide; shared cache read-only.

# OQ56 unit13 — actual fixed-position and count events, frozen v1

Source p35 §4 formula(9), contract Q0. Use existing sampleLaw/sampleCoordinate, actual categoryMeasure/categoryMass and categoryBelowMass. All finite n use this same infinite probability space; this unit has no conditional-law theorem.

Namespace Shao.OQ5.P35:
sampleCategory (i : ℕ) (ω : ℕ → ℝ) : ℕ := decodeCategory (sampleCoordinate i ω)
fixedCategoryEvent (n j : ℕ) (J : Finset (Fin n)) : Set (ℕ → ℝ) := {ω | ∀ i : Fin n, if i ∈ J then sampleCategory i.val ω = j else sampleCategory i.val ω < j}
exactCategoryEvent (n K j : ℕ) : Set (ℕ → ℝ) := {ω | (Finset.univ.filter (fun i : Fin n => sampleCategory i.val ω = j)).card = K ∧ ∀ i : Fin n, sampleCategory i.val ω ≤ j}
targetCategoryCount (j : ℕ) : ℕ := 4 ^ j
rareSampleSize (j : ℕ) : ℕ := targetCategoryCount j ^ 4
rareCategoryEvent (j : ℕ) : Set (ℕ → ℝ) := exactCategoryEvent (rareSampleSize j) (targetCategoryCount j) j

Exact required conclusions:
measurable_sampleCategory (i : ℕ) : Measurable (sampleCategory i)
map_sampleCategory (i : ℕ) : MeasureTheory.Measure.map (sampleCategory i) sampleLaw = categoryMeasure
iIndepFun_sampleCategory : ProbabilityTheory.iIndepFun sampleCategory sampleLaw
measurableSet_fixedCategoryEvent (n j : ℕ) (J : Finset (Fin n)) : MeasurableSet (fixedCategoryEvent n j J)
measurableSet_exactCategoryEvent (n K j : ℕ) : MeasurableSet (exactCategoryEvent n K j)
fixedCategoryEvent_probability (n j : ℕ) (J : Finset (Fin n)) : sampleLaw.real (fixedCategoryEvent n j J) = categoryMass j ^ J.card * categoryBelowMass j ^ (n - J.card)
exactCategoryEvent_eq_biUnion (n K j : ℕ) : exactCategoryEvent n K j = ⋃ J ∈ (Finset.univ : Finset (Fin n)).powersetCard K, fixedCategoryEvent n j J
fixedCategoryEvent_disjoint (n j : ℕ) (J J' : Finset (Fin n)) (hJJ : J ≠ J') : Disjoint (fixedCategoryEvent n j J) (fixedCategoryEvent n j J')
exactCategoryEvent_probability (n K j : ℕ) (hK : K ≤ n) : sampleLaw.real (exactCategoryEvent n K j) = (n.choose K : ℝ) * categoryMass j ^ K * categoryBelowMass j ^ (n - K)
targetCategoryCount_le_rareSampleSize (j : ℕ) : targetCategoryCount j ≤ rareSampleSize j
rareCategoryEvent_probability (j : ℕ) (hj : 1 ≤ j) : sampleLaw.real (rareCategoryEvent j) = ((rareSampleSize j).choose (targetCategoryCount j) : ℝ) * categoryMass j ^ targetCategoryCount j * categoryBelowMass j ^ (rareSampleSize j - targetCategoryCount j)
rareCategoryEvent_probability_pos (j : ℕ) (hj : 1 ≤ j) : 0 < sampleLaw.real (rareCategoryEvent j)

The helper count formula explicitly restricts K≤n, discharged for each actual rare event; its event is the literal count/no-larger event, not a union-only surrogate. Fixed-position events require all remaining coordinates to be strictly below j. Keep empty n, j=0 and K=0 cases in general helper statements as written; 0^0 uses ordinary Lean natural-power convention. Rare source statements retain j≥1. There is no eventual exponential lower bound claim yet. No Q1/generic conditional iid duplication: root owns ConditionalIID. Supporting source-specific finite counting/measurability/product helpers permitted. No changed premises, fourth moments, distribution arrays, sorry/admit/new axiom/unsafe/native_decide. Server-only compilation; independent source/statement review before implementation, fresh proof/semantic and axiom audit after.

# OQ56 unit14 — actual full-L2 canonical residual operator, frozen v1

Source p35 §1 formula(1), §3 following formula(8): canonical residual operator on L²(realLaw) is f↦-Z∫Zf, rank exactly1 and only nonzero eigenvalue -EZ². Exact existing raw feature, residual, realLaw and featureVariance are unchanged. No finite-dimensional ambient-space or spectrum assertion.

Namespace Shao.OQ5.P35:
abbrev ObservationL2 := MeasureTheory.Lp ℝ 2 realLaw
memLp_observationFeature : MeasureTheory.MemLp observationFeature 2 realLaw
featureL2 : ObservationL2 := MeasureTheory.MemLp.toLp observationFeature memLp_observationFeature
residualOperator : ObservationL2 →L[ℝ] ObservationL2 := InnerProductSpace.rankOne ℝ (-featureL2) featureL2

Exact required conclusions:
featureL2_coe : (featureL2 : ℝ → ℝ) =ᵐ[realLaw] observationFeature
inner_featureL2_self : inner ℝ featureL2 featureL2 = featureVariance
featureL2_ne_zero : featureL2 ≠ 0
integrable_feature_mul_Lp (f : ObservationL2) : MeasureTheory.Integrable (fun y => observationFeature y * f y) realLaw
inner_featureL2 (f : ObservationL2) : inner ℝ featureL2 f = ∫ y, observationFeature y * f y ∂realLaw
integrable_residual_mul_Lp_right (f : ObservationL2) (x : ℝ) : MeasureTheory.Integrable (fun y => populationResidual x y * f y) realLaw
residualOperator_apply_ae (f : ObservationL2) : (residualOperator f : ℝ → ℝ) =ᵐ[realLaw] (fun x => ∫ y, populationResidual x y * f y ∂realLaw)
memLp_residualIntegral (f : ObservationL2) : MeasureTheory.MemLp (fun x => ∫ y, populationResidual x y * f y ∂realLaw) 2 realLaw
residualOperator_range : LinearMap.range residualOperator.toLinearMap = Submodule.span ℝ ({featureL2} : Set ObservationL2)
residualOperator_rank : residualOperator.toLinearMap.rank = 1
residualOperator_feature : residualOperator featureL2 = (-featureVariance) • featureL2
residualOperator_nonzero_eigenvalues : {λ : ℝ | λ ≠ 0 ∧ Module.End.HasEigenvalue residualOperator.toLinearMap λ} = {(-featureVariance)}

The full domain is every f in the actual quotient L² space. Feature/CLM representatives agree only AE, and all output/kernel action equalities retain that AE qualifier; no pointwise representative assertion. All kernel sections are actually integrable for every such f and every real x before action identity; no assumed integrability premise, fourth feature moment, iid or d/Z independence input. featureVariance>0 is already proved, so the eigenvalue set equality asserts actual existence and uniqueness among nonzero eigenvalues; 0 is neither included nor excluded as a spectrum/eigenvalue claim. The rank statement refers to the residual, not full populationKernel. Additional helpers allowed, no premise changes. Independent source review before proof; assigned-server actual Lean, fresh independent proof/semantic and transitive axiom audits after. No sorry/admit/new axiom/unsafe/native_decide; caches read-only.

# OQ56 unit15 — sharp finite real binomial lower bound, frozen v1

Source p35§4 proof of(9), Q0: choose(n,K)≥(n/K)^K. This is a deterministic scalar helper in the p35 namespace, strictly weaker than any probability root. No probability or asymptotic premises.

Namespace Shao.OQ5.P35, exact required conclusion:
real_pow_div_le_choose (n K : ℕ) (hK : 0 < K) (hKn : K ≤ n) : ((n : ℝ)/(K : ℝ)) ^ K ≤ (n.choose K : ℝ)

Keep both natural hypotheses. All powers are ordinary natural powers, real casts exact; division denominators positive. This is a general finite helper to be discharged at n=k⁴,K=k in the source, not a new hypothesis of the root. No Stirling/external theorem as an assumption, no alternate weaker factorial bound substituted. Supporting induction/product identities permitted. Author may not change premise/quantifier or move shared code. Independent source/statement review before proof; server-only actual compilation, independent proof/source and axiom checks after. No sorry/admit/new axiom/unsafe/native_decide.

# OQ56 unit16 — source-bound eventual rare-event lower bound, frozen v1

Source p35§4 formula(9), Q0. Existing actual sampleLaw, rareCategoryEvent, targetCategoryCount=4^j, rareSampleSize=targetCount^4, categoryScale=(4:ℝ)^j and categoryBelowMass=P(C<j) are unchanged. All n use one fixed sample law.

Namespace Shao.OQ5.P35, exact required conclusions:
rareSampleSize_tail_error (j : ℕ) (hj : 1 ≤ j) : (rareSampleSize j : ℝ) * (1-categoryBelowMass j) = (16384/16383 : ℝ) * (1/64 : ℝ) ^ j
categoryBelowMass_power_tendsto : Filter.Tendsto (fun j => categoryBelowMass j ^ (rareSampleSize j-targetCategoryCount j)) Filter.atTop (nhds (1 : ℝ))
rareCategoryEvent_half_lower : ∀ᶠ j in Filter.atTop, (1/2 : ℝ) * (categoryScale j)⁻¹ ^ (4*targetCategoryCount j) ≤ sampleLaw.real (rareCategoryEvent j)
rareCategoryEvent_exp_comparison : ∀ᶠ j in Filter.atTop, Real.exp (-5*categoryScale j*Real.log (categoryScale j)) ≤ (1/2 : ℝ) * (categoryScale j)⁻¹ ^ (4*targetCategoryCount j)
rareCategoryEvent_exp_lower : ∀ᶠ j in Filter.atTop, Real.exp (-5*categoryScale j*Real.log (categoryScale j)) ≤ sampleLaw.real (rareCategoryEvent j)

The inverse has real type and natural exponent4*K_j, exactly k_j^(-4k_j). The first identity explicitly excludes j=0 (special zero atom); limit/eventual outputs use full j:Nat domain and require actual eventual arguments, without substituting a finite check, an unspecified subsequence or an invented numerical cutoff. Helpers can prove explicit positivity and derived numerical ranges if actually established, but the required outputs remain these eventual statements. Use exact actual count-event probability, sharp binomial helper and Bernoulli/geometric limit; no new probabilistic assumptions, triangular array or Q1 theorem. All logs/exponential comparisons must have required positivity before use. This closes only Q0, not conditional moments/studentizer/tail conclusions. Independent source/statement review before proof; server actual Lean and independent proof/semantic/axiom gates after. No sorry/admit/new axiom/unsafe/native_decide; shared cache read-only.
