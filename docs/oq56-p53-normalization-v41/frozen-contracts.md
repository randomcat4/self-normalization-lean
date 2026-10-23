# Fixed-law real normalization — frozen interfaces

This record preserves the exact pre-implementation contracts of units127–130. The four modules use the same actual fixed real observation law and its unchanged infinite iid sample. Public payload: 19 concrete definitions/propositions and60 theorem types. Only the source-bound normalization and counterexample scope is included; OQ6/RS2 and all unresolved root groups remain open. Acceptance and exact-object receipts are recorded separately in server-checks.json and proof-review.md.



---

## Unit127 original frozen contract

# Unit127 frozen actual variance-one real population

Original p53 section1 permits fixed positive scaling, with a deterministic change of the exponential parameter. This module uses the ACTUAL fixedreal law, its actualG²integral, c=(sqrt(v))^-1, Gnorm=cG, Znorm=sqrt(c)Z andhnorm=c h. Samealpha/x/N/measure throughout.

The actualsigma is strictlypositive fromv>=1/3. No c<=1 orv>=1 is assumed. Tau0=min(1,((sqrt(c))^alpha)^-1)>0 limits the normalized exponentialclaim. The overallscope projectionvariance1 obligation remainsOPEN until all normalizedstatistic/operator/tailclaims are also paid.

```lean
def sparseRealProjectionVariance (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  ∫ z, (sparseRealG α x N z) ^ 2 ∂(sparseRealMeasure α x N)

def sparseRealNormalizationScale (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  (Real.sqrt (sparseRealProjectionVariance α x N))⁻¹

def sparseNormalizedRealG (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℝ) : ℝ :=
  sparseRealNormalizationScale α x N * sparseRealG α x N z

def sparseNormalizedRealZ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (z : ℝ) : ℝ :=
  Real.sqrt (sparseRealNormalizationScale α x N) * sparseRealZ α x N z

def sparseNormalizedRealKernel (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (u v : ℝ) : ℝ :=
  sparseRealNormalizationScale α x N * sparseRealKernel α x N u v

def sparseNormalizedRealResidual (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (u v : ℝ) : ℝ :=
  sparseRealNormalizationScale α x N * sparseRealResidual α x N u v

def sparseNormalizedRealExpParameter (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : ℝ :=
  min 1 ((Real.sqrt (sparseRealNormalizationScale α x N)) ^ α)⁻¹

theorem sparseRealNormalizationScale_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < sparseRealNormalizationScale α x N

theorem sparseRealNormalizationScale_sq_mul_variance :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (sparseRealNormalizationScale α x N) ^ 2 * sparseRealProjectionVariance α x N = 1

theorem measurable_sparseNormalizedRealG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseNormalizedRealG α x N)

theorem measurable_sparseNormalizedRealZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseNormalizedRealZ α x N)

theorem measurable_sparseNormalizedRealKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Measurable (fun w : ℝ × ℝ => sparseNormalizedRealKernel α x N w.1 w.2)

theorem sparseNormalizedRealG_indep_Z :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.IndepFun (sparseNormalizedRealG α x N) (sparseNormalizedRealZ α x N)
    (sparseRealMeasure α x N)

theorem sparseNormalizedRealG_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (fun z => -sparseNormalizedRealG α x N z) =
    (sparseRealMeasure α x N).map (sparseNormalizedRealG α x N)

theorem sparseNormalizedRealZ_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (fun z => -sparseNormalizedRealZ α x N z) =
    (sparseRealMeasure α x N).map (sparseNormalizedRealZ α x N)

theorem integral_sparseNormalizedRealG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseNormalizedRealG α x N z ∂(sparseRealMeasure α x N)) = 0

theorem integral_sparseNormalizedRealZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseNormalizedRealZ α x N z ∂(sparseRealMeasure α x N)) = 0

theorem integral_sparseNormalizedRealG_sq_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, (sparseNormalizedRealG α x N z) ^ 2 ∂(sparseRealMeasure α x N)) = 1

theorem integral_sparseNormalizedRealZ_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ z, (sparseNormalizedRealZ α x N z) ^ 2 ∂(sparseRealMeasure α x N)

theorem integrable_sparseNormalizedRealG_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseNormalizedRealG α x N z| ^ q) (sparseRealMeasure α x N)

theorem integrable_sparseNormalizedRealZ_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseNormalizedRealZ α x N z| ^ q) (sparseRealMeasure α x N)

theorem integrable_sparseNormalizedRealKernel_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun w : ℝ × ℝ => |sparseNormalizedRealKernel α x N w.1 w.2| ^ q)
    ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))

theorem sparseNormalizedRealExpParameter_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < sparseNormalizedRealExpParameter α x N

theorem sparseNormalizedRealZ_exp_bound :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  ∀ τ : ℝ, 0 < τ → τ ≤ sparseNormalizedRealExpParameter α x N →
  Integrable (fun z => Real.exp (τ * |sparseNormalizedRealZ α x N z| ^ α))
    (sparseRealMeasure α x N) ∧
  (∫ z, Real.exp (τ * |sparseNormalizedRealZ α x N z| ^ α) ∂(sparseRealMeasure α x N)) ≤ (5 / 4 : ℝ)

theorem sparseNormalizedRealKernel_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ u v : ℝ,
  sparseNormalizedRealKernel α x N u v = sparseNormalizedRealKernel α x N v u

theorem sparseNormalizedRealKernel_decomposition :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u v : ℝ,
  sparseNormalizedRealKernel α x N u v =
    sparseNormalizedRealG α x N u + sparseNormalizedRealG α x N v +
      sparseNormalizedRealZ α x N u * sparseNormalizedRealZ α x N v

theorem integrable_sparseNormalizedRealKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun w : ℝ × ℝ => sparseNormalizedRealKernel α x N w.1 w.2)
    ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))

theorem sparseNormalizedRealKernel_right_projection :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ℝ,
  Integrable (sparseNormalizedRealKernel α x N u) (sparseRealMeasure α x N) ∧
  (∫ v, sparseNormalizedRealKernel α x N u v ∂(sparseRealMeasure α x N)) =
    sparseNormalizedRealG α x N u

theorem integral_sparseNormalizedRealKernel_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ w : ℝ × ℝ, sparseNormalizedRealKernel α x N w.1 w.2
    ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) = 0

theorem sparseNormalizedRealResidual_decomposition :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u v : ℝ,
  sparseNormalizedRealKernel α x N u v - sparseNormalizedRealG α x N u - sparseNormalizedRealG α x N v =
    sparseNormalizedRealResidual α x N u v ∧
  sparseNormalizedRealResidual α x N u v = sparseNormalizedRealZ α x N u * sparseNormalizedRealZ α x N v

theorem sparseNormalizedRealResidual_right_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ℝ,
  Integrable (sparseNormalizedRealResidual α x N u) (sparseRealMeasure α x N) ∧
  (∫ v, sparseNormalizedRealResidual α x N u v ∂(sparseRealMeasure α x N)) = 0
```

All literal declarations frozen BEFORE implementation. Authors cannotchange assumptions, values or signatures. Existing P52sqrt3 specialization is an implementation-pattern reference only andcannot normalizeP53variablevariance. Only local newmodule work is authorized now; no oldproof replay orlocalLean.


---

## Unit128 original frozen contract

# Unit128 frozen actual normalized original statistic and tails

Actual fixed P53 law remains unchanged. The kernel is c h with c=(sqrt integralG²)^-1. Original centered-row jackknife from FiniteRows is used literally. The numerator includes the actual normalized populationmean. Prove pointwise T identity for alln andall observations, including the total divisionbyzero convention; no positivity premise on the sampledenominator. Positivityforn>=3 transfers separatelyAE. Both actual whole-iid tail limits keep exactlythegivenxandN.

```lean
def sparseNormalizedRealSampleU (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))

def sparseNormalizedRealSampleRowMean (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) (i : Fin n) : ℝ :=
  Shao.OQ6.FiniteRows.rowMean (fun a b => sparseNormalizedRealKernel α x N (ξ a) (ξ b)) i

def sparseNormalizedRealSampleStudentizerSq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))

def sparseNormalizedRealSampleStudentizer (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Real.sqrt (sparseNormalizedRealSampleStudentizerSq α x N ξ)

def sparseNormalizedRealSampleStudentized (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (sparseNormalizedRealSampleU α x N ξ -
      ∫ w : ℝ × ℝ, sparseNormalizedRealKernel α x N w.1 w.2
        ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) /
    sparseNormalizedRealSampleStudentizer α x N ξ

def sparseNormalizedRealSampleStudentizedTailProbability (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n : ℕ) (y : ℝ) : ℝ :=
  (sparseRealSampleMeasure α x N).real
    {ξ : ℕ → ℝ | y ≤ sparseNormalizedRealSampleStudentized α x N
      (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)}

theorem measurable_sparseNormalizedRealSampleU :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleU α x N ξ)

theorem measurable_sparseNormalizedRealSampleRowMean :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (i : Fin n),
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleRowMean α x N ξ i)

theorem measurable_sparseNormalizedRealSampleStudentizerSq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleStudentizerSq α x N ξ)

theorem measurable_sparseNormalizedRealSampleStudentizer :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleStudentizer α x N ξ)

theorem measurable_sparseNormalizedRealSampleStudentized :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleStudentized α x N ξ)

theorem measurable_sparseNormalizedRealSampleStudentized_sample :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : ℕ → ℝ => sparseNormalizedRealSampleStudentized α x N
    (fun i : Fin n => sparseRealSampleCoordinate i.val ξ))

theorem sparseNormalizedRealSampleU_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleU α x N ξ = sparseRealNormalizationScale α x N * sparseRealSampleU α x N ξ

theorem sparseNormalizedRealSampleRowMean_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ) (i : Fin n),
  sparseNormalizedRealSampleRowMean α x N ξ i = sparseRealNormalizationScale α x N *
    Shao.OQ6.FiniteRows.rowMean (fun a b => sparseRealKernel α x N (ξ a) (ξ b)) i

theorem sparseNormalizedRealSampleStudentizerSq_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleStudentizerSq α x N ξ =
    (sparseRealNormalizationScale α x N) ^ 2 * sparseRealSampleStudentizerSq α x N ξ

theorem sparseNormalizedRealSampleStudentizer_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleStudentizer α x N ξ =
    sparseRealNormalizationScale α x N * sparseRealSampleStudentizer α x N ξ

theorem sparseNormalizedRealSampleStudentized_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleStudentized α x N ξ = sparseRealSampleStudentized α x N ξ

theorem sparseNormalizedRealSampleStudentizedTailProbability_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ (n : ℕ) (y : ℝ),
  sparseNormalizedRealSampleStudentizedTailProbability α x N n y =
    sparseRealSampleStudentizedTailProbability α x N n y

theorem sparseNormalizedRealSampleStudentizer_prefix_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ n : ℕ, 3 ≤ n →
  ∀ᵐ ξ : ℕ → ℝ ∂sparseRealSampleMeasure α x N,
    0 < sparseNormalizedRealSampleStudentizer α x N
      (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)

theorem tendsto_sparseNormalizedRealSampleStudentized_logTail_normalized_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => Real.log (sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
    (-(x (N j) ^ 2) / 2)) atTop (nhds 0)

theorem tendsto_sparseNormalizedRealSampleStudentized_gaussianTail_ratio_atTop :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop
```

All interfaces andvalues frozenbeforeimplementation. Private genericfinite scalinghelpers may beprovedlocally; do notchange sharedFiniteRows. Population/scale from127 mustbequalifiedbeforeanyserverexecution. No positivePE/generalrootclosure claimed.


---

## Unit129 original frozen contract

# Unit129 frozen normalized actual real L² residual operator

The actual measure is unchanged. The normalized feature is sqrt(c) times Z and the normalized residual is c times ZZ′, with c the actual inverse square root of the projection variance. The operator is defined by the normalized L² feature on the SAME full real L² space. All literal values and complete types are frozen below before implementation.

The scalar c is nonnegative even when the totalized raw variance is zero. Thus the feature/residual identification can be proved without Core. Alpha>0 gives raw Z L²; Core is used only where explicitly present for nonzero and exact rank one. Do not silently insert Core into other signatures. Independently establish row integrability and per-f AE representatives.

```lean
def sparseNormalizedRealFeatureL2 (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    Lp ℝ 2 (sparseRealMeasure α x N) :=
  (memLp_sparseNormalizedRealZ α x N hα).toLp (sparseNormalizedRealZ α x N)

def sparseNormalizedRealResidualOperator (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) :
    (Lp ℝ 2 (sparseRealMeasure α x N)) →L[ℝ] (Lp ℝ 2 (sparseRealMeasure α x N)) :=
  InnerProductSpace.rankOne ℝ (sparseNormalizedRealFeatureL2 α x N hα) (sparseNormalizedRealFeatureL2 α x N hα)

theorem memLp_sparseNormalizedRealZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α),
  MemLp (sparseNormalizedRealZ α x N) 2 (sparseRealMeasure α x N)

theorem sparseNormalizedRealFeatureL2_coe :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  (sparseNormalizedRealFeatureL2 α x N hα : ℝ → ℝ) =ᵐ[(sparseRealMeasure α x N)] sparseNormalizedRealZ α x N

theorem integrable_sparseNormalizedRealZ_mul_Lp :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  Integrable (fun u => sparseNormalizedRealZ α x N u * f u) (sparseRealMeasure α x N)

theorem inner_sparseNormalizedRealFeatureL2 :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  inner ℝ (sparseNormalizedRealFeatureL2 α x N hα) f = ∫ u, sparseNormalizedRealZ α x N u * f u ∂(sparseRealMeasure α x N)

theorem inner_sparseNormalizedRealFeatureL2_self :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  inner ℝ (sparseNormalizedRealFeatureL2 α x N hα) (sparseNormalizedRealFeatureL2 α x N hα) = ∫ u, (sparseNormalizedRealZ α x N u) ^ 2 ∂(sparseRealMeasure α x N)

theorem sparseNormalizedRealFeatureL2_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparseNormalizedRealFeatureL2 α x N hα ≠ 0

theorem integrable_sparseNormalizedRealResidual_mul_Lp_right :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ (f : Lp ℝ 2 (sparseRealMeasure α x N)) (u : ℝ),
  Integrable (fun v => sparseNormalizedRealResidual α x N u v * f v) (sparseRealMeasure α x N)

theorem sparseNormalizedRealResidualOperator_apply_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  (sparseNormalizedRealResidualOperator α x N hα f : ℝ → ℝ) =ᵐ[(sparseRealMeasure α x N)]
    (fun u => ∫ v, sparseNormalizedRealResidual α x N u v * f v ∂(sparseRealMeasure α x N))

theorem memLp_sparseNormalizedRealResidualIntegral :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  MemLp (fun u => ∫ v, sparseNormalizedRealResidual α x N u v * f v ∂(sparseRealMeasure α x N)) 2 (sparseRealMeasure α x N)

theorem sparseNormalizedRealResidualOperator_isSelfAdjoint :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  IsSelfAdjoint (sparseNormalizedRealResidualOperator α x N hα)

theorem sparseNormalizedRealResidualOperator_quadratic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  inner ℝ f (sparseNormalizedRealResidualOperator α x N hα f) = (inner ℝ (sparseNormalizedRealFeatureL2 α x N hα) f) ^ 2

theorem sparseNormalizedRealResidualOperator_positive :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), ∀ f : Lp ℝ 2 (sparseRealMeasure α x N),
  0 ≤ inner ℝ f (sparseNormalizedRealResidualOperator α x N hα f)

theorem sparseNormalizedRealResidualOperator_rank :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  (sparseNormalizedRealResidualOperator α x N hα).toLinearMap.rank = 1

theorem sparseNormalizedRealResidualOperator_ne_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α), SparseSelectionCore α x N →
  sparseNormalizedRealResidualOperator α x N hα ≠ 0
```

No whole-kernel PSD or common null set for all L² functions is claimed. Do not modify the raw or normalized models, shared definitions, imports or assumptions. Actual normalized existential and window assembly remains unpaid.


---

## Unit130 original frozen contract

# Unit130 frozen normalized fixed-real-law counterexample assembly

Original p53 sections 1–5, with the overall variance-one convention of scope01. These literal predicates expose actual values on the same unchanged real observation law and infinite iid process. They preserve the given sequence and one subsequence selected before sampling. Normalized theta is present in the literal T identity; its genuine zero value is supplied separately by the population predicate.

Projection variance is exactly one. The normalized exponential parameter is an explicit positive tau0 from127; the range is 0<tau<=tau0. All other law/moment/symmetry/independence/residual/fullL2/originaljackknife/tail statements remain explicit conclusions. No premise supplies any desired moment, independence, positive denominator or tail behavior. The final existential theorem dischargesCore fromthe twooriginal inputlimits. Bothoriginalsection5windowexistence conclusionsare included.

```lean
def SparseNormalizedFixedRealPopulation (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  let μ := sparseRealMeasure α x N
  let G := sparseNormalizedRealG α x N
  let Z := sparseNormalizedRealZ α x N
  let h := sparseNormalizedRealKernel α x N
  IsProbabilityMeasure μ ∧
  Measurable G ∧ Measurable Z ∧
  ProbabilityTheory.IndepFun G Z μ ∧
  μ.map (fun z => -G z) = μ.map G ∧
  μ.map (fun z => -Z z) = μ.map Z ∧
  (∫ z, G z ∂μ) = 0 ∧ (∫ z, Z z ∂μ) = 0 ∧
  (∫ z, (G z) ^ 2 ∂μ) = 1 ∧
  0 < (∫ z, (Z z) ^ 2 ∂μ) ∧
  (∀ q : ℝ, 0 < q →
    Integrable (fun z => |G z| ^ q) μ ∧
    Integrable (fun z => |Z z| ^ q) μ ∧
    Integrable (fun w : ℝ × ℝ => |h w.1 w.2| ^ q) (μ.prod μ)) ∧
  0 < sparseNormalizedRealExpParameter α x N ∧
  (∀ τ : ℝ, 0 < τ → τ ≤ sparseNormalizedRealExpParameter α x N →
    Integrable (fun z => Real.exp (τ * |Z z| ^ α)) μ ∧
    (∫ z, Real.exp (τ * |Z z| ^ α) ∂μ) ≤ (5 / 4 : ℝ)) ∧
  Measurable (fun w : ℝ × ℝ => h w.1 w.2) ∧
  (∀ u v : ℝ, h u v = h v u) ∧
  (∀ u v : ℝ, h u v = G u + G v + Z u * Z v) ∧
  (∀ u : ℝ, Integrable (h u) μ ∧ (∫ v, h u v ∂μ) = G u) ∧
  Integrable (fun w : ℝ × ℝ => h w.1 w.2) (μ.prod μ) ∧
  (∫ w : ℝ × ℝ, h w.1 w.2 ∂(μ.prod μ)) = 0

def SparseNormalizedFixedRealRankOne (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) : Prop :=
  let μ := sparseRealMeasure α x N
  let G := sparseNormalizedRealG α x N
  let Z := sparseNormalizedRealZ α x N
  let h := sparseNormalizedRealKernel α x N
  let H := sparseNormalizedRealResidual α x N
  let A := sparseNormalizedRealResidualOperator α x N hα
  (∀ u v : ℝ, h u v - G u - G v = H u v ∧ H u v = Z u * Z v) ∧
  (∀ u : ℝ, Integrable (H u) μ ∧ (∫ v, H u v ∂μ) = 0) ∧
  (∀ f : Lp ℝ 2 μ,
    (A f : ℝ → ℝ) =ᵐ[μ] (fun u => ∫ v, H u v * f v ∂μ)) ∧
  IsSelfAdjoint A ∧
  (∀ f : Lp ℝ 2 μ, 0 ≤ inner ℝ f (A f)) ∧
  A.toLinearMap.rank = 1 ∧ A ≠ 0

def SparseNormalizedFixedRealIIDStatistic (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Prop :=
  let μ := sparseRealMeasure α x N
  let ν := sparseRealSampleMeasure α x N
  let X := sparseRealSampleCoordinate
  IsProbabilityMeasure ν ∧
  (∀ i : ℕ, Measurable (X i)) ∧
  ProbabilityTheory.iIndepFun X ν ∧
  (∀ i : ℕ, ν.map (X i) = μ) ∧
  (∀ n : ℕ, ν.map (fun ξ (i : Fin n) => X i.val ξ) =
    Measure.pi (fun _ : Fin n => μ)) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleU α x N ξ =
    Shao.OQ6.FiniteRows.uStatistic (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleStudentizerSq α x N ξ =
    Shao.OQ6.FiniteRows.jackknifeSq (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleStudentizer α x N ξ =
    Real.sqrt (sparseNormalizedRealSampleStudentizerSq α x N ξ)) ∧
  (∀ (n : ℕ) (ξ : Fin n → ℝ), sparseNormalizedRealSampleStudentized α x N ξ =
    Real.sqrt (n : ℝ) *
      (sparseNormalizedRealSampleU α x N ξ -
        ∫ w : ℝ × ℝ, sparseNormalizedRealKernel α x N w.1 w.2 ∂(μ.prod μ)) /
      sparseNormalizedRealSampleStudentizer α x N ξ) ∧
  (∀ n : ℕ, 3 ≤ n → ∀ᵐ ξ : ℕ → ℝ ∂ν,
    0 < sparseNormalizedRealSampleStudentizer α x N (fun i : Fin n => X i.val ξ))

def SparseNormalizedFixedRealCounterexample (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α) : Prop :=
  SparseSelectionCore α x N ∧
  N 0 = 1 ∧ StrictMono N ∧ Tendsto N atTop atTop ∧
  (∀ j : ℕ, 2 ^ j ≤ N j) ∧
  SparseNormalizedFixedRealPopulation α x N ∧
  SparseNormalizedFixedRealRankOne α x N hα ∧
  SparseNormalizedFixedRealIIDStatistic α x N ∧
  (∀ᶠ j : ℕ in atTop,
    0 < sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j))) ∧
  Tendsto (fun j : ℕ => Real.log (sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
    (-(x (N j) ^ 2) / 2)) atTop (nhds 0) ∧
  Tendsto (fun j : ℕ => sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop

theorem sparseNormalizedFixedRealPopulation_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  0 < α → SparseSelectionCore α x N → SparseNormalizedFixedRealPopulation α x N

theorem sparseNormalizedFixedRealRankOne_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  SparseSelectionCore α x N → SparseNormalizedFixedRealRankOne α x N hα

theorem sparseNormalizedFixedRealIIDStatistic :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  SparseNormalizedFixedRealIIDStatistic α x N

theorem sparseNormalizedFixedRealCounterexample_of_core :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (hα : 0 < α),
  α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  SparseNormalizedFixedRealCounterexample α x N hα

theorem exists_sparseNormalizedFixedRealCounterexample :
  ∀ (α : ℝ) (x : ℕ → ℝ) (hα : 0 < α), α < 1 →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  ∃ N : ℕ → ℕ, SparseNormalizedFixedRealCounterexample α x N hα

theorem exists_sparseNormalizedFixedRealCounterexample_relativeWindow :
  ∀ (p α : ℝ) (hα : 0 < α), 2 < p → p ≤ 3 → α < 2 * (p - 2) / (2 * p - 1) →
  ∃ N : ℕ → ℕ, SparseNormalizedFixedRealCounterexample α (sparseRelativeWindow p) N hα

theorem exists_sparseNormalizedFixedRealCounterexample_twoFifths :
  ∃ N : ℕ → ℕ, SparseNormalizedFixedRealCounterexample (2 / 5 : ℝ) sparseFifthPowerWindow N (by norm_num)
```

All values and types frozen before implementation. This freeze and future local proof do not certify root closure. The exact127/128/129 dependencies, target-source fidelity, entire proof, actual owned types/values and transitive axioms must all qualify before acceptance. No whole-kernel PSD, positive PE, general RS2/OQ6 closure, critical constant or firstness is claimed.
