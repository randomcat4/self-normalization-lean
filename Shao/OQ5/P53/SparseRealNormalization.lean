import Shao.OQ5.P53.SparseRealModel

/-!
# Actual variance-one normalization of the fixed p53 real population

The measure, alpha and selected sequences stay fixed. The normalizing scalar
uses the actual second moment. The exponential parameter is adjusted by the
scaled feature. This file makes no operator or sample-statistic assertion.
-/

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

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

private theorem projection_variance_pos (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    0 < sparseRealProjectionVariance α x N := by
  have hv := integral_sparseRealG_sq_ge α x N hα hN
  change (1 / 3 : ℝ) ≤ sparseRealProjectionVariance α x N at hv
  linarith

private theorem raw_G_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    Integrable (sparseRealG α x N) (sparseRealMeasure α x N) := by
  apply (integrable_norm_iff (measurable_sparseRealG α x N).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs, Real.rpow_one] using
    integrable_sparseRealG_rpow α x N hα hN 1 (by norm_num)

private theorem raw_Z_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) :
    Integrable (sparseRealZ α x N) (sparseRealMeasure α x N) := by
  apply (integrable_norm_iff (measurable_sparseRealZ α x N).aestronglyMeasurable).mp
  simpa only [Real.norm_eq_abs, Real.rpow_one] using
    integrable_sparseRealZ_rpow α x N hα 1 (by norm_num)

private theorem raw_G_sq_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) (hN : SparseSelectionCore α x N) :
    Integrable (fun z => (sparseRealG α x N z) ^ 2) (sparseRealMeasure α x N) := by
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparseRealG_rpow α x N hα hN 2 (by norm_num)

private theorem raw_Z_sq_integrable (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hα : 0 < α) :
    Integrable (fun z => (sparseRealZ α x N z) ^ 2) (sparseRealMeasure α x N) := by
  simpa only [Real.rpow_two, sq_abs] using
    integrable_sparseRealZ_rpow α x N hα 2 (by norm_num)

private theorem scaled_symmetric (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : Measurable f)
    (hs : μ.map (fun z => -f z) = μ.map f) (c : ℝ) :
    μ.map (fun z => -(c * f z)) = μ.map (fun z => c * f z) := by
  have hc : Measurable (fun t : ℝ => c * t) := measurable_const.mul measurable_id
  have hneg : Measurable (fun z : ℝ => -f z) := hf.neg
  have hmap :
      (μ.map (fun z : ℝ => -f z)).map (fun t : ℝ => c * t) =
        μ.map ((fun t : ℝ => c * t) ∘ (fun z : ℝ => -f z)) :=
    Measure.map_map hc hneg
  calc
    μ.map (fun z => -(c * f z)) =
        (μ.map (fun z => -f z)).map (fun t : ℝ => c * t) := by
      simpa only [Function.comp_def, mul_neg] using hmap.symm
    _ = (μ.map f).map (fun t : ℝ => c * t) := by rw [hs]
    _ = μ.map (fun z => c * f z) := Measure.map_map hc hf

private theorem abs_scaled_rpow (c t q : ℝ) :
    |c * t| ^ q = |c| ^ q * |t| ^ q := by
  rw [abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg t)]

theorem sparseRealNormalizationScale_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < sparseRealNormalizationScale α x N := by
  intro α x N hα hN
  exact inv_pos.mpr (Real.sqrt_pos.mpr (projection_variance_pos α x N hα hN))

theorem sparseRealNormalizationScale_sq_mul_variance :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (sparseRealNormalizationScale α x N) ^ 2 * sparseRealProjectionVariance α x N = 1 := by
  intro α x N hα hN
  have hv := projection_variance_pos α x N hα hN
  unfold sparseRealNormalizationScale
  rw [inv_pow, Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

theorem measurable_sparseNormalizedRealG :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseNormalizedRealG α x N) := by
  intro α x N
  exact measurable_const.mul (measurable_sparseRealG α x N)

theorem measurable_sparseNormalizedRealZ :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), Measurable (sparseNormalizedRealZ α x N) := by
  intro α x N
  exact measurable_const.mul (measurable_sparseRealZ α x N)

theorem measurable_sparseNormalizedRealKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Measurable (fun w : ℝ × ℝ => sparseNormalizedRealKernel α x N w.1 w.2) := by
  intro α x N
  exact measurable_const.mul (measurable_sparseRealKernel α x N)

theorem sparseNormalizedRealG_indep_Z :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.IndepFun (sparseNormalizedRealG α x N) (sparseNormalizedRealZ α x N)
    (sparseRealMeasure α x N) := by
  intro α x N
  have hG : Measurable (fun t : ℝ => sparseRealNormalizationScale α x N * t) :=
    measurable_const.mul measurable_id
  have hZ : Measurable (fun t : ℝ => Real.sqrt (sparseRealNormalizationScale α x N) * t) :=
    measurable_const.mul measurable_id
  exact (sparseRealG_indep_Z α x N).comp hG hZ

theorem sparseNormalizedRealG_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (fun z => -sparseNormalizedRealG α x N z) =
    (sparseRealMeasure α x N).map (sparseNormalizedRealG α x N) := by
  intro α x N
  exact scaled_symmetric _ _ (measurable_sparseRealG α x N)
    (sparseRealG_symmetric α x N) (sparseRealNormalizationScale α x N)

theorem sparseNormalizedRealZ_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseRealMeasure α x N).map (fun z => -sparseNormalizedRealZ α x N z) =
    (sparseRealMeasure α x N).map (sparseNormalizedRealZ α x N) := by
  intro α x N
  exact scaled_symmetric _ _ (measurable_sparseRealZ α x N)
    (sparseRealZ_symmetric α x N) (Real.sqrt (sparseRealNormalizationScale α x N))

theorem integral_sparseNormalizedRealG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseNormalizedRealG α x N z ∂(sparseRealMeasure α x N)) = 0 := by
  intro α x N hα hN
  have _hI : Integrable (sparseNormalizedRealG α x N) (sparseRealMeasure α x N) :=
    (raw_G_integrable α x N hα hN).const_mul (sparseRealNormalizationScale α x N)
  unfold sparseNormalizedRealG
  rw [integral_const_mul, integral_sparseRealG_zero α x N hα hN, mul_zero]

theorem integral_sparseNormalizedRealZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, sparseNormalizedRealZ α x N z ∂(sparseRealMeasure α x N)) = 0 := by
  intro α x N hα _hN
  have _hI : Integrable (sparseNormalizedRealZ α x N) (sparseRealMeasure α x N) :=
    (raw_Z_integrable α x N hα).const_mul (Real.sqrt (sparseRealNormalizationScale α x N))
  unfold sparseNormalizedRealZ
  rw [integral_const_mul, integral_sparseRealZ_zero α x N hα, mul_zero]

theorem integral_sparseNormalizedRealG_sq_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ z, (sparseNormalizedRealG α x N z) ^ 2 ∂(sparseRealMeasure α x N)) = 1 := by
  intro α x N hα hN
  have heq : (fun z => (sparseNormalizedRealG α x N z) ^ 2) =
      (fun z => (sparseRealNormalizationScale α x N) ^ 2 * (sparseRealG α x N z) ^ 2) := by
    funext z
    exact mul_pow _ _ 2
  have _hI : Integrable (fun z => (sparseNormalizedRealG α x N z) ^ 2)
      (sparseRealMeasure α x N) := by
    rw [heq]
    exact (raw_G_sq_integrable α x N hα hN).const_mul _
  rw [heq, integral_const_mul]
  exact sparseRealNormalizationScale_sq_mul_variance α x N hα hN

theorem integral_sparseNormalizedRealZ_sq_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < ∫ z, (sparseNormalizedRealZ α x N z) ^ 2 ∂(sparseRealMeasure α x N) := by
  intro α x N hα hN
  have hc := sparseRealNormalizationScale_pos α x N hα hN
  have heq : (fun z => (sparseNormalizedRealZ α x N z) ^ 2) =
      (fun z => sparseRealNormalizationScale α x N * (sparseRealZ α x N z) ^ 2) := by
    funext z
    rw [sparseNormalizedRealZ, mul_pow, Real.sq_sqrt hc.le]
  have _hI : Integrable (fun z => (sparseNormalizedRealZ α x N z) ^ 2)
      (sparseRealMeasure α x N) := by
    rw [heq]
    exact (raw_Z_sq_integrable α x N hα).const_mul _
  rw [heq, integral_const_mul]
  exact mul_pos hc (integral_sparseRealZ_sq_pos α x N hα hN)

theorem integrable_sparseNormalizedRealG_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseNormalizedRealG α x N z| ^ q) (sparseRealMeasure α x N) := by
  intro α x N hα hN q hq
  simpa only [sparseNormalizedRealG, abs_scaled_rpow] using
    (integrable_sparseRealG_rpow α x N hα hN q hq).const_mul
      (|sparseRealNormalizationScale α x N| ^ q)

theorem integrable_sparseNormalizedRealZ_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun z => |sparseNormalizedRealZ α x N z| ^ q) (sparseRealMeasure α x N) := by
  intro α x N hα _hN q hq
  simpa only [sparseNormalizedRealZ, abs_scaled_rpow] using
    (integrable_sparseRealZ_rpow α x N hα q hq).const_mul
      (|Real.sqrt (sparseRealNormalizationScale α x N)| ^ q)

theorem integrable_sparseNormalizedRealKernel_rpow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ q : ℝ, 0 < q →
  Integrable (fun w : ℝ × ℝ => |sparseNormalizedRealKernel α x N w.1 w.2| ^ q)
    ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)) := by
  intro α x N hα hN q hq
  simpa only [sparseNormalizedRealKernel, abs_scaled_rpow] using
    (integrable_sparseRealKernel_rpow α x N hα hN q hq).const_mul
      (|sparseRealNormalizationScale α x N| ^ q)

theorem sparseNormalizedRealExpParameter_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  0 < sparseNormalizedRealExpParameter α x N := by
  intro α x N hα hN
  have hs : 0 < Real.sqrt (sparseRealNormalizationScale α x N) :=
    Real.sqrt_pos.mpr (sparseRealNormalizationScale_pos α x N hα hN)
  exact lt_min (by norm_num) (inv_pos.mpr (Real.rpow_pos_of_pos hs α))

theorem sparseNormalizedRealZ_exp_bound :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  ∀ τ : ℝ, 0 < τ → τ ≤ sparseNormalizedRealExpParameter α x N →
  Integrable (fun z => Real.exp (τ * |sparseNormalizedRealZ α x N z| ^ α))
    (sparseRealMeasure α x N) ∧
  (∫ z, Real.exp (τ * |sparseNormalizedRealZ α x N z| ^ α) ∂(sparseRealMeasure α x N)) ≤ (5 / 4 : ℝ) := by
  intro α x N hα hN τ hτ hτ0
  have hs : 0 < Real.sqrt (sparseRealNormalizationScale α x N) :=
    Real.sqrt_pos.mpr (sparseRealNormalizationScale_pos α x N hα hN)
  have hLambda : 0 < (Real.sqrt (sparseRealNormalizationScale α x N)) ^ α :=
    Real.rpow_pos_of_pos hs α
  have hτinv : τ ≤ ((Real.sqrt (sparseRealNormalizationScale α x N)) ^ α)⁻¹ :=
    le_trans hτ0 (min_le_right _ _)
  have hTauLambda : τ * (Real.sqrt (sparseRealNormalizationScale α x N)) ^ α ≤ 1 := by
    calc
      _ ≤ ((Real.sqrt (sparseRealNormalizationScale α x N)) ^ α)⁻¹ *
          (Real.sqrt (sparseRealNormalizationScale α x N)) ^ α :=
        mul_le_mul_of_nonneg_right hτinv hLambda.le
      _ = 1 := inv_mul_cancel₀ hLambda.ne'
  have heq : (fun z => Real.exp (τ * |sparseNormalizedRealZ α x N z| ^ α)) =
      (fun z => Real.exp ((τ * (Real.sqrt (sparseRealNormalizationScale α x N)) ^ α) *
        |sparseRealZ α x N z| ^ α)) := by
    funext z
    rw [sparseNormalizedRealZ, abs_mul, abs_of_nonneg hs.le,
      Real.mul_rpow hs.le (abs_nonneg _)]
    exact congrArg Real.exp (by ring)
  rw [heq]
  exact ⟨integrable_sparseRealZ_exp α x N hα _ (mul_pos hτ hLambda) hTauLambda,
    integral_sparseRealZ_exp_le α x N hα _ (mul_pos hτ hLambda) hTauLambda⟩

theorem sparseNormalizedRealKernel_symmetric :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ u v : ℝ,
  sparseNormalizedRealKernel α x N u v = sparseNormalizedRealKernel α x N v u := by
  intro α x N u v
  unfold sparseNormalizedRealKernel
  rw [sparseRealKernel_symmetric α x N u v]

theorem sparseNormalizedRealKernel_decomposition :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u v : ℝ,
  sparseNormalizedRealKernel α x N u v =
    sparseNormalizedRealG α x N u + sparseNormalizedRealG α x N v +
      sparseNormalizedRealZ α x N u * sparseNormalizedRealZ α x N v := by
  intro α x N hα hN u v
  have hc := sparseRealNormalizationScale_pos α x N hα hN
  dsimp only [sparseNormalizedRealKernel, sparseNormalizedRealG, sparseNormalizedRealZ,
    sparseRealKernel]
  calc
    _ = sparseRealNormalizationScale α x N * sparseRealG α x N u +
        sparseRealNormalizationScale α x N * sparseRealG α x N v +
        (Real.sqrt (sparseRealNormalizationScale α x N)) ^ 2 *
          (sparseRealZ α x N u * sparseRealZ α x N v) := by
      rw [Real.sq_sqrt hc.le]
      ring
    _ = _ := by ring

theorem integrable_sparseNormalizedRealKernel :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  Integrable (fun w : ℝ × ℝ => sparseNormalizedRealKernel α x N w.1 w.2)
    ((sparseRealMeasure α x N).prod (sparseRealMeasure α x N)) := by
  intro α x N hα hN
  exact (integrable_sparseRealKernel α x N hα hN).const_mul (sparseRealNormalizationScale α x N)

theorem sparseNormalizedRealKernel_right_projection :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ℝ,
  Integrable (sparseNormalizedRealKernel α x N u) (sparseRealMeasure α x N) ∧
  (∫ v, sparseNormalizedRealKernel α x N u v ∂(sparseRealMeasure α x N)) =
    sparseNormalizedRealG α x N u := by
  intro α x N hα hN u
  have hI : Integrable (sparseNormalizedRealKernel α x N u) (sparseRealMeasure α x N) :=
    (integrable_sparseRealKernel_right α x N hα hN u).const_mul (sparseRealNormalizationScale α x N)
  refine ⟨hI, ?_⟩
  unfold sparseNormalizedRealKernel sparseNormalizedRealG
  rw [integral_const_mul, integral_sparseRealKernel_right α x N hα hN u]

theorem integral_sparseNormalizedRealKernel_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N →
  (∫ w : ℝ × ℝ, sparseNormalizedRealKernel α x N w.1 w.2
    ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) = 0 := by
  intro α x N hα hN
  have _hI := integrable_sparseNormalizedRealKernel α x N hα hN
  unfold sparseNormalizedRealKernel
  rw [integral_const_mul, integral_sparseRealKernel_zero α x N hα hN, mul_zero]

theorem sparseNormalizedRealResidual_decomposition :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u v : ℝ,
  sparseNormalizedRealKernel α x N u v - sparseNormalizedRealG α x N u - sparseNormalizedRealG α x N v =
    sparseNormalizedRealResidual α x N u v ∧
  sparseNormalizedRealResidual α x N u v = sparseNormalizedRealZ α x N u * sparseNormalizedRealZ α x N v := by
  intro α x N hα hN u v
  have hres : sparseNormalizedRealKernel α x N u v - sparseNormalizedRealG α x N u -
      sparseNormalizedRealG α x N v = sparseNormalizedRealResidual α x N u v := by
    dsimp only [sparseNormalizedRealKernel, sparseNormalizedRealG, sparseNormalizedRealResidual]
    calc
      _ = sparseRealNormalizationScale α x N *
          (sparseRealKernel α x N u v - sparseRealG α x N u - sparseRealG α x N v) := by ring
      _ = _ := by rw [sparseRealResidual_decomposition α x N u v]
  refine ⟨hres, ?_⟩
  rw [← hres, sparseNormalizedRealKernel_decomposition α x N hα hN u v]
  ring

theorem sparseNormalizedRealResidual_right_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ u : ℝ,
  Integrable (sparseNormalizedRealResidual α x N u) (sparseRealMeasure α x N) ∧
  (∫ v, sparseNormalizedRealResidual α x N u v ∂(sparseRealMeasure α x N)) = 0 := by
  intro α x N hα _hN u
  have hI : Integrable (sparseNormalizedRealResidual α x N u) (sparseRealMeasure α x N) :=
    (integrable_sparseRealResidual_right α x N hα u).const_mul (sparseRealNormalizationScale α x N)
  refine ⟨hI, ?_⟩
  unfold sparseNormalizedRealResidual
  rw [integral_const_mul, integral_sparseRealResidual_right_zero α x N hα u, mul_zero]

end Shao.OQ5.P53
