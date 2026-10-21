import Shao.OQ5.P35.RealMoments
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Kernel moments and Hoeffding identities for the fixed p35 law

Source: `current/oq56/inputs02/p35.md`, §3, formulas (1) and (8).
All expectations use the existing real law. Products of feature second moments
refer to the two distinct coordinates of the product law; no same-coordinate
fourth moment or offset/feature independence is assumed.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

open MeasureTheory

noncomputable section

/-- The actual mean of the category offset under the fixed real law. -/
def offsetMean : ℝ := ∫ x, observationOffset x ∂realLaw

/-- The mean of the raw, unscaled population kernel. -/
def populationMean : ℝ := 2 * offsetMean

/-- The centered first Hoeffding projection of the raw population kernel. -/
def populationProjection (x : ℝ) : ℝ :=
  decodeNoise x + observationOffset x - offsetMean

/-- The negative rank-one canonical residual, before any variance scaling. -/
def populationResidual (x y : ℝ) : ℝ :=
  -observationFeature x * observationFeature y

theorem integrable_observationOffset : Integrable observationOffset realLaw := by
  simpa only [pow_one] using integrable_observationOffset_pow 1 (by norm_num)

private theorem offset_sq_integrable_for_kernel :
    Integrable (fun x => observationOffset x ^ 2) realLaw :=
  integrable_observationOffset_pow 2 (by norm_num)

theorem integrable_populationKernel :
    Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2)
      (realLaw.prod realLaw) := by
  unfold populationKernel
  exact ((((integrable_decodeNoise.comp_fst realLaw).add
    (integrable_decodeNoise.comp_snd realLaw)).add
    (integrable_observationOffset.comp_fst realLaw)).add
    (integrable_observationOffset.comp_snd realLaw)).sub
    (integrable_observationFeature.mul_prod integrable_observationFeature)

private theorem five_term_square_bound (a b c d e : ℝ) :
    (a + b + c + d - e) ^ 2 ≤
      5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (a + e), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (b + e), sq_nonneg (c - d), sq_nonneg (c + e), sq_nonneg (d + e)]

theorem integrable_populationKernel_sq :
    Integrable (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2 ^ 2)
      (realLaw.prod realLaw) := by
  have hbound : Integrable (fun xy : ℝ × ℝ => 5 *
      (decodeNoise xy.1 ^ 2 + decodeNoise xy.2 ^ 2 +
        observationOffset xy.1 ^ 2 + observationOffset xy.2 ^ 2 +
        observationFeature xy.1 ^ 2 * observationFeature xy.2 ^ 2))
      (realLaw.prod realLaw) :=
    (((((integrable_decodeNoise_sq.comp_fst realLaw).add
      (integrable_decodeNoise_sq.comp_snd realLaw)).add
      (offset_sq_integrable_for_kernel.comp_fst realLaw)).add
      (offset_sq_integrable_for_kernel.comp_snd realLaw)).add
      (integrable_observationFeature_sq.mul_prod integrable_observationFeature_sq)).const_mul 5
  have hm : AEStronglyMeasurable
      (fun xy : ℝ × ℝ => populationKernel xy.1 xy.2 ^ 2)
      (realLaw.prod realLaw) :=
    (measurable_populationKernel.pow_const 2).aestronglyMeasurable
  apply hbound.mono' hm
  filter_upwards [] with xy
  rw [Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (populationKernel xy.1 xy.2))]
  simpa only [populationKernel, mul_pow] using
    five_term_square_bound (decodeNoise xy.1) (decodeNoise xy.2)
      (observationOffset xy.1) (observationOffset xy.2)
      (observationFeature xy.1 * observationFeature xy.2)

theorem integrable_populationKernel_right (x : ℝ) :
    Integrable (populationKernel x) realLaw := by
  unfold populationKernel
  exact ((((integrable_const (decodeNoise x)).add integrable_decodeNoise).add
    (integrable_const (observationOffset x))).add integrable_observationOffset).sub
    (integrable_observationFeature.const_mul (observationFeature x))

theorem integral_populationKernel_right (x : ℝ) :
    (∫ y, populationKernel x y ∂realLaw) =
      populationProjection x + populationMean := by
  have hA : Integrable (fun y => decodeNoise x + decodeNoise y) realLaw :=
    (integrable_const (decodeNoise x)).add integrable_decodeNoise
  have hB : Integrable (fun y => decodeNoise x + decodeNoise y + observationOffset x)
      realLaw := hA.add (integrable_const (observationOffset x))
  have hC : Integrable (fun y => decodeNoise x + decodeNoise y +
      observationOffset x + observationOffset y) realLaw := hB.add integrable_observationOffset
  unfold populationKernel
  rw [integral_sub hC (integrable_observationFeature.const_mul (observationFeature x)),
    integral_add hB integrable_observationOffset,
    integral_add hA (integrable_const (observationOffset x)),
    integral_add (integrable_const (decodeNoise x)) integrable_decodeNoise,
    integral_const_mul, integral_decodeNoise, integral_observationFeature]
  simp only [integral_const, probReal_univ, one_smul, mul_zero, sub_zero, add_zero]
  unfold populationProjection populationMean offsetMean
  ring

private theorem projection_integrable_for_kernel :
    Integrable populationProjection realLaw := by
  unfold populationProjection
  exact (integrable_decodeNoise.add integrable_observationOffset).sub
    (integrable_const offsetMean)

private theorem projection_integral_for_kernel :
    (∫ x, populationProjection x ∂realLaw) = 0 := by
  have hs : Integrable (fun x => decodeNoise x + observationOffset x) realLaw :=
    integrable_decodeNoise.add integrable_observationOffset
  unfold populationProjection
  rw [integral_sub hs (integrable_const offsetMean),
    integral_add integrable_decodeNoise integrable_observationOffset,
    integral_decodeNoise, integral_const, probReal_univ, one_smul]
  simp only [offsetMean, zero_add, sub_self]

theorem integral_populationKernel :
    (∫ xy : ℝ × ℝ, populationKernel xy.1 xy.2 ∂realLaw.prod realLaw) =
      populationMean := by
  rw [integral_prod _ integrable_populationKernel]
  simp_rw [integral_populationKernel_right]
  rw [integral_add projection_integrable_for_kernel (integrable_const populationMean),
    projection_integral_for_kernel, integral_const, probReal_univ, one_smul, zero_add]

theorem populationResidual_decomposition (x y : ℝ) :
    populationKernel x y - populationMean - populationProjection x -
      populationProjection y = populationResidual x y := by
  unfold populationKernel populationMean populationProjection populationResidual
  ring

theorem integrable_populationResidual_right (x : ℝ) :
    Integrable (populationResidual x) realLaw := by
  unfold populationResidual
  exact integrable_observationFeature.const_mul (-observationFeature x)

theorem integral_populationResidual_right (x : ℝ) :
    (∫ y, populationResidual x y ∂realLaw) = 0 := by
  unfold populationResidual
  rw [integral_const_mul, integral_observationFeature, mul_zero]

theorem integrable_populationResidual_sq :
    Integrable (fun xy : ℝ × ℝ => populationResidual xy.1 xy.2 ^ 2)
      (realLaw.prod realLaw) := by
  simpa only [populationResidual, mul_pow, neg_sq] using
    integrable_observationFeature_sq.mul_prod integrable_observationFeature_sq

theorem integral_populationResidual_sq :
    (∫ xy : ℝ × ℝ, populationResidual xy.1 xy.2 ^ 2 ∂realLaw.prod realLaw) =
      featureVariance ^ 2 := by
  simp only [populationResidual, mul_pow, neg_sq]
  rw [integral_prod_mul (fun x => observationFeature x ^ 2)
    (fun y => observationFeature y ^ 2), integral_observationFeature_sq, pow_two]

end
end Shao.OQ5.P35
