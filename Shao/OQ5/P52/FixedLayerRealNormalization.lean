import Shao.OQ5.P52.FixedLayerRealMoments
import Shao.OQ5.P52.FixedLayerRealCanonical

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal

namespace Shao.OQ5.P52

noncomputable section

attribute [local instance] fixedRealObservationLaw_isProbabilityMeasure

def fixedNormalizedRealKernel (z : ℝ × ℝ) : ℝ :=
  Real.sqrt 3 * fixedRealKernel z

def fixedNormalizedRealFirstProjection (x : ℝ) : ℝ :=
  ∫ y : ℝ, fixedNormalizedRealKernel (x, y) ∂fixedRealObservationLaw

def fixedNormalizedRealCanonicalResidual (z : ℝ × ℝ) : ℝ :=
  fixedNormalizedRealKernel z - fixedNormalizedRealFirstProjection z.1 -
    fixedNormalizedRealFirstProjection z.2

private theorem normalization_scale_pos : 0 < Real.sqrt 3 :=
  Real.sqrt_pos.mpr (by norm_num)

private theorem normalization_scale_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

theorem measurable_fixedNormalizedRealKernel :
    Measurable fixedNormalizedRealKernel := by
  exact measurable_const.mul measurable_fixedRealKernel

theorem fixedNormalizedRealKernel_symmetric (x y : ℝ) :
    fixedNormalizedRealKernel (x, y) = fixedNormalizedRealKernel (y, x) := by
  change Real.sqrt 3 * fixedRealKernel (x, y) = Real.sqrt 3 * fixedRealKernel (y, x)
  rw [fixedRealKernel_symmetric]

theorem fixedNormalizedRealKernel_memLp (ν : ℝ) (hν : 1 ≤ ν) :
    MemLp fixedNormalizedRealKernel (ENNReal.ofReal ν)
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  exact (fixedRealKernel_memLp ν hν).const_mul (Real.sqrt 3)

theorem integrable_fixedNormalizedRealKernel :
    Integrable fixedNormalizedRealKernel
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  exact integrable_fixedRealKernel.const_mul (Real.sqrt 3)

private theorem normalization_kernel_row_integrable :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      Integrable (fun y : ℝ => fixedNormalizedRealKernel (x, y)) fixedRealObservationLaw :=
  integrable_fixedNormalizedRealKernel.prod_right_ae

theorem integral_fixedNormalizedRealKernel_eq_zero :
    (∫ z : ℝ × ℝ, fixedNormalizedRealKernel z
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = 0 := by
  have _hI := integrable_fixedNormalizedRealKernel
  change (∫ z : ℝ × ℝ, Real.sqrt 3 * fixedRealKernel z
    ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = 0
  rw [integral_const_mul, integral_fixedRealKernel_eq_zero, mul_zero]

theorem fixedNormalizedRealFirstProjection_eq (x : ℝ) :
    fixedNormalizedRealFirstProjection x = Real.sqrt 3 * fixedRealFirstProjection x := by
  change (∫ y : ℝ, Real.sqrt 3 * fixedRealKernel (x, y) ∂fixedRealObservationLaw) =
    Real.sqrt 3 * ∫ y : ℝ, fixedRealKernel (x, y) ∂fixedRealObservationLaw
  exact integral_const_mul _ _

private theorem normalization_projection_function :
    fixedNormalizedRealFirstProjection = (fun x : ℝ => Real.sqrt 3 * fixedRealFirstProjection x) :=
  funext fixedNormalizedRealFirstProjection_eq

theorem measurable_fixedNormalizedRealFirstProjection :
    Measurable fixedNormalizedRealFirstProjection := by
  rw [normalization_projection_function]
  exact measurable_const.mul measurable_fixedRealFirstProjection

theorem fixedNormalizedRealFirstProjection_memLp_two :
    MemLp fixedNormalizedRealFirstProjection 2 fixedRealObservationLaw := by
  rw [normalization_projection_function]
  exact fixedRealFirstProjection_memLp_two.const_mul (Real.sqrt 3)

private theorem normalization_projection_integrable :
    Integrable fixedNormalizedRealFirstProjection fixedRealObservationLaw := by
  have _hrows := normalization_kernel_row_integrable
  exact integrable_fixedNormalizedRealKernel.integral_prod_left

private theorem normalization_projection_sq_integrable :
    Integrable (fun x : ℝ => fixedNormalizedRealFirstProjection x ^ 2)
      fixedRealObservationLaw :=
  fixedNormalizedRealFirstProjection_memLp_two.integrable_sq

theorem integral_fixedNormalizedRealFirstProjection_eq_zero :
    (∫ x : ℝ, fixedNormalizedRealFirstProjection x ∂fixedRealObservationLaw) = 0 := by
  have _hI := normalization_projection_integrable
  rw [normalization_projection_function, integral_const_mul,
    integral_fixedRealFirstProjection_eq_zero, mul_zero]

theorem integral_fixedNormalizedRealFirstProjection_sq :
    (∫ x : ℝ, fixedNormalizedRealFirstProjection x ^ 2
      ∂fixedRealObservationLaw) = 1 := by
  have _hI := normalization_projection_sq_integrable
  have heq : (fun x : ℝ => fixedNormalizedRealFirstProjection x ^ 2) =
      (fun x : ℝ => (3 : ℝ) * fixedRealFirstProjection x ^ 2) := by
    funext x
    rw [fixedNormalizedRealFirstProjection_eq, mul_pow, normalization_scale_sq]
  rw [heq, integral_const_mul, integral_fixedRealFirstProjection_sq]
  norm_num

theorem fixedNormalizedRealFirstProjection_abs_le_sqrt_three_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      |fixedNormalizedRealFirstProjection x| ≤ Real.sqrt 3 := by
  filter_upwards [fixedRealFirstProjection_abs_le_one_ae] with x hx
  rw [fixedNormalizedRealFirstProjection_eq, abs_mul,
    abs_of_nonneg normalization_scale_pos.le]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hx normalization_scale_pos.le

theorem map_fixedNormalizedRealFirstProjection :
    fixedRealObservationLaw.map fixedNormalizedRealFirstProjection =
      Shao.OQ5.P50.layerNoiseLaw.map (fun t : ℝ => Real.sqrt 3 * t) := by
  rw [normalization_projection_function]
  have hs : Measurable (fun t : ℝ => Real.sqrt 3 * t) :=
    measurable_const.mul measurable_id
  calc
    _ = (fixedRealObservationLaw.map fixedRealFirstProjection).map
        (fun t : ℝ => Real.sqrt 3 * t) :=
      (Measure.map_map hs measurable_fixedRealFirstProjection).symm
    _ = _ := by rw [map_fixedRealFirstProjection]

theorem fixedNormalizedRealFirstProjection_indep_categories :
    ProbabilityTheory.IndepFun fixedNormalizedRealFirstProjection
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2) fixedRealObservationLaw := by
  rw [normalization_projection_function]
  have hs : Measurable (fun t : ℝ => Real.sqrt 3 * t) :=
    measurable_const.mul measurable_id
  change ProbabilityTheory.IndepFun
    ((fun t : ℝ => Real.sqrt 3 * t) ∘ fixedRealFirstProjection)
    ((id : (ℕ → Fin 3) → (ℕ → Fin 3)) ∘
      (fun x : ℝ => (Shao.OQ5.P50.layerDecode x).2)) fixedRealObservationLaw
  exact fixedRealFirstProjection_indep_categories.comp hs measurable_id

theorem fixedNormalizedRealCanonicalResidual_eq (z : ℝ × ℝ) :
    fixedNormalizedRealCanonicalResidual z = Real.sqrt 3 * fixedRealCanonicalResidual z := by
  dsimp only [fixedNormalizedRealCanonicalResidual, fixedNormalizedRealKernel,
    fixedRealCanonicalResidual]
  simp only [fixedNormalizedRealFirstProjection_eq]
  ring

private theorem normalization_residual_function :
    fixedNormalizedRealCanonicalResidual =
      (fun z : ℝ × ℝ => Real.sqrt 3 * fixedRealCanonicalResidual z) :=
  funext fixedNormalizedRealCanonicalResidual_eq

theorem fixedNormalizedRealCanonicalResidual_memLp_two :
    MemLp fixedNormalizedRealCanonicalResidual 2
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  rw [normalization_residual_function]
  exact fixedRealCanonicalResidual_memLp_two.const_mul (Real.sqrt 3)

private theorem normalization_residual_integrable :
    Integrable fixedNormalizedRealCanonicalResidual
      (fixedRealObservationLaw.prod fixedRealObservationLaw) :=
  MemLp.integrable (by norm_num) fixedNormalizedRealCanonicalResidual_memLp_two

theorem integrable_fixedNormalizedRealCanonicalResidual_row_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      Integrable (fun y : ℝ => fixedNormalizedRealCanonicalResidual (x, y))
        fixedRealObservationLaw := by
  exact normalization_residual_integrable.prod_right_ae

theorem integral_fixedNormalizedRealCanonicalResidual_row_eq_zero_ae :
    ∀ᵐ x : ℝ ∂fixedRealObservationLaw,
      (∫ y : ℝ, fixedNormalizedRealCanonicalResidual (x, y)
        ∂fixedRealObservationLaw) = 0 := by
  filter_upwards [integrable_fixedNormalizedRealCanonicalResidual_row_ae,
    integrable_fixedRealCanonicalResidual_row_ae,
    integral_fixedRealCanonicalResidual_row_eq_zero_ae] with x _hscaled _hraw hz
  have heq : (fun y : ℝ => fixedNormalizedRealCanonicalResidual (x, y)) =
      (fun y : ℝ => Real.sqrt 3 * fixedRealCanonicalResidual (x, y)) :=
    funext fun y => fixedNormalizedRealCanonicalResidual_eq (x, y)
  rw [heq, integral_const_mul, hz, mul_zero]

theorem fixedNormalizedRealCanonicalResidual_ae_eq_categoryResidual :
    fixedNormalizedRealCanonicalResidual =ᵐ[fixedRealObservationLaw.prod fixedRealObservationLaw]
      (fun z : ℝ × ℝ => Real.sqrt 3 * fixedCategoryResidualKernel
        ((Shao.OQ5.P50.layerDecode z.1).2,
          (Shao.OQ5.P50.layerDecode z.2).2)) := by
  filter_upwards [fixedRealCanonicalResidual_ae_eq_categoryResidual] with z hz
  rw [fixedNormalizedRealCanonicalResidual_eq, hz]

theorem integrable_fixedNormalizedRealKernel_abs_pow (m : ℕ) :
    Integrable (fun z : ℝ × ℝ => |fixedNormalizedRealKernel z| ^ m)
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  have heq : (fun z : ℝ × ℝ => |fixedNormalizedRealKernel z| ^ m) =
      (fun z : ℝ × ℝ => (Real.sqrt 3) ^ m * |fixedRealKernel z| ^ m) := by
    funext z
    simp only [fixedNormalizedRealKernel, abs_mul,
      abs_of_nonneg normalization_scale_pos.le, mul_pow]
  rw [heq]
  exact (integrable_fixedRealKernel_abs_pow m).const_mul ((Real.sqrt 3) ^ m)

private theorem normalization_abs_rpow (η : ℝ) (z : ℝ × ℝ) :
    |fixedNormalizedRealKernel z| ^ η = (Real.sqrt 3) ^ η * |fixedRealKernel z| ^ η := by
  rw [fixedNormalizedRealKernel, abs_mul, abs_of_nonneg normalization_scale_pos.le,
    Real.mul_rpow normalization_scale_pos.le (abs_nonneg _)]

private theorem normalization_exp_function (η lambda : ℝ) :
    (fun z : ℝ × ℝ => Real.exp (lambda * |fixedNormalizedRealKernel z| ^ η)) =
      (fun z : ℝ × ℝ => Real.exp ((lambda * (Real.sqrt 3) ^ η) * |fixedRealKernel z| ^ η)) := by
  funext z
  rw [normalization_abs_rpow]
  exact congrArg Real.exp (mul_assoc lambda ((Real.sqrt 3) ^ η) (|fixedRealKernel z| ^ η)).symm

theorem integrable_fixedNormalizedRealKernel_subcritical_exp (η lambda : ℝ)
    (hη0 : 0 < η) (hη : η < 1 / 5) (hlambda : 0 < lambda) :
    Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |fixedNormalizedRealKernel z| ^ η))
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  rw [normalization_exp_function η lambda]
  exact integrable_fixedRealKernel_subcritical_exp η (lambda * (Real.sqrt 3) ^ η)
    hη0 hη (mul_pos hlambda (Real.rpow_pos_of_pos normalization_scale_pos η))

theorem lintegral_fixedNormalizedRealKernel_critical_exp_eq_top
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫⁻ z : ℝ × ℝ,
      ENNReal.ofReal (Real.exp (lambda * |fixedNormalizedRealKernel z| ^ (1 / 5 : ℝ)))
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) = ⊤ := by
  have hcoef : 0 < lambda * (Real.sqrt 3) ^ (1 / 5 : ℝ) :=
    mul_pos hlambda (Real.rpow_pos_of_pos normalization_scale_pos _)
  calc
    _ = ∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (Real.exp ((lambda * (Real.sqrt 3) ^ (1 / 5 : ℝ)) *
          |fixedRealKernel z| ^ (1 / 5 : ℝ)))
        ∂fixedRealObservationLaw.prod fixedRealObservationLaw := by
      apply lintegral_congr
      intro z
      exact congrArg ENNReal.ofReal
        (congrFun (normalization_exp_function (1 / 5 : ℝ) lambda) z)
    _ = ⊤ := lintegral_fixedRealKernel_critical_exp_eq_top
      (lambda * (Real.sqrt 3) ^ (1 / 5 : ℝ)) hcoef

theorem not_integrable_fixedNormalizedRealKernel_critical_exp
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ¬ Integrable (fun z : ℝ × ℝ =>
      Real.exp (lambda * |fixedNormalizedRealKernel z| ^ (1 / 5 : ℝ)))
      (fixedRealObservationLaw.prod fixedRealObservationLaw) := by
  intro hf
  have hfin := hf.hasFiniteIntegral
  change (∫⁻ z : ℝ × ℝ,
    ‖Real.exp (lambda * |fixedNormalizedRealKernel z| ^ (1 / 5 : ℝ))‖ₑ
    ∂fixedRealObservationLaw.prod fixedRealObservationLaw) < ⊤ at hfin
  have heq : (∫⁻ z : ℝ × ℝ,
      ‖Real.exp (lambda * |fixedNormalizedRealKernel z| ^ (1 / 5 : ℝ))‖ₑ
      ∂fixedRealObservationLaw.prod fixedRealObservationLaw) =
      ∫⁻ z : ℝ × ℝ,
        ENNReal.ofReal (Real.exp (lambda * |fixedNormalizedRealKernel z| ^ (1 / 5 : ℝ)))
        ∂fixedRealObservationLaw.prod fixedRealObservationLaw :=
    lintegral_congr (fun _ => Real.enorm_of_nonneg (Real.exp_pos _).le)
  rw [heq, lintegral_fixedNormalizedRealKernel_critical_exp_eq_top lambda hlambda] at hfin
  exact (lt_irrefl _) hfin

end

end Shao.OQ5.P52
