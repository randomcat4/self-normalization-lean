import Shao.C2.BridgeCompletionGlobalContinuity
import Shao.C2.InitialBrownianIdentity
import Shao.C2.GaussianCDFBridgeDerivative

noncomputable section
namespace Shao.C2.BridgeIntervalEndpointDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeCompletionGlobalContinuity

theorem bridge_interval_density_integrable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => gaussianPDFReal 0 1 w * intervalCompletion (bridgeLaw B P) a y T w) := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  have hc : Continuous (fun w : ℝ => gaussianPDFReal 0 1 w * intervalCompletion (bridgeLaw B P) a y T w) := by
    apply Continuous.mul _ (bridge_interval_continuous_endpoint B P hB a y T hT)
    unfold gaussianPDFReal
    fun_prop
  apply (integrable_gaussianPDFReal 0 1).mono' hc.aestronglyMeasurable
  filter_upwards [] with w
  have hb := (completion_bounds (bridgeLaw B P) a y T w).2.2.2.2
  have hp := gaussianPDFReal_nonneg 0 1 w
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hb.1)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.2 hp

theorem bridge_interval_integral_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) (hT : 0 < T) :
    HasDerivAt (fun v : ℝ =>
      ∫ w : ℝ in Iic v, intervalCompletion (bridgeLaw B P) a y T w ∂(gaussianReal 0 1))
      (gaussianPDFReal 0 1 z * intervalCompletion (bridgeLaw B P) a y T z) z := by
  let f : ℝ → ℝ := fun w => intervalCompletion (bridgeLaw B P) a y T w
  let φ : ℝ → ℝ := gaussianPDFReal 0 1
  have hi : Integrable (fun w => φ w * f w) := bridge_interval_density_integrable B P hB a y T hT
  have hc : Continuous (fun w => φ w * f w) := by
    apply Continuous.mul _ (bridge_interval_continuous_endpoint B P hB a y T hT)
    dsimp only [φ]
    unfold gaussianPDFReal
    fun_prop
  have he (v : ℝ) : (∫ w : ℝ in Iic v, f w ∂(gaussianReal 0 1)) =
      ∫ w : ℝ in Iic v, φ w * f w := by
    calc
      _ = ∫ w : ℝ, (Iic v).indicator f w ∂(gaussianReal 0 1) :=
        (integral_indicator measurableSet_Iic).symm
      _ = ∫ w : ℝ, φ w * (Iic v).indicator f w := by
        simpa only [smul_eq_mul] using
          (integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1)
            (f := (Iic v).indicator f) (by norm_num))
      _ = ∫ w : ℝ, (Iic v).indicator (fun x => φ x * f x) w := by
        apply integral_congr_ae
        exact Eventually.of_forall fun w => by
          by_cases hw : w ∈ Iic v <;> simp [hw]
      _ = _ := integral_indicator measurableSet_Iic
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hi.intervalIntegrable (a := 0) (b := z))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hEq : (fun v : ℝ => ∫ w : ℝ in Iic v, f w ∂(gaussianReal 0 1)) =
      (fun v : ℝ => (∫ w : ℝ in Iic 0, φ w * f w) + ∫ w : ℝ in (0 : ℝ)..v, φ w * f w) := by
    funext v
    rw [he v]
    have hdiff := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := v)
      hi.integrableOn hi.integrableOn
    linarith
  change HasDerivAt (fun v : ℝ => ∫ w : ℝ in Iic v, f w ∂(gaussianReal 0 1)) (φ z * f z) z
  rw [hEq]
  exact hd.const_add _

theorem brownian_interval_joint_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z : ℝ) :
    HasDerivAt (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v})
      (gaussianPDFReal 0 1 z * intervalCompletion (bridgeLaw B P) a 0 1 z) z := by
  have he : (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v}) =
      (fun v : ℝ => ∫ w : ℝ in Iic v, intervalCompletion (bridgeLaw B P) a 0 1 w ∂(gaussianReal 0 1)) := by
    funext v
    rw [brownian_initial_joint B P hB a v]
    simpa only [Set.indicator, mem_Iic] using
      (integral_indicator (μ := gaussianReal 0 1)
        (f := fun w : ℝ => intervalCompletion (bridgeLaw B P) a 0 1 w) measurableSet_Iic)
  rw [he]
  exact bridge_interval_integral_hasDerivAt B P hB a 0 1 z (by norm_num)

theorem brownian_interval_density_ratio {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z : ℝ) :
    deriv (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v}) z /
        gaussianPDFReal 0 1 z = intervalCompletion (bridgeLaw B P) a 0 1 z := by
  rw [(brownian_interval_joint_hasDerivAt B P hB a z).deriv]
  have hp : gaussianPDFReal 0 1 z ≠ 0 := (gaussianPDFReal_pos 0 1 z (by norm_num)).ne'
  field_simp [hp]

end Shao.C2.BridgeIntervalEndpointDensity
