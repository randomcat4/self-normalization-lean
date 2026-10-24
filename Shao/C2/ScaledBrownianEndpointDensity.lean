import Shao.C2.ScaledBrownianIdentity

noncomputable section
namespace Shao.C2.ScaledBrownianEndpointDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeCompletionGlobalContinuity Shao.C2.ScaledBrownianIdentity

theorem gaussianPDFReal_standard_affine_scale (y T z : ℝ) (hT : 0 < T) :
    gaussianPDFReal 0 1 ((z - y) / Real.sqrt T) / Real.sqrt T =
      gaussianPDFReal y ⟨T, hT.le⟩ z := by
  have he : -((z - y) / Real.sqrt T) ^ 2 / 2 = -(z - y) ^ 2 / (2 * T) := by
    rw [div_pow, Real.sq_sqrt hT.le]
    ring
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  change (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((z - y) / Real.sqrt T) ^ 2 / 2) / Real.sqrt T =
    (Real.sqrt (2 * Real.pi * T))⁻¹ * Real.exp (-(z - y) ^ 2 / (2 * T))
  rw [he, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi), mul_inv_rev]
  ring

private theorem bounded_continuous_gaussian_density_integrable (f : ℝ → ℝ)
    (hf : Continuous f) (hb : ∀ w : ℝ, 0 ≤ f w ∧ f w ≤ 1) :
    Integrable (fun w : ℝ => gaussianPDFReal 0 1 w * f w) := by
  have hc : Continuous (fun w : ℝ => gaussianPDFReal 0 1 w * f w) := by
    apply Continuous.mul _ hf
    unfold gaussianPDFReal
    fun_prop
  apply (integrable_gaussianPDFReal 0 1).mono' hc.aestronglyMeasurable
  filter_upwards [] with w
  have hp := gaussianPDFReal_nonneg 0 1 w
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (hb w).1)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb w).2 hp

private theorem bounded_continuous_gaussian_integral_hasDerivAt (f : ℝ → ℝ)
    (hf : Continuous f) (hb : ∀ w : ℝ, 0 ≤ f w ∧ f w ≤ 1) (z : ℝ) :
    HasDerivAt (fun v : ℝ => ∫ w : ℝ in Iic v, f w ∂(gaussianReal 0 1))
      (gaussianPDFReal 0 1 z * f z) z := by
  let φ : ℝ → ℝ := gaussianPDFReal 0 1
  have hi : Integrable (fun w => φ w * f w) := bounded_continuous_gaussian_density_integrable f hf hb
  have hc : Continuous (fun w => φ w * f w) := by
    apply Continuous.mul _ hf
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

theorem bridge_scaled_integral_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) (hT : 0 < T) :
    HasDerivAt (fun v : ℝ => ∫ w : ℝ,
      (if y + Real.sqrt T * w ≤ v then
        intervalCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w) else 0)
        ∂(gaussianReal 0 1))
      (gaussianPDFReal y ⟨T, hT.le⟩ z * intervalCompletion (bridgeLaw B P) a y T z) z := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  let f : ℝ → ℝ := fun w => intervalCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w)
  let u : ℝ → ℝ := fun v => (v - y) / Real.sqrt T
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hf : Continuous f :=
    (bridge_interval_continuous_endpoint B P hB a y T hT).comp (by fun_prop)
  have hb (w : ℝ) : 0 ≤ f w ∧ f w ≤ 1 :=
    (completion_bounds (bridgeLaw B P) a y T (y + Real.sqrt T * w)).2.2.2.2
  have hu0 : HasDerivAt (fun v : ℝ => v - y) 1 z := (hasDerivAt_id z).sub_const y
  have hu : HasDerivAt u (1 / Real.sqrt T) z := hu0.div_const (Real.sqrt T)
  have hd := (bounded_continuous_gaussian_integral_hasDerivAt f hf hb (u z)).comp z hu
  have huz : y + Real.sqrt T * u z = z := by
    dsimp only [u]
    field_simp [ne_of_gt hs]
    ring
  have hφ : gaussianPDFReal 0 1 (u z) / Real.sqrt T = gaussianPDFReal y ⟨T, hT.le⟩ z :=
    gaussianPDFReal_standard_affine_scale y T z hT
  have hcoef : (gaussianPDFReal 0 1 (u z) * f (u z)) * (1 / Real.sqrt T) =
      gaussianPDFReal y ⟨T, hT.le⟩ z * intervalCompletion (bridgeLaw B P) a y T z := by
    dsimp only [f]
    rw [huz]
    calc
      _ = (gaussianPDFReal 0 1 (u z) / Real.sqrt T) *
          intervalCompletion (bridgeLaw B P) a y T z := by ring
      _ = _ := by rw [hφ]
  have he (v : ℝ) : (∫ w : ℝ, (if y + Real.sqrt T * w ≤ v then f w else 0) ∂(gaussianReal 0 1)) =
      ∫ w : ℝ in Iic (u v), f w ∂(gaussianReal 0 1) := by
    rw [← integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by
      have hwiff : y + Real.sqrt T * w ≤ v ↔ w ≤ u v := by
        dsimp only [u]
        rw [le_div_iff₀ hs]
        constructor <;> intro h <;> nlinarith only [h]
      simp only [Set.indicator, mem_Iic, ← hwiff]
  have hfun : (fun v : ℝ => ∫ w : ℝ,
      (if y + Real.sqrt T * w ≤ v then intervalCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w) else 0)
      ∂(gaussianReal 0 1)) = (fun v : ℝ => ∫ w : ℝ in Iic (u v), f w ∂(gaussianReal 0 1)) := by
    funext v
    exact he v
  rw [hfun, ← hcoef]
  exact hd

theorem brownian_scaled_interval_joint_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) (hT : 0 < T) :
    HasDerivAt (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt T * B 1 ω ≤ v})
      (gaussianPDFReal y ⟨T, hT.le⟩ z * intervalCompletion (bridgeLaw B P) a y T z) z := by
  have he : (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt T * B 1 ω ≤ v}) =
      (fun v : ℝ => ∫ w : ℝ,
        (if y + Real.sqrt T * w ≤ v then intervalCompletion (bridgeLaw B P) a y T (y + Real.sqrt T * w) else 0)
        ∂(gaussianReal 0 1)) := by
    funext v
    exact brownian_scaled_initial_joint B P hB a y T v
  rw [he]
  exact bridge_scaled_integral_hasDerivAt B P hB a y T z hT

theorem brownian_scaled_interval_density_ratio {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) (hT : 0 < T) :
    deriv (fun v : ℝ => P.real {ω |
      (∀ t : BridgeTime, |y + Real.sqrt T * B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧
        y + Real.sqrt T * B 1 ω ≤ v}) z /
      gaussianPDFReal y ⟨T, hT.le⟩ z = intervalCompletion (bridgeLaw B P) a y T z := by
  rw [(brownian_scaled_interval_joint_hasDerivAt B P hB a y T z hT).deriv]
  have hv : (⟨T, hT.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have hz : T = 0 := congrArg (fun v : ℝ≥0 => (v : ℝ)) h
    linarith only [hz, hT]
  have hp : gaussianPDFReal y ⟨T, hT.le⟩ z ≠ 0 :=
    (gaussianPDFReal_pos y ⟨T, hT.le⟩ z hv).ne'
  field_simp [hp]

end Shao.C2.ScaledBrownianEndpointDensity
