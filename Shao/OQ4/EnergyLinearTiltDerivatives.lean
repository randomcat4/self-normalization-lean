import Shao.OQ4.EnergyLinearTiltLaw
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual parameter derivatives and centered-square identity for the same linear energy tilt. -/

namespace Shao.OQ4

open MeasureTheory Filter
open scoped Topology

/-- A local bound at closed-support points; it is used only on the actual μ-full support set. -/
theorem energyLinear_local_power_bound (h t u x : ℝ) (k : ℕ) (hh : 0 ≤ h)
    (hx : |x| ≤ 2 * h) (hu : |u - t| ≤ 1) :
    ‖x ^ k * Real.exp (u * x)‖ ≤ (2 * h) ^ k * Real.exp (2 * h * (|t| + 1)) := by
  have hu' : |u| ≤ |t| + 1 := by
    calc
      _ = |(u - t) + t| := congrArg abs (by ring)
      _ ≤ |u - t| + |t| := abs_add_le _ _
      _ ≤ _ := by linarith
  have harg : u * x ≤ 2 * h * (|t| + 1) :=
    (energyLinear_exponent_bounds h u x hx).2.trans
      (mul_le_mul_of_nonneg_left hu' (by positivity))
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx k
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hp (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _) (by positivity)

section Admissible

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (T h s : ℝ)
  (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
  (hSq : Integrable (fun x : ℝ => x ^ 2) ν)
  (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)

include hT hh hs hSq hsecond

theorem energyLinearNormalizer_hasDerivAt (_hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (t : ℝ) :
    HasDerivAt (energyLinearNormalizer ν h s) (energyLinearFirstNumerator ν h s t) t := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  have hN : Set.Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hB : ∀ᵐ x ∂energyTiltedLaw ν h s, ∀ u ∈ Set.Ioo (t - 1) (t + 1),
      ‖x * Real.exp (u * x)‖ ≤ (2 * h) * Real.exp (2 * h * (|t| + 1)) := by
    filter_upwards [energyTiltedLaw_ae_support ν h s] with x hx
    intro u hu
    simpa only [pow_one] using energyLinear_local_power_bound h t u x 1 (by linarith) hx
      (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hD : ∀ᵐ x ∂energyTiltedLaw ν h s, ∀ u ∈ Set.Ioo (t - 1) (t + 1),
      HasDerivAt (fun v : ℝ => Real.exp (v * x)) (x * Real.exp (u * x)) u := by
    exact Eventually.of_forall fun x u _ => by
      simpa only [id_eq, one_mul, mul_one, mul_comm] using ((hasDerivAt_id u).mul_const x).exp
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := energyTiltedLaw ν h s) (F := fun u x : ℝ => Real.exp (u * x))
    (F' := fun u x : ℝ => x * Real.exp (u * x))
    (bound := fun _x : ℝ => (2 * h) * Real.exp (2 * h * (|t| + 1))) hN
    (Eventually.of_forall fun u => (show Measurable (fun x : ℝ => Real.exp (u * x)) by fun_prop).aestronglyMeasurable)
    (energyLinear_integrability ν T h s hT hh hs hSq hsecond t).1
    (show AEStronglyMeasurable (fun x : ℝ => x * Real.exp (t * x)) (energyTiltedLaw ν h s) from
      (by fun_prop : Measurable (fun x : ℝ => x * Real.exp (t * x))).aestronglyMeasurable)
    hB (integrable_const _) hD
  exact hd.2

theorem energyLinearFirstNumerator_hasDerivAt (_hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (t : ℝ) :
    HasDerivAt (energyLinearFirstNumerator ν h s) (energyLinearSecondNumerator ν h s t) t := by
  have : IsProbabilityMeasure (energyTiltedLaw ν h s) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  have hN : Set.Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hB : ∀ᵐ x ∂energyTiltedLaw ν h s, ∀ u ∈ Set.Ioo (t - 1) (t + 1),
      ‖x ^ 2 * Real.exp (u * x)‖ ≤ (2 * h) ^ 2 * Real.exp (2 * h * (|t| + 1)) := by
    filter_upwards [energyTiltedLaw_ae_support ν h s] with x hx
    intro u hu
    exact energyLinear_local_power_bound h t u x 2 (by linarith) hx
      (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  have hD : ∀ᵐ x ∂energyTiltedLaw ν h s, ∀ u ∈ Set.Ioo (t - 1) (t + 1),
      HasDerivAt (fun v : ℝ => x * Real.exp (v * x)) (x ^ 2 * Real.exp (u * x)) u := by
    exact Eventually.of_forall fun x u _ => by
      have he : HasDerivAt (fun v : ℝ => Real.exp (v * x)) (x * Real.exp (u * x)) u := by
        simpa only [id_eq, one_mul, mul_one, mul_comm] using ((hasDerivAt_id u).mul_const x).exp
      simpa only [pow_two, mul_assoc] using he.const_mul x
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := energyTiltedLaw ν h s) (F := fun u x : ℝ => x * Real.exp (u * x))
    (F' := fun u x : ℝ => x ^ 2 * Real.exp (u * x))
    (bound := fun _x : ℝ => (2 * h) ^ 2 * Real.exp (2 * h * (|t| + 1))) hN
    (Eventually.of_forall fun u => (show Measurable (fun x : ℝ => x * Real.exp (u * x)) by fun_prop).aestronglyMeasurable)
    (energyLinear_integrability ν T h s hT hh hs hSq hsecond t).2.1
    (show AEStronglyMeasurable (fun x : ℝ => x ^ 2 * Real.exp (t * x)) (energyTiltedLaw ν h s) from
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2 * Real.exp (t * x))).aestronglyMeasurable)
    hB (integrable_const _) hD
  exact hd.2

theorem energyLinear_logNormalizer_hasDerivAt (_hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (t : ℝ) :
    HasDerivAt (fun u => Real.log (energyLinearNormalizer ν h s u)) (energyLinearMean ν h s t) t := by
  exact (energyLinearNormalizer_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t).log
    (ne_of_gt (energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t))

theorem energyLinearMean_hasDerivAt (_hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (t : ℝ) :
    HasDerivAt (energyLinearMean ν h s)
      (energyLinearSecondNumerator ν h s t / energyLinearNormalizer ν h s t - energyLinearMean ν h s t ^ 2) t := by
  have hL := energyLinearNormalizer_pos ν T h s hT hh hs hSq hsecond t
  have hd := (energyLinearFirstNumerator_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t).div
    (energyLinearNormalizer_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t) (ne_of_gt hL)
  have hd' : HasDerivAt (energyLinearMean ν h s)
      ((energyLinearSecondNumerator ν h s t * energyLinearNormalizer ν h s t -
        energyLinearFirstNumerator ν h s t * energyLinearFirstNumerator ν h s t) /
        energyLinearNormalizer ν h s t ^ 2) t := by
    convert hd using 1
    funext u
    simp only [energyLinearMean, Pi.div_apply]
  convert hd' using 1
  unfold energyLinearMean
  field_simp [ne_of_gt hL]

/-- The variance identity is a genuine centered-square integral under the same actual law. -/
theorem energyLinear_centeredSquare_integral (t : ℝ) :
    Integrable (fun x : ℝ => (x - energyLinearMean ν h s t) ^ 2) (energyLinearTiltLaw ν h s t) ∧
    (∫ x : ℝ, (x - energyLinearMean ν h s t) ^ 2 ∂energyLinearTiltLaw ν h s t) =
      energyLinearSecondNumerator ν h s t / energyLinearNormalizer ν h s t - energyLinearMean ν h s t ^ 2 := by
  have : IsProbabilityMeasure (energyLinearTiltLaw ν h s t) :=
    energyLinearTiltLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond t
  obtain ⟨hi, hq, _hc, _hfirst, hmean, hsecond', _hthird⟩ :=
    energyLinearTiltLaw_moments ν T h s hT hh hs hSq hsecond t
  let m : ℝ := energyLinearMean ν h s t
  have hp : Integrable (fun x : ℝ => x ^ 2 - (2 * m) * x + m ^ 2) (energyLinearTiltLaw ν h s t) :=
    (hq.sub (hi.const_mul (2 * m))).add (integrable_const (m ^ 2))
  have hI : Integrable (fun x : ℝ => (x - m) ^ 2) (energyLinearTiltLaw ν h s t) := by
    convert hp using 1
    ext x
    ring
  refine ⟨hI, ?_⟩
  have hAdd : (∫ x : ℝ, x ^ 2 - (2 * m) * x + m ^ 2 ∂energyLinearTiltLaw ν h s t) =
      (∫ x : ℝ, x ^ 2 - (2 * m) * x ∂energyLinearTiltLaw ν h s t) +
      (∫ _x : ℝ, m ^ 2 ∂energyLinearTiltLaw ν h s t) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add (μ := energyLinearTiltLaw ν h s t) (hq.sub (hi.const_mul (2 * m))) (integrable_const (m ^ 2))
  have hSub : (∫ x : ℝ, x ^ 2 - (2 * m) * x ∂energyLinearTiltLaw ν h s t) =
      (∫ x : ℝ, x ^ 2 ∂energyLinearTiltLaw ν h s t) -
      (∫ x : ℝ, (2 * m) * x ∂energyLinearTiltLaw ν h s t) := by
    simpa only [Pi.sub_apply] using integral_sub (μ := energyLinearTiltLaw ν h s t) hq (hi.const_mul (2 * m))
  calc
    _ = ∫ x : ℝ, x ^ 2 - (2 * m) * x + m ^ 2 ∂energyLinearTiltLaw ν h s t := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [m]; ring
    _ = _ := by
      rw [hAdd, hSub, integral_const_mul, hmean, hsecond', integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      dsimp only [m]
      ring

theorem energyLinearMean_hasDerivAt_centeredSquare (_hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) (t : ℝ) :
    HasDerivAt (energyLinearMean ν h s)
      (∫ x : ℝ, (x - energyLinearMean ν h s t) ^ 2 ∂energyLinearTiltLaw ν h s t) t := by
  rw [(energyLinear_centeredSquare_integral ν T h s hT hh hs hSq hsecond t).2]
  exact energyLinearMean_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t

theorem energyLinearMean_derivative_nonneg (t : ℝ) :
    0 ≤ energyLinearSecondNumerator ν h s t / energyLinearNormalizer ν h s t - energyLinearMean ν h s t ^ 2 := by
  rw [← (energyLinear_centeredSquare_integral ν T h s hT hh hs hSq hsecond t).2]
  exact integral_nonneg fun _ => sq_nonneg _

theorem energyLinear_family_continuous (_hCube : Integrable (fun x : ℝ => |x| ^ 3) ν) :
    Continuous (energyLinearNormalizer ν h s) ∧ Continuous (energyLinearFirstNumerator ν h s) ∧
    Continuous (energyLinearMean ν h s) ∧ Continuous (fun t => Real.log (energyLinearNormalizer ν h s t)) := by
  exact ⟨continuous_iff_continuousAt.mpr fun t =>
      (energyLinearNormalizer_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t).continuousAt,
    continuous_iff_continuousAt.mpr fun t =>
      (energyLinearFirstNumerator_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t).continuousAt,
    continuous_iff_continuousAt.mpr fun t =>
      (energyLinearMean_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t).continuousAt,
    continuous_iff_continuousAt.mpr fun t =>
      (energyLinear_logNormalizer_hasDerivAt ν T h s hT hh hs hSq hsecond _hCube t).continuousAt⟩

end Admissible

end Shao.OQ4
