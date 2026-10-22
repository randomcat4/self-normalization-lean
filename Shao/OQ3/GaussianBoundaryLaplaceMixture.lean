import Shao.OQ3.SourceGaussianBoundaryProfile
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Topology Interval

noncomputable section

private def mixtureKernel (b t : ℝ) : ℝ :=
  Real.exp (-(b ^ 2 / 2) * (1 + t ^ 2)) / (1 + t ^ 2)

private def mixtureValue (b : ℝ) : ℝ :=
  (2 / Real.pi) * ∫ t : ℝ in Set.Ioi 0, mixtureKernel b t

private def gaussianPrimitive (b : ℝ) : ℝ :=
  (2 / Real.sqrt (2 * Real.pi)) *
    ((∫ z : ℝ in Set.Ioi 0, Real.exp (-(z ^ 2) / 2)) -
      ∫ z : ℝ in (0 : ℝ)..b, Real.exp (-(z ^ 2) / 2))

private theorem mixtureKernel_nonneg (b t : ℝ) : 0 ≤ mixtureKernel b t := by
  unfold mixtureKernel
  positivity

private theorem mixtureKernel_le (b t : ℝ) :
    mixtureKernel b t ≤ (1 + t ^ 2)⁻¹ := by
  have hd : 0 < 1 + t ^ 2 := by positivity
  have he : -(b ^ 2 / 2) * (1 + t ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg b]) hd.le
  simpa only [mixtureKernel, one_div] using
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr he) hd.le

private theorem mixtureKernel_continuous (b : ℝ) : Continuous (mixtureKernel b) := by
  unfold mixtureKernel
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    positivity

private theorem mixtureKernel_integrable (b : ℝ) :
    IntegrableOn (mixtureKernel b) (Set.Ioi 0) := by
  apply integrable_inv_one_add_sq.integrableOn.mono'
    (mixtureKernel_continuous b).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mixtureKernel_nonneg b t)]
    exact mixtureKernel_le b t)

private theorem mixtureValue_continuous : Continuous mixtureValue := by
  have h := continuous_of_dominated
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))
    (F := mixtureKernel) (bound := fun t : ℝ => (1 + t ^ 2)⁻¹)
    (fun b => (mixtureKernel_continuous b).aestronglyMeasurable)
    (fun b => ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mixtureKernel_nonneg b t)]
      exact mixtureKernel_le b t))
    integrable_inv_one_add_sq.integrableOn
    (ae_of_all _ (fun t => by unfold mixtureKernel; fun_prop))
  exact continuous_const.mul h

private theorem mixtureValue_zero : mixtureValue 0 = 1 := by
  have heq : mixtureKernel 0 = fun t : ℝ => (1 + t ^ 2)⁻¹ := by
    funext t
    unfold mixtureKernel
    norm_num
  unfold mixtureValue
  rw [heq, integral_Ioi_inv_one_add_sq]
  norm_num

private theorem gaussian_half_integrable :
    Integrable (fun z : ℝ => Real.exp (-(z ^ 2) / 2)) := by
  have heq : (fun z : ℝ => Real.exp (-(z ^ 2) / 2)) =
      (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) := by
    funext z
    congr 1
    ring
  rw [heq]
  exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)

private theorem gaussianPrimitive_continuous : Continuous gaussianPrimitive := by
  have hc : Continuous (fun z : ℝ => Real.exp (-(z ^ 2) / 2)) := by fun_prop
  unfold gaussianPrimitive
  exact continuous_const.mul (continuous_const.sub
    (intervalIntegral.differentiable_integral_of_continuous (a := (0 : ℝ)) hc).continuous)

private theorem gaussianPrimitive_zero : gaussianPrimitive 0 = 1 := by
  have heq : (fun z : ℝ => Real.exp (-(z ^ 2) / 2)) =
      (fun z : ℝ => Real.exp (-(1 / 2 : ℝ) * z ^ 2)) := by
    funext z
    congr 1
    ring
  have harg : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
  have hr : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  unfold gaussianPrimitive
  rw [intervalIntegral.integral_same, sub_zero, heq, integral_gaussian_Ioi, harg]
  field_simp

private theorem gaussianPrimitive_hasDerivAt (b : ℝ) :
    HasDerivAt gaussianPrimitive
      (-(2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(b ^ 2) / 2)) b := by
  have hc : Continuous (fun z : ℝ => Real.exp (-(z ^ 2) / 2)) := by fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 b)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := ((hasDerivAt_const b
    (∫ z : ℝ in Set.Ioi 0, Real.exp (-(z ^ 2) / 2))).sub hd).const_mul
      (2 / Real.sqrt (2 * Real.pi))
  unfold gaussianPrimitive
  simpa only [Pi.sub_apply, zero_sub, mul_neg, neg_mul] using h

private theorem mixtureKernel_hasDerivAt (u t : ℝ) :
    HasDerivAt (fun b : ℝ => mixtureKernel b t)
      (-u * Real.exp (-(u ^ 2 / 2) * (1 + t ^ 2))) u := by
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  have h := (((((hasDerivAt_id u).pow 2).div_const 2).neg.mul_const
    (1 + t ^ 2)).exp).div_const (1 + t ^ 2)
  convert h using 1 <;> dsimp [mixtureKernel] <;> field_simp <;> ring

private theorem mixtureValue_hasDerivAt (b : ℝ) (hb : 0 < b) :
    HasDerivAt mixtureValue
      (-(2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(b ^ 2) / 2)) b := by
  let bound : ℝ → ℝ := fun t => 2 * b * Real.exp (-(b ^ 2 / 8) * t ^ 2)
  have hbi : IntegrableOn bound (Set.Ioi 0) := by
    exact ((integrable_exp_neg_mul_sq
      (by positivity : (0 : ℝ) < b ^ 2 / 8)).const_mul (2 * b)).integrableOn
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioi 0),
      ∀ u ∈ Set.Ioo (b / 2) (2 * b),
        ‖-u * Real.exp (-(u ^ 2 / 2) * (1 + t ^ 2))‖ ≤ bound t := by
    apply ae_of_all
    intro t u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hu2 : b ^ 2 / 8 ≤ u ^ 2 / 2 := by nlinarith [hu.1]
    have he : -(u ^ 2 / 2) * (1 + t ^ 2) ≤ -(b ^ 2 / 8) * t ^ 2 := by
      calc
        _ ≤ -(u ^ 2 / 2) * t ^ 2 := by nlinarith [sq_nonneg u]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg t)
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hu0,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hu.2.le (Real.exp_le_exp.mpr he)
      (Real.exp_pos _).le (by linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))
    (F := mixtureKernel)
    (F' := fun u t : ℝ => -u * Real.exp (-(u ^ 2 / 2) * (1 + t ^ 2)))
    (bound := bound) (s := Set.Ioo (b / 2) (2 * b))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall (fun u => (mixtureKernel_continuous u).aestronglyMeasurable))
    (mixtureKernel_integrable b)
    (by exact (show Continuous (fun t : ℝ =>
      -b * Real.exp (-(b ^ 2 / 2) * (1 + t ^ 2))) by fun_prop).aestronglyMeasurable)
    hbound hbi (ae_of_all _ (fun t u _ => mixtureKernel_hasDerivAt u t))
  have heq : (fun t : ℝ => -b * Real.exp (-(b ^ 2 / 2) * (1 + t ^ 2))) =
      (fun t : ℝ => (-b * Real.exp (-(b ^ 2 / 2))) *
        Real.exp (-(b ^ 2 / 2) * t ^ 2)) := by
    funext t
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  have hi : (∫ t : ℝ in Set.Ioi 0,
      -b * Real.exp (-(b ^ 2 / 2) * (1 + t ^ 2))) =
      (-b * Real.exp (-(b ^ 2 / 2))) * (Real.sqrt (Real.pi / (b ^ 2 / 2)) / 2) := by
    rw [heq, integral_const_mul, integral_gaussian_Ioi]
  have hsqrt : Real.sqrt (Real.pi / (b ^ 2 / 2)) =
      Real.sqrt (2 * Real.pi) / b := by
    have harg : Real.pi / (b ^ 2 / 2) = (2 * Real.pi) / b ^ 2 := by
      field_simp
    rw [harg, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have hr : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hc : Real.sqrt (2 * Real.pi) / Real.pi = 2 / Real.sqrt (2 * Real.pi) := by
    apply (div_eq_div_iff Real.pi_ne_zero hr).mpr
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  have hcoef : (2 / Real.pi) * ((-b * Real.exp (-(b ^ 2 / 2))) *
      ((Real.sqrt (2 * Real.pi) / b) / 2)) =
      -(2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(b ^ 2) / 2) := by
    calc
      _ = -(Real.sqrt (2 * Real.pi) / Real.pi) * Real.exp (-(b ^ 2) / 2) := by
        field_simp
        <;> ring
      _ = _ := by rw [hc]
  unfold mixtureValue
  convert h.2.const_mul (2 / Real.pi) using 1
  rw [hi, hsqrt, hcoef]

private theorem mixtureValue_eq_primitive (b : ℝ) (hb : 0 ≤ b) :
    mixtureValue b = gaussianPrimitive b := by
  let D : ℝ → ℝ := fun u => mixtureValue u - gaussianPrimitive u
  have hDc : Continuous D := mixtureValue_continuous.sub gaussianPrimitive_continuous
  have hD0 : D 0 = 0 := by dsimp [D]; rw [mixtureValue_zero, gaussianPrimitive_zero]; ring
  have hDd (u : ℝ) (hu : 0 < u) : HasDerivAt D 0 u := by
    change HasDerivAt (fun y : ℝ => mixtureValue y - gaussianPrimitive y) 0 u
    convert! (mixtureValue_hasDerivAt u hu).sub (gaussianPrimitive_hasDerivAt u) using 1 <;>
      simp
  have hconst {u v : ℝ} (hu : 0 < u) (hv : 0 < v) : D u = D v := by
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun y hy => (hDd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hDd y hy).deriv) hu hv
  by_cases hb0 : b = 0
  · subst b
    rw [mixtureValue_zero, gaussianPrimitive_zero]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hlim0 : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto D (𝓝 (0 : ℝ)) (𝓝 (D 0)) := hDc.continuousAt.tendsto
    simpa only [hD0] using
      (h.mono_left nhdsWithin_le_nhds : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 (D 0)))
  have hlimb : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 (D b)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => D b)
      (𝓝[>] (0 : ℝ)) (𝓝 (D b))).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hconst hbp hu
  exact sub_eq_zero.mp (tendsto_nhds_unique hlimb hlim0)

private theorem gaussianPrimitive_eq_tail (b : ℝ) (hb : 0 ≤ b) :
    gaussianPrimitive b = (2 / Real.sqrt (2 * Real.pi)) *
      ∫ z : ℝ in Set.Ioi b, Real.exp (-(z ^ 2) / 2) := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi gaussian_half_integrable.integrableOn hb
  have heq : (∫ z : ℝ in Set.Ioi 0, Real.exp (-(z ^ 2) / 2)) -
      (∫ z : ℝ in (0 : ℝ)..b, Real.exp (-(z ^ 2) / 2)) =
      ∫ z : ℝ in Set.Ioi b, Real.exp (-(z ^ 2) / 2) := by linarith
  unfold gaussianPrimitive
  rw [heq]

theorem gaussianBoundaryWeight_neg_laplace_mixture
    (kappa x : ℝ) (hk : 0 < kappa) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2))
      (Set.Ioi 0) ∧
    gaussianBoundaryWeight kappa (-x) = (2 / Real.pi) *
      (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2)) := by
  let b : ℝ := kappa * Real.sqrt x
  have hb : 0 ≤ b := mul_nonneg hk.le (Real.sqrt_nonneg x)
  have hb2 : b ^ 2 = kappa ^ 2 * x := by dsimp [b]; rw [mul_pow, Real.sq_sqrt hx]
  have hker : (fun t : ℝ =>
      Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2)) =
      mixtureKernel b := by
    funext t
    unfold mixtureKernel
    rw [hb2]
    congr 1
    congr 1
    ring
  refine ⟨by rw [hker]; exact mixtureKernel_integrable b, ?_⟩
  have hweight : gaussianBoundaryWeight kappa (-x) = gaussianPrimitive b := by
    rw [gaussianBoundaryWeight_eq_piecewise kappa hk]
    by_cases hh : 0 ≤ -x
    · have hx0 : x = 0 := by linarith
      subst x
      simp only [neg_zero, le_refl, ite_true, b, Real.sqrt_zero, mul_zero,
        gaussianPrimitive_zero]
    · rw [if_neg hh, neg_neg]
      exact (gaussianPrimitive_eq_tail b hb).symm
  calc
    gaussianBoundaryWeight kappa (-x) = gaussianPrimitive b := hweight
    _ = mixtureValue b := (mixtureValue_eq_primitive b hb).symm
    _ = _ := by unfold mixtureValue; rw [← hker]

end

end Shao.OQ3
