import Shao.C2.BrownianKilledComposition
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
namespace Shao.C2.BrownianKilledDensitySemigroup
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BrownianKilledKernel Shao.C2.BrownianKilledSemigroup
open Shao.C2.BrownianBridgeLawUniversality Shao.C2.BrownianKilledEndpointDensity

private theorem killed_density_uniform_bound {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (T : ℝ≥0) :
    0 ≤ gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z ∧
      gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z ≤
        (Real.sqrt (2 * Real.pi * (T : ℝ)))⁻¹ := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  have hI := completion_bounds (bridgeLaw B P) a y (T : ℝ) z
  have hp := gaussianPDFReal_nonneg y T z
  refine ⟨mul_nonneg hp hI.2.2.2.2.1, ?_⟩
  calc
    _ ≤ gaussianPDFReal y T z * 1 := mul_le_mul_of_nonneg_left hI.2.2.2.2.2 hp
    _ = gaussianPDFReal y T z := mul_one _
    _ ≤ _ := by
      unfold gaussianPDFReal
      have he : Real.exp (-(z - y) ^ 2 / (2 * (T : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he
        (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * (T : ℝ))))

theorem actualIntervalKernel_rowCDF_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    HasDerivAt (fun v : ℝ => (actualIntervalKernel B P a T y).real (Iic v))
      (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) z := by
  have heq : (fun v : ℝ => (actualIntervalKernel B P a T y).real (Iic v)) =
      (fun v : ℝ => P.real {ω |
        (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ≤ v}) := by
    funext v
    exact actualIntervalKernel_real_eq_survival B P hB a y T hT (Iic v) measurableSet_Iic
  rw [heq]
  exact brownian_physical_interval_joint_hasDerivAt_fixedLaw B P hB a y z T hT

theorem actual_killed_density_semigroup_row {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y w : ℝ) (T S : ℝ≥0) (hT : T ≠ 0) (hS : S ≠ 0) :
    Integrable (fun z : ℝ => gaussianPDFReal z S w *
      intervalCompletion (bridgeLaw B P) a z (S : ℝ) w) (actualIntervalKernel B P a T y) ∧
    gaussianPDFReal y (T + S) w * intervalCompletion (bridgeLaw B P) a y ((T + S : ℝ≥0) : ℝ) w =
      ∫ z : ℝ, gaussianPDFReal z S w * intervalCompletion (bridgeLaw B P) a z (S : ℝ) w
        ∂actualIntervalKernel B P a T y := by
  let K := actualIntervalKernel B P a T y
  let F : ℝ → ℝ → ℝ := fun v z => (actualIntervalKernel B P a S z).real (Iic v)
  let D : ℝ → ℝ → ℝ := fun v z => gaussianPDFReal z S v *
    intervalCompletion (bridgeLaw B P) a z (S : ℝ) v
  let C : ℝ := (Real.sqrt (2 * Real.pi * (S : ℝ)))⁻¹
  letI : IsFiniteKernel (actualIntervalKernel B P a T) :=
    actualIntervalKernel_isFiniteKernel B P hB a T hT
  have hF (v : ℝ) : Measurable (F v) :=
    ENNReal.measurable_toReal.comp ((actualIntervalKernel B P a S).measurable_coe measurableSet_Iic)
  have hD : Continuous (D w) :=
    (killed_density_joint_continuous B P hB a S hS).comp (continuous_id.prodMk continuous_const)
  have hFi : Integrable (F w) K :=
    (actualIntervalKernel_semigroup_real B P hB a y T S hT hS (Iic w) measurableSet_Iic).1
  have hb : ∀ᵐ z ∂K, ∀ v ∈ (univ : Set ℝ), ‖D v z‖ ≤ C := by
    exact Eventually.of_forall fun z v _ => by
      have hh := killed_density_uniform_bound B P hB a z v S
      change ‖gaussianPDFReal z S v * intervalCompletion (bridgeLaw B P) a z (S : ℝ) v‖ ≤
        (Real.sqrt (2 * Real.pi * (S : ℝ)))⁻¹
      simpa only [Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  have hd : ∀ᵐ z ∂K, ∀ v ∈ (univ : Set ℝ), HasDerivAt (fun v => F v z) (D v z) v :=
    Eventually.of_forall fun z v _ => actualIntervalKernel_rowCDF_hasDerivAt B P hB a z v S hS
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := K) (F := F) (F' := D) (bound := fun _ => C) (x₀ := w)
    (s := univ) (Filter.univ_mem : (univ : Set ℝ) ∈ 𝓝 w)
    (Eventually.of_forall fun v => (hF v).aestronglyMeasurable)
    hFi hD.aestronglyMeasurable hb (integrable_const C) hd
  have hTS : T + S ≠ 0 :=
    (add_pos (pos_iff_ne_zero.mpr hT) (pos_iff_ne_zero.mpr hS)).ne'
  have heq : (fun v : ℝ => ∫ z, F v z ∂K) =
      (fun v : ℝ => (actualIntervalKernel B P a (T + S) y).real (Iic v)) := by
    funext v
    exact (actualIntervalKernel_semigroup_real B P hB a y T S hT hS (Iic v) measurableSet_Iic).2.symm
  have hh := hdiff.2
  rw [heq] at hh
  exact ⟨hdiff.1, (actualIntervalKernel_rowCDF_hasDerivAt B P hB a y w (T + S) hTS).unique hh⟩

theorem actual_killed_density_convolution {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y w : ℝ) (T S : ℝ≥0) (hT : T ≠ 0) (hS : S ≠ 0) :
    Integrable (fun z : ℝ =>
      (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) *
      (gaussianPDFReal z S w * intervalCompletion (bridgeLaw B P) a z (S : ℝ) w)) volume ∧
    gaussianPDFReal y (T + S) w * intervalCompletion (bridgeLaw B P) a y ((T + S : ℝ≥0) : ℝ) w =
      ∫ z : ℝ,
        (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) *
        (gaussianPDFReal z S w * intervalCompletion (bridgeLaw B P) a z (S : ℝ) w) := by
  let f : ℝ → ℝ := fun z => gaussianPDFReal y T z *
    intervalCompletion (bridgeLaw B P) a y (T : ℝ) z
  let g : ℝ → ℝ := fun z => gaussianPDFReal z S w *
    intervalCompletion (bridgeLaw B P) a z (S : ℝ) w
  let C : ℝ := (Real.sqrt (2 * Real.pi * (S : ℝ)))⁻¹
  have hf : Continuous f :=
    (killed_density_joint_continuous B P hB a T hT).comp (continuous_const.prodMk continuous_id)
  have hg : Continuous g :=
    (killed_density_joint_continuous B P hB a S hS).comp (continuous_id.prodMk continuous_const)
  have hfn (z : ℝ) : 0 ≤ f z := (killed_density_uniform_bound B P hB a y z T).1
  have hgn (z : ℝ) : 0 ≤ g z := (killed_density_uniform_bound B P hB a z w S).1
  have hi : Integrable (fun z => f z * g z) volume := by
    apply ((integrable_killed_density B P hB a y T hT).const_mul C).mono'
      (hf.mul hg).aestronglyMeasurable
    exact Eventually.of_forall fun z => by
      change ‖f z * g z‖ ≤ C * f z
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfn z) (hgn z))]
      calc
        f z * g z ≤ f z * C := mul_le_mul_of_nonneg_left
          (killed_density_uniform_bound B P hB a z w S).2 (hfn z)
        _ = C * f z := mul_comm _ _
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ z, g z ∂actualIntervalKernel B P a T y :=
      (actual_killed_density_semigroup_row B P hB a y w T S hT hS).2
    _ = ∫ z, g z ∂volume.withDensity (fun z => ENNReal.ofReal (f z)) := by
      rw [actualIntervalKernel_apply_eq_density B P hB a y T hT]
    _ = ∫ z, (ENNReal.ofReal (f z)).toReal • g z :=
      integral_withDensity_eq_integral_toReal_smul
        (ENNReal.measurable_ofReal.comp hf.measurable)
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change (ENNReal.ofReal (f z)).toReal • g z = f z * g z
        rw [ENNReal.toReal_ofReal (hfn z), smul_eq_mul]

end Shao.C2.BrownianKilledDensitySemigroup
