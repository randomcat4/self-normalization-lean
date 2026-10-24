import Shao.C2.BrownianKilledEndpointDensity
import Mathlib.Probability.Kernel.WithDensity

noncomputable section
namespace Shao.C2.BrownianKilledKernel
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeIntervalContinuity Shao.C2.BridgeCompletionGlobalContinuity
open Shao.C2.BrownianKilledEndpointDensity

def actualIntervalKernel {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (a : ℝ) (T : ℝ≥0) : Kernel ℝ ℝ :=
  (Kernel.const ℝ volume).withDensity (fun y z : ℝ =>
    ENNReal.ofReal (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z))

theorem bridge_interval_joint_continuous {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a T : ℝ) (hT : 0 < T) :
    Continuous (fun p : ℝ × ℝ => intervalCompletion (bridgeLaw B P) a p.1 T p.2) := by
  let ν := bridgeLaw B P
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B P hB
  have hU : Continuous (fun p : ℝ × ℝ => upperCompletion ν a p.1 T p.2) := by
    have heq : (fun p : ℝ × ℝ => upperCompletion ν a p.1 T p.2) =
        (fun p : ℝ × ℝ => 1 - Real.exp (-2 * max (a - p.1) 0 * max (a - p.2) 0 / T)) :=
      funext fun p => bridge_upper_formula_pospart B P hB a p.1 T p.2 hT
    rw [heq]
    fun_prop
  have hL : Continuous (fun p : ℝ × ℝ => lowerCompletion ν a p.1 T p.2) := by
    have heq : (fun p : ℝ × ℝ => lowerCompletion ν a p.1 T p.2) =
        (fun p : ℝ × ℝ => 1 - Real.exp (-2 * max (a + p.1) 0 * max (a + p.2) 0 / T)) :=
      funext fun p => bridge_lower_formula_pospart B P hB a p.1 T p.2 hT
    rw [heq]
    fun_prop
  apply continuous_iff_continuousAt.2
  rintro ⟨y, z⟩
  have hpair : Continuous (fun p : ℝ × ℝ => (y, p.2)) := by fun_prop
  have hU0 : Tendsto (fun p : ℝ × ℝ =>
      |upperCompletion ν a p.1 T p.2 - upperCompletion ν a y T p.2|)
      (nhds (y, z)) (nhds 0) := by
    simpa only [Pi.sub_apply, Function.comp_def, sub_self, abs_zero] using
      ((hU.continuousAt (x := (y, z))).sub ((hU.comp hpair).continuousAt (x := (y, z)))).abs.tendsto
  have hL0 : Tendsto (fun p : ℝ × ℝ =>
      |lowerCompletion ν a p.1 T p.2 - lowerCompletion ν a y T p.2|)
      (nhds (y, z)) (nhds 0) := by
    simpa only [Pi.sub_apply, Function.comp_def, sub_self, abs_zero] using
      ((hL.continuousAt (x := (y, z))).sub ((hL.comp hpair).continuousAt (x := (y, z)))).abs.tendsto
  have hEnd : Continuous (fun p : ℝ × ℝ => intervalCompletion ν a y T p.2) :=
    (bridge_interval_continuous_endpoint B P hB a y T hT).comp continuous_snd
  have hEnd0 : Tendsto (fun p : ℝ × ℝ =>
      |intervalCompletion ν a y T p.2 - intervalCompletion ν a y T z|)
      (nhds (y, z)) (nhds 0) := by
    simpa only [Pi.sub_apply, Function.comp_def, sub_self, abs_zero] using
      (hEnd.continuousAt.sub (show ContinuousAt
        (fun _ : ℝ × ℝ => intervalCompletion ν a y T z) (y, z) from continuousAt_const)).abs.tendsto
  have hbound (p : ℝ × ℝ) :
      |intervalCompletion ν a p.1 T p.2 - intervalCompletion ν a y T z| ≤
        (|upperCompletion ν a p.1 T p.2 - upperCompletion ν a y T p.2| +
          |lowerCompletion ν a p.1 T p.2 - lowerCompletion ν a y T p.2|) +
            |intervalCompletion ν a y T p.2 - intervalCompletion ν a y T z| := by
    calc
      _ ≤ |intervalCompletion ν a p.1 T p.2 - intervalCompletion ν a y T p.2| +
          |intervalCompletion ν a y T p.2 - intervalCompletion ν a y T z| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add (interval_start_abs_increment ν a y p.1 T p.2) le_rfl
  have hi0 := squeeze_zero
    (fun p : ℝ × ℝ => abs_nonneg (intervalCompletion ν a p.1 T p.2 - intervalCompletion ν a y T z))
    hbound (by simpa using (hU0.add hL0).add hEnd0)
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [Real.dist_eq] using hi0

theorem killed_density_joint_continuous {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    Continuous (fun p : ℝ × ℝ => gaussianPDFReal p.1 T p.2 *
      intervalCompletion (bridgeLaw B P) a p.1 (T : ℝ) p.2) := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
  apply Continuous.mul _ (bridge_interval_joint_continuous B P hB a (T : ℝ) hTpos)
  unfold gaussianPDFReal
  fun_prop

theorem actualIntervalKernel_apply_eq_density {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    actualIntervalKernel B P a T y = volume.withDensity (fun z : ℝ =>
      ENNReal.ofReal (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z)) := by
  have hm : Measurable (Function.uncurry (fun y z : ℝ =>
      ENNReal.ofReal (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z))) :=
    ENNReal.measurable_ofReal.comp (killed_density_joint_continuous B P hB a T hT).measurable
  calc
    actualIntervalKernel B P a T y = ((Kernel.const ℝ volume) y).withDensity (fun z : ℝ =>
        ENNReal.ofReal (gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z)) :=
      Kernel.withDensity_apply _ hm y
    _ = _ := by rw [Kernel.const_apply]

theorem actualIntervalKernel_apply_eq_survival {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    actualIntervalKernel B P a T y A =
      ENNReal.ofReal (P.real {ω |
        (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ∈ A}) := by
  letI : IsProbabilityMeasure (bridgeLaw B P) := isProbabilityMeasure_bridgeLaw B P hB
  rw [actualIntervalKernel_apply_eq_density B P hB a y T hT, withDensity_apply _ hA]
  have hi := (integrable_killed_density B P hB a y T hT).integrableOn (s := A)
  have hnn : 0 ≤ᵐ[volume.restrict A] (fun z : ℝ => gaussianPDFReal y T z *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) := by
    exact Eventually.of_forall fun z => mul_nonneg (gaussianPDFReal_nonneg y T z)
      (completion_bounds (bridgeLaw B P) a y (T : ℝ) z).2.2.2.2.1
  calc
    _ = ENNReal.ofReal (∫ z : ℝ in A, gaussianPDFReal y T z *
        intervalCompletion (bridgeLaw B P) a y (T : ℝ) z) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnn).symm
    _ = _ := congrArg ENNReal.ofReal (brownian_physical_interval_joint_eq_integral B P hB a y T hT A hA).symm

theorem actualIntervalKernel_real_eq_survival {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (actualIntervalKernel B P a T y).real A =
      P.real {ω | (∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a) ∧ y + B T ω ∈ A} := by
  rw [measureReal_def, actualIntervalKernel_apply_eq_survival B P hB a y T hT A hA,
    ENNReal.toReal_ofReal measureReal_nonneg]

theorem actualIntervalKernel_mass_le_one {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    actualIntervalKernel B P a T y univ ≤ 1 := by
  rw [actualIntervalKernel_apply_eq_survival B P hB a y T hT univ MeasurableSet.univ]
  calc
    _ ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal measureReal_le_one
    _ = 1 := by norm_num

theorem actualIntervalKernel_isFiniteKernel {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    IsFiniteKernel (actualIntervalKernel B P a T) := by
  constructor
  exact ⟨1, by simp, fun y => actualIntervalKernel_mass_le_one B P hB a y T hT⟩

end Shao.C2.BrownianKilledKernel
