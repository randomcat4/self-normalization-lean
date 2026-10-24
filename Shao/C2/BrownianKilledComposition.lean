import Shao.C2.BrownianKilledSemigroup
import Mathlib.Probability.Kernel.Composition.Comp

noncomputable section
namespace Shao.C2.BrownianKilledComposition
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BrownianKilledKernel Shao.C2.BrownianKilledSemigroup

theorem actualIntervalKernel_comp {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) (T S : ℝ≥0) (hT : T ≠ 0) (hS : S ≠ 0) :
    actualIntervalKernel B P a (T + S) =
      (actualIntervalKernel B P a S) ∘ₖ (actualIntervalKernel B P a T) := by
  letI : IsFiniteKernel (actualIntervalKernel B P a S) :=
    actualIntervalKernel_isFiniteKernel B P hB a S hS
  have hTS : T + S ≠ 0 :=
    (add_pos (pos_iff_ne_zero.mpr hT) (pos_iff_ne_zero.mpr hS)).ne'
  letI : IsFiniteKernel (actualIntervalKernel B P a (T + S)) :=
    actualIntervalKernel_isFiniteKernel B P hB a (T + S) hTS
  ext y A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  have hrow := actualIntervalKernel_semigroup_real B P hB a y T S hT hS A hA
  calc
    _ = ENNReal.ofReal ((actualIntervalKernel B P a (T + S) y).real A) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal (∫ z : ℝ, (actualIntervalKernel B P a S z).real A
        ∂actualIntervalKernel B P a T y) := congrArg ENNReal.ofReal hrow.2
    _ = ∫⁻ z : ℝ, ENNReal.ofReal ((actualIntervalKernel B P a S z).real A)
        ∂actualIntervalKernel B P a T y :=
      ofReal_integral_eq_lintegral_ofReal hrow.1 (Eventually.of_forall fun _ => measureReal_nonneg)
    _ = _ := lintegral_congr_ae (Eventually.of_forall fun z =>
      ENNReal.ofReal_toReal (measure_ne_top (actualIntervalKernel B P a S z) A))

theorem actualIntervalKernel_comp_comm {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a : ℝ) (T S : ℝ≥0) (hT : T ≠ 0) (hS : S ≠ 0) :
    (actualIntervalKernel B P a S) ∘ₖ (actualIntervalKernel B P a T) =
      (actualIntervalKernel B P a T) ∘ₖ (actualIntervalKernel B P a S) := by
  rw [← actualIntervalKernel_comp B P hB a T S hT hS,
    ← actualIntervalKernel_comp B P hB a S T hS hT, add_comm T S]

end Shao.C2.BrownianKilledComposition
