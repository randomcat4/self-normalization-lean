import Shao.C2.BrownianKilledKernel

noncomputable section
namespace Shao.C2.BrownianKilledAction
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
open Shao.C2.BrownianKilledKernel

theorem actualIntervalKernel_row_eq_map_restrict {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    actualIntervalKernel B P a T y =
      (P.restrict {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}).map
        (fun ω => y + B T ω) := by
  let S : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}
  have hE : AEMeasurable (fun ω => y + B T ω) P :=
    aemeasurable_const.add (hB.toIsPreBrownianReal.aemeasurable T)
  have hEr : AEMeasurable (fun ω => y + B T ω) (P.restrict S) :=
    hE.mono_measure Measure.restrict_le_self
  apply Measure.ext
  intro A hA
  rw [actualIntervalKernel_apply_eq_survival B P hB a y T hT A hA,
    Measure.map_apply_of_aemeasurable hEr hA,
    Measure.restrict_apply₀ (hEr.nullMeasurable hA)]
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
  congr 1
  ext ω
  exact and_comm

theorem actualIntervalKernel_action_bounded {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f) (hbound : ∃ M : ℝ, ∀ z, |f z| ≤ M) :
    Integrable f (actualIntervalKernel B P a T y) ∧
      Integrable (fun ω => f (y + B T ω))
        (P.restrict {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}) ∧
      (∫ z : ℝ, f z ∂actualIntervalKernel B P a T y) =
        ∫ ω, f (y + B T ω) ∂P.restrict {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a} := by
  let S : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ T → |y + B s ω| < a}
  letI : IsFiniteKernel (actualIntervalKernel B P a T) :=
    actualIntervalKernel_isFiniteKernel B P hB a T hT
  have hE : AEMeasurable (fun ω => y + B T ω) P :=
    aemeasurable_const.add (hB.toIsPreBrownianReal.aemeasurable T)
  have hEr : AEMeasurable (fun ω => y + B T ω) (P.restrict S) :=
    hE.mono_measure Measure.restrict_le_self
  obtain ⟨M, hM⟩ := hbound
  have hleft : Integrable f (actualIntervalKernel B P a T y) := by
    apply Integrable.of_bound hf.aestronglyMeasurable M
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hM z
  have hright : Integrable (fun ω => f (y + B T ω)) (P.restrict S) := by
    apply Integrable.of_bound (hf.comp_aemeasurable hEr).aestronglyMeasurable M
    exact Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_def] using hM (y + B T ω)
  refine ⟨hleft, hright, ?_⟩
  rw [actualIntervalKernel_row_eq_map_restrict B P hB a y T hT]
  exact integral_map hEr hf.aestronglyMeasurable

end Shao.C2.BrownianKilledAction
