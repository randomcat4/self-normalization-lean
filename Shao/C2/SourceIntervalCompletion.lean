import Shao.C2.CompletionMeasurability

noncomputable section
namespace Shao.C2.SourceIntervalCompletion
open MeasureTheory Set
open Shao.C2.BridgeDomination Shao.C2.CompletionMeasurability

def sourceIntervalCompletion (ν : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  if 0 < T then intervalCompletion ν a y T z
  else if T = 0 ∧ y = z ∧ |y| < a then 1 else 0

theorem sourceIntervalCompletion_pos (ν : Measure BridgeNoise) (a y T z : ℝ)
    (hT : 0 < T) :
    sourceIntervalCompletion ν a y T z = intervalCompletion ν a y T z := by
  simp only [sourceIntervalCompletion, if_pos hT]

theorem sourceIntervalCompletion_reachable_zero (ν : Measure BridgeNoise) (a y : ℝ) :
    sourceIntervalCompletion ν a y 0 y = if |y| < a then 1 else 0 := by
  simp [sourceIntervalCompletion]

theorem sourceIntervalCompletion_zero_nonreachable (ν : Measure BridgeNoise)
    (a y z : ℝ) (hyz : y ≠ z) :
    sourceIntervalCompletion ν a y 0 z = 0 := by
  simp [sourceIntervalCompletion, hyz]

theorem sourceIntervalCompletion_exterior (ν : Measure BridgeNoise) (a y T z : ℝ)
    (h : ¬ (|y| < a ∧ |z| < a)) :
    sourceIntervalCompletion ν a y T z = 0 := by
  have he : strictInterval a y T z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    have hp := bridgePath_endpoints y T z g
    apply h
    constructor
    · exact abs_lt.mpr ⟨by simpa [hp.1] using hg.2 0, by simpa [hp.1] using hg.1 0⟩
    · exact abs_lt.mpr ⟨by simpa [hp.2] using hg.2 1, by simpa [hp.2] using hg.1 1⟩
  unfold sourceIntervalCompletion
  split_ifs with hT ht
  · simp [intervalCompletion, he]
  · exact False.elim (h ⟨ht.2.2, ht.2.1 ▸ ht.2.2⟩)
  · rfl

theorem sourceIntervalCompletion_nonpositive_wall (ν : Measure BridgeNoise)
    (a y T z : ℝ) (ha : a ≤ 0) :
    sourceIntervalCompletion ν a y T z = 0 := by
  apply sourceIntervalCompletion_exterior
  intro h
  linarith [abs_nonneg y, h.1]

theorem sourceIntervalCompletion_bounds (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z : ℝ) :
    0 ≤ sourceIntervalCompletion ν a y T z ∧ sourceIntervalCompletion ν a y T z ≤ 1 := by
  unfold sourceIntervalCompletion
  split_ifs
  · exact (completion_bounds ν a y T z).2.2.2.2
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem measurable_sourceIntervalCompletion_parameters (ν : Measure BridgeNoise) [SFinite ν] :
    Measurable (fun p : CompletionParameters =>
      sourceIntervalCompletion ν p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have ha : Measurable (fun p : CompletionParameters => p.1) := by fun_prop
  have hy : Measurable (fun p : CompletionParameters => p.2.1) := by fun_prop
  have hT : Measurable (fun p : CompletionParameters => p.2.2.1) := by fun_prop
  have hz : Measurable (fun p : CompletionParameters => p.2.2.2) := by fun_prop
  have hpos : MeasurableSet {p : CompletionParameters | 0 < p.2.2.1} :=
    measurableSet_lt measurable_const hT
  have hzero : MeasurableSet {p : CompletionParameters |
      p.2.2.1 = 0 ∧ p.2.1 = p.2.2.2 ∧ |p.2.1| < p.1} :=
    (measurableSet_eq_fun hT measurable_const).inter
      ((measurableSet_eq_fun hy hz).inter (measurableSet_lt (continuous_abs.measurable.comp hy) ha))
  unfold sourceIntervalCompletion
  exact Measurable.ite hpos (measurable_intervalCompletion_parameters ν)
    (Measurable.ite hzero measurable_const measurable_const)

end Shao.C2.SourceIntervalCompletion
