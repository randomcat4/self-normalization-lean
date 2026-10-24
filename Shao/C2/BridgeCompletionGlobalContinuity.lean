import Shao.C2.BridgeIntervalContinuity

noncomputable section
namespace Shao.C2.BridgeCompletionGlobalContinuity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.BridgeIntervalContinuity

theorem bridge_upper_formula_pospart {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) (hT : 0 < T) :
    upperCompletion (bridgeLaw B P) a y T z =
      1 - Real.exp (-2 * max (a - y) 0 * max (a - z) 0 / T) := by
  by_cases hi : y < a ∧ z < a
  · have hy0 : 0 ≤ a - y := by linarith [hi.1]
    have hz0 : 0 ≤ a - z := by linarith [hi.2]
    rw [max_eq_left hy0, max_eq_left hz0]
    exact Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a y T z hT hi.1 hi.2
  · have he : strictUpper a y T z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hp := bridgePath_endpoints y T z g
      apply hi
      exact ⟨by simpa only [hp.1] using hg 0, by simpa only [hp.2] using hg 1⟩
    rcases not_and_or.mp hi with hy | hz
    · have hd : a - y ≤ 0 := by linarith
      simp [upperCompletion, lowerCompletion, he, max_eq_right hd]
    · have hd : a - z ≤ 0 := by linarith
      simp [upperCompletion, lowerCompletion, he, max_eq_right hd]

theorem bridge_lower_formula_pospart {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ) (hT : 0 < T) :
    lowerCompletion (bridgeLaw B P) a y T z =
      1 - Real.exp (-2 * max (a + y) 0 * max (a + z) 0 / T) := by
  by_cases hi : -a < y ∧ -a < z
  · have hy0 : 0 ≤ a + y := by linarith [hi.1]
    have hz0 : 0 ≤ a + z := by linarith [hi.2]
    rw [max_eq_left hy0, max_eq_left hz0]
    exact Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a y T z hT hi.1 hi.2
  · have he : strictLower a y T z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      have hp := bridgePath_endpoints y T z g
      apply hi
      exact ⟨by simpa only [hp.1] using hg 0, by simpa only [hp.2] using hg 1⟩
    rcases not_and_or.mp hi with hy | hz
    · have hd : a + y ≤ 0 := by linarith
      simp [upperCompletion, lowerCompletion, he, max_eq_right hd]
    · have hd : a + z ≤ 0 := by linarith
      simp [upperCompletion, lowerCompletion, he, max_eq_right hd]

theorem bridge_interval_continuous_start {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a T z : ℝ) (hT : 0 < T) :
    Continuous (fun w : ℝ => intervalCompletion (bridgeLaw B P) a w T z) := by
  let ν := bridgeLaw B P
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B P hB
  have hU : Continuous (fun w : ℝ => upperCompletion ν a w T z) := by
    have heq : (fun w : ℝ => upperCompletion ν a w T z) =
        (fun w : ℝ => 1 - Real.exp (-2 * max (a - w) 0 * max (a - z) 0 / T)) :=
      funext fun w => bridge_upper_formula_pospart B P hB a w T z hT
    rw [heq]
    fun_prop
  have hL : Continuous (fun w : ℝ => lowerCompletion ν a w T z) := by
    have heq : (fun w : ℝ => lowerCompletion ν a w T z) =
        (fun w : ℝ => 1 - Real.exp (-2 * max (a + w) 0 * max (a + z) 0 / T)) :=
      funext fun w => bridge_lower_formula_pospart B P hB a w T z hT
    rw [heq]
    fun_prop
  apply continuous_iff_continuousAt.2
  intro y
  have hU0 : Tendsto (fun w : ℝ => |upperCompletion ν a w T z - upperCompletion ν a y T z|) (nhds y) (nhds 0) := by
    simpa using (hU.continuousAt.sub (show ContinuousAt (fun _ : ℝ => upperCompletion ν a y T z) y from continuousAt_const)).abs.tendsto
  have hL0 : Tendsto (fun w : ℝ => |lowerCompletion ν a w T z - lowerCompletion ν a y T z|) (nhds y) (nhds 0) := by
    simpa using (hL.continuousAt.sub (show ContinuousAt (fun _ : ℝ => lowerCompletion ν a y T z) y from continuousAt_const)).abs.tendsto
  have hi0 := squeeze_zero (fun w : ℝ => abs_nonneg
    (intervalCompletion ν a w T z - intervalCompletion ν a y T z))
    (fun w => interval_start_abs_increment ν a y w T z)
    (by simpa using hU0.add hL0)
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [Real.dist_eq] using hi0

theorem bridge_interval_continuous_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T : ℝ) (hT : 0 < T) :
    Continuous (fun w : ℝ => intervalCompletion (bridgeLaw B P) a y T w) := by
  let ν := bridgeLaw B P
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B P hB
  have hU : Continuous (fun w : ℝ => upperCompletion ν a y T w) := by
    have heq : (fun w : ℝ => upperCompletion ν a y T w) =
        (fun w : ℝ => 1 - Real.exp (-2 * max (a - y) 0 * max (a - w) 0 / T)) :=
      funext fun w => bridge_upper_formula_pospart B P hB a y T w hT
    rw [heq]
    fun_prop
  have hL : Continuous (fun w : ℝ => lowerCompletion ν a y T w) := by
    have heq : (fun w : ℝ => lowerCompletion ν a y T w) =
        (fun w : ℝ => 1 - Real.exp (-2 * max (a + y) 0 * max (a + w) 0 / T)) :=
      funext fun w => bridge_lower_formula_pospart B P hB a y T w hT
    rw [heq]
    fun_prop
  apply continuous_iff_continuousAt.2
  intro z
  have hU0 : Tendsto (fun w : ℝ => |upperCompletion ν a y T w - upperCompletion ν a y T z|) (nhds z) (nhds 0) := by
    simpa using (hU.continuousAt.sub (show ContinuousAt (fun _ : ℝ => upperCompletion ν a y T z) z from continuousAt_const)).abs.tendsto
  have hL0 : Tendsto (fun w : ℝ => |lowerCompletion ν a y T w - lowerCompletion ν a y T z|) (nhds z) (nhds 0) := by
    simpa using (hL.continuousAt.sub (show ContinuousAt (fun _ : ℝ => lowerCompletion ν a y T z) z from continuousAt_const)).abs.tendsto
  have hi0 := squeeze_zero (fun w : ℝ => abs_nonneg
    (intervalCompletion ν a y T w - intervalCompletion ν a y T z))
    (fun w => interval_endpoint_abs_increment ν a y T z w)
    (by simpa using hU0.add hL0)
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [Real.dist_eq] using hi0

end Shao.C2.BridgeCompletionGlobalContinuity
