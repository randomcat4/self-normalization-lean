import Shao.C2.BridgeIntervalActualBounds

noncomputable section
namespace Shao.C2.BridgeIntervalContinuity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open Shao.C2.HalfLineReflectionFormula

theorem interval_start_abs_increment (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y y' T z : ℝ) :
    |intervalCompletion ν a y' T z - intervalCompletion ν a y T z| ≤
      |upperCompletion ν a y' T z - upperCompletion ν a y T z| +
        |lowerCompletion ν a y' T z - lowerCompletion ν a y T z| := by
  rcases le_total y y' with h | h
  · have hu := upper_deficit_antitone ν a y y' T z z h le_rfl
    have hl := lower_deficit_monotone ν a y y' T z z h le_rfl
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (upperCompletion ν a y' T z - upperCompletion ν a y T z), neg_le_abs (upperCompletion ν a y' T z - upperCompletion ν a y T z),
      le_abs_self (lowerCompletion ν a y' T z - lowerCompletion ν a y T z), neg_le_abs (lowerCompletion ν a y' T z - lowerCompletion ν a y T z), abs_nonneg (upperCompletion ν a y' T z - upperCompletion ν a y T z), abs_nonneg (lowerCompletion ν a y' T z - lowerCompletion ν a y T z)]
  · have hu := upper_deficit_antitone ν a y' y T z z h le_rfl
    have hl := lower_deficit_monotone ν a y' y T z z h le_rfl
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (upperCompletion ν a y' T z - upperCompletion ν a y T z), neg_le_abs (upperCompletion ν a y' T z - upperCompletion ν a y T z),
      le_abs_self (lowerCompletion ν a y' T z - lowerCompletion ν a y T z), neg_le_abs (lowerCompletion ν a y' T z - lowerCompletion ν a y T z), abs_nonneg (upperCompletion ν a y' T z - upperCompletion ν a y T z), abs_nonneg (lowerCompletion ν a y' T z - lowerCompletion ν a y T z)]

theorem interval_endpoint_abs_increment (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z z' : ℝ) :
    |intervalCompletion ν a y T z' - intervalCompletion ν a y T z| ≤
      |upperCompletion ν a y T z' - upperCompletion ν a y T z| +
        |lowerCompletion ν a y T z' - lowerCompletion ν a y T z| := by
  rcases le_total z z' with h | h
  · have hu := upper_deficit_antitone ν a y y T z z' le_rfl h
    have hl := lower_deficit_monotone ν a y y T z z' le_rfl h
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (upperCompletion ν a y T z' - upperCompletion ν a y T z), neg_le_abs (upperCompletion ν a y T z' - upperCompletion ν a y T z),
      le_abs_self (lowerCompletion ν a y T z' - lowerCompletion ν a y T z), neg_le_abs (lowerCompletion ν a y T z' - lowerCompletion ν a y T z), abs_nonneg (upperCompletion ν a y T z' - upperCompletion ν a y T z), abs_nonneg (lowerCompletion ν a y T z' - lowerCompletion ν a y T z)]
  · have hu := upper_deficit_antitone ν a y y T z' z le_rfl h
    have hl := lower_deficit_monotone ν a y y T z' z le_rfl h
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (upperCompletion ν a y T z' - upperCompletion ν a y T z), neg_le_abs (upperCompletion ν a y T z' - upperCompletion ν a y T z),
      le_abs_self (lowerCompletion ν a y T z' - lowerCompletion ν a y T z), neg_le_abs (lowerCompletion ν a y T z' - lowerCompletion ν a y T z), abs_nonneg (upperCompletion ν a y T z' - upperCompletion ν a y T z), abs_nonneg (lowerCompletion ν a y T z' - lowerCompletion ν a y T z)]

theorem actual_interval_continuousAt_start {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ)
    (hT : 0 < T) (hy : |y| < a) (hz : |z| < a) :
    ContinuousAt (fun w : ℝ => intervalCompletion (bridgeLaw B P) a w T z) y := by
  let ν := bridgeLaw B P
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B P hB
  have hequpper : (fun w : ℝ => upperCompletion ν a w T z) =ᶠ[nhds y]
      (fun w : ℝ => upperReflection a w T z) := by
    filter_upwards [Iio_mem_nhds (abs_lt.mp hy).2] with w hw
    change upperCompletion (bridgeLaw B P) a w T z = _
    rw [Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a w T z hT hw (abs_lt.mp hz).2]
    unfold upperReflection
    first | rfl | congr 2 <;> ring
  have hU : ContinuousAt (fun w : ℝ => upperCompletion ν a w T z) y :=
    ((upperReflection_hasDerivAt a y T z).congr_of_eventuallyEq hequpper).continuousAt
  have heqlower : (fun w : ℝ => lowerCompletion ν a w T z) =ᶠ[nhds y]
      (fun w : ℝ => lowerReflection a w T z) := by
    filter_upwards [Ioi_mem_nhds (abs_lt.mp hy).1] with w hw
    change lowerCompletion (bridgeLaw B P) a w T z = _
    rw [Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a w T z hT hw (abs_lt.mp hz).1]
    unfold lowerReflection
    first | rfl | congr 2 <;> ring
  have hL : ContinuousAt (fun w : ℝ => lowerCompletion ν a w T z) y :=
    ((lowerReflection_hasDerivAt a y T z).congr_of_eventuallyEq heqlower).continuousAt
  have hU0 : Tendsto (fun w : ℝ => |upperCompletion ν a w T z - upperCompletion ν a y T z|) (nhds y) (nhds 0) := by
    simpa using (hU.sub (show ContinuousAt (fun _ : ℝ => upperCompletion ν a y T z) y from continuousAt_const)).abs.tendsto
  have hL0 : Tendsto (fun w : ℝ => |lowerCompletion ν a w T z - lowerCompletion ν a y T z|) (nhds y) (nhds 0) := by
    simpa using (hL.sub (show ContinuousAt (fun _ : ℝ => lowerCompletion ν a y T z) y from continuousAt_const)).abs.tendsto
  have hi0 := squeeze_zero (fun w : ℝ => abs_nonneg
    (intervalCompletion ν a w T z - intervalCompletion ν a y T z))
    (fun w => interval_start_abs_increment ν a y w T z)
    (by simpa using hU0.add hL0)
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [Real.dist_eq] using hi0

theorem actual_interval_continuousAt_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ)
    (hT : 0 < T) (hy : |y| < a) (hz : |z| < a) :
    ContinuousAt (fun w : ℝ => intervalCompletion (bridgeLaw B P) a y T w) z := by
  let ν := bridgeLaw B P
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_bridgeLaw B P hB
  have hequpper : (fun w : ℝ => upperCompletion ν a y T w) =ᶠ[nhds z]
      (fun w : ℝ => upperReflection a w T y) := by
    filter_upwards [Iio_mem_nhds (abs_lt.mp hz).2] with w hw
    change upperCompletion (bridgeLaw B P) a y T w = _
    rw [Shao.C2.BridgeUpperAffineIdentification.bridge_upper_formula B P hB a y T w hT (abs_lt.mp hy).2 hw]
    unfold upperReflection
    first | rfl | congr 2 <;> ring
  have hU : ContinuousAt (fun w : ℝ => upperCompletion ν a y T w) z :=
    ((upperReflection_hasDerivAt a z T y).congr_of_eventuallyEq hequpper).continuousAt
  have heqlower : (fun w : ℝ => lowerCompletion ν a y T w) =ᶠ[nhds z]
      (fun w : ℝ => lowerReflection a w T y) := by
    filter_upwards [Ioi_mem_nhds (abs_lt.mp hz).1] with w hw
    change lowerCompletion (bridgeLaw B P) a y T w = _
    rw [Shao.C2.BridgeLowerIdentification.bridge_lower_formula B P hB a y T w hT (abs_lt.mp hy).1 hw]
    unfold lowerReflection
    first | rfl | congr 2 <;> ring
  have hL : ContinuousAt (fun w : ℝ => lowerCompletion ν a y T w) z :=
    ((lowerReflection_hasDerivAt a z T y).congr_of_eventuallyEq heqlower).continuousAt
  have hU0 : Tendsto (fun w : ℝ => |upperCompletion ν a y T w - upperCompletion ν a y T z|) (nhds z) (nhds 0) := by
    simpa using (hU.sub (show ContinuousAt (fun _ : ℝ => upperCompletion ν a y T z) z from continuousAt_const)).abs.tendsto
  have hL0 : Tendsto (fun w : ℝ => |lowerCompletion ν a y T w - lowerCompletion ν a y T z|) (nhds z) (nhds 0) := by
    simpa using (hL.sub (show ContinuousAt (fun _ : ℝ => lowerCompletion ν a y T z) z from continuousAt_const)).abs.tendsto
  have hi0 := squeeze_zero (fun w : ℝ => abs_nonneg
    (intervalCompletion ν a y T w - intervalCompletion ν a y T z))
    (fun w => interval_endpoint_abs_increment ν a y T z w)
    (by simpa using hU0.add hL0)
  apply tendsto_iff_dist_tendsto_zero.2
  simpa only [Real.dist_eq] using hi0

end Shao.C2.BridgeIntervalContinuity
