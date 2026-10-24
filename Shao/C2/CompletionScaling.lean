import Shao.C2.BridgeDomination

noncomputable section
namespace Shao.C2.CompletionScaling
open MeasureTheory
open Shao.C2.BridgeDomination

theorem bridgePath_scale (c : ℝ) (hc : 0 < c) (y T z : ℝ) (hT : 0 ≤ T) (g : BridgeNoise) :
    bridgePath (c * y) (c ^ 2 * T) (c * z) g = c • bridgePath y T z g := by
  have hs : Real.sqrt (c ^ 2 * T) = c * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  ext t
  simp only [bridgePath, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul, hs]
  ring

theorem upperCompletion_scale (ν : Measure BridgeNoise)
    (c : ℝ) (hc : 0 < c) (a y T z : ℝ) (hT : 0 ≤ T) :
    upperCompletion ν (c * a) (c * y) (c ^ 2 * T) (c * z) = upperCompletion ν a y T z := by
  have hcancel (u v : ℝ) : c * u < c * v ↔ u < v := by
    constructor
    · intro h; by_contra hh
      have hh' := mul_le_mul_of_nonneg_left (le_of_not_gt hh) hc.le
      linarith
    · intro h; exact mul_lt_mul_of_pos_left h hc
  unfold upperCompletion
  congr 1
  ext g
  simp only [strictUpper, strictUpper, strictLower, Set.mem_setOf_eq, Set.mem_inter_iff,
    bridgePath_scale c hc y T z hT, ContinuousMap.smul_apply, smul_eq_mul, ← mul_neg,
    hcancel]

theorem lowerCompletion_scale (ν : Measure BridgeNoise)
    (c : ℝ) (hc : 0 < c) (a y T z : ℝ) (hT : 0 ≤ T) :
    lowerCompletion ν (c * a) (c * y) (c ^ 2 * T) (c * z) = lowerCompletion ν a y T z := by
  have hcancel (u v : ℝ) : c * u < c * v ↔ u < v := by
    constructor
    · intro h; by_contra hh
      have hh' := mul_le_mul_of_nonneg_left (le_of_not_gt hh) hc.le
      linarith
    · intro h; exact mul_lt_mul_of_pos_left h hc
  unfold lowerCompletion
  congr 1
  ext g
  simp only [strictLower, strictUpper, strictLower, Set.mem_setOf_eq, Set.mem_inter_iff,
    bridgePath_scale c hc y T z hT, ContinuousMap.smul_apply, smul_eq_mul, ← mul_neg,
    hcancel]

theorem intervalCompletion_scale (ν : Measure BridgeNoise)
    (c : ℝ) (hc : 0 < c) (a y T z : ℝ) (hT : 0 ≤ T) :
    intervalCompletion ν (c * a) (c * y) (c ^ 2 * T) (c * z) = intervalCompletion ν a y T z := by
  have hcancel (u v : ℝ) : c * u < c * v ↔ u < v := by
    constructor
    · intro h; by_contra hh
      have hh' := mul_le_mul_of_nonneg_left (le_of_not_gt hh) hc.le
      linarith
    · intro h; exact mul_lt_mul_of_pos_left h hc
  unfold intervalCompletion
  congr 1
  ext g
  simp only [strictInterval, strictUpper, strictLower, Set.mem_setOf_eq, Set.mem_inter_iff,
    bridgePath_scale c hc y T z hT, ContinuousMap.smul_apply, smul_eq_mul, ← mul_neg,
    hcancel]

theorem initial_raw_completion_eq_normalized (ν : Measure BridgeNoise)
    (x Q S : ℝ) (hQ : 0 < Q) :
    intervalCompletion ν (x * Real.sqrt Q) 0 Q S =
      intervalCompletion ν x 0 1 (S / Real.sqrt Q) := by
  have hs : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  have hz : Real.sqrt Q * (S / Real.sqrt Q) = S := by
    field_simp
  have h := intervalCompletion_scale ν (Real.sqrt Q) (Real.sqrt_pos.mpr hQ)
    x 0 1 (S / Real.sqrt Q) (by norm_num)
  simpa only [mul_zero, zero_mul, mul_one, hs, hz, mul_comm] using h

end Shao.C2.CompletionScaling
