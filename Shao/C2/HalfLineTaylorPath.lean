import Shao.C2.HalfLineTaylorSegment
import Shao.C2.HalfLineMixedProfiles
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
namespace Shao.C2.HalfLineTaylorPath
open Shao.C2.HalfLineTaylorSegment Shao.C2.HalfLineMixedProfiles
open Shao.C2.HalfLineTimeProfiles

def completionAlongSegment (u v T b θ : ℝ) : ℝ :=
  1 - Real.exp (-2 * segmentDistance u b θ * v / segmentEnergy T b θ)
def exponentSlope (u v T b : ℝ) : ℝ := 2 * v * b * (T - u * b)

theorem completionAlongSegment_hasDerivAt (u v T b θ : ℝ)
    (hE : 0 < segmentEnergy T b θ) :
    HasDerivAt (completionAlongSegment u v T b)
      (-exponentSlope u v T b / (segmentEnergy T b θ) ^ 2 *
        Real.exp (-2 * segmentDistance u b θ * v / segmentEnergy T b θ)) θ := by
  have hD : HasDerivAt (segmentEnergy T b) (-(b ^ 2)) θ := by
    unfold segmentEnergy
    convert (hasDerivAt_const θ T).sub ((hasDerivAt_id θ).mul_const (b ^ 2)) using 1
    · funext t; rfl
    · ring
  have hU : HasDerivAt (segmentDistance u b) (-b) θ := by
    unfold segmentDistance
    convert (hasDerivAt_const θ u).sub ((hasDerivAt_id θ).mul_const b) using 1
    · funext t; rfl
    · ring
  have hQ := ((hU.const_mul (-2)).mul_const v).div hD (ne_of_gt hE)
  have h := (hasDerivAt_const θ 1).sub hQ.exp
  convert h using 1 <;> try rfl <;> try (funext t; rfl)
  dsimp only [Pi.div_apply, exponentSlope]
  field_simp [ne_of_gt hE] <;> dsimp only [segmentEnergy, segmentDistance] <;> ring

theorem completionAlongSegment_second_hasDerivAt (u v T b θ : ℝ)
    (hE : 0 < segmentEnergy T b θ) :
    HasDerivAt (deriv (completionAlongSegment u v T b))
      (-(exponentSlope u v T b ^ 2 / (segmentEnergy T b θ) ^ 4 +
          2 * exponentSlope u v T b * b ^ 2 / (segmentEnergy T b θ) ^ 3) *
        Real.exp (-2 * segmentDistance u b θ * v / segmentEnergy T b θ)) θ := by
  have hD : HasDerivAt (segmentEnergy T b) (-(b ^ 2)) θ := by
    unfold segmentEnergy
    convert (hasDerivAt_const θ T).sub ((hasDerivAt_id θ).mul_const (b ^ 2)) using 1
    · funext t; rfl
    · ring
  have hU : HasDerivAt (segmentDistance u b) (-b) θ := by
    unfold segmentDistance
    convert (hasDerivAt_const θ u).sub ((hasDerivAt_id θ).mul_const b) using 1
    · funext t; rfl
    · ring
  have hQ := ((hU.const_mul (-2)).mul_const v).div hD (ne_of_gt hE)
  have hC := (hasDerivAt_const θ (-exponentSlope u v T b)).div (hD.pow 2)
    (pow_ne_zero 2 (ne_of_gt hE))
  have h := hC.mul hQ.exp
  have hf : HasDerivAt
      (fun t : ℝ => -exponentSlope u v T b / (segmentEnergy T b t) ^ 2 *
        Real.exp (-2 * segmentDistance u b t * v / segmentEnergy T b t))
      (-(exponentSlope u v T b ^ 2 / (segmentEnergy T b θ) ^ 4 +
          2 * exponentSlope u v T b * b ^ 2 / (segmentEnergy T b θ) ^ 3) *
        Real.exp (-2 * segmentDistance u b θ * v / segmentEnergy T b θ)) θ := by
    convert h using 1 <;> try rfl <;> try (funext t; rfl)
    dsimp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.neg_apply]
    field_simp [ne_of_gt hE] <;> dsimp only [segmentEnergy, segmentDistance, exponentSlope] <;> ring
  apply hf.congr_of_eventuallyEq
  filter_upwards [hD.continuousAt.eventually (Ioi_mem_nhds hE)] with t ht
  exact (completionAlongSegment_hasDerivAt u v T b t ht).deriv

theorem completionAlongSegment_third_hasDerivAt (u v T b θ : ℝ)
    (hE : 0 < segmentEnergy T b θ) :
    HasDerivAt (deriv (deriv (completionAlongSegment u v T b)))
      (-(exponentSlope u v T b ^ 3 / (segmentEnergy T b θ) ^ 6 +
          6 * exponentSlope u v T b ^ 2 * b ^ 2 / (segmentEnergy T b θ) ^ 5 +
          6 * exponentSlope u v T b * b ^ 4 / (segmentEnergy T b θ) ^ 4) *
        Real.exp (-2 * segmentDistance u b θ * v / segmentEnergy T b θ)) θ := by
  have hD : HasDerivAt (segmentEnergy T b) (-(b ^ 2)) θ := by
    unfold segmentEnergy
    convert (hasDerivAt_const θ T).sub ((hasDerivAt_id θ).mul_const (b ^ 2)) using 1
    · funext t; rfl
    · ring
  have hU : HasDerivAt (segmentDistance u b) (-b) θ := by
    unfold segmentDistance
    convert (hasDerivAt_const θ u).sub ((hasDerivAt_id θ).mul_const b) using 1
    · funext t; rfl
    · ring
  have hQ := ((hU.const_mul (-2)).mul_const v).div hD (ne_of_gt hE)
  have hA := (hasDerivAt_const θ (exponentSlope u v T b ^ 2)).div (hD.pow 4)
    (pow_ne_zero 4 (ne_of_gt hE))
  have hB := (hasDerivAt_const θ (2 * exponentSlope u v T b * b ^ 2)).div (hD.pow 3)
    (pow_ne_zero 3 (ne_of_gt hE))
  have h := (hA.add hB).neg.mul hQ.exp
  have hf : HasDerivAt
      (fun t : ℝ => -(exponentSlope u v T b ^ 2 / (segmentEnergy T b t) ^ 4 +
          2 * exponentSlope u v T b * b ^ 2 / (segmentEnergy T b t) ^ 3) *
        Real.exp (-2 * segmentDistance u b t * v / segmentEnergy T b t))
      (-(exponentSlope u v T b ^ 3 / (segmentEnergy T b θ) ^ 6 +
          6 * exponentSlope u v T b ^ 2 * b ^ 2 / (segmentEnergy T b θ) ^ 5 +
          6 * exponentSlope u v T b * b ^ 4 / (segmentEnergy T b θ) ^ 4) *
        Real.exp (-2 * segmentDistance u b θ * v / segmentEnergy T b θ)) θ := by
    convert h using 1 <;> try rfl <;> try (funext t; rfl)
    dsimp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, Pi.neg_apply]
    field_simp [ne_of_gt hE] <;> dsimp only [segmentEnergy, segmentDistance, exponentSlope] <;> ring
  apply hf.congr_of_eventuallyEq
  filter_upwards [hD.continuousAt.eventually (Ioi_mem_nhds hE)] with t ht
  exact (completionAlongSegment_second_hasDerivAt u v T b t ht).deriv

theorem completionAlongSegment_contDiffAt (u v T b θ : ℝ)
    (hE : 0 < segmentEnergy T b θ) (n : ℕ) :
    ContDiffAt ℝ n (completionAlongSegment u v T b) θ := by
  have hD : ContDiffAt ℝ n (segmentEnergy T b) θ := by
    unfold segmentEnergy
    fun_prop
  have hU : ContDiffAt ℝ n (segmentDistance u b) θ := by
    unfold segmentDistance
    fun_prop
  unfold completionAlongSegment
  exact contDiffAt_const.sub ((((contDiffAt_const.mul hU).mul contDiffAt_const).div hD (ne_of_gt hE)).exp)

theorem compensated_second_taylor_identity (u v T b : ℝ) (hT : 0 < T) :
    (deriv (completionAlongSegment u v T b) 0 +
        (1 / 2 : ℝ) * deriv (deriv (completionAlongSegment u v T b)) 0) -
      (b - b ^ 2 * (u - v) / T) * (-slopeTime u v T) =
    b ^ 3 * deriv (slopeTime u v) T +
      (1 / 2 : ℝ) * b ^ 4 * deriv (deriv (timeCompletion (2 * u * v))) T := by
  have hE : 0 < segmentEnergy T b 0 := by simpa only [segmentEnergy, zero_mul, sub_zero] using hT
  rw [(completionAlongSegment_hasDerivAt u v T b 0 hE).deriv,
    (completionAlongSegment_second_hasDerivAt u v T b 0 hE).deriv,
    (slopeTime_hasDerivAt u v T hT).deriv,
    (timeCompletion_second_hasDerivAt (2 * u * v) T hT).deriv]
  dsimp only [segmentEnergy, segmentDistance, exponentSlope, slopeTime]
  simp only [zero_mul, sub_zero]
  field_simp [ne_of_gt hT] <;> ring

end Shao.C2.HalfLineTaylorPath
