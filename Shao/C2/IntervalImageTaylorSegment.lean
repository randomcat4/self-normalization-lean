import Shao.C2.IntervalImageLocalRegularity
import Shao.C2.IntervalGaussianLocal

noncomputable section
namespace Shao.C2.IntervalImageTaylorSegment
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedCandidate Shao.C2.IntervalImageSmallTimeSum
open Shao.C2.CompletionFirstProfile Shao.C2.HalfLineTaylorSegment Shao.C2.IntervalGaussianLocal

theorem segment_space_closed (a y b θ : ℝ) (hy : |y| < a) (hnew : |y + b| ≤ a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : |y + θ * b| ≤ a := by
  have hU : 0 < a - y := by linarith only [(abs_lt.mp hy).2]
  have hL : 0 < a + y := by linarith only [(abs_lt.mp hy).1]
  have hnU : 0 ≤ (a - y) - b := by linarith only [(abs_le.mp hnew).2]
  have hnL : 0 ≤ (a + y) - (-b) := by linarith only [(abs_le.mp hnew).1]
  have h1 := segment_distance_nonneg (a - y) b θ hU hnU hθ0 hθ1
  have h2 := segment_distance_nonneg (a + y) (-b) θ hL hnL hθ0 hθ1
  dsimp only [segmentDistance] at h1 h2
  exact abs_le.2 ⟨by linarith only [h2], by linarith only [h1]⟩

theorem segment_space_interior (a y b θ : ℝ) (hy : |y| < a) (hnew : |y + b| ≤ a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) : |y + θ * b| < a := by
  have hU : 0 < a - y := by linarith only [(abs_lt.mp hy).2]
  have hL : 0 < a + y := by linarith only [(abs_lt.mp hy).1]
  have hnU : 0 ≤ (a - y) - b := by linarith only [(abs_le.mp hnew).2]
  have hnL : 0 ≤ (a + y) - (-b) := by linarith only [(abs_le.mp hnew).1]
  have h1 := segment_distance_pos (a - y) b θ hU hnU hθ0 hθ1
  have h2 := segment_distance_pos (a + y) (-b) θ hL hnL hθ0 hθ1
  dsimp only [segmentDistance] at h1 h2
  exact abs_lt.2 ⟨by linarith only [h2], by linarith only [h1]⟩

theorem interval_segment_profile_transport (a y z T b θ : ℝ) (r j : ℕ)
    (hy : |y| < a) (hz : |z| ≤ a) (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2)
    (hnew : |y + b| ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 / Real.sqrt (segmentEnergy T b θ)) ^ r *
      (1 + |z - (y + θ * b)| / Real.sqrt (segmentEnergy T b θ)) ^ j *
      intervalProfile a (y + θ * b) (segmentEnergy T b θ) z ≤
    (2 : ℝ) ^ r * (3 : ℝ) ^ j * (1 / Real.sqrt T) ^ r *
      (1 + |z - y| / Real.sqrt T) ^ j * intervalIncrementProfile a y T z b := by
  have hU : 0 < a - y := by linarith only [(abs_lt.mp hy).2]
  have hL : 0 < a + y := by linarith only [(abs_lt.mp hy).1]
  have hvU : 0 ≤ a - z := by linarith only [(abs_le.mp hz).2]
  have hvL : 0 ≤ a + z := by linarith only [(abs_le.mp hz).1]
  have hnU : 0 ≤ (a - y) - b := by linarith only [(abs_le.mp hnew).2]
  have hnL : 0 ≤ (a + y) - (-b) := by linarith only [(abs_le.mp hnew).1]
  have hbneg : (-b) ^ 2 ≤ T / 2 := by simpa only [neg_sq] using hsmall
  have h1 := segment_profile_transport (a - y) (a - z) (z - y) T b θ
    hU hvU hT hsmall hnU hθ0 hθ1 r j
  have h2 := segment_profile_transport (a + y) (a + z) (-(z - y)) T (-b) θ
    hL hvL hT hbneg hnL hθ0 hθ1 r j
  have he : segmentEnergy T (-b) θ = segmentEnergy T b θ := by
    simp only [segmentEnergy, neg_sq]
  have hd1 : z - y - θ * b = z - (y + θ * b) := by ring
  have hd2 : -(z - y) - θ * (-b) = -(z - (y + θ * b)) := by ring
  have hu : segmentDistance (a - y) b θ = a - (y + θ * b) := by
    dsimp only [segmentDistance]; ring
  have hl : segmentDistance (a + y) (-b) θ = a + (y + θ * b) := by
    dsimp only [segmentDistance]; ring
  have hp : incrementProfile (a + y) (a + z) T (-b) = incrementProfile (a + y) (a + z) T b := by
    simp only [incrementProfile, abs_neg]
  rw [hd1, hu] at h1
  rw [he, hd2, hl, abs_neg, abs_neg, hp] at h2
  calc
    _ = (1 / Real.sqrt (segmentEnergy T b θ)) ^ r *
        (1 + |z - (y + θ * b)| / Real.sqrt (segmentEnergy T b θ)) ^ j *
          Real.exp (-(a - (y + θ * b)) * (a - z) / segmentEnergy T b θ) +
      (1 / Real.sqrt (segmentEnergy T b θ)) ^ r *
        (1 + |z - (y + θ * b)| / Real.sqrt (segmentEnergy T b θ)) ^ j *
          Real.exp (-(a + (y + θ * b)) * (a + z) / segmentEnergy T b θ) := by
      dsimp only [intervalProfile, upperProfile, lowerProfile]
      ring
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by dsimp only [intervalIncrementProfile]; ring

theorem mixed_scale_inv_sqrt (j l : ℕ) (d T : ℝ) (hT : 0 < T) :
    (4 / Real.sqrt T * (1 + |d| / Real.sqrt T)) ^ j / T ^ l =
      (4 : ℝ) ^ j * (1 / Real.sqrt T) ^ (j + 2 * l) * (1 + |d| / Real.sqrt T) ^ j := by
  have htwo : (1 / Real.sqrt T) ^ 2 = 1 / T := by
    rw [one_div_pow, Real.sq_sqrt hT.le]
  rw [pow_add, pow_mul, htwo]
  simp only [mul_pow, div_pow, one_div_pow, one_pow]
  ring

theorem mixedImageCandidate_segment_smallTime_profile (j l : ℕ) (a y z T b θ : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hTime : T ≤ a ^ 2)
    (hnew : |y + b| ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    |mixedImageCandidate j l a z (segmentEnergy T b θ) (y + θ * b) -
      (if j = 0 ∧ l = 0 then 1 else 0)| ≤
    (4 * (4 : ℝ) ^ j * mixedTimeConstant j l * (2 : ℝ) ^ (j + 2 * l) * (3 : ℝ) ^ j) *
      (1 / Real.sqrt T) ^ (j + 2 * l) * (1 + |z - y| / Real.sqrt T) ^ j *
      intervalIncrementProfile a y T z b := by
  have hS := segment_energy_bounds T b θ hT hsmall hθ0 hθ1
  have hyS := segment_space_closed a y b θ hy hnew hθ0 hθ1
  have hP := mixedImageCandidate_smallTime_profile j l a z (segmentEnergy T b θ) (y + θ * b)
    hl ha hz hS.1 hyS (hS.2.2.trans hTime)
  have htrans := interval_segment_profile_transport a y z T b θ (j + 2 * l) j
    hy hz hT hsmall hnew hθ0 hθ1
  have hC : 0 ≤ 4 * (4 : ℝ) ^ j * mixedTimeConstant j l :=
    mul_nonneg (by positivity) (mixedTimeConstant_nonneg j l)
  calc
    _ ≤ 4 * (4 / Real.sqrt (segmentEnergy T b θ) *
        (1 + |z - (y + θ * b)| / Real.sqrt (segmentEnergy T b θ))) ^ j *
        mixedTimeConstant j l / (segmentEnergy T b θ) ^ l *
        intervalProfile a (y + θ * b) (segmentEnergy T b θ) z := hP
    _ = (4 * (4 : ℝ) ^ j * mixedTimeConstant j l) *
      ((1 / Real.sqrt (segmentEnergy T b θ)) ^ (j + 2 * l) *
        (1 + |z - (y + θ * b)| / Real.sqrt (segmentEnergy T b θ)) ^ j *
          intervalProfile a (y + θ * b) (segmentEnergy T b θ) z) := by
      have he := mixed_scale_inv_sqrt j l (z - (y + θ * b)) (segmentEnergy T b θ) hS.1
      calc
        _ = 4 * mixedTimeConstant j l *
          ((4 / Real.sqrt (segmentEnergy T b θ) *
            (1 + |z - (y + θ * b)| / Real.sqrt (segmentEnergy T b θ))) ^ j /
            (segmentEnergy T b θ) ^ l) * intervalProfile a (y + θ * b) (segmentEnergy T b θ) z := by ring
        _ = _ := by rw [he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htrans hC
    _ = _ := by ring

theorem intervalImageCandidate_segment_mixed_smallTime_profile (j l : ℕ) (a y z T b θ : ℝ)
    (hl : l ≤ 3) (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hTime : T ≤ a ^ 2)
    (hnew : |y + b| ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    |iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) (y + θ * b))
      (segmentEnergy T b θ) - (if j = 0 ∧ l = 0 then 1 else 0)| ≤
    (4 * (4 : ℝ) ^ j * mixedTimeConstant j l * (2 : ℝ) ^ (j + 2 * l) * (3 : ℝ) ^ j) *
      (1 / Real.sqrt T) ^ (j + 2 * l) * (1 + |z - y| / Real.sqrt T) ^ j *
      intervalIncrementProfile a y T z b := by
  have hS := segment_energy_bounds T b θ hT hsmall hθ0 hθ1.le
  have hyS := segment_space_interior a y b θ hy hnew hθ0 hθ1
  rw [intervalImageCandidate_mixed_iteratedDeriv j l a z (segmentEnergy T b θ) (y + θ * b)
    hl ha hz hS.1 hyS]
  exact mixedImageCandidate_segment_smallTime_profile j l a y z T b θ
    hl ha hy hz hT hsmall hTime hnew hθ0 hθ1.le

end Shao.C2.IntervalImageTaylorSegment

