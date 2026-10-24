import Shao.C2.ProjectionOvershoot
import Shao.C2.SourceIntervalCompletion

noncomputable section
namespace Shao.C2.ActualIntervalProjection
open MeasureTheory
open Shao.C2.BridgeDomination Shao.C2.SourceIntervalCompletion
open Shao.C2.ProjectionOvershoot

def sourceRemainder (ν : Measure BridgeNoise) (a y T z b : ℝ) : ℝ :=
  sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z - sourceIntervalCompletion ν a y T z -
    (b - b ^ 2 * (z - y) / T) * deriv (fun w => sourceIntervalCompletion ν a w T z) y

def upperOvershoot (ν : Measure BridgeNoise) (a y T z b : ℝ) : ℝ :=
  projectionOvershoot b (a - y) T (z - y)
    (deriv (fun w => sourceIntervalCompletion ν a w T z) y)

def lowerOvershoot (ν : Measure BridgeNoise) (a y T z b : ℝ) : ℝ :=
  projectionOvershoot (-b) (a + y) T (y - z)
    (-deriv (fun w => sourceIntervalCompletion ν a w T z) y)

theorem source_upper_projection_identity (ν : Measure BridgeNoise) (a y T z b : ℝ)
    (ha : 0 < a) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T)
    (hcross : a ≤ y + b)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion ν a w T z) y) :
    sourceRemainder ν a y T z b =
      sourceRemainder ν a y T z (a - y) + upperOvershoot ν a y T z b := by
  have hbf : sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).2
    linarith only [hcross, hh]
  have hpf : sourceIntervalCompletion ν a (y + (a - y)) (T - (a - y) ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).2
    linarith only [hh]
  dsimp only [sourceRemainder]
  rw [hbf, hpf]
  have hh := zero_future_remainder_projection_identity
    (sourceIntervalCompletion ν a y T z) b (a - y) T (z - y)
      (deriv (fun w => sourceIntervalCompletion ν a w T z) y)
  simpa only [zeroFutureRemainder, upperOvershoot, zero_sub] using hh

theorem source_lower_projection_identity (ν : Measure BridgeNoise) (a y T z b : ℝ)
    (ha : 0 < a) (hy : |y| < a) (hz : |z| < a) (hT : 0 < T)
    (hcross : y + b ≤ -a)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion ν a w T z) y) :
    sourceRemainder ν a y T z b =
      sourceRemainder ν a y T z (-a - y) + lowerOvershoot ν a y T z b := by
  have hbf : sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).1
    linarith only [hcross, hh]
  have hpf : sourceIntervalCompletion ν a (y + (-a - y)) (T - (-a - y) ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).1
    linarith only [hh]
  dsimp only [sourceRemainder, lowerOvershoot]
  rw [hbf, hpf]
  have hh := zero_future_remainder_projection_identity
    (sourceIntervalCompletion ν a y T z) (-b) (a + y) T (y - z)
      (-deriv (fun w => sourceIntervalCompletion ν a w T z) y)
  dsimp only [zeroFutureRemainder] at hh
  convert hh using 1 <;> ring

theorem source_upper_projection_negative_budget (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b K : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| < a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hcross : a ≤ y + b) (hK : 0 ≤ K)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion ν a w T z) y)
    (hProjected : |sourceRemainder ν a y T z (a - y)| ≤ K * |a - y| ^ 3) :
    |sourceRemainder ν a y T z (a - y)| + max (-upperOvershoot ν a y T z b) 0 ≤
        K * (a - y) * b ^ 2 ∧
      K * (a - y) * b ^ 2 ≤ K * |b| ^ 3 := by
  have hbf : sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).2
    linarith only [hcross, hh]
  have hpf : sourceIntervalCompletion ν a (y + (a - y)) (T - (a - y) ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).2
    linarith only [hh]
  have hu : 0 < a - y := by linarith only [(abs_lt.mp hy).2]
  have huB : a - y ≤ b := by linarith only [hcross]
  have hbpos : 0 < b := hu.trans_le huB
  have he : z - y < a - y := by linarith only [(abs_lt.mp hz).2]
  have hRu : sourceRemainder ν a y T z (a - y) =
      zeroFutureRemainder (sourceIntervalCompletion ν a y T z) (a - y) T (z - y)
        (deriv (fun w => sourceIntervalCompletion ν a w T z) y) := by
    simp only [sourceRemainder, hpf, zero_sub, zeroFutureRemainder]
  have hp : |zeroFutureRemainder (sourceIntervalCompletion ν a y T z) (a - y) T (z - y)
      (deriv (fun w => sourceIntervalCompletion ν a w T z) y)| ≤ K * (a - y) ^ 3 := by
    rw [← hRu]
    simpa only [abs_of_pos hu] using hProjected
  have hF := (sourceIntervalCompletion_bounds ν a y T z).1
  have hh := projection_own_negative_budget (sourceIntervalCompletion ν a y T z)
    b (a - y) T (z - y) (deriv (fun w => sourceIntervalCompletion ν a w T z) y) K
      hF hK hu huB hT hsmall he hp
  rw [← hRu] at hh
  simpa only [upperOvershoot, abs_of_pos hbpos] using hh

theorem source_lower_projection_negative_budget (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (a y T z b K : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| < a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hcross : y + b ≤ -a) (hK : 0 ≤ K)
    (hRegular : DifferentiableAt ℝ (fun w => sourceIntervalCompletion ν a w T z) y)
    (hProjected : |sourceRemainder ν a y T z (-a - y)| ≤ K * |-a - y| ^ 3) :
    |sourceRemainder ν a y T z (-a - y)| + max (-lowerOvershoot ν a y T z b) 0 ≤
        K * (a + y) * b ^ 2 ∧
      K * (a + y) * b ^ 2 ≤ K * |b| ^ 3 := by
  have hbf : sourceIntervalCompletion ν a (y + b) (T - b ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).1
    linarith only [hcross, hh]
  have hpf : sourceIntervalCompletion ν a (y + (-a - y)) (T - (-a - y) ^ 2) z = 0 := by
    apply sourceIntervalCompletion_exterior
    intro h
    have hh := (abs_lt.mp h.1).1
    linarith only [hh]
  have hu : 0 < a + y := by linarith only [(abs_lt.mp hy).1]
  have huB : a + y ≤ -b := by linarith only [hcross]
  have hbneg : b < 0 := by linarith only [hu, huB]
  have he : y - z < a + y := by linarith only [(abs_lt.mp hz).1]
  have hRu : sourceRemainder ν a y T z (-a - y) =
      zeroFutureRemainder (sourceIntervalCompletion ν a y T z) (a + y) T (y - z)
        (-deriv (fun w => sourceIntervalCompletion ν a w T z) y) := by
    simp only [sourceRemainder, hpf, zero_sub, zeroFutureRemainder]
    ring
  have hpabs : |-a - y| = a + y := by
    rw [abs_of_neg (by linarith only [hu] : -a - y < 0)]
    ring
  have hp : |zeroFutureRemainder (sourceIntervalCompletion ν a y T z) (a + y) T (y - z)
      (-deriv (fun w => sourceIntervalCompletion ν a w T z) y)| ≤ K * (a + y) ^ 3 := by
    rw [← hRu]
    simpa only [hpabs] using hProjected
  have hF := (sourceIntervalCompletion_bounds ν a y T z).1
  have hh := projection_own_negative_budget (sourceIntervalCompletion ν a y T z)
    (-b) (a + y) T (y - z) (-deriv (fun w => sourceIntervalCompletion ν a w T z) y) K
      hF hK hu huB hT (by simpa only [neg_sq] using hsmall) he hp
  rw [← hRu, neg_sq] at hh
  simpa only [lowerOvershoot, abs_of_neg hbneg] using hh

end Shao.C2.ActualIntervalProjection
