import Shao.C2.IntervalImageRevealBounds

noncomputable section
namespace Shao.C2.IntervalImageWallLimit
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageJointContinuity Shao.C2.IntervalImageTaylorSegment
open Shao.C2.IntervalImageRevealBounds Shao.C2.IntervalGaussianLocal

theorem intervalImageCandidate_joint_continuousOn (a z H U : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hH : 0 < H) (hHU : H ≤ U) :
    ContinuousOn (fun p : ℝ × ℝ => intervalImageCandidate a z p.2 p.1)
      (Icc (-a) a ×ˢ Icc H U) := by
  have heq : (fun p : ℝ × ℝ => intervalImageCandidate a z p.2 p.1) =
      (fun p : ℝ × ℝ => mixedImageCandidate 0 0 a z p.2 p.1) := by
    funext p
    exact (mixedImageCandidate_zero 0 a z p.2 p.1).symm
  rw [heq]
  exact mixedImageCandidate_joint_continuousOn 0 0 a z H U (by norm_num) ha hz hH hHU

theorem intervalImageCandidate_scaled_step_continuousOn (a y z T b : ℝ)
    (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a) :
    ContinuousOn (fun θ : ℝ => intervalImageCandidate a z (T - (θ * b) ^ 2) (y + θ * b))
      (Icc (0 : ℝ) 1) := by
  have hc := intervalImageCandidate_joint_continuousOn a z (T / 2) T ha hz
    (by linarith only [hT]) (by linarith only [hT])
  have hp : ContinuousOn (fun θ : ℝ => (y + θ * b, T - (θ * b) ^ 2)) (Icc (0 : ℝ) 1) := by
    fun_prop
  apply hc.comp hp
  intro θ hθ
  have hyθ := segment_space_closed a y b θ hy hnew hθ.1 hθ.2
  have hθsq : θ ^ 2 ≤ 1 := by nlinarith only [hθ.1, hθ.2]
  have hbθ : (θ * b) ^ 2 ≤ b ^ 2 := by
    calc
      _ = θ ^ 2 * b ^ 2 := mul_pow θ b 2
      _ ≤ 1 * b ^ 2 := mul_le_mul_of_nonneg_right hθsq (sq_nonneg b)
      _ = _ := one_mul _
  exact ⟨abs_le.mp hyθ, by nlinarith only [hbθ, hsmall], by nlinarith only [sq_nonneg (θ * b)]⟩

theorem intervalImageCandidate_compensated_small_step_closed_bound (a y z T b : ℝ)
    (ha : 0 < a) (hy : |y| < a) (hz : |z| ≤ a)
    (hT : 0 < T) (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| ≤ a) :
    |intervalImageCandidate a z (T - b ^ 2) (y + b) - intervalImageCandidate a z T y -
        (b - b ^ 2 * (z - y) / T) * deriv (intervalImageCandidate a z T) y| ≤
      compensatedProfileConstant * (|b| / Real.sqrt T) ^ 3 *
        (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z b := by
  let L : ℝ → ℝ := fun θ =>
    |intervalImageCandidate a z (T - (θ * b) ^ 2) (y + θ * b) - intervalImageCandidate a z T y -
      (θ * b - (θ * b) ^ 2 * (z - y) / T) * deriv (intervalImageCandidate a z T) y|
  let R : ℝ → ℝ := fun θ => compensatedProfileConstant * (|θ * b| / Real.sqrt T) ^ 3 *
    (1 + |z - y| / Real.sqrt T) ^ 3 * intervalIncrementProfile a y T z (θ * b)
  have hFc := intervalImageCandidate_scaled_step_continuousOn a y z T b ha hy hz hT hsmall hnew
  have hpoly : ContinuousOn (fun θ : ℝ =>
      (θ * b - (θ * b) ^ 2 * (z - y) / T) * deriv (intervalImageCandidate a z T) y)
      (Icc (0 : ℝ) 1) := by fun_prop
  have hL : ContinuousOn L (Icc (0 : ℝ) 1) := by
    exact ((hFc.sub continuousOn_const).sub hpoly).abs
  have hR : Continuous R := by
    dsimp only [R, intervalIncrementProfile, Shao.C2.HalfLineTaylorSegment.incrementProfile]
    fun_prop
  have hm : ∀ᶠ θ : ℝ in 𝓝[<] (1 : ℝ), θ ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with θ hθ
    exact ⟨hθ.1.le, hθ.2.le⟩
  have ht : Tendsto (fun θ : ℝ => θ) (𝓝[<] (1 : ℝ)) (𝓝[Icc (0 : ℝ) 1] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_id.mono_left nhdsWithin_le_nhds, hm⟩
  have hL0 : Tendsto L (𝓝[Icc (0 : ℝ) 1] (1 : ℝ)) (𝓝 (L 1)) :=
    hL 1 ⟨by norm_num, by norm_num⟩
  have hR0 : Tendsto R (𝓝 (1 : ℝ)) (𝓝 (R 1)) := hR.continuousAt
  have hineq : L ≤ᶠ[𝓝[<] (1 : ℝ)] R := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with θ hθ
    have hθsq : θ ^ 2 ≤ 1 := by nlinarith only [hθ.1.le, hθ.2.le]
    have hbθ : (θ * b) ^ 2 ≤ b ^ 2 := by
      calc
        _ = θ ^ 2 * b ^ 2 := mul_pow θ b 2
        _ ≤ 1 * b ^ 2 := mul_le_mul_of_nonneg_right hθsq (sq_nonneg b)
        _ = _ := one_mul _
    exact intervalImageCandidate_compensated_small_step_bound a y z T (θ * b) ha hy hz hT
      (hbθ.trans hsmall) (segment_space_interior a y b θ hy hnew hθ.1.le hθ.2)
  have hfinal := le_of_tendsto_of_tendsto (hL0.comp ht) (hR0.mono_left nhdsWithin_le_nhds) hineq
  simpa only [L, R, one_mul] using hfinal

end Shao.C2.IntervalImageWallLimit
