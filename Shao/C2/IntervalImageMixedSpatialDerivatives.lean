import Shao.C2.IntervalImageJointContinuity

noncomputable section
namespace Shao.C2.IntervalImageMixedSpatialDerivatives
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageExponents Shao.C2.IntervalImageSpatialProfiles
open Shao.C2.IntervalImageSpatialConvergence Shao.C2.IntervalImageSpatialDerivatives
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageIntSeries
open Shao.C2.IntervalImageTimeDerivatives Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageTimeProfiles Shao.C2.IntervalImageHigherTime Shao.C2.IntervalImageMixedTerms
open Shao.C2.IntervalImageMixedConvergence Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageMixedIntSeries Shao.C2.IntervalImageMixedTraces
open Shao.C2.IntervalImageJointContinuity

theorem affineSpatial_mixed_hasDerivAt (j l : ℕ) (c k T y : ℝ) (hl : l ≤ 3) (hT : 0 < T) :
    HasDerivAt (fun w => iteratedDeriv l (fun S => iteratedDeriv j (affineImageTerm c k S) w) T)
      (iteratedDeriv l (fun S => iteratedDeriv (j + 1) (affineImageTerm c k S) y) T) y := by
  have hC : HasDerivAt (fun w : ℝ => c * w + k) c y :=
    by simpa only [id_eq, mul_one] using ((hasDerivAt_id y).const_mul c).add_const k
  have hE := ((hC.neg).div_const T).exp
  have hQ := hC.div_const T
  have hcases : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa only [iteratedDeriv_zero] using affineImageTerm_iterated_hasDerivAt j c k T y
  · have hv (i : ℕ) (w : ℝ) : iteratedDeriv 1
        (fun S => iteratedDeriv i (affineImageTerm c k S) w) T = affineSpatialTimeSlope i c k w T := by
      rw [iteratedDeriv_succ, iteratedDeriv_zero]
      exact (affineSpatial_time_hasDerivAt i c k w T hT).deriv
    have hf : (fun w => iteratedDeriv 1 (fun S => iteratedDeriv j (affineImageTerm c k S) w) T) =
        (fun w => affineSpatialTimeSlope j c k w T) := by
      funext w
      exact hv j w
    rw [hf, hv (j + 1) y]
    have hP := (hC.div_const (T ^ 2)).sub_const ((j : ℝ) / T)
    have hd := (hP.mul_const ((-c / T) ^ j)).mul hE
    convert hd using 1 <;>
      (try funext w) <;>
      (try dsimp only [affineSpatialTimeSlope, Pi.pow_apply, Pi.mul_apply, Pi.div_apply,
        Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]) <;>
      simp only [Nat.cast_add, Nat.cast_one, pow_succ] <;>
      field_simp [ne_of_gt hT] <;> ring
  · have hv (i : ℕ) (w : ℝ) : iteratedDeriv 2
        (fun S => iteratedDeriv i (affineImageTerm c k S) w) T = affineSpatialTimeSecond i c k w T := by
      exact affineSpatial_time_iteratedDeriv_two i c k w T hT
    have hf : (fun w => iteratedDeriv 2 (fun S => iteratedDeriv j (affineImageTerm c k S) w) T) =
        (fun w => affineSpatialTimeSecond j c k w T) := by
      funext w
      exact hv j w
    rw [hf, hv (j + 1) y]
    have hP := (((hQ.pow 2).sub (hQ.const_mul (2 * ((j : ℝ) + 1)))).add_const ((j : ℝ) * ((j : ℝ) + 1))).div_const (T ^ 2)
    have hd := (hP.mul_const ((-c / T) ^ j)).mul hE
    convert hd using 1 <;>
      (try funext w) <;>
      (try dsimp only [affineSpatialTimeSecond, Pi.pow_apply, Pi.mul_apply, Pi.div_apply,
        Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]) <;>
      simp only [Nat.cast_add, Nat.cast_one, pow_succ] <;>
      field_simp [ne_of_gt hT] <;> ring
  · have hv (i : ℕ) (w : ℝ) : iteratedDeriv 3
        (fun S => iteratedDeriv i (affineImageTerm c k S) w) T = affineSpatialTimeThird i c k w T := by
      exact affineSpatial_time_iteratedDeriv_three i c k w T hT
    have hf : (fun w => iteratedDeriv 3 (fun S => iteratedDeriv j (affineImageTerm c k S) w) T) =
        (fun w => affineSpatialTimeThird j c k w T) := by
      funext w
      exact hv j w
    rw [hf, hv (j + 1) y]
    have hP := ((((hQ.pow 3).sub ((hQ.pow 2).const_mul (3 * ((j : ℝ) + 2)))).add (hQ.const_mul (3 * ((j : ℝ) + 1) * ((j : ℝ) + 2)))).sub_const ((j : ℝ) * ((j : ℝ) + 1) * ((j : ℝ) + 2))).div_const (T ^ 3)
    have hd := (hP.mul_const ((-c / T) ^ j)).mul hE
    convert hd using 1 <;>
      (try funext w) <;>
      (try dsimp only [affineSpatialTimeThird, Pi.pow_apply, Pi.mul_apply, Pi.div_apply,
        Pi.add_apply, Pi.sub_apply, Pi.neg_apply, id_eq]) <;>
      simp only [Nat.cast_add, Nat.cast_one, pow_succ] <;>
      field_simp [ne_of_gt hT] <;> ring

theorem mixedImageA_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ) (m : ℤ)
    (hl : l ≤ 3) (hT : 0 < T) :
    HasDerivAt (fun w => mixedImageA j l a z T w m) (mixedImageA (j + 1) l a z T y m) y := by
  let c : ℝ := -4 * (m : ℝ) * a
  let k : ℝ := 8 * (m : ℝ) ^ 2 * a ^ 2 + 4 * (m : ℝ) * a * z
  have hf (S : ℝ) : (fun w => Real.exp (-imageA a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageA, c, k]
    ring
  have hwhole (i : ℕ) (w : ℝ) : (fun S => spatialImageA i a z S w m) =
      (fun S => iteratedDeriv i (affineImageTerm c k S) w) := by
    funext S
    rw [spatialImageA, hf]
  have he (i : ℕ) : (fun w => mixedImageA i l a z T w m) =
      (fun w => iteratedDeriv l (fun S => iteratedDeriv i (affineImageTerm c k S) w) T) := by
    funext w
    rw [mixedImageA, hwhole]
  rw [he j, show mixedImageA (j + 1) l a z T y m = _ from congrFun (he (j + 1)) y]
  exact affineSpatial_mixed_hasDerivAt j l c k T y hl hT

theorem mixedImageB_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ) (m : ℤ)
    (hl : l ≤ 3) (hT : 0 < T) :
    HasDerivAt (fun w => mixedImageB j l a z T w m) (mixedImageB (j + 1) l a z T y m) y := by
  let c : ℝ := 2 * (z + (2 * (m : ℝ) + 1) * a)
  let k : ℝ := 2 * ((2 * (m : ℝ) + 1) * a) * (z + (2 * (m : ℝ) + 1) * a)
  have hf (S : ℝ) : (fun w => Real.exp (-imageB a w z (m : ℝ) / S)) =
      affineImageTerm c k S := by
    funext w
    dsimp only [affineImageTerm]
    congr 1
    dsimp only [imageB, c, k]
    ring
  have hwhole (i : ℕ) (w : ℝ) : (fun S => spatialImageB i a z S w m) =
      (fun S => iteratedDeriv i (affineImageTerm c k S) w) := by
    funext S
    rw [spatialImageB, hf]
  have he (i : ℕ) : (fun w => mixedImageB i l a z T w m) =
      (fun w => iteratedDeriv l (fun S => iteratedDeriv i (affineImageTerm c k S) w) T) := by
    funext w
    rw [mixedImageB, hwhole]
  rw [he j, show mixedImageB (j + 1) l a z T y m = _ from congrFun (he (j + 1)) y]
  exact affineSpatial_mixed_hasDerivAt j l c k T y hl hT

theorem mixedTailBlock_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ) (n : ℕ)
    (hl : l ≤ 3) (hT : 0 < T) :
    HasDerivAt (fun w => mixedTailBlock j l a z T w n) (mixedTailBlock (j + 1) l a z T y n) y := by
  exact (((mixedImageA_spatial_hasDerivAt j l a z T y ((n : ℤ) + 2) hl hT).add
    (mixedImageA_spatial_hasDerivAt j l a z T y (-((n : ℤ) + 2)) hl hT)).sub
    (mixedImageB_spatial_hasDerivAt j l a z T y ((n : ℤ) + 1) hl hT)).sub
    (mixedImageB_spatial_hasDerivAt j l a z T y (-((n : ℤ) + 2)) hl hT)

theorem mixedTailSum_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasDerivAt (mixedTailSum j l a z T) (mixedTailSum (j + 1) l a z T y) y := by
  have hyI : y ∈ Ioo (-a) a := abs_lt.mp hy
  have hu := (gaussianMajorant_summable a T ha hT).mul_left
    (4 * spatialPrefactor (j + 1) a T * mixedTimeConstant (j + 1) l / T ^ l)
  have hg : ∀ n w, w ∈ Ioo (-a) a → HasDerivAt
      (fun v => mixedTailBlock j l a z T v n) (mixedTailBlock (j + 1) l a z T w n) w := by
    intro n w _
    exact mixedTailBlock_spatial_hasDerivAt j l a z T w n hl hT
  have hg' : ∀ n w, w ∈ Ioo (-a) a → ‖mixedTailBlock (j + 1) l a z T w n‖ ≤
      (4 * spatialPrefactor (j + 1) a T * mixedTimeConstant (j + 1) l / T ^ l) *
        gaussianMajorant a T n := by
    intro n w hw
    exact mixedTailBlock_bound (j + 1) l a z T T n
      ⟨(w, T), (abs_lt.mpr hw).le, le_rfl, le_rfl⟩ hl ha hz hT le_rfl
  have hg0 := mixedTailBlock_summable j l a z T T
    ⟨(y, T), hy.le, le_rfl, le_rfl⟩ hl ha hz hT le_rfl
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hg hg' hyI hg0 hyI

theorem mixedFiniteImages_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ)
    (hl : l ≤ 3) (hT : 0 < T) :
    HasDerivAt (mixedFiniteImages j l a z T) (mixedFiniteImages (j + 1) l a z T y) y := by
  exact ((((mixedImageA_spatial_hasDerivAt j l a z T y 0 hl hT).add
    (mixedImageA_spatial_hasDerivAt j l a z T y 1 hl hT)).add
    (mixedImageA_spatial_hasDerivAt j l a z T y (-1) hl hT)).sub
    (mixedImageB_spatial_hasDerivAt j l a z T y 0 hl hT)).sub
    (mixedImageB_spatial_hasDerivAt j l a z T y (-1) hl hT)

theorem mixedImageCandidate_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasDerivAt (mixedImageCandidate j l a z T) (mixedImageCandidate (j + 1) l a z T y) y := by
  exact (mixedFiniteImages_spatial_hasDerivAt j l a z T y hl hT).add
    (mixedTailSum_spatial_hasDerivAt j l a z T y hl ha hz hT hy)

theorem intervalImageCandidate_mixed_spatial_hasDerivAt (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    HasDerivAt (fun w => iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) w) T)
      (iteratedDeriv l (fun S => iteratedDeriv (j + 1) (intervalImageCandidate a z S) y) T) y := by
  have heq : (fun w => iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) w) T)
      =ᶠ[𝓝 y] mixedImageCandidate j l a z T := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with w hw
    exact intervalImageCandidate_mixed_iteratedDeriv j l a z T w hl ha hz hT (abs_lt.mpr hw)
  rw [intervalImageCandidate_mixed_iteratedDeriv (j + 1) l a z T y hl ha hz hT hy]
  exact (mixedImageCandidate_spatial_hasDerivAt j l a z T y hl ha hz hT hy).congr_of_eventuallyEq heq

theorem intervalImageCandidate_mixed_commute (j l : ℕ) (a z T y : ℝ) (hl : l ≤ 3)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv j (fun w => iteratedDeriv l (fun S => intervalImageCandidate a z S w) T) y =
      iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) T := by
  induction j generalizing y with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (fun w => iteratedDeriv l (fun S => intervalImageCandidate a z S w) T)
        =ᶠ[𝓝 y] (fun w => iteratedDeriv l (fun S => iteratedDeriv j (intervalImageCandidate a z S) w) T) := by
      filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with w hw
      exact ih w (abs_lt.mpr hw)
    rw [heq.deriv_eq]
    exact (intervalImageCandidate_mixed_spatial_hasDerivAt j l a z T y hl ha hz hT hy).deriv

end Shao.C2.IntervalImageMixedSpatialDerivatives

