import Shao.C2.IntervalImageSineIdentity
import Shao.C2.IntervalImageJointDerivatives
import Shao.C2.IntervalSineHighTimeProfiles

noncomputable section
namespace Shao.C2.IntervalImageSineProfiles
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageSineIdentity Shao.C2.IntervalImageCandidateSpatial
open Shao.C2.IntervalImageMixedCandidate Shao.C2.IntervalImageMixedSpatialDerivatives
open Shao.C2.IntervalSineNormalizedDerivatives Shao.C2.IntervalSineNormalizedHighTime
open Shao.C2.IntervalSineHighTimeProfiles Shao.C2.CompletionFirstProfile

theorem intervalImageCandidate_spatial_eq_normalized (j : ℕ) (a z T y : ℝ)
    (hj : j ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    iteratedDeriv j (intervalImageCandidate a z T) y = normalizedMixedFamily j 0 a z T y := by
  have heq : intervalImageCandidate a z T =ᶠ[𝓝 y] normalizedSineCandidate a z T := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with w hw
    exact intervalImageCandidate_eq_normalizedSineCandidate a z T w ha hz hT (abs_lt.mpr hw).le
  exact (Filter.EventuallyEq.iteratedDeriv_eq j heq).trans
    (normalizedSineCandidate_spatial_iteratedDeriv j a z T y hj ha hT)

theorem mixedImageCandidate_eq_normalized (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    mixedImageCandidate j l a z T y = normalizedMixedFamily j l a z T y := by
  have hj : j ≤ 3 := by omega
  have heq : (fun S => iteratedDeriv j (intervalImageCandidate a z S) y) =ᶠ[𝓝 T]
      (fun S => iteratedDeriv j (normalizedSineCandidate a z S) y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    exact (intervalImageCandidate_spatial_eq_normalized j a z S y hj ha hz hS hy).trans
      (normalizedSineCandidate_spatial_iteratedDeriv j a z S y hj ha hS).symm
  rw [← intervalImageCandidate_mixed_iteratedDeriv j l a z T y (by omega) ha hz hT hy]
  exact (Filter.EventuallyEq.iteratedDeriv_eq l heq).trans
    (normalizedSineCandidate_mixed_iteratedDeriv j l a z T y hjl ha hT)

theorem mixedImageCandidate_highTime_bound (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T)
    (hlarge : a ^ 2 ≤ T) (hy : |y| < a) :
    ‖mixedImageCandidate j l a z T y‖ ≤
      normalizedDerivativeConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) := by
  rw [mixedImageCandidate_eq_normalized j l a z T y hjl ha hz hT hy]
  exact normalizedMixedFamily_highTime_bound j l a z T y hjl ha hT hlarge hy.le hz

theorem intervalImageCandidate_sub_one_highTime_profile (j l : ℕ) (a z T y : ℝ)
    (hjl : j + l ≤ 3) (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T)
    (hlarge : a ^ 2 ≤ T) (hy : |y| < a) :
    ‖iteratedDeriv l (fun S => iteratedDeriv j (fun w => intervalImageCandidate a z S w - 1) y) T‖ ≤
      normalizedProfileConstant j l * (1 / Real.sqrt T) ^ (j + 2 * l) *
        (1 + |z - y| / Real.sqrt T) ^ j * intervalProfile a y T z := by
  have heq : (fun S => iteratedDeriv j (fun w => intervalImageCandidate a z S w - 1) y) =ᶠ[𝓝 T]
      (fun S => iteratedDeriv j (fun w => normalizedSineCandidate a z S w - 1) y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with S hS
    apply Filter.EventuallyEq.iteratedDeriv_eq j
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hy)] with w hw
    rw [intervalImageCandidate_eq_normalizedSineCandidate a z S w ha hz hS (abs_lt.mpr hw).le]
  rw [Filter.EventuallyEq.iteratedDeriv_eq l heq]
  exact normalizedSineCandidate_sub_one_highTime_profile j l a z T y hjl ha hT hlarge hy.le hz

end Shao.C2.IntervalImageSineProfiles
