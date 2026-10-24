import Shao.C2.IntervalImageSineProfiles

noncomputable section
namespace Shao.C2.IntervalImageRevealDerivatives
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageJointDerivatives

def pathFirst (a z T y b θ : ℝ) : ℝ :=
  b * mixedImageCandidate 1 0 a z (T - θ * b ^ 2) (y + θ * b) -
    b ^ 2 * mixedImageCandidate 0 1 a z (T - θ * b ^ 2) (y + θ * b)

def pathSecond (a z T y b θ : ℝ) : ℝ :=
  b ^ 2 * mixedImageCandidate 2 0 a z (T - θ * b ^ 2) (y + θ * b) -
    2 * b ^ 3 * mixedImageCandidate 1 1 a z (T - θ * b ^ 2) (y + θ * b) +
      b ^ 4 * mixedImageCandidate 0 2 a z (T - θ * b ^ 2) (y + θ * b)

def pathThird (a z T y b θ : ℝ) : ℝ :=
  b ^ 3 * mixedImageCandidate 3 0 a z (T - θ * b ^ 2) (y + θ * b) -
    3 * b ^ 4 * mixedImageCandidate 2 1 a z (T - θ * b ^ 2) (y + θ * b) +
      3 * b ^ 5 * mixedImageCandidate 1 2 a z (T - θ * b ^ 2) (y + θ * b) -
        b ^ 6 * mixedImageCandidate 0 3 a z (T - θ * b ^ 2) (y + θ * b)

theorem pathFirst_hasDerivAt (a z T y b θ : ℝ) (ha : 0 < a) (hz : |z| ≤ a)
    (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    HasDerivAt (pathFirst a z T y b) (pathSecond a z T y b θ) θ := by
  have h10 := mixedImageCandidate_path_hasDerivAt 1 0 a z T y b θ (by norm_num) ha hz hS hy
  have h01 := mixedImageCandidate_path_hasDerivAt 0 1 a z T y b θ (by norm_num) ha hz hS hy
  have hd := (h10.const_mul b).sub (h01.const_mul (b ^ 2))
  convert hd using 1 <;> (try funext t) <;>
    simp only [pathFirst, pathSecond, Pi.sub_apply, Pi.mul_apply] <;> ring

theorem pathSecond_hasDerivAt (a z T y b θ : ℝ) (ha : 0 < a) (hz : |z| ≤ a)
    (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    HasDerivAt (pathSecond a z T y b) (pathThird a z T y b θ) θ := by
  have h20 := mixedImageCandidate_path_hasDerivAt 2 0 a z T y b θ (by norm_num) ha hz hS hy
  have h11 := mixedImageCandidate_path_hasDerivAt 1 1 a z T y b θ (by norm_num) ha hz hS hy
  have h02 := mixedImageCandidate_path_hasDerivAt 0 2 a z T y b θ (by norm_num) ha hz hS hy
  have hd := ((h20.const_mul (b ^ 2)).sub (h11.const_mul (2 * b ^ 3))).add (h02.const_mul (b ^ 4))
  convert hd using 1 <;> (try funext t) <;>
    simp only [pathSecond, pathThird, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] <;> ring

theorem intervalImageCandidate_path_iteratedDeriv_two (a z T y b θ : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    iteratedDeriv 2 (fun t : ℝ => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b)) θ =
      pathSecond a z T y b θ := by
  have hSnear : {t : ℝ | 0 < T - t * b ^ 2} ∈ 𝓝 θ := by
    have hc : Continuous (fun t : ℝ => T - t * b ^ 2) := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds hS
  have hynear : {t : ℝ | |y + t * b| < a} ∈ 𝓝 θ := by
    have hc : Continuous (fun t : ℝ => |y + t * b|) := by fun_prop
    exact (isOpen_lt hc continuous_const).mem_nhds hy
  have heq : deriv (fun t : ℝ => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b)) =ᶠ[𝓝 θ]
      pathFirst a z T y b := by
    filter_upwards [hSnear, hynear] with t hSt hyt
    have hd := intervalImageCandidate_mixed_path_hasDerivAt 0 0 a z T y b t (by norm_num) ha hz hSt hyt
    simpa only [iteratedDeriv_zero, pathFirst] using hd.deriv
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    heq.deriv_eq.trans (pathFirst_hasDerivAt a z T y b θ ha hz hS hy).deriv

theorem intervalImageCandidate_path_iteratedDeriv_three (a z T y b θ : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    iteratedDeriv 3 (fun t : ℝ => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b)) θ =
      pathThird a z T y b θ := by
  have hSnear : {t : ℝ | 0 < T - t * b ^ 2} ∈ 𝓝 θ := by
    have hc : Continuous (fun t : ℝ => T - t * b ^ 2) := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds hS
  have hynear : {t : ℝ | |y + t * b| < a} ∈ 𝓝 θ := by
    have hc : Continuous (fun t : ℝ => |y + t * b|) := by fun_prop
    exact (isOpen_lt hc continuous_const).mem_nhds hy
  have heq : iteratedDeriv 2 (fun t : ℝ => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b)) =ᶠ[𝓝 θ]
      pathSecond a z T y b := by
    filter_upwards [hSnear, hynear] with t hSt hyt
    exact intervalImageCandidate_path_iteratedDeriv_two a z T y b t ha hz hSt hyt
  simpa only [iteratedDeriv_succ] using
    heq.deriv_eq.trans (pathSecond_hasDerivAt a z T y b θ ha hz hS hy).deriv

end Shao.C2.IntervalImageRevealDerivatives
