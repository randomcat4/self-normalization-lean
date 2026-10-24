import Shao.C2.IntervalImageRevealDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
namespace Shao.C2.IntervalImageRevealRegularity
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageLocalRegularity Shao.C2.IntervalImageCandidatePDE
open Shao.C2.IntervalImageRevealDerivatives Shao.C2.IntervalImageJointDerivatives

private theorem contDiffOn_succ_of_hasDerivAt (n : ℕ) (f g : ℝ → ℝ) (s : Set ℝ)
    (hs : IsOpen s) (hd : ∀ x ∈ s, HasDerivAt f (g x) x) (hg : ContDiffOn ℝ n g s) :
    ContDiffOn ℝ (n + 1 : ℕ) f s := by
  have hD : DifferentiableOn ℝ f s := fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hg' : ContDiffOn ℝ n (deriv f) s := hg.congr fun x hx => (hd x hx).deriv
  simpa only [Nat.cast_add, Nat.cast_one] using
    (contDiffOn_succ_iff_deriv_of_isOpen (n := n) hs).2 ⟨hD, by simp, hg'⟩

theorem pathThird_continuousAt (a z T y b θ : ℝ) (ha : 0 < a) (hz : |z| ≤ a)
    (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    ContinuousAt (pathThird a z T y b) θ := by
  have hp : ContinuousAt (fun t : ℝ => (y + t * b, T - t * b ^ 2)) θ := by fun_prop
  have hM (j l : ℕ) (hl : l ≤ 3) : ContinuousAt
      (fun t : ℝ => mixedImageCandidate j l a z (T - t * b ^ 2) (y + t * b)) θ :=
    (mixedImageCandidate_continuousAt j l a z (T - θ * b ^ 2) (y + θ * b) hl ha hz hS hy).comp (f := fun t : ℝ => (y + t * b, T - t * b ^ 2)) (x := θ) hp
  unfold pathThird
  exact ((((hM 3 0 (by norm_num)).const_mul (b ^ 3)).sub
    ((hM 2 1 (by norm_num)).const_mul (3 * b ^ 4))).add
      ((hM 1 2 (by norm_num)).const_mul (3 * b ^ 5))).sub
        ((hM 0 3 (by norm_num)).const_mul (b ^ 6))

theorem intervalImageCandidate_path_contDiffAt_three (a z T y b θ : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hS : 0 < T - θ * b ^ 2) (hy : |y + θ * b| < a) :
    ContDiffAt ℝ (3 : ℕ)
      (fun t : ℝ => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b)) θ := by
  let U : Set ℝ := {t | 0 < T - t * b ^ 2 ∧ |y + t * b| < a}
  let f : ℝ → ℝ := fun t => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b)
  have hU : IsOpen U := by
    have hct : Continuous (fun t : ℝ => T - t * b ^ 2) := by fun_prop
    have hcy : Continuous (fun t : ℝ => |y + t * b|) := by fun_prop
    exact (isOpen_lt continuous_const hct).inter (isOpen_lt hcy continuous_const)
  have hD0 : ∀ t ∈ U, HasDerivAt f (pathFirst a z T y b t) t := by
    intro t ht
    simpa only [f, pathFirst, iteratedDeriv_zero] using
      intervalImageCandidate_mixed_path_hasDerivAt 0 0 a z T y b t (by norm_num) ha hz ht.1 ht.2
  have hD1 : ∀ t ∈ U, HasDerivAt (pathFirst a z T y b) (pathSecond a z T y b t) t :=
    fun t ht => pathFirst_hasDerivAt a z T y b t ha hz ht.1 ht.2
  have hD2 : ∀ t ∈ U, HasDerivAt (pathSecond a z T y b) (pathThird a z T y b t) t :=
    fun t ht => pathSecond_hasDerivAt a z T y b t ha hz ht.1 ht.2
  have hC3 : ContDiffOn ℝ (0 : ℕ) (pathThird a z T y b) U := by
    apply contDiffOn_zero.2
    intro t ht
    exact (pathThird_continuousAt a z T y b t ha hz ht.1 ht.2).continuousWithinAt
  have hC2 := contDiffOn_succ_of_hasDerivAt 0 (pathSecond a z T y b) (pathThird a z T y b) U hU hD2 hC3
  have hC1 := contDiffOn_succ_of_hasDerivAt 1 (pathFirst a z T y b) (pathSecond a z T y b) U hU hD1 hC2
  have hC0 := contDiffOn_succ_of_hasDerivAt 2 f (pathFirst a z T y b) U hU hD0 hC1
  exact (hC0 θ ⟨hS, hy⟩).contDiffAt (hU.mem_nhds ⟨hS, hy⟩)

theorem mixedImageCandidate_base_PDE (a z T y : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    mixedImageCandidate 0 1 a z T y =
      (1 / 2 : ℝ) * mixedImageCandidate 2 0 a z T y +
        (z - y) / T * mixedImageCandidate 1 0 a z T y := by
  have h01 : deriv (fun S => intervalImageCandidate a z S y) T = mixedImageCandidate 0 1 a z T y := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      intervalImageCandidate_mixed_iteratedDeriv 0 1 a z T y (by norm_num) ha hz hT hy
  have h20 : iteratedDeriv 2 (intervalImageCandidate a z T) y = mixedImageCandidate 2 0 a z T y := by
    simpa only [iteratedDeriv_zero] using
      intervalImageCandidate_mixed_iteratedDeriv 2 0 a z T y (by norm_num) ha hz hT hy
  have h10 : iteratedDeriv 1 (intervalImageCandidate a z T) y = mixedImageCandidate 1 0 a z T y := by
    simpa only [iteratedDeriv_zero] using
      intervalImageCandidate_mixed_iteratedDeriv 1 0 a z T y (by norm_num) ha hz hT hy
  have heq := (intervalImageCandidate_time_hasDerivAt a z T y ha hz hT hy).deriv
  rw [h01, h20, h10] at heq
  exact heq

theorem compensated_second_taylor_identity (a z T y b : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a) :
    pathFirst a z T y b 0 + (1 / 2 : ℝ) * pathSecond a z T y b 0 -
      (b - b ^ 2 * (z - y) / T) * mixedImageCandidate 1 0 a z T y =
      -b ^ 3 * mixedImageCandidate 1 1 a z T y +
        (1 / 2 : ℝ) * b ^ 4 * mixedImageCandidate 0 2 a z T y := by
  unfold pathFirst pathSecond
  simp only [zero_mul, sub_zero, add_zero]
  rw [mixedImageCandidate_base_PDE a z T y ha hz hT hy]
  ring

end Shao.C2.IntervalImageRevealRegularity
