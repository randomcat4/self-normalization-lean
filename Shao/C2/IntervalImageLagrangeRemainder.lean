import Shao.C2.IntervalImageRevealRegularity
import Shao.C2.IntervalImageTaylorSegment
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
namespace Shao.C2.IntervalImageLagrangeRemainder
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Shao.C2.IntervalImageCandidateSpatial Shao.C2.IntervalImageMixedCandidate
open Shao.C2.IntervalImageRevealDerivatives Shao.C2.IntervalImageRevealRegularity
open Shao.C2.IntervalImageTaylorSegment Shao.C2.HalfLineTaylorSegment
open Shao.C2.IntervalImageJointDerivatives

theorem segment_space_strict (a y b θ : ℝ) (hy : |y| < a) (hnew : |y + b| < a)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : |y + θ * b| < a := by
  rcases lt_or_eq_of_le hθ1 with hlt | heq
  · exact segment_space_interior a y b θ hy hnew.le hθ0 hlt
  · simpa only [heq, one_mul] using hnew

theorem intervalImageCandidate_path_contDiffOn_three (a z T y b : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a)
    (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| < a) :
    ContDiffOn ℝ (3 : ℕ)
      (fun t : ℝ => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b))
      (Icc (0 : ℝ) 1) := by
  intro t ht
  have hE := (segment_energy_bounds T b t hT hsmall ht.1 ht.2).1
  have hY := segment_space_strict a y b t hy hnew ht.1 ht.2
  exact (intervalImageCandidate_path_contDiffAt_three a z T y b t ha hz hE hY).contDiffWithinAt

theorem compensated_lagrange_remainder (a z T y b : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hT : 0 < T) (hy : |y| < a)
    (hsmall : b ^ 2 ≤ T / 2) (hnew : |y + b| < a) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      intervalImageCandidate a z (T - b ^ 2) (y + b) - intervalImageCandidate a z T y -
          (b - b ^ 2 * (z - y) / T) * deriv (intervalImageCandidate a z T) y =
        (1 / 6 : ℝ) * pathThird a z T y b θ -
          b ^ 3 * mixedImageCandidate 1 1 a z T y +
            (1 / 2 : ℝ) * b ^ 4 * mixedImageCandidate 0 2 a z T y := by
  let g : ℝ → ℝ := fun t => intervalImageCandidate a z (T - t * b ^ 2) (y + t * b)
  have hzero : (0 : ℝ) ≠ 1 := by norm_num
  have hle : (0 : ℝ) ≤ 1 := by norm_num
  have hf : ContDiffOn ℝ (3 : ℕ) g (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le hle, g] using
      intervalImageCandidate_path_contDiffOn_three a z T y b ha hz hT hy hsmall hnew
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc hzero
  have hz0 : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := by simp
  have hC0 : ContDiffAt ℝ (3 : ℕ) g 0 := by
    simpa only [g, zero_mul, sub_zero, add_zero] using
      intervalImageCandidate_path_contDiffAt_three a z T y b 0 ha hz
        (by simpa only [zero_mul, sub_zero] using hT)
        (by simpa only [zero_mul, add_zero] using hy)
  have hiter (n : ℕ) (hn : n ≤ 3) :
      iteratedDerivWithin n g (uIcc (0 : ℝ) 1) 0 = iteratedDeriv n g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu (hC0.of_le (by exact_mod_cast hn)) hz0
  have hpoly : taylorWithinEval g 2 (uIcc (0 : ℝ) 1) 0 1 =
      g 0 + deriv g 0 + (1 / 2 : ℝ) * deriv (deriv g) 0 := by
    simp only [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hiter 0 (by norm_num), hiter 1 (by norm_num), hiter 2 (by norm_num)]
    norm_num [iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
    <;> ring
  obtain ⟨θ, hθ, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hzero hf
  have hθ' : θ ∈ Ioo (0 : ℝ) 1 := by
    simpa only [uIoo_of_lt (by norm_num : (0 : ℝ) < 1)] using hθ
  have hE := (segment_energy_bounds T b θ hT hsmall hθ'.1.le hθ'.2.le).1
  have hY := segment_space_strict a y b θ hy hnew hθ'.1.le hθ'.2.le
  have h3 : iteratedDeriv 3 g θ = pathThird a z T y b θ :=
    intervalImageCandidate_path_iteratedDeriv_three a z T y b θ ha hz hE hY
  rw [hpoly, h3] at hrem
  norm_num at hrem
  have h1 : deriv g 0 = pathFirst a z T y b 0 := by
    simpa only [g, pathFirst, iteratedDeriv_zero] using
      (intervalImageCandidate_mixed_path_hasDerivAt 0 0 a z T y b 0 (by norm_num) ha hz
        (by simpa only [zero_mul, sub_zero] using hT)
        (by simpa only [zero_mul, add_zero] using hy)).deriv
  have h2 : deriv (deriv g) 0 = pathSecond a z T y b 0 := by
    simpa only [g, iteratedDeriv_succ, iteratedDeriv_zero] using
      intervalImageCandidate_path_iteratedDeriv_two a z T y b 0 ha hz
        (by simpa only [zero_mul, sub_zero] using hT)
        (by simpa only [zero_mul, add_zero] using hy)
  have h10 : deriv (intervalImageCandidate a z T) y = mixedImageCandidate 1 0 a z T y := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      intervalImageCandidate_mixed_iteratedDeriv 1 0 a z T y (by norm_num) ha hz hT hy
  have hc := compensated_second_taylor_identity a z T y b ha hz hT hy
  rw [← h1, ← h2, ← h10] at hc
  have hfinal : g 1 - g 0 - (b - b ^ 2 * (z - y) / T) *
      deriv (intervalImageCandidate a z T) y =
      (1 / 6 : ℝ) * pathThird a z T y b θ - b ^ 3 * mixedImageCandidate 1 1 a z T y +
        (1 / 2 : ℝ) * b ^ 4 * mixedImageCandidate 0 2 a z T y := by
    linarith only [hrem, hc]
  refine ⟨θ, hθ', ?_⟩
  simpa only [g, one_mul, zero_mul, sub_zero, add_zero] using hfinal

end Shao.C2.IntervalImageLagrangeRemainder
