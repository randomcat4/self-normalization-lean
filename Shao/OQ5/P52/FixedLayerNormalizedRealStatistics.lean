import Shao.OQ5.P52.FixedLayerRealStatistics
import Shao.OQ5.P52.FixedLayerRealNormalization

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

def fixedNormalizedRealSampleU {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedNormalizedRealKernel (x i, x k))

def fixedNormalizedRealSampleRowMean {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Shao.OQ6.FiniteRows.rowMean (fun a b => fixedNormalizedRealKernel (x a, x b)) i

def fixedNormalizedRealSampleStudentizerSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => fixedNormalizedRealKernel (x i, x k))

def fixedNormalizedRealSampleStudentizer {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (fixedNormalizedRealSampleStudentizerSq x)

def fixedNormalizedRealSampleStudentized {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (fixedNormalizedRealSampleU x -
      ∫ z : ℝ × ℝ, fixedNormalizedRealKernel z
        ∂fixedRealObservationLaw.prod fixedRealObservationLaw) /
    fixedNormalizedRealSampleStudentizer x

def fixedNormalizedRealSampleStudentizedTailProbability (n : ℕ) (x : ℝ) : ℝ :=
  fixedRealSampleLaw.real
    {ξ : ℕ → ℝ |
      x ≤ fixedNormalizedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)}

private theorem normalized_statistics_scale_pos : 0 < Real.sqrt 3 :=
  Real.sqrt_pos.mpr (by norm_num)

private theorem normalized_statistics_scale_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem normalized_pair_sum_scale (n : ℕ) (a : ℝ)
    (H : Fin n → Fin n → ℝ) :
    Shao.OQ5.P35.unorderedPairSum (fun i k => a * H i k) =
      a * Shao.OQ5.P35.unorderedPairSum H := by
  classical
  unfold Shao.OQ5.P35.unorderedPairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i < k
  · simp only [ite_eq_left hik]
  · simp only [ite_eq_right hik, mul_zero]

private theorem normalized_u_scale (n : ℕ) (a : ℝ)
    (H : Fin n → Fin n → ℝ) :
    Shao.OQ6.FiniteRows.uStatistic (fun i k => a * H i k) =
      a * Shao.OQ6.FiniteRows.uStatistic H := by
  unfold Shao.OQ6.FiniteRows.uStatistic
  rw [normalized_pair_sum_scale]
  ring

private theorem normalized_row_scale (n : ℕ) (a : ℝ)
    (H : Fin n → Fin n → ℝ) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (fun k l => a * H k l) i =
      a * Shao.OQ6.FiniteRows.rowMean H i := by
  classical
  simp only [Shao.OQ6.FiniteRows.rowMean, ← Finset.mul_sum]
  ring

private theorem normalized_square_scale (n : ℕ) (a : ℝ)
    (H : Fin n → Fin n → ℝ) :
    Shao.OQ6.FiniteRows.jackknifeSq (fun i k => a * H i k) =
      a ^ 2 * Shao.OQ6.FiniteRows.jackknifeSq H := by
  unfold Shao.OQ6.FiniteRows.jackknifeSq
  simp only [normalized_row_scale, normalized_u_scale, ← mul_sub, mul_pow,
    ← Finset.mul_sum]
  ring

theorem measurable_fixedNormalizedRealSampleU (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleU x) := by
  classical
  unfold fixedNormalizedRealSampleU Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  by_cases hik : i < k
  · simpa only [ite_eq_left hik, Function.comp_def] using
      measurable_fixedNormalizedRealKernel.comp
        ((measurable_pi_apply i).prodMk (measurable_pi_apply k))
  · simp only [ite_eq_right hik]
    exact measurable_const

theorem measurable_fixedNormalizedRealSampleRowMean (n : ℕ) (i : Fin n) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleRowMean x i) := by
  classical
  unfold fixedNormalizedRealSampleRowMean Shao.OQ6.FiniteRows.rowMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  exact measurable_fixedNormalizedRealKernel.comp
    ((measurable_pi_apply i).prodMk (measurable_pi_apply k))

theorem measurable_fixedNormalizedRealSampleStudentizerSq (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleStudentizerSq x) := by
  unfold fixedNormalizedRealSampleStudentizerSq Shao.OQ6.FiniteRows.jackknifeSq
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_fixedNormalizedRealSampleRowMean n i).sub
    (measurable_fixedNormalizedRealSampleU n)).pow_const 2

theorem measurable_fixedNormalizedRealSampleStudentizer (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleStudentizer x) := by
  exact (measurable_fixedNormalizedRealSampleStudentizerSq n).sqrt

theorem measurable_fixedNormalizedRealSampleStudentized (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedNormalizedRealSampleStudentized x) := by
  exact (((measurable_fixedNormalizedRealSampleU n).sub measurable_const).const_mul
    (Real.sqrt (n : ℝ))).div (measurable_fixedNormalizedRealSampleStudentizer n)

theorem measurable_fixedNormalizedRealSampleStudentized_sample (n : ℕ) :
    Measurable (fun ξ : ℕ → ℝ =>
      fixedNormalizedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)) := by
  exact (measurable_fixedNormalizedRealSampleStudentized n).comp
    (Measurable.of_eval (fun i => measurable_fixedRealSampleCoordinate i.val))

theorem fixedNormalizedRealSampleU_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleU x = Real.sqrt 3 * fixedRealSampleU x := by
  change Shao.OQ6.FiniteRows.uStatistic
      (fun i k => Real.sqrt 3 * fixedRealKernel (x i, x k)) =
    Real.sqrt 3 * Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedRealKernel (x i, x k))
  exact normalized_u_scale n (Real.sqrt 3) _

theorem fixedNormalizedRealSampleRowMean_eq (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    fixedNormalizedRealSampleRowMean x i = Real.sqrt 3 *
      Shao.OQ6.FiniteRows.rowMean (fun a b => fixedRealKernel (x a, x b)) i := by
  change Shao.OQ6.FiniteRows.rowMean
      (fun a b => Real.sqrt 3 * fixedRealKernel (x a, x b)) i =
    Real.sqrt 3 * Shao.OQ6.FiniteRows.rowMean (fun a b => fixedRealKernel (x a, x b)) i
  exact normalized_row_scale n (Real.sqrt 3) _ i

theorem fixedNormalizedRealSampleStudentizerSq_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleStudentizerSq x = 3 * fixedRealSampleStudentizerSq x := by
  change Shao.OQ6.FiniteRows.jackknifeSq
      (fun i k => Real.sqrt 3 * fixedRealKernel (x i, x k)) =
    3 * Shao.OQ6.FiniteRows.jackknifeSq (fun i k => fixedRealKernel (x i, x k))
  rw [normalized_square_scale, normalized_statistics_scale_sq]

theorem fixedNormalizedRealSampleStudentizer_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleStudentizer x = Real.sqrt 3 * fixedRealSampleStudentizer x := by
  unfold fixedNormalizedRealSampleStudentizer fixedRealSampleStudentizer
  rw [fixedNormalizedRealSampleStudentizerSq_eq]
  exact Real.sqrt_mul (by norm_num) _

theorem fixedNormalizedRealSampleStudentized_eq (n : ℕ) (x : Fin n → ℝ) :
    fixedNormalizedRealSampleStudentized x = fixedRealSampleStudentized x := by
  unfold fixedNormalizedRealSampleStudentized fixedRealSampleStudentized
  rw [integral_fixedNormalizedRealKernel_eq_zero, sub_zero,
    fixedNormalizedRealSampleU_eq, fixedNormalizedRealSampleStudentizer_eq]
  rw [mul_left_comm (Real.sqrt (n : ℝ)) (Real.sqrt 3) (fixedRealSampleU x)]
  exact mul_div_mul_left _ _ (ne_of_gt normalized_statistics_scale_pos)

theorem fixedNormalizedRealSampleStudentizer_prefix_pos_ae (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ξ ∂fixedRealSampleLaw,
      0 < fixedNormalizedRealSampleStudentizer
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ) := by
  filter_upwards [fixedRealSampleStudentizer_prefix_pos_ae n hn] with ξ hξ
  rw [fixedNormalizedRealSampleStudentizer_eq]
  exact mul_pos normalized_statistics_scale_pos hξ

theorem fixedNormalizedRealSampleStudentizedTailProbability_eq_real (n : ℕ) (x : ℝ) :
    fixedNormalizedRealSampleStudentizedTailProbability n x =
      fixedRealSampleStudentizedTailProbability n x := by
  unfold fixedNormalizedRealSampleStudentizedTailProbability
    fixedRealSampleStudentizedTailProbability
  congr 1
  ext ξ
  change (x ≤ fixedNormalizedRealSampleStudentized
      (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)) ↔
    (x ≤ fixedRealSampleStudentized
      (fun i : Fin n => fixedRealSampleCoordinate i.val ξ))
  rw [fixedNormalizedRealSampleStudentized_eq]

theorem fixedNormalizedRealSampleStudentizedTailProbability_eq (n : ℕ) (x : ℝ) :
    fixedNormalizedRealSampleStudentizedTailProbability n x =
      fixedSampleStudentizedTailProbability n x := by
  rw [fixedNormalizedRealSampleStudentizedTailProbability_eq_real,
    fixedRealSampleStudentizedTailProbability_eq]

theorem fixedNormalizedRealSampleStudentizedTailProbability_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ fixedNormalizedRealSampleStudentizedTailProbability n x := by
  rw [fixedNormalizedRealSampleStudentizedTailProbability_eq_real]
  exact fixedRealSampleStudentizedTailProbability_nonneg n x

theorem fixedNormalizedRealSampleStudentizedTailProbability_le_one (n : ℕ) (x : ℝ) :
    fixedNormalizedRealSampleStudentizedTailProbability n x ≤ 1 := by
  rw [fixedNormalizedRealSampleStudentizedTailProbability_eq_real]
  exact fixedRealSampleStudentizedTailProbability_le_one n x

end

end Shao.OQ5.P52
