import Shao.OQ5.P53.SparseRealNormalization
import Shao.OQ5.P53.SparseBalancedTailLimits

/-!
# Actual normalized original jackknife and identical tails

Source p53 section1: fixed positive kernel scaling preserves the original
studentized statistic. Local generic finite-sum identities follow the same
algebra as accepted P52 normalized statistics, with the actual P53 scale.
The true normalized population mean is included before its proven zero value
is used. Equality holds pointwise even when the sample denominator is zero.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

namespace Shao.OQ5.P53

def sparseNormalizedRealSampleU (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))

def sparseNormalizedRealSampleRowMean (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) (i : Fin n) : ℝ :=
  Shao.OQ6.FiniteRows.rowMean (fun a b => sparseNormalizedRealKernel α x N (ξ a) (ξ b)) i

def sparseNormalizedRealSampleStudentizerSq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => sparseNormalizedRealKernel α x N (ξ i) (ξ k))

def sparseNormalizedRealSampleStudentizer (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Real.sqrt (sparseNormalizedRealSampleStudentizerSq α x N ξ)

def sparseNormalizedRealSampleStudentized (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (sparseNormalizedRealSampleU α x N ξ -
      ∫ w : ℝ × ℝ, sparseNormalizedRealKernel α x N w.1 w.2
        ∂((sparseRealMeasure α x N).prod (sparseRealMeasure α x N))) /
    sparseNormalizedRealSampleStudentizer α x N ξ

def sparseNormalizedRealSampleStudentizedTailProbability (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n : ℕ) (y : ℝ) : ℝ :=
  (sparseRealSampleMeasure α x N).real
    {ξ : ℕ → ℝ | y ≤ sparseNormalizedRealSampleStudentized α x N
      (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)}

private theorem normalized_pair_sum_scale (n : ℕ) (a : ℝ) (H : Fin n → Fin n → ℝ) :
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

private theorem normalized_u_scale (n : ℕ) (a : ℝ) (H : Fin n → Fin n → ℝ) :
    Shao.OQ6.FiniteRows.uStatistic (fun i k => a * H i k) =
      a * Shao.OQ6.FiniteRows.uStatistic H := by
  unfold Shao.OQ6.FiniteRows.uStatistic
  rw [normalized_pair_sum_scale]
  ring

private theorem normalized_row_scale (n : ℕ) (a : ℝ) (H : Fin n → Fin n → ℝ) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (fun k l => a * H k l) i =
      a * Shao.OQ6.FiniteRows.rowMean H i := by
  classical
  simp only [Shao.OQ6.FiniteRows.rowMean, ← Finset.mul_sum]
  ring

private theorem normalized_square_scale (n : ℕ) (a : ℝ) (H : Fin n → Fin n → ℝ) :
    Shao.OQ6.FiniteRows.jackknifeSq (fun i k => a * H i k) =
      a ^ 2 * Shao.OQ6.FiniteRows.jackknifeSq H := by
  unfold Shao.OQ6.FiniteRows.jackknifeSq
  simp only [normalized_row_scale, normalized_u_scale, ← mul_sub, mul_pow, ← Finset.mul_sum]
  ring

theorem sparseNormalizedRealSampleU_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleU α x N ξ = sparseRealNormalizationScale α x N * sparseRealSampleU α x N ξ := by
  intro α x N n ξ
  exact normalized_u_scale n (sparseRealNormalizationScale α x N)
    (fun i k => sparseRealKernel α x N (ξ i) (ξ k))

theorem sparseNormalizedRealSampleRowMean_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ) (i : Fin n),
  sparseNormalizedRealSampleRowMean α x N ξ i = sparseRealNormalizationScale α x N *
    Shao.OQ6.FiniteRows.rowMean (fun a b => sparseRealKernel α x N (ξ a) (ξ b)) i := by
  intro α x N n ξ i
  exact normalized_row_scale n (sparseRealNormalizationScale α x N)
    (fun a b => sparseRealKernel α x N (ξ a) (ξ b)) i

theorem sparseNormalizedRealSampleStudentizerSq_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleStudentizerSq α x N ξ =
    (sparseRealNormalizationScale α x N) ^ 2 * sparseRealSampleStudentizerSq α x N ξ := by
  intro α x N n ξ
  exact normalized_square_scale n (sparseRealNormalizationScale α x N)
    (fun i k => sparseRealKernel α x N (ξ i) (ξ k))

theorem measurable_sparseNormalizedRealSampleU :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleU α x N ξ) := by
  intro α x N n
  have heq : (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleU α x N ξ) =
      (fun ξ : Fin n → ℝ => sparseRealNormalizationScale α x N * sparseRealSampleU α x N ξ) := by
    funext ξ
    exact sparseNormalizedRealSampleU_eq α x N n ξ
  rw [heq]
  exact (measurable_sparseRealSampleU α x N n).const_mul _

theorem measurable_sparseNormalizedRealSampleRowMean :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (i : Fin n),
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleRowMean α x N ξ i) := by
  intro α x N n i
  classical
  unfold sparseNormalizedRealSampleRowMean Shao.OQ6.FiniteRows.rowMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  have hpair : Measurable (fun ξ : Fin n → ℝ => (ξ i, ξ k)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply k)
  exact (measurable_sparseNormalizedRealKernel α x N).comp hpair

theorem measurable_sparseNormalizedRealSampleStudentizerSq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleStudentizerSq α x N ξ) := by
  intro α x N n
  have heq : (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleStudentizerSq α x N ξ) =
      (fun ξ : Fin n → ℝ => (sparseRealNormalizationScale α x N) ^ 2 * sparseRealSampleStudentizerSq α x N ξ) := by
    funext ξ
    exact sparseNormalizedRealSampleStudentizerSq_eq α x N n ξ
  rw [heq]
  exact (measurable_sparseRealSampleStudentizerSq α x N n).const_mul _

theorem measurable_sparseNormalizedRealSampleStudentizer :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleStudentizer α x N ξ) := by
  intro α x N n
  exact (measurable_sparseNormalizedRealSampleStudentizerSq α x N n).sqrt

theorem measurable_sparseNormalizedRealSampleStudentized :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseNormalizedRealSampleStudentized α x N ξ) := by
  intro α x N n
  exact (((measurable_sparseNormalizedRealSampleU α x N n).sub measurable_const).const_mul
    (Real.sqrt (n : ℝ))).div (measurable_sparseNormalizedRealSampleStudentizer α x N n)

theorem measurable_sparseNormalizedRealSampleStudentized_sample :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : ℕ → ℝ => sparseNormalizedRealSampleStudentized α x N
    (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)) := by
  intro α x N n
  exact (measurable_sparseNormalizedRealSampleStudentized α x N n).comp
    (Measurable.of_eval (fun i => measurable_sparseRealSampleCoordinate i.val))

theorem sparseNormalizedRealSampleStudentizer_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleStudentizer α x N ξ =
    sparseRealNormalizationScale α x N * sparseRealSampleStudentizer α x N ξ := by
  intro α x N hα hN n ξ
  unfold sparseNormalizedRealSampleStudentizer sparseRealSampleStudentizer
  rw [sparseNormalizedRealSampleStudentizerSq_eq,
    Real.sqrt_mul (sq_nonneg (sparseRealNormalizationScale α x N)),
    Real.sqrt_sq (sparseRealNormalizationScale_pos α x N hα hN).le]

theorem sparseNormalizedRealSampleStudentized_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseNormalizedRealSampleStudentized α x N ξ = sparseRealSampleStudentized α x N ξ := by
  intro α x N hα hN n ξ
  unfold sparseNormalizedRealSampleStudentized sparseRealSampleStudentized
  rw [integral_sparseNormalizedRealKernel_zero α x N hα hN, sub_zero,
    sparseNormalizedRealSampleU_eq, sparseNormalizedRealSampleStudentizer_eq α x N hα hN]
  rw [mul_left_comm (Real.sqrt (n : ℝ)) (sparseRealNormalizationScale α x N) (sparseRealSampleU α x N ξ)]
  exact mul_div_mul_left _ _ (ne_of_gt (sparseRealNormalizationScale_pos α x N hα hN))

theorem sparseNormalizedRealSampleStudentizedTailProbability_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ (n : ℕ) (y : ℝ),
  sparseNormalizedRealSampleStudentizedTailProbability α x N n y =
    sparseRealSampleStudentizedTailProbability α x N n y := by
  intro α x N hα hN n y
  unfold sparseNormalizedRealSampleStudentizedTailProbability sparseRealSampleStudentizedTailProbability
  congr 1
  ext ξ
  change (y ≤ sparseNormalizedRealSampleStudentized α x N
    (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)) ↔
    (y ≤ sparseRealSampleStudentized α x N (fun i : Fin n => sparseRealSampleCoordinate i.val ξ))
  rw [sparseNormalizedRealSampleStudentized_eq α x N hα hN]

theorem sparseNormalizedRealSampleStudentizer_prefix_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → SparseSelectionCore α x N → ∀ n : ℕ, 3 ≤ n →
  ∀ᵐ ξ : ℕ → ℝ ∂sparseRealSampleMeasure α x N,
    0 < sparseNormalizedRealSampleStudentizer α x N
      (fun i : Fin n => sparseRealSampleCoordinate i.val ξ) := by
  intro α x N hα hN n hn
  filter_upwards [sparseRealSampleStudentizer_prefix_pos_ae α x N n hn] with ξ hξ
  rw [sparseNormalizedRealSampleStudentizer_eq α x N hα hN]
  exact mul_pos (sparseRealNormalizationScale_pos α x N hα hN) hξ

theorem tendsto_sparseNormalizedRealSampleStudentized_logTail_normalized_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => Real.log (sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j))) /
    (-(x (N j) ^ 2) / 2)) atTop (nhds 0) := by
  intro α x N hα hα1 hN hSuper hSmall
  simpa only [sparseNormalizedRealSampleStudentizedTailProbability_eq α x N hα hN] using
    tendsto_sparseRealSampleStudentized_logTail_normalized_zero α x N hα hα1 hN hSuper hSmall

theorem tendsto_sparseNormalizedRealSampleStudentized_gaussianTail_ratio_atTop :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), 0 < α → α < 1 → SparseSelectionCore α x N →
  Tendsto (fun n : ℕ => x n / (n : ℝ) ^ sparseDelta α) atTop atTop →
  Tendsto (fun n : ℕ => sparseRatio x n) atTop (nhds 0) →
  Tendsto (fun j : ℕ => sparseNormalizedRealSampleStudentizedTailProbability α x N (N j) (x (N j)) /
    Shao.OQ5.P35.standardNormalUpperTail (x (N j))) atTop atTop := by
  intro α x N hα hα1 hN hSuper hSmall
  simpa only [sparseNormalizedRealSampleStudentizedTailProbability_eq α x N hα hN] using
    tendsto_sparseRealSampleStudentized_gaussianTail_ratio_atTop α x N hα hα1 hN hSuper hSmall

end Shao.OQ5.P53
