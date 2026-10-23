import Shao.OQ5.P53.SparsePopulationKernel
import Shao.OQ6.FiniteRows

/-!
# Actual p53 finite sample statistics

The positive residual, unordered-pair U, and original centered-row jackknife
are retained literally. The deterministic identities hold for arbitrary fixed
parameters and every sample; no population moment or selection hypothesis is
used. The zero-square implication prepares the later atomless-noise argument.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseSampleResidualPairSum (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ω : Fin n → SparseObs) : ℝ :=
  Shao.OQ5.P35.unorderedPairSum (fun i k => sparsePopulationResidual α x N (ω i) (ω k))

def sparseSampleResidualRow (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (ω : Fin n → SparseObs) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, sparsePopulationResidual α x N (ω i) (ω k)

def sparseSampleAdjustedRow (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (ω : Fin n → SparseObs) (i : Fin n) : ℝ :=
  sparsePopulationG α x N (ω i) + sparseSampleResidualRow α x N ω i / ((n : ℝ) - 2)

def sparseSampleU (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ω : Fin n → SparseObs) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => sparsePopulationKernel α x N (ω i) (ω k))

def sparseSampleStudentizerSq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ω : Fin n → SparseObs) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => sparsePopulationKernel α x N (ω i) (ω k))

def sparseSampleStudentizer (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ω : Fin n → SparseObs) : ℝ :=
  Real.sqrt (sparseSampleStudentizerSq α x N ω)

def sparseSampleStudentized (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ω : Fin n → SparseObs) : ℝ :=
  Real.sqrt (n : ℝ) * sparseSampleU α x N ω / sparseSampleStudentizer α x N ω

private theorem sampleSize_ne_zero (n : ℕ) (hn : 3 ≤ n) : (n : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hn))

private theorem sampleSize_sub_one_ne_zero (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  apply ne_of_gt
  exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn)

private theorem sampleSize_sub_two_ne_zero (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) - 2 ≠ 0 := by
  apply sub_ne_zero.mpr
  apply ne_of_gt
  exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hn)

theorem sparseSampleResidualRow_eq_factor :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ω : Fin n → SparseObs) (i : Fin n),
  sparseSampleResidualRow α x N ω i = sparsePopulationZ α x N (ω i) *
    ((∑ k : Fin n, sparsePopulationZ α x N (ω k)) - sparsePopulationZ α x N (ω i)) := by
  intro α x N n ω i
  classical
  unfold sparseSampleResidualRow sparsePopulationResidual
  rw [← Finset.mul_sum, Finset.sum_erase_eq_sub (by simp)]

theorem sparseSample_rowMean_formula :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ (ω : Fin n → SparseObs) (i : Fin n),
  Shao.OQ6.FiniteRows.rowMean (fun a b => sparsePopulationKernel α x N (ω a) (ω b)) i =
    (((n : ℝ) - 2) / ((n : ℝ) - 1)) * sparsePopulationG α x N (ω i) +
      (∑ k : Fin n, sparsePopulationG α x N (ω k)) / ((n : ℝ) - 1) +
      sparseSampleResidualRow α x N ω i / ((n : ℝ) - 1) := by
  intro α x N n hn ω i
  classical
  have h1 := sampleSize_sub_one_ne_zero n hn
  have hG : (∑ k ∈ Finset.univ.erase i,
      (sparsePopulationG α x N (ω i) + sparsePopulationG α x N (ω k))) =
      ((n : ℝ) - 2) * sparsePopulationG α x N (ω i) +
        ∑ k : Fin n, sparsePopulationG α x N (ω k) := by
    rw [Finset.sum_erase_eq_sub (by simp)]
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  change ((n : ℝ) - 1)⁻¹ *
    (∑ k ∈ Finset.univ.erase i,
      ((sparsePopulationG α x N (ω i) + sparsePopulationG α x N (ω k)) +
        sparsePopulationResidual α x N (ω i) (ω k))) = _
  rw [Finset.sum_add_distrib, hG]
  change ((n : ℝ) - 1)⁻¹ *
    (((n : ℝ) - 2) * sparsePopulationG α x N (ω i) +
      (∑ k : Fin n, sparsePopulationG α x N (ω k)) +
      sparseSampleResidualRow α x N ω i) = _
  field_simp [h1]

private theorem sum_full_rows (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (hn : 3 ≤ n) (ω : Fin n → SparseObs) :
    (∑ i : Fin n,
      Shao.OQ6.FiniteRows.rowMean (fun a b => sparsePopulationKernel α x N (ω a) (ω b)) i) =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
          (∑ i : Fin n, sparsePopulationG α x N (ω i)) +
        (n : ℝ) * ((∑ i : Fin n, sparsePopulationG α x N (ω i)) / ((n : ℝ) - 1)) +
        (∑ i : Fin n, sparseSampleResidualRow α x N ω i) / ((n : ℝ) - 1) := by
  simp_rw [sparseSample_rowMean_formula α x N n hn ω]
  simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sparseSampleU_eq_projection_add_residual :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ ω : Fin n → SparseObs,
  sparseSampleU α x N ω = (2 / (n : ℝ)) * (∑ i : Fin n, sparsePopulationG α x N (ω i)) +
    (n.choose 2 : ℝ)⁻¹ * sparseSampleResidualPairSum α x N ω := by
  intro α x N n hn ω
  have hn0 := sampleSize_ne_zero n hn
  have h1 := sampleSize_sub_one_ne_zero n hn
  have hrows := Shao.OQ6.FiniteRows.sum_rowMean
    (fun i k => sparsePopulationKernel α x N (ω i) (ω k))
    (fun i k => sparsePopulationKernel_symmetric α x N (ω i) (ω k)) hn
  have hresidual : (∑ i : Fin n, sparseSampleResidualRow α x N ω i) =
      2 * sparseSampleResidualPairSum α x N ω := by
    apply Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
      (fun i k => sparsePopulationResidual α x N (ω i) (ω k))
    intro i k
    unfold sparsePopulationResidual
    exact mul_comm _ _
  apply mul_left_cancel₀ hn0
  change (n : ℝ) *
    Shao.OQ6.FiniteRows.uStatistic
      (fun i k => sparsePopulationKernel α x N (ω i) (ω k)) = _
  rw [← hrows, sum_full_rows α x N n hn ω, hresidual,
    ← Shao.OQ5.P35.pairCount_eq_choose n]
  unfold Shao.OQ5.P35.pairCount
  field_simp [hn0, h1]
  ring

private theorem mean_full_rows (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (hn : 3 ≤ n) (ω : Fin n → SparseObs) :
    Shao.OQ5.P35.mean
      (Shao.OQ6.FiniteRows.rowMean
        (fun i k => sparsePopulationKernel α x N (ω i) (ω k))) =
      sparseSampleU α x N ω := by
  have hn0 := sampleSize_ne_zero n hn
  unfold Shao.OQ5.P35.mean
  rw [Shao.OQ6.FiniteRows.sum_rowMean
    (fun i k => sparsePopulationKernel α x N (ω i) (ω k))
    (fun i k => sparsePopulationKernel_symmetric α x N (ω i) (ω k)) hn]
  change (n : ℝ)⁻¹ * ((n : ℝ) * sparseSampleU α x N ω) = sparseSampleU α x N ω
  field_simp [hn0]

theorem sparseSample_centered_rowMean :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ (ω : Fin n → SparseObs) (i : Fin n),
  Shao.OQ6.FiniteRows.rowMean (fun a b => sparsePopulationKernel α x N (ω a) (ω b)) i -
    sparseSampleU α x N ω = (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
      Shao.OQ5.P35.center (sparseSampleAdjustedRow α x N ω) i := by
  intro α x N n hn ω i
  have hn0 := sampleSize_ne_zero n hn
  have h1 := sampleSize_sub_one_ne_zero n hn
  have h2 := sampleSize_sub_two_ne_zero n hn
  let a : ℝ := ((n : ℝ) - 2) / ((n : ℝ) - 1)
  let c : ℝ := (∑ k : Fin n, sparsePopulationG α x N (ω k)) / ((n : ℝ) - 1)
  have hq : ∀ k,
      Shao.OQ6.FiniteRows.rowMean
        (fun u v => sparsePopulationKernel α x N (ω u) (ω v)) k =
        a * sparseSampleAdjustedRow α x N ω k + c := by
    intro k
    dsimp only [a, c]
    rw [sparseSample_rowMean_formula α x N n hn ω k]
    unfold sparseSampleAdjustedRow
    field_simp [h1, h2]
    ring
  calc
    _ = Shao.OQ5.P35.center
        (Shao.OQ6.FiniteRows.rowMean
          (fun u v => sparsePopulationKernel α x N (ω u) (ω v))) i := by
      simp only [Shao.OQ5.P35.center, mean_full_rows α x N n hn ω]
    _ = a * Shao.OQ5.P35.center (sparseSampleAdjustedRow α x N ω) i := by
      unfold Shao.OQ5.P35.center Shao.OQ5.P35.mean
      simp_rw [hq]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hn0]
      ring

theorem sparseSampleStudentizerSq_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ ω : Fin n → SparseObs,
  0 ≤ sparseSampleStudentizerSq α x N ω := by
  intro α x N n hn ω
  exact Shao.OQ6.FiniteRows.jackknifeSq_nonneg
    (fun i k => sparsePopulationKernel α x N (ω i) (ω k)) hn

theorem sparseSampleStudentizerSq_eq_centered_adjusted_rows :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ ω : Fin n → SparseObs,
  sparseSampleStudentizerSq α x N ω = (4 / ((n : ℝ) - 1)) *
    ∑ i : Fin n, (Shao.OQ5.P35.center (sparseSampleAdjustedRow α x N ω) i) ^ 2 := by
  intro α x N n hn ω
  have h1 := sampleSize_sub_one_ne_zero n hn
  have h2 := sampleSize_sub_two_ne_zero n hn
  unfold sparseSampleStudentizerSq Shao.OQ6.FiniteRows.jackknifeSq
  change (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    (∑ i : Fin n,
      (Shao.OQ6.FiniteRows.rowMean
        (fun u v => sparsePopulationKernel α x N (ω u) (ω v)) i -
        sparseSampleU α x N ω) ^ 2) = _
  simp_rw [sparseSample_centered_rowMean α x N n hn ω]
  simp only [mul_pow, ← Finset.mul_sum]
  field_simp [h1, h2]

theorem sparseSampleStudentizer_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ω : Fin n → SparseObs),
  0 ≤ sparseSampleStudentizer α x N ω := by
  intro α x N n ω
  exact Real.sqrt_nonneg _

theorem sparseSampleStudentizer_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ ω : Fin n → SparseObs,
  (sparseSampleStudentizer α x N ω) ^ 2 = sparseSampleStudentizerSq α x N ω := by
  intro α x N n hn ω
  exact Real.sq_sqrt (sparseSampleStudentizerSq_nonneg α x N n hn ω)

theorem sparseSampleStudentizerSq_eq_zero_imp_adjustedRow_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ ω : Fin n → SparseObs,
  sparseSampleStudentizerSq α x N ω = 0 → ∀ i k : Fin n,
    sparseSampleAdjustedRow α x N ω i = sparseSampleAdjustedRow α x N ω k := by
  intro α x N n hn ω hzero i k
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [sparseSampleStudentizerSq_eq_centered_adjusted_rows α x N n hn ω] at hzero
  have hp : (4 / ((n : ℝ) - 1)) ≠ 0 :=
    ne_of_gt (div_pos (by norm_num) (by linarith))
  have hs : (∑ a : Fin n,
      (Shao.OQ5.P35.center (sparseSampleAdjustedRow α x N ω) a) ^ 2) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hp
  have hall := (Finset.sum_sq_eq_zero_iff Finset.univ
    (Shao.OQ5.P35.center (sparseSampleAdjustedRow α x N ω))).mp hs
  have hi := hall i (Finset.mem_univ i)
  have hk := hall k (Finset.mem_univ k)
  unfold Shao.OQ5.P35.center at hi hk
  linarith

theorem measurable_sparseSampleResidualRow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (i : Fin n),
  Measurable (fun ω : Fin n → SparseObs => sparseSampleResidualRow α x N ω i) := by
  intro α x N n i
  classical
  unfold sparseSampleResidualRow sparsePopulationResidual
  apply Finset.measurable_sum
  intro k _
  exact ((measurable_sparsePopulationZ α x N).comp (measurable_pi_apply i)).mul
    ((measurable_sparsePopulationZ α x N).comp (measurable_pi_apply k))

theorem measurable_sparseSampleAdjustedRow :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (i : Fin n),
  Measurable (fun ω : Fin n → SparseObs => sparseSampleAdjustedRow α x N ω i) := by
  intro α x N n i
  exact ((measurable_sparsePopulationG α x N).comp (measurable_pi_apply i)).add
    ((measurable_sparseSampleResidualRow α x N n i).div_const _)

theorem measurable_sparseSampleU :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ω : Fin n → SparseObs => sparseSampleU α x N ω) := by
  intro α x N n
  classical
  unfold sparseSampleU Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  by_cases hik : i < k
  · have hm : Measurable (fun ω : Fin n → SparseObs => (ω i, ω k)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply k)
    simpa only [ite_eq_left hik, Function.comp_def] using
      (measurable_sparsePopulationKernel α x N).comp hm
  · simp only [ite_eq_right hik]
    exact measurable_const

private theorem measurable_full_row (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (i : Fin n) :
    Measurable (fun ω : Fin n → SparseObs =>
      Shao.OQ6.FiniteRows.rowMean
        (fun a b => sparsePopulationKernel α x N (ω a) (ω b)) i) := by
  classical
  unfold Shao.OQ6.FiniteRows.rowMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  have hm : Measurable (fun ω : Fin n → SparseObs => (ω i, ω k)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply k)
  exact (measurable_sparsePopulationKernel α x N).comp hm

theorem measurable_sparseSampleStudentizerSq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ω : Fin n → SparseObs => sparseSampleStudentizerSq α x N ω) := by
  intro α x N n
  unfold sparseSampleStudentizerSq Shao.OQ6.FiniteRows.jackknifeSq
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_full_row α x N n i).sub (measurable_sparseSampleU α x N n)).pow_const 2

theorem measurable_sparseSampleStudentizer :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ω : Fin n → SparseObs => sparseSampleStudentizer α x N ω) := by
  intro α x N n
  exact (measurable_sparseSampleStudentizerSq α x N n).sqrt

theorem measurable_sparseSampleStudentized :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ω : Fin n → SparseObs => sparseSampleStudentized α x N ω) := by
  intro α x N n
  exact ((measurable_sparseSampleU α x N n).const_mul (Real.sqrt (n : ℝ))).div
    (measurable_sparseSampleStudentizer α x N n)

end Shao.OQ5.P53
