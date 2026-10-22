import Shao.OQ5.P52.FixedLayerErasedRowMoments
import Shao.OQ5.P52.FixedLayerErasedPairMoments
import Shao.OQ6.FiniteRows

/-!
# Original finite sample statistics for the full masked kernel

The unordered U and centered-row jackknife square retain their original
definitions. Finite double counting and sample centering give their exact
noise/residual decompositions at every sample, including off-mask points.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedSampleU {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedKernel (x i, x k))

def fixedSampleStudentizerSq {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => fixedKernel (x i, x k))

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

private theorem full_row_formula (n : ℕ) (hn : 3 ≤ n)
    (x : Fin n → LayerObs) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (fun a b => fixedKernel (x a, x b)) i =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) * (x i).1 +
        (∑ k : Fin n, (x k).1) / ((n : ℝ) - 1) +
        fixedErasedResidualRow i x / ((n : ℝ) - 1) := by
  classical
  have h1 := sampleSize_sub_one_ne_zero n hn
  have hnoise : (∑ k ∈ Finset.univ.erase i, ((x i).1 + (x k).1)) =
      ((n : ℝ) - 2) * (x i).1 + ∑ k : Fin n, (x k).1 := by
    rw [Finset.sum_erase_eq_sub (by simp)]
    simp only [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  change ((n : ℝ) - 1)⁻¹ *
    (∑ k ∈ Finset.univ.erase i,
      (((x i).1 + (x k).1) + fixedResidualKernel (x i, x k))) = _
  rw [Finset.sum_add_distrib, hnoise]
  change ((n : ℝ) - 1)⁻¹ *
    (((n : ℝ) - 2) * (x i).1 + (∑ k : Fin n, (x k).1) +
      fixedErasedResidualRow i x) = _
  field_simp [h1]

private theorem sum_full_rows (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    (∑ i : Fin n,
      Shao.OQ6.FiniteRows.rowMean (fun a b => fixedKernel (x a, x b)) i) =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) * (∑ i : Fin n, (x i).1) +
        (n : ℝ) * ((∑ i : Fin n, (x i).1) / ((n : ℝ) - 1)) +
        (∑ i : Fin n, fixedErasedResidualRow i x) / ((n : ℝ) - 1) := by
  simp_rw [full_row_formula n hn x]
  simp only [div_eq_mul_inv, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem fixedSampleU_eq_noise_add_residual
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    fixedSampleU x = (2 / (n : ℝ)) * (∑ i : Fin n, (x i).1) +
      (n.choose 2 : ℝ)⁻¹ * fixedErasedResidualPairSum x := by
  have hn0 := sampleSize_ne_zero n hn
  have h1 := sampleSize_sub_one_ne_zero n hn
  have hrows := Shao.OQ6.FiniteRows.sum_rowMean
    (fun i k => fixedKernel (x i, x k))
    (fun i k => fixedKernel_symmetric (x i) (x k)) hn
  have hresidual : (∑ i : Fin n, fixedErasedResidualRow i x) =
      2 * fixedErasedResidualPairSum x :=
    Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
      (fun i k => fixedResidualKernel (x i, x k))
      (fun i k => fixedResidualKernel_symmetric (x i) (x k))
  apply mul_left_cancel₀ hn0
  change (n : ℝ) *
    Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedKernel (x i, x k)) = _
  rw [← hrows, sum_full_rows n hn x, hresidual,
    ← Shao.OQ5.P35.pairCount_eq_choose n]
  unfold Shao.OQ5.P35.pairCount
  field_simp [hn0, h1]
  ring

theorem fixedSampleStudentizerSq_nonneg
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    0 ≤ fixedSampleStudentizerSq x :=
  Shao.OQ6.FiniteRows.jackknifeSq_nonneg
    (fun i k => fixedKernel (x i, x k)) hn

private theorem mean_full_rows (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    Shao.OQ5.P35.mean
      (Shao.OQ6.FiniteRows.rowMean (fun i k => fixedKernel (x i, x k))) =
      fixedSampleU x := by
  have hn0 := sampleSize_ne_zero n hn
  unfold Shao.OQ5.P35.mean
  rw [Shao.OQ6.FiniteRows.sum_rowMean
    (fun i k => fixedKernel (x i, x k))
    (fun i k => fixedKernel_symmetric (x i) (x k)) hn]
  change (n : ℝ)⁻¹ * ((n : ℝ) * fixedSampleU x) = fixedSampleU x
  field_simp [hn0]

private theorem centered_full_row (n : ℕ) (hn : 3 ≤ n)
    (x : Fin n → LayerObs) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (fun a b => fixedKernel (x a, x b)) i -
        fixedSampleU x =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
        Shao.OQ5.P35.center
          (fun k : Fin n =>
            (x k).1 + fixedErasedResidualRow k x / ((n : ℝ) - 2)) i := by
  have hn0 := sampleSize_ne_zero n hn
  have h1 := sampleSize_sub_one_ne_zero n hn
  have h2 := sampleSize_sub_two_ne_zero n hn
  let a : ℝ := ((n : ℝ) - 2) / ((n : ℝ) - 1)
  let c : ℝ := (∑ k : Fin n, (x k).1) / ((n : ℝ) - 1)
  let b : Fin n → ℝ := fun k =>
    (x k).1 + fixedErasedResidualRow k x / ((n : ℝ) - 2)
  have hq : ∀ k,
      Shao.OQ6.FiniteRows.rowMean (fun u v => fixedKernel (x u, x v)) k =
        a * b k + c := by
    intro k
    dsimp only [a, b, c]
    rw [full_row_formula n hn x k]
    field_simp [h1, h2]
    ring
  calc
    _ = Shao.OQ5.P35.center
        (Shao.OQ6.FiniteRows.rowMean (fun u v => fixedKernel (x u, x v))) i := by
      simp only [Shao.OQ5.P35.center, mean_full_rows n hn x]
    _ = a * Shao.OQ5.P35.center b i := by
      unfold Shao.OQ5.P35.center Shao.OQ5.P35.mean
      simp_rw [hq]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hn0]
      ring

theorem fixedSampleStudentizerSq_eq_centered_residual_rows
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    fixedSampleStudentizerSq x = (4 / ((n : ℝ) - 1)) *
      ∑ i : Fin n,
        (Shao.OQ5.P35.center
          (fun k : Fin n =>
            (x k).1 + fixedErasedResidualRow k x / ((n : ℝ) - 2)) i) ^ 2 := by
  have h1 := sampleSize_sub_one_ne_zero n hn
  have h2 := sampleSize_sub_two_ne_zero n hn
  unfold fixedSampleStudentizerSq Shao.OQ6.FiniteRows.jackknifeSq
  change (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    (∑ i : Fin n,
      (Shao.OQ6.FiniteRows.rowMean (fun u v => fixedKernel (x u, x v)) i -
        fixedSampleU x) ^ 2) = _
  simp_rw [centered_full_row n hn x]
  simp only [mul_pow, ← Finset.mul_sum]
  field_simp [h1, h2]

end
end Shao.OQ5.P52
