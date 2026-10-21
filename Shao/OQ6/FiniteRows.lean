import Shao.OQ5.P35.RowIdentity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Arbitrary symmetric finite rows

Finite deterministic algebra from original p39, lines 59–72. The U-statistic
counts each unordered off-diagonal pair once. The centered jackknife and the
uncentered row square retain their original coefficients. Square roots,
event conversion and probability are separate later units.
-/

set_option autoImplicit false

namespace Shao.OQ6.FiniteRows

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- Average every unordered off-diagonal pair exactly once. -/
def uStatistic (H : Fin n → Fin n → ℝ) : ℝ :=
  (n.choose 2 : ℝ)⁻¹ * Shao.OQ5.P35.unorderedPairSum H

/-- Mean of row i excluding the diagonal entry. -/
def rowMean (H : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.erase i, H i j

/-- The original centered-row jackknife square. -/
def jackknifeSq (H : Fin n → Fin n → ℝ) : ℝ :=
  (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, (rowMean H i - uStatistic H) ^ 2

/-- The source uncentered row square s_*². -/
def uncenteredSq (H : Fin n → Fin n → ℝ) : ℝ :=
  (((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, rowMean H i ^ 2

theorem sum_rowMean (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hn : 3 ≤ n) :
    (∑ i : Fin n, rowMean H i) = (n : ℝ) * uStatistic H := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hn))
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    apply ne_of_gt
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn)
  calc
    (∑ i : Fin n, rowMean H i) =
        ((n : ℝ) - 1)⁻¹ * (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, H i j) := by
      simp only [rowMean, Finset.mul_sum]
    _ = ((n : ℝ) - 1)⁻¹ * (2 * Shao.OQ5.P35.unorderedPairSum H) := by
      rw [Shao.OQ5.P35.offDiagonalSum_eq_two_unordered H hH]
    _ = (n : ℝ) * uStatistic H := by
      unfold uStatistic
      rw [← Shao.OQ5.P35.pairCount_eq_choose n]
      unfold Shao.OQ5.P35.pairCount
      field_simp [hn0, hn1]

theorem sum_centered_rowMean_sq (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hn : 3 ≤ n) :
    (∑ i : Fin n, (rowMean H i - uStatistic H) ^ 2) =
      (∑ i : Fin n, rowMean H i ^ 2) - (n : ℝ) * uStatistic H ^ 2 := by
  have hc : (∑ i : Fin n, 2 * rowMean H i * uStatistic H) =
      2 * (∑ i : Fin n, rowMean H i) * uStatistic H := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hc, sum_rowMean H hH hn]
  ring

theorem jackknifeSq_nonneg (H : Fin n → Fin n → ℝ) (hn : 3 ≤ n) :
    0 ≤ jackknifeSq H := by
  have h1 : 0 ≤ (n : ℝ) - 1 := by
    apply sub_nonneg.mpr
    exact_mod_cast (le_trans (by decide : 1 ≤ 3) hn)
  exact mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) h1) (sq_nonneg _))
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem uncenteredSq_nonneg (H : Fin n → Fin n → ℝ) (hn : 3 ≤ n) :
    0 ≤ uncenteredSq H := by
  have h1 : 0 ≤ (n : ℝ) - 1 := by
    apply sub_nonneg.mpr
    exact_mod_cast (le_trans (by decide : 1 ≤ 3) hn)
  exact mul_nonneg (div_nonneg h1 (sq_nonneg _))
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem uncenteredSq_eq_jackknifeSq_add
    (H : Fin n → Fin n → ℝ)
    (hH : ∀ i j, H i j = H j i) (hn : 3 ≤ n) :
    uncenteredSq H = jackknifeSq H / 4 +
      (((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
        (n : ℝ) * uStatistic H ^ 2 := by
  unfold uncenteredSq jackknifeSq
  rw [sum_centered_rowMean_sq H hH hn]
  ring

end

end Shao.OQ6.FiniteRows
