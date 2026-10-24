import Shao.OQ6.FiniteRows

/-!
# Residual expansion of the actual uncentered row square

Finite deterministic algebra from original p39, lines 74–88, equation (4).
The projection-energy division is cleared, so the equality also covers zero
projection energy. Both mixed terms are retained. No probability, canonical
degeneracy, positive-denominator event conversion or root closure is asserted.
-/

set_option autoImplicit false

namespace Shao.OQ6.FiniteRows

noncomputable section

open scoped BigOperators

private theorem residual_rowMean_formula
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (i : Fin n) :
    rowMean (fun i j => g i + g j + r i j) i =
      (((n : ℝ) - 2) * g i + (∑ j : Fin n, g j) +
        (∑ j ∈ Finset.univ.erase i, r i j)) / ((n : ℝ) - 1) := by
  classical
  have hsum : (∑ j : Fin n, (g i + g j)) =
      (n : ℝ) * g i + (∑ j : Fin n, g j) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have herased : (∑ j ∈ Finset.univ.erase i, (g i + g j)) =
      ((n : ℝ) - 2) * g i + (∑ j : Fin n, g j) := by
    rw [Finset.sum_erase_eq_sub (by simp), hsum]
    ring
  unfold rowMean
  rw [Finset.sum_add_distrib, herased, div_eq_mul_inv]
  ring

private theorem finite_sum_affine_sq
    {n : ℕ} (g psi : Fin n → ℝ) (a S : ℝ) :
    (∑ i : Fin n, (a * g i + S + psi i) ^ 2) =
      a ^ 2 * (∑ i : Fin n, g i ^ 2) + (n : ℝ) * S ^ 2 +
        (∑ i : Fin n, psi i ^ 2) +
        2 * a * S * (∑ i : Fin n, g i) +
        2 * a * (∑ i : Fin n, g i * psi i) +
        2 * S * (∑ i : Fin n, psi i) := by
  have hpoint (i : Fin n) :
      (a * g i + S + psi i) ^ 2 =
        a ^ 2 * g i ^ 2 + S ^ 2 + psi i ^ 2 +
          (2 * a * S) * g i + (2 * a) * (g i * psi i) +
          (2 * S) * psi i := by
    ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem uncenteredSq_sub_projectionSq_expansion
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, r i j = r j i) (hn : 3 ≤ n) :
    let psi : Fin n → ℝ := fun i =>
      ∑ j ∈ Finset.univ.erase i, r i j
    let S : ℝ := ∑ i : Fin n, g i
    let Q : ℝ := ∑ i : Fin n, g i ^ 2
    let F : ℝ := Shao.OQ5.P35.unorderedPairSum r
    ((n : ℝ) - 1) *
        (Shao.OQ6.FiniteRows.uncenteredSq
          (fun i j => g i + g j + r i j) - Q / (n : ℝ)) =
      Q / (n : ℝ) +
        ((3 * (n : ℝ) - 4) / ((n : ℝ) - 2) ^ 2) * S ^ 2 +
        (2 / ((n : ℝ) - 2)) * (∑ i : Fin n, g i * psi i) +
        (4 / ((n : ℝ) - 2) ^ 2) * S * F +
        (∑ i : Fin n, psi i ^ 2) / ((n : ℝ) - 2) ^ 2 := by
  classical
  dsimp only
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hn))
  have h1 : (n : ℝ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    apply ne_of_gt
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn)
  have h2 : (n : ℝ) - 2 ≠ 0 := by
    apply sub_ne_zero.mpr
    apply ne_of_gt
    exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hn)
  have hpsi : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, r i j) =
      2 * Shao.OQ5.P35.unorderedPairSum r :=
    Shao.OQ5.P35.offDiagonalSum_eq_two_unordered r hr
  have hsum :
      (∑ i : Fin n,
        (((n : ℝ) - 2) * g i + (∑ j : Fin n, g j) +
          (∑ j ∈ Finset.univ.erase i, r i j)) ^ 2) =
        ((n : ℝ) - 2) ^ 2 * (∑ i : Fin n, g i ^ 2) +
          (3 * (n : ℝ) - 4) * (∑ i : Fin n, g i) ^ 2 +
          2 * ((n : ℝ) - 2) *
            (∑ i : Fin n, g i * (∑ j ∈ Finset.univ.erase i, r i j)) +
          4 * (∑ i : Fin n, g i) * Shao.OQ5.P35.unorderedPairSum r +
          (∑ i : Fin n, (∑ j ∈ Finset.univ.erase i, r i j) ^ 2) := by
    rw [finite_sum_affine_sq, hpsi]
    ring
  unfold uncenteredSq
  simp_rw [residual_rowMean_formula]
  simp only [div_pow]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [hsum]
  field_simp [hn0, h1, h2] <;> ring

end

end Shao.OQ6.FiniteRows
