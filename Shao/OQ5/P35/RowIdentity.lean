import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual degree-two jackknife row identity for p35

This file is finite deterministic algebra. The U-statistic is defined from the
unordered pair sum and is connected to row averages by a separate double-counting
proof. No probability statement or rare-category cancellation is included.

Source: current/oq56/inputs02/p35.md, lines 28–46, formula (3).
The real-valued pair count is proved equal to the cast of Nat.choose n 2.
-/

namespace Shao.OQ5.P35

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- The symmetric kernel matrix used in the p35 counterexample. -/
def kernel (A d Z : Fin n → ℝ) (i j : Fin n) : ℝ :=
  A i + A j + d i + d j - Z i * Z j

/-- Sum each unordered pair exactly once, by the order on Fin n. -/
def unorderedPairSum (H : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then H i j else 0

/-- The real-valued number of unordered pairs. -/
def pairCount (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) - 1) / 2

/-- The original unordered-pair U-statistic, not a definition by row averages. -/
def uStatistic (A d Z : Fin n → ℝ) : ℝ :=
  (pairCount n)⁻¹ * unorderedPairSum (kernel A d Z)

/-- The mean of row i excluding the diagonal entry. -/
def rowMean (A d Z : Fin n → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.erase i, kernel A d Z i j

/-- Arithmetic mean of a finite real vector. -/
def mean (f : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i : Fin n, f i

/-- Projection off the constant vector, expressed coordinatewise. -/
def center (f : Fin n → ℝ) (i : Fin n) : ℝ := f i - mean f

/-- The adjusted row vector b in p35. -/
def adjustedRow (A d Z : Fin n → ℝ) (i : Fin n) : ℝ :=
  A i + d i - Z i * ((∑ j : Fin n, Z j) - Z i) / ((n : ℝ) - 2)

/-- The square of the original centered-row jackknife Studentizer. -/
def studentizerSq (A d Z : Fin n → ℝ) : ℝ :=
  (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, (rowMean A d Z i - uStatistic A d Z) ^ 2

private theorem two_mul_choose_two (n : ℕ) :
    2 * (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp [Nat.choose]
  | succ n ih =>
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.cast_succ]
    calc
      2 * ((n : ℝ) + (n.choose 2 : ℝ)) =
          2 * (n : ℝ) + 2 * (n.choose 2 : ℝ) := by ring
      _ = 2 * (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) := by rw [ih]
      _ = ((n : ℝ) + 1) * (((n : ℝ) + 1) - 1) := by ring

/-- The denominator is exactly the original binomial normalization. -/
theorem pairCount_eq_choose (n : ℕ) : pairCount n = (n.choose 2 : ℝ) := by
  unfold pairCount
  apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  calc
    (n : ℝ) * ((n : ℝ) - 1) = 2 * (n.choose 2 : ℝ) :=
      (two_mul_choose_two n).symm
    _ = (n.choose 2 : ℝ) * 2 := by ring

theorem uStatistic_eq_choose_normalization (A d Z : Fin n → ℝ) :
    uStatistic A d Z =
      (n.choose 2 : ℝ)⁻¹ *
        (∑ i : Fin n, ∑ j : Fin n, if i < j then kernel A d Z i j else 0) := by
  rw [uStatistic, pairCount_eq_choose]
  rfl

theorem kernel_symmetric (A d Z : Fin n → ℝ) (i j : Fin n) :
    kernel A d Z i j = kernel A d Z j i := by
  unfold kernel
  ring

private theorem erasedRowSum_eq_indicator (H : Fin n → Fin n → ℝ) (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, H i j) =
      ∑ j : Fin n, if j ≠ i then H i j else 0 := by
  classical
  calc
    (∑ j ∈ Finset.univ.erase i, H i j) =
        ∑ j ∈ Finset.univ.erase i, if j ≠ i then H i j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := by simpa using (Finset.mem_erase.mp hj).1
      simp [hji]
    _ = ∑ j : Fin n, if j ≠ i then H i j else 0 :=
      Finset.sum_erase (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => if j ≠ i then H i j else 0) (a := i) (by simp)

/-- Double counting for any symmetric matrix, including n = 0 and n = 1. -/
theorem offDiagonalSum_eq_two_unordered
    (H : Fin n → Fin n → ℝ) (hH : ∀ i j, H i j = H j i) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, H i j) =
      2 * unorderedPairSum H := by
  classical
  have hlower :
      (∑ i : Fin n, ∑ j : Fin n, if j < i then H i j else 0) =
        unorderedPairSum H := by
    unfold unorderedPairSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      exact hH j i
    · simp [hij]
  calc
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, H i j) =
        ∑ i : Fin n, ∑ j : Fin n, if j ≠ i then H i j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact erasedRowSum_eq_indicator H i
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then H i j else 0) + (if j < i then H i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rcases lt_trichotomy i j with hij | hij | hji
      · simp [hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]
      · subst j
        simp
      · simp [hji, ne_of_lt hji, not_lt_of_ge (le_of_lt hji)]
    _ = unorderedPairSum H +
        (∑ i : Fin n, ∑ j : Fin n, if j < i then H i j else 0) := by
      simp only [Finset.sum_add_distrib, unorderedPairSum]
    _ = 2 * unorderedPairSum H := by rw [hlower]; ring

private theorem real_sampleSize_ne_zero (hn : 3 ≤ n) : (n : ℝ) ≠ 0 := by
  have h : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)

private theorem real_sampleSize_sub_one_ne_zero (hn : 3 ≤ n) :
    (n : ℝ) - 1 ≠ 0 := by
  have h : (1 : ℕ) < n := lt_of_lt_of_le (by decide : 1 < 3) hn
  have hc : ((1 : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h
  apply sub_ne_zero.mpr
  simpa only [Nat.cast_one] using (ne_of_gt hc)

private theorem real_sampleSize_sub_two_ne_zero (hn : 3 ≤ n) :
    (n : ℝ) - 2 ≠ 0 := by
  have h : (2 : ℕ) < n := lt_of_lt_of_le (by decide : 2 < 3) hn
  have hc : ((2 : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h
  apply sub_ne_zero.mpr
  simpa only [Nat.cast_ofNat] using (ne_of_gt hc)

/-- The actual row-mean formula, with all cross-coordinate terms retained. -/
theorem rowMean_formula (A d Z : Fin n → ℝ) (hn : 3 ≤ n) (i : Fin n) :
    rowMean A d Z i =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) * (A i + d i) +
        (∑ j : Fin n, (A j + d j)) / ((n : ℝ) - 1) -
        Z i * ((∑ j : Fin n, Z j) - Z i) / ((n : ℝ) - 1) := by
  have h1 := real_sampleSize_sub_one_ne_zero hn
  have hsum :
      (∑ j : Fin n, kernel A d Z i j) =
        (n : ℝ) * (A i + d i) +
          (∑ j : Fin n, (A j + d j)) - Z i * ∑ j : Fin n, Z j := by
    simp only [kernel, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  unfold rowMean
  rw [Finset.sum_erase_eq_sub (by simp), hsum]
  unfold kernel
  field_simp [h1]; ring

/-- The row means sum to n times the independently defined unordered-pair U. -/
theorem sum_rowMean (A d Z : Fin n → ℝ) (hn : 3 ≤ n) :
    (∑ i : Fin n, rowMean A d Z i) = (n : ℝ) * uStatistic A d Z := by
  have hn0 := real_sampleSize_ne_zero hn
  have h1 := real_sampleSize_sub_one_ne_zero hn
  calc
    (∑ i : Fin n, rowMean A d Z i) =
        ((n : ℝ) - 1)⁻¹ *
          (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, kernel A d Z i j) := by
      simp only [rowMean, Finset.mul_sum]
    _ = ((n : ℝ) - 1)⁻¹ * (2 * unorderedPairSum (kernel A d Z)) := by
      rw [offDiagonalSum_eq_two_unordered (kernel A d Z) (kernel_symmetric A d Z)]
    _ = (n : ℝ) * uStatistic A d Z := by
      unfold uStatistic pairCount
      field_simp [hn0, h1]

private theorem mean_rowMean (A d Z : Fin n → ℝ) (hn : 3 ≤ n) :
    mean (rowMean A d Z) = uStatistic A d Z := by
  have hn0 := real_sampleSize_ne_zero hn
  unfold mean
  rw [sum_rowMean A d Z hn]
  field_simp [hn0]

/-- Each centered original row is the prescribed multiple of the centered b row. -/
theorem centered_rowMean (A d Z : Fin n → ℝ) (hn : 3 ≤ n) (i : Fin n) :
    rowMean A d Z i - uStatistic A d Z =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) * center (adjustedRow A d Z) i := by
  have hn0 := real_sampleSize_ne_zero hn
  have h1 := real_sampleSize_sub_one_ne_zero hn
  have h2 := real_sampleSize_sub_two_ne_zero hn
  let a : ℝ := ((n : ℝ) - 2) / ((n : ℝ) - 1)
  let c : ℝ := (∑ j : Fin n, (A j + d j)) / ((n : ℝ) - 1)
  have hq : ∀ j, rowMean A d Z j = a * adjustedRow A d Z j + c := by
    intro j
    dsimp [a, c]
    rw [rowMean_formula A d Z hn j]
    unfold adjustedRow
    field_simp [h1, h2]; ring
  calc
    rowMean A d Z i - uStatistic A d Z = center (rowMean A d Z) i := by
      simp only [center, mean_rowMean A d Z hn]
    _ = a * center (adjustedRow A d Z) i := by
      unfold center mean
      simp_rw [hq]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hn0]; ring

/-- Formula (3) for the genuine centered-row Studentizer square. -/
theorem studentizerSq_eq_centeredRow (A d Z : Fin n → ℝ) (hn : 3 ≤ n) :
    studentizerSq A d Z =
      (4 / ((n : ℝ) - 1)) *
        ∑ i : Fin n, (center (adjustedRow A d Z) i) ^ 2 := by
  have h1 := real_sampleSize_sub_one_ne_zero hn
  have h2 := real_sampleSize_sub_two_ne_zero hn
  unfold studentizerSq
  simp_rw [centered_rowMean A d Z hn]
  simp only [mul_pow, ← Finset.mul_sum]
  field_simp [h1, h2]

end

end Shao.OQ5.P35
