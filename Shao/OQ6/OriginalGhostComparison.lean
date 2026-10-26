import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace Shao.OQ6.OriginalGhostComparison

theorem finite_sqrt_sum_sq_sub_le
    (n : ℕ) (a b : Fin n → ℝ) :
    Real.sqrt (∑ i : Fin n, (a i - b i) ^ (2 : ℕ)) ≤
      Real.sqrt (∑ i : Fin n, (a i) ^ (2 : ℕ)) +
        Real.sqrt (∑ i : Fin n, (b i) ^ (2 : ℕ)) := by
  let qa : ℝ := ∑ i : Fin n, (a i) ^ (2 : ℕ)
  let qb : ℝ := ∑ i : Fin n, (b i) ^ (2 : ℕ)
  let diffEnergy : ℝ := ∑ i : Fin n, (a i - b i) ^ (2 : ℕ)
  let cross : ℝ := ∑ i : Fin n, a i * b i
  let rootA : ℝ := Real.sqrt qa
  let rootB : ℝ := Real.sqrt qb
  let rootDiff : ℝ := Real.sqrt diffEnergy
  let lagrange : ℝ :=
    ∑ i : Fin n, ∑ j : Fin n, (a i * b j - a j * b i) ^ (2 : ℕ)
  let rootProduct : ℝ := rootA * rootB
  let rootSum : ℝ := rootA + rootB
  have hSquareOrder : ∀ x y : ℝ, (0 : ℝ) ≤ x → (0 : ℝ) ≤ y →
      x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) → x ≤ y := by
    intro x y hx hy hxy
    by_cases h : x ≤ y
    · exact h
    · have hyx : y < x := lt_of_not_ge h
      have hxpos : (0 : ℝ) < x := lt_of_le_of_lt hy hyx
      have hsumpos : (0 : ℝ) < x + y := add_pos_of_pos_of_nonneg hxpos hy
      have hproductpos : (0 : ℝ) < (x - y) * (x + y) :=
        mul_pos (sub_pos.mpr hyx) hsumpos
      nlinarith only [hxy, hproductpos]
  have hqa : (0 : ℝ) ≤ qa := by
    dsimp only [qa]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (a i)
  have hqb : (0 : ℝ) ≤ qb := by
    dsimp only [qb]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (b i)
  have hdiffNonneg : (0 : ℝ) ≤ diffEnergy := by
    dsimp only [diffEnergy]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (a i - b i)
  have hlagrangeNonneg : (0 : ℝ) ≤ lagrange := by
    dsimp only [lagrange]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg (a i * b j - a j * b i)
  have hproductAA :
      (∑ i : Fin n, ∑ j : Fin n, (a i) ^ (2 : ℕ) * (b j) ^ (2 : ℕ)) =
        qa * qb := by
    dsimp only [qa, qb]
    exact (Fintype.sum_mul_sum
      (fun i : Fin n => (a i) ^ (2 : ℕ))
      (fun j : Fin n => (b j) ^ (2 : ℕ))).symm
  have hproductBB :
      (∑ i : Fin n, ∑ j : Fin n, (a j) ^ (2 : ℕ) * (b i) ^ (2 : ℕ)) =
        qb * qa := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, (a j) ^ (2 : ℕ) * (b i) ^ (2 : ℕ)) =
          ∑ i : Fin n, ∑ j : Fin n, (b i) ^ (2 : ℕ) * (a j) ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      _ = qb * qa := by
        dsimp only [qa, qb]
        exact (Fintype.sum_mul_sum
          (fun i : Fin n => (b i) ^ (2 : ℕ))
          (fun j : Fin n => (a j) ^ (2 : ℕ))).symm
  have hproductCross :
      (∑ i : Fin n, ∑ j : Fin n,
        (2 : ℝ) * ((a i * b i) * (a j * b j))) =
        (2 : ℝ) * (cross * cross) := by
    dsimp only [cross]
    rw [Fintype.sum_mul_sum]
    simp_rw [Finset.mul_sum]
  have hlagrange :
      lagrange = (2 : ℝ) * (qa * qb - cross ^ (2 : ℕ)) := by
    calc
      lagrange = ∑ i : Fin n, ∑ j : Fin n,
          ((a i) ^ (2 : ℕ) * (b j) ^ (2 : ℕ) +
            (a j) ^ (2 : ℕ) * (b i) ^ (2 : ℕ) -
            (2 : ℝ) * ((a i * b i) * (a j * b j))) := by
        dsimp only [lagrange]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ i : Fin n, ∑ j : Fin n,
            (a i) ^ (2 : ℕ) * (b j) ^ (2 : ℕ)) +
          (∑ i : Fin n, ∑ j : Fin n,
            (a j) ^ (2 : ℕ) * (b i) ^ (2 : ℕ)) -
          (∑ i : Fin n, ∑ j : Fin n,
            (2 : ℝ) * ((a i * b i) * (a j * b j))) := by
        simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = qa * qb + qb * qa - (2 : ℝ) * (cross * cross) := by
        rw [hproductAA, hproductBB, hproductCross]
      _ = (2 : ℝ) * (qa * qb - cross ^ (2 : ℕ)) := by ring
  have hcsSq : cross ^ (2 : ℕ) ≤ qa * qb := by
    nlinarith only [hlagrange, hlagrangeNonneg]
  have hrootANonneg : (0 : ℝ) ≤ rootA := Real.sqrt_nonneg qa
  have hrootBNonneg : (0 : ℝ) ≤ rootB := Real.sqrt_nonneg qb
  have hrootDiffNonneg : (0 : ℝ) ≤ rootDiff := Real.sqrt_nonneg diffEnergy
  have hrootASq : rootA ^ (2 : ℕ) = qa := Real.sq_sqrt hqa
  have hrootBSq : rootB ^ (2 : ℕ) = qb := Real.sq_sqrt hqb
  have hrootDiffSq : rootDiff ^ (2 : ℕ) = diffEnergy := Real.sq_sqrt hdiffNonneg
  have hrootProductNonneg : (0 : ℝ) ≤ rootProduct :=
    mul_nonneg hrootANonneg hrootBNonneg
  have hrootProductSq : rootProduct ^ (2 : ℕ) = qa * qb := by
    change (rootA * rootB) ^ (2 : ℕ) = qa * qb
    calc
      (rootA * rootB) ^ (2 : ℕ) =
          rootA ^ (2 : ℕ) * rootB ^ (2 : ℕ) := by ring
      _ = qa * qb := by rw [hrootASq, hrootBSq]
  have hcrossLower : -cross ≤ rootProduct := by
    by_cases hc : (0 : ℝ) ≤ -cross
    · apply hSquareOrder (-cross) rootProduct hc hrootProductNonneg
      nlinarith only [hcsSq, hrootProductSq]
    · exact le_trans (le_of_lt (lt_of_not_ge hc)) hrootProductNonneg
  have hdiffIdentity : diffEnergy = qa + qb - (2 : ℝ) * cross := by
    dsimp only [diffEnergy, qa, qb, cross]
    calc
      (∑ i : Fin n, (a i - b i) ^ (2 : ℕ)) =
          ∑ i : Fin n, ((a i) ^ (2 : ℕ) + (b i) ^ (2 : ℕ) -
            (2 : ℝ) * (a i * b i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : Fin n, (a i) ^ (2 : ℕ)) +
          (∑ i : Fin n, (b i) ^ (2 : ℕ)) -
          (2 : ℝ) * (∑ i : Fin n, a i * b i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrootSumNonneg : (0 : ℝ) ≤ rootSum :=
    add_nonneg hrootANonneg hrootBNonneg
  have hrootSumSq : rootSum ^ (2 : ℕ) = qa + qb + (2 : ℝ) * rootProduct := by
    change (rootA + rootB) ^ (2 : ℕ) = qa + qb + (2 : ℝ) * (rootA * rootB)
    calc
      (rootA + rootB) ^ (2 : ℕ) =
          rootA ^ (2 : ℕ) + rootB ^ (2 : ℕ) +
            (2 : ℝ) * (rootA * rootB) := by ring
      _ = qa + qb + (2 : ℝ) * (rootA * rootB) := by rw [hrootASq, hrootBSq]
  have hdiffBound : diffEnergy ≤ rootSum ^ (2 : ℕ) := by
    nlinarith only [hdiffIdentity, hcrossLower, hrootSumSq]
  change rootDiff ≤ rootSum
  apply hSquareOrder rootDiff rootSum hrootDiffNonneg hrootSumNonneg
  nlinarith only [hrootDiffSq, hdiffBound]

theorem ghost_good_vector_tail_comparison
    (n : ℕ) (a b : Fin n → ℝ) (t : ℝ)
    (ht : (1 : ℝ) ≤ t)
    (ha : t * (Real.sqrt (∑ i : Fin n, (a i) ^ (2 : ℕ)) +
      (4 : ℝ) * Real.sqrt (n : ℝ)) < |∑ i : Fin n, a i|)
    (hbSum : |∑ i : Fin n, b i| ≤ (2 : ℝ) * Real.sqrt (n : ℝ))
    (hbSq : (∑ i : Fin n, (b i) ^ (2 : ℕ)) ≤ (4 : ℝ) * (n : ℝ)) :
    t * Real.sqrt (∑ i : Fin n, (a i - b i) ^ (2 : ℕ)) <
      |∑ i : Fin n, (a i - b i)| := by
  let nReal : ℝ := (n : ℝ)
  let sumA : ℝ := ∑ i : Fin n, a i
  let sumB : ℝ := ∑ i : Fin n, b i
  let sumDiff : ℝ := ∑ i : Fin n, (a i - b i)
  let qa : ℝ := ∑ i : Fin n, (a i) ^ (2 : ℕ)
  let qb : ℝ := ∑ i : Fin n, (b i) ^ (2 : ℕ)
  let diffEnergy : ℝ := ∑ i : Fin n, (a i - b i) ^ (2 : ℕ)
  let rootA : ℝ := Real.sqrt qa
  let rootB : ℝ := Real.sqrt qb
  let rootDiff : ℝ := Real.sqrt diffEnergy
  let rootN : ℝ := Real.sqrt nReal
  let rootFourN : ℝ := Real.sqrt ((4 : ℝ) * nReal)
  have hSquareOrder : ∀ x y : ℝ, (0 : ℝ) ≤ x → (0 : ℝ) ≤ y →
      x ^ (2 : ℕ) ≤ y ^ (2 : ℕ) → x ≤ y := by
    intro x y hx hy hxy
    by_cases h : x ≤ y
    · exact h
    · have hyx : y < x := lt_of_not_ge h
      have hxpos : (0 : ℝ) < x := lt_of_le_of_lt hy hyx
      have hsumpos : (0 : ℝ) < x + y := add_pos_of_pos_of_nonneg hxpos hy
      have hproductpos : (0 : ℝ) < (x - y) * (x + y) :=
        mul_pos (sub_pos.mpr hyx) hsumpos
      nlinarith only [hxy, hproductpos]
  have hnRealNonneg : (0 : ℝ) ≤ nReal := Nat.cast_nonneg n
  have hrootNNonneg : (0 : ℝ) ≤ rootN := Real.sqrt_nonneg nReal
  have hrootNSq : rootN ^ (2 : ℕ) = nReal := Real.sq_sqrt hnRealNonneg
  have hqbNonneg : (0 : ℝ) ≤ qb := by
    dsimp only [qb]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (b i)
  have hrootBNonneg : (0 : ℝ) ≤ rootB := Real.sqrt_nonneg qb
  have hrootBSq : rootB ^ (2 : ℕ) = qb := Real.sq_sqrt hqbNonneg
  have hfourNNonneg : (0 : ℝ) ≤ (4 : ℝ) * nReal := by
    nlinarith only [hnRealNonneg]
  have htwiceRootNNonneg : (0 : ℝ) ≤ (2 : ℝ) * rootN := by
    linarith only [hrootNNonneg]
  have hrootFourNNonneg : (0 : ℝ) ≤ rootFourN :=
    Real.sqrt_nonneg ((4 : ℝ) * nReal)
  have hrootFourNSq : rootFourN ^ (2 : ℕ) = (4 : ℝ) * nReal :=
    Real.sq_sqrt hfourNNonneg
  have hrootFourNIdentity : rootFourN = (2 : ℝ) * rootN := by
    change Real.sqrt ((4 : ℝ) * nReal) = (2 : ℝ) * rootN
    apply (Real.sqrt_eq_iff_eq_sq hfourNNonneg htwiceRootNNonneg).2
    nlinarith only [hrootNSq]
  have hqbBound : qb ≤ (4 : ℝ) * nReal := hbSq
  have hrootBBound : rootB ≤ rootFourN := by
    apply hSquareOrder rootB rootFourN hrootBNonneg hrootFourNNonneg
    nlinarith only [hrootBSq, hrootFourNSq, hqbBound]
  have hghostRoot : rootB ≤ (2 : ℝ) * rootN := by
    rw [← hrootFourNIdentity]
    exact hrootBBound
  have htNonneg : (0 : ℝ) ≤ t := by linarith only [ht]
  have haLocal : t * (rootA + (4 : ℝ) * rootN) < |sumA| := ha
  have hbSumLocal : |sumB| ≤ (2 : ℝ) * rootN := hbSum
  have hsumDiff : sumDiff = sumA - sumB := by
    dsimp only [sumDiff, sumA, sumB]
    exact Finset.sum_sub_distrib a b
  have htriangle : |sumA| ≤ |sumA - sumB| + |sumB| := by
    calc
      |sumA| = |(sumA - sumB) + sumB| := by rw [sub_add_cancel]
      _ ≤ |sumA - sumB| + |sumB| := abs_add_le (sumA - sumB) sumB
  have hreverse : |sumA| - (2 : ℝ) * rootN ≤ |sumA - sumB| := by
    linarith only [htriangle, hbSumLocal]
  have hstrict : t * rootA + ((4 : ℝ) * t - (2 : ℝ)) * rootN <
      |sumA| - (2 : ℝ) * rootN := by
    nlinarith only [haLocal]
  have hcoefficient : (2 : ℝ) * t ≤ (4 : ℝ) * t - (2 : ℝ) := by
    linarith only [ht]
  have hcoefficientScaled : ((2 : ℝ) * t) * rootN ≤
      ((4 : ℝ) * t - (2 : ℝ)) * rootN :=
    mul_le_mul_of_nonneg_right hcoefficient hrootNNonneg
  have hslack : t * (rootA + (2 : ℝ) * rootN) ≤
      t * rootA + ((4 : ℝ) * t - (2 : ℝ)) * rootN := by
    nlinarith only [hcoefficientScaled]
  have hghostScaled : t * (rootA + rootB) ≤
      t * (rootA + (2 : ℝ) * rootN) := by
    apply mul_le_mul_of_nonneg_left ?_ htNonneg
    linarith only [hghostRoot]
  have hminkowski : rootDiff ≤ rootA + rootB :=
    finite_sqrt_sum_sq_sub_le n a b
  have hminkowskiScaled : t * rootDiff ≤ t * (rootA + rootB) :=
    mul_le_mul_of_nonneg_left hminkowski htNonneg
  change t * rootDiff < |sumDiff|
  calc
    t * rootDiff ≤ t * (rootA + rootB) := hminkowskiScaled
    _ ≤ t * (rootA + (2 : ℝ) * rootN) := hghostScaled
    _ ≤ t * rootA + ((4 : ℝ) * t - (2 : ℝ)) * rootN := hslack
    _ < |sumA| - (2 : ℝ) * rootN := hstrict
    _ ≤ |sumA - sumB| := hreverse
    _ = |sumDiff| := by rw [hsumDiff]

end Shao.OQ6.OriginalGhostComparison
