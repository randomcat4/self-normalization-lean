import Shao.OQ6.FiniteRows
import Shao.OQ5.P35.TargetCancellation

/-!
# Finite positive-rank-one balanced blocks

Deterministic algebra from original p45, lines 10–49, used by p53, lines 90–103.
The actual unordered-pair U-statistic, row means, and original jackknife square
are imported from FiniteRows. No probability, moment, or operator claim is made.
-/

set_option autoImplicit false

namespace Shao.OQ5.P45

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- The positive-residual kernel of p45 (1). -/
def positiveKernel (G Z : Fin n → ℝ) (i j : Fin n) : ℝ :=
  G i + G j + Z i * Z j

/-- The adjusted row b in p45 (2), with the original real denominator. -/
def adjustedRow (G Z : Fin n → ℝ) (i : Fin n) : ℝ :=
  G i + Z i * ((∑ j : Fin n, Z j) - Z i) / ((n : ℝ) - 2)

/-- The deterministic information from the balanced target configuration. -/
def BalancedTarget (A G Z : Fin n → ℝ) (J : Finset (Fin n))
    (t d : ℝ) : Prop :=
  (∀ i ∈ J, G i = A i + d) ∧
  (∀ i ∈ J, (Z i) ^ 2 = t ^ 2) ∧
  (∑ i ∈ J, Z i) = 0 ∧
  d = t ^ 2 / ((n : ℝ) - 2)

private theorem kernel_eq_neg_old (G Z : Fin n → ℝ) (i j : Fin n) :
    positiveKernel G Z i j =
      -Shao.OQ5.P35.kernel (fun k => -G k) (fun _ => 0) Z i j := by
  unfold positiveKernel Shao.OQ5.P35.kernel
  ring

private theorem rowMean_eq_neg_old (G Z : Fin n → ℝ) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (positiveKernel G Z) i =
      -Shao.OQ5.P35.rowMean (fun k => -G k) (fun _ => 0) Z i := by
  unfold Shao.OQ6.FiniteRows.rowMean Shao.OQ5.P35.rowMean
  simp_rw [kernel_eq_neg_old]
  rw [Finset.sum_neg_distrib]
  ring

private theorem uStatistic_eq_neg_old (G Z : Fin n → ℝ) :
    Shao.OQ6.FiniteRows.uStatistic (positiveKernel G Z) =
      -Shao.OQ5.P35.uStatistic (fun k => -G k) (fun _ => 0) Z := by
  have hp : Shao.OQ5.P35.unorderedPairSum (positiveKernel G Z) =
      -Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ5.P35.kernel (fun k => -G k) (fun _ => 0) Z) := by
    unfold Shao.OQ5.P35.unorderedPairSum
    calc
      (∑ i : Fin n, ∑ j : Fin n, if i < j then positiveKernel G Z i j else 0) =
          ∑ i : Fin n, ∑ j : Fin n,
            -(if i < j then
                Shao.OQ5.P35.kernel (fun k => -G k) (fun _ => 0) Z i j else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs
        · exact kernel_eq_neg_old G Z i j
        · exact neg_zero.symm
      _ = -(∑ i : Fin n, ∑ j : Fin n,
          if i < j then
            Shao.OQ5.P35.kernel (fun k => -G k) (fun _ => 0) Z i j else 0) := by
        simp only [Finset.sum_neg_distrib]
  unfold Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.uStatistic
  rw [Shao.OQ5.P35.pairCount_eq_choose, hp]
  ring

private theorem adjustedRow_eq_neg_old (G Z : Fin n → ℝ) (i : Fin n) :
    adjustedRow G Z i =
      -Shao.OQ5.P35.adjustedRow (fun k => -G k) (fun _ => 0) Z i := by
  unfold adjustedRow Shao.OQ5.P35.adjustedRow
  ring

private theorem center_adjustedRow_eq_neg_old (G Z : Fin n → ℝ) (i : Fin n) :
    Shao.OQ5.P35.center (adjustedRow G Z) i =
      -Shao.OQ5.P35.center
        (Shao.OQ5.P35.adjustedRow (fun k => -G k) (fun _ => 0) Z) i := by
  unfold Shao.OQ5.P35.center Shao.OQ5.P35.mean
  simp_rw [adjustedRow_eq_neg_old]
  rw [Finset.sum_neg_distrib]
  ring

private theorem real_size_ne_zero (hn : 3 ≤ n) : (n : ℝ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hn))

private theorem real_size_sub_one_ne_zero (hn : 3 ≤ n) : (n : ℝ) - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  apply ne_of_gt
  exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hn)

private theorem real_size_sub_two_ne_zero (hn : 3 ≤ n) : (n : ℝ) - 2 ≠ 0 := by
  apply sub_ne_zero.mpr
  apply ne_of_gt
  exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hn)

private theorem sum_split_target (J : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) =
      (∑ i ∈ J, f i) + (∑ i : Fin n, if i ∈ J then 0 else f i) := by
  classical
  have hp : ∀ i : Fin n,
      f i = (if i ∈ J then f i else 0) + (if i ∈ J then 0 else f i) := by
    intro i
    split_ifs <;> simp
  calc
    (∑ i : Fin n, f i) =
        ∑ i : Fin n, ((if i ∈ J then f i else 0) +
          (if i ∈ J then 0 else f i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hp i
    _ = (∑ i ∈ J, f i) + (∑ i : Fin n, if i ∈ J then 0 else f i) := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_mem_eq]

private theorem sum_feature_eq_background (J : Finset (Fin n)) (Z : Fin n → ℝ)
    (hbalance : (∑ i ∈ J, Z i) = 0) :
    (∑ i : Fin n, Z i) = Shao.OQ5.P35.backgroundSum J Z := by
  rw [sum_split_target J Z, hbalance, zero_add]
  rfl

private theorem sum_feature_sq (J : Finset (Fin n)) (Z : Fin n → ℝ) (t : ℝ)
    (hsq : ∀ i ∈ J, (Z i) ^ 2 = t ^ 2) :
    (∑ i : Fin n, (Z i) ^ 2) =
      (J.card : ℝ) * t ^ 2 + Shao.OQ5.P35.backgroundSqSum J Z := by
  classical
  have ht : (∑ i ∈ J, (Z i) ^ 2) = (J.card : ℝ) * t ^ 2 := by
    calc
      (∑ i ∈ J, (Z i) ^ 2) = ∑ i ∈ J, t ^ 2 := by
        apply Finset.sum_congr rfl
        exact hsq
      _ = (J.card : ℝ) * t ^ 2 := by simp
  have hb : (∑ i : Fin n, if i ∈ J then 0 else (Z i) ^ 2) =
      Shao.OQ5.P35.backgroundSqSum J Z := by
    unfold Shao.OQ5.P35.backgroundSqSum
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ J <;> simp [Shao.OQ5.P35.backgroundFeature, hi]
  rw [sum_split_target J (fun i => (Z i) ^ 2), ht, hb]

private theorem sum_projection (A G : Fin n → ℝ) (J : Finset (Fin n)) (d : ℝ)
    (hG : ∀ i ∈ J, G i = A i + d) :
    (∑ i : Fin n, G i) =
      (∑ i ∈ J, A i) + (J.card : ℝ) * d +
        (∑ i : Fin n, if i ∈ J then 0 else G i) := by
  have ht : (∑ i ∈ J, G i) = (∑ i ∈ J, A i) + (J.card : ℝ) * d := by
    calc
      (∑ i ∈ J, G i) = ∑ i ∈ J, (A i + d) := by
        apply Finset.sum_congr rfl
        exact hG
      _ = (∑ i ∈ J, A i) + (J.card : ℝ) * d := by
        rw [Finset.sum_add_distrib]
        simp
  rw [sum_split_target J G, ht]

private theorem uStatistic_eq_sums (G Z : Fin n → ℝ) (hn : 3 ≤ n) :
    Shao.OQ6.FiniteRows.uStatistic (positiveKernel G Z) =
      (2 / (n : ℝ)) * (∑ i : Fin n, G i) +
        ((∑ i : Fin n, Z i) ^ 2 - ∑ i : Fin n, (Z i) ^ 2) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
  rw [uStatistic_eq_neg_old,
    Shao.OQ5.P35.uStatistic_eq_sums (fun k => -G k) (fun _ => 0) Z hn]
  simp only [add_zero, Finset.sum_neg_distrib]
  ring

theorem positiveKernel_symmetric (G Z : Fin n → ℝ) (i j : Fin n) :
    positiveKernel G Z i j = positiveKernel G Z j i := by
  unfold positiveKernel
  ring

theorem centered_rowMean (G Z : Fin n → ℝ) (hn : 3 ≤ n) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (positiveKernel G Z) i -
        Shao.OQ6.FiniteRows.uStatistic (positiveKernel G Z) =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
        Shao.OQ5.P35.center (adjustedRow G Z) i := by
  rw [rowMean_eq_neg_old, uStatistic_eq_neg_old, center_adjustedRow_eq_neg_old]
  calc
    -Shao.OQ5.P35.rowMean (fun k => -G k) (fun _ => 0) Z i -
        -Shao.OQ5.P35.uStatistic (fun k => -G k) (fun _ => 0) Z =
      -(Shao.OQ5.P35.rowMean (fun k => -G k) (fun _ => 0) Z i -
        Shao.OQ5.P35.uStatistic (fun k => -G k) (fun _ => 0) Z) := by ring
    _ = -((((n : ℝ) - 2) / ((n : ℝ) - 1)) *
        Shao.OQ5.P35.center
          (Shao.OQ5.P35.adjustedRow (fun k => -G k) (fun _ => 0) Z) i) := by
      rw [Shao.OQ5.P35.centered_rowMean (fun k => -G k) (fun _ => 0) Z hn i]
    _ = _ := by ring

theorem jackknifeSq_eq_centeredRow (G Z : Fin n → ℝ) (hn : 3 ≤ n) :
    Shao.OQ6.FiniteRows.jackknifeSq (positiveKernel G Z) =
      (4 / ((n : ℝ) - 1)) *
        ∑ i : Fin n, (Shao.OQ5.P35.center (adjustedRow G Z) i) ^ 2 := by
  have h1 := real_size_sub_one_ne_zero hn
  have h2 := real_size_sub_two_ne_zero hn
  unfold Shao.OQ6.FiniteRows.jackknifeSq
  simp_rw [centered_rowMean G Z hn]
  simp only [mul_pow, ← Finset.mul_sum]
  field_simp [h1, h2]

theorem adjustedRow_eq_target (A G Z : Fin n → ℝ) (hn : 3 ≤ n)
    (J : Finset (Fin n)) (t d : ℝ)
    (hblock : BalancedTarget A G Z J t d) (i : Fin n) (hi : i ∈ J) :
    adjustedRow G Z i =
      A i + Z i * Shao.OQ5.P35.backgroundSum J Z / ((n : ℝ) - 2) := by
  rcases hblock with ⟨hG, hsq, hbalance, hd⟩
  have h2 := real_size_sub_two_ne_zero hn
  unfold adjustedRow
  rw [sum_feature_eq_background J Z hbalance, hG i hi, hd, ← hsq i hi]
  field_simp [h2]
  ring

theorem adjustedRow_eq_background (G Z : Fin n → ℝ) (hn : 3 ≤ n)
    (J : Finset (Fin n)) (hbalance : (∑ j ∈ J, Z j) = 0)
    (i : Fin n) (hi : i ∉ J) :
    adjustedRow G Z i =
      G i + Z i * (Shao.OQ5.P35.backgroundSum J Z - Z i) /
        ((n : ℝ) - 2) := by
  have h2 := real_size_sub_two_ne_zero hn
  have hfeature : Shao.OQ5.P35.backgroundFeature J Z i = Z i := by
    simp [Shao.OQ5.P35.backgroundFeature, hi]
  calc
    adjustedRow G Z i =
        G i + Shao.OQ5.P35.backgroundFeature J Z i *
          (Shao.OQ5.P35.backgroundSum J Z - Shao.OQ5.P35.backgroundFeature J Z i) /
            ((n : ℝ) - 2) := by
      unfold adjustedRow
      rw [sum_feature_eq_background J Z hbalance, hfeature]
    _ = _ := by
      field_simp [h2]
      rw [hfeature]

theorem uStatistic_eq_balancedBlock (A G Z : Fin n → ℝ) (hn : 3 ≤ n)
    (J : Finset (Fin n)) (t d : ℝ)
    (hblock : BalancedTarget A G Z J t d) :
    Shao.OQ6.FiniteRows.uStatistic (positiveKernel G Z) =
      (J.card : ℝ) * d / ((n : ℝ) - 1) +
        (2 / (n : ℝ)) * (∑ i ∈ J, A i) +
        (2 / (n : ℝ)) * (∑ i : Fin n, if i ∈ J then 0 else G i) +
        (Shao.OQ5.P35.backgroundSum J Z ^ 2 -
            Shao.OQ5.P35.backgroundSqSum J Z) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
  rcases hblock with ⟨hG, hsq, hbalance, hd⟩
  have hn0 := real_size_ne_zero hn
  have h1 := real_size_sub_one_ne_zero hn
  have h2 := real_size_sub_two_ne_zero hn
  rw [uStatistic_eq_sums G Z hn, sum_projection A G J d hG,
    sum_feature_eq_background J Z hbalance, sum_feature_sq J Z t hsq, hd]
  field_simp [hn0, h1, h2]
  ring

end

end Shao.OQ5.P45
