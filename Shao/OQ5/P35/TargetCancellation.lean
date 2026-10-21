import Shao.OQ5.P35.RowIdentity

/-!
# Finite target-set cancellation for the original p35 construction

All vectors have the full sample dimension Fin n. The target set can be empty,
a singleton, or all coordinates. The two identities retain every interaction
between target and background coordinates. There is no probability statement.

Source: current/oq56/inputs02/p35.md, lines 48–64, formulas (4)–(6).
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- The real-valued target indicator. -/
def targetIndicator (J : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∈ J then 1 else 0

/-- The feature vector with target coordinates set to zero. -/
def backgroundFeature (J : Finset (Fin n)) (Z : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ J then 0 else Z i

/-- The offset vector with target coordinates set to zero. -/
def backgroundOffset (J : Finset (Fin n)) (d : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ J then 0 else d i

/-- The feature sum over background coordinates, represented in the full dimension. -/
def backgroundSum (J : Finset (Fin n)) (Z : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, backgroundFeature J Z i

/-- The background sum of squares, represented in the full dimension. -/
def backgroundSqSum (J : Finset (Fin n)) (Z : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (backgroundFeature J Z i) ^ 2

private theorem sum_targetIndicator (J : Finset (Fin n)) :
    (∑ i : Fin n, targetIndicator J i) = (J.card : ℝ) := by
  classical
  unfold targetIndicator
  rw [Finset.sum_ite_mem_eq]
  simp

private theorem sum_split_target (J : Finset (Fin n)) (f : Fin n → ℝ) (t : ℝ)
    (hf : ∀ i ∈ J, f i = t) :
    (∑ i : Fin n, f i) =
      (J.card : ℝ) * t + ∑ i : Fin n, if i ∈ J then 0 else f i := by
  classical
  have hpoint : ∀ i : Fin n,
      f i = t * targetIndicator J i + (if i ∈ J then 0 else f i) := by
    intro i
    by_cases hi : i ∈ J
    · simp [targetIndicator, hi, hf i hi]
    · simp [targetIndicator, hi]
  calc
    (∑ i : Fin n, f i) =
        ∑ i : Fin n, (t * targetIndicator J i + (if i ∈ J then 0 else f i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint i
    _ = t * (∑ i : Fin n, targetIndicator J i) +
        ∑ i : Fin n, if i ∈ J then 0 else f i := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (J.card : ℝ) * t + ∑ i : Fin n, if i ∈ J then 0 else f i := by
      rw [sum_targetIndicator J]
      ring

private theorem sum_feature (J : Finset (Fin n)) (Z : Fin n → ℝ) (t : ℝ)
    (hZ : ∀ i ∈ J, Z i = t) :
    (∑ i : Fin n, Z i) = (J.card : ℝ) * t + backgroundSum J Z := by
  simpa only [backgroundSum, backgroundFeature] using sum_split_target J Z t hZ

private theorem sum_offset (J : Finset (Fin n)) (d : Fin n → ℝ) (δ : ℝ)
    (hd : ∀ i ∈ J, d i = δ) :
    (∑ i : Fin n, d i) =
      (J.card : ℝ) * δ + ∑ i : Fin n, backgroundOffset J d i := by
  simpa only [backgroundOffset] using sum_split_target J d δ hd

private theorem sum_feature_sq (J : Finset (Fin n)) (Z : Fin n → ℝ) (t : ℝ)
    (hZ : ∀ i ∈ J, Z i = t) :
    (∑ i : Fin n, (Z i) ^ 2) = (J.card : ℝ) * t ^ 2 + backgroundSqSum J Z := by
  classical
  have htarget : ∀ i ∈ J, (Z i) ^ 2 = t ^ 2 := by
    intro i hi
    rw [hZ i hi]
  have hbg :
      (∑ i : Fin n, if i ∈ J then 0 else (Z i) ^ 2) = backgroundSqSum J Z := by
    unfold backgroundSqSum
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiJ : i ∈ J
    · simp [backgroundFeature, hiJ]
    · simp [backgroundFeature, hiJ]
  calc
    (∑ i : Fin n, (Z i) ^ 2) =
        (J.card : ℝ) * t ^ 2 +
          ∑ i : Fin n, if i ∈ J then 0 else (Z i) ^ 2 :=
      sum_split_target J (fun i => (Z i) ^ 2) (t ^ 2) htarget
    _ = (J.card : ℝ) * t ^ 2 + backgroundSqSum J Z := by rw [hbg]

private theorem target_size_ne_zero (hn : 3 ≤ n) : (n : ℝ) ≠ 0 := by
  have h : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hn
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)

private theorem target_size_sub_one_ne_zero (hn : 3 ≤ n) :
    (n : ℝ) - 1 ≠ 0 := by
  have h : (1 : ℕ) < n := lt_of_lt_of_le (by decide : 1 < 3) hn
  have hc : ((1 : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h
  apply sub_ne_zero.mpr
  simpa only [Nat.cast_one] using (ne_of_gt hc)

private theorem target_size_sub_two_ne_zero (hn : 3 ≤ n) :
    (n : ℝ) - 2 ≠ 0 := by
  have h : (2 : ℕ) < n := lt_of_lt_of_le (by decide : 2 < 3) hn
  have hc : ((2 : ℕ) : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h
  apply sub_ne_zero.mpr
  simpa only [Nat.cast_ofNat] using (ne_of_gt hc)

/-- A general finite-sum formula for the original unordered-pair U-statistic.
Its connection to unordered pairs is the double-counting theorem in RowIdentity. -/
theorem uStatistic_eq_sums (A d Z : Fin n → ℝ) (hn : 3 ≤ n) :
    uStatistic A d Z =
      (2 / (n : ℝ)) * (∑ i : Fin n, (A i + d i)) -
        (((∑ i : Fin n, Z i) ^ 2 - ∑ i : Fin n, (Z i) ^ 2) /
          ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hn0 := target_size_ne_zero hn
  have h1 := target_size_sub_one_ne_zero hn
  have hprod :
      (∑ i : Fin n, Z i * ((∑ j : Fin n, Z j) - Z i)) =
        (∑ i : Fin n, Z i) ^ 2 - ∑ i : Fin n, (Z i) ^ 2 := by
    calc
      (∑ i : Fin n, Z i * ((∑ j : Fin n, Z j) - Z i)) =
          ∑ i : Fin n, (Z i * (∑ j : Fin n, Z j) - (Z i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i : Fin n, Z i) * (∑ j : Fin n, Z j) -
          ∑ i : Fin n, (Z i) ^ 2 := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      _ = (∑ i : Fin n, Z i) ^ 2 - ∑ i : Fin n, (Z i) ^ 2 := by ring
  have hsumq :
      (∑ i : Fin n, rowMean A d Z i) =
        2 * (∑ i : Fin n, (A i + d i)) -
          (((∑ i : Fin n, Z i) ^ 2 - ∑ i : Fin n, (Z i) ^ 2) /
            ((n : ℝ) - 1)) := by
    simp_rw [rowMean_formula A d Z hn]
    simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [hprod]
    field_simp [h1]
    ring
  apply mul_left_cancel₀ hn0
  calc
    (n : ℝ) * uStatistic A d Z =
        2 * (∑ i : Fin n, (A i + d i)) -
          (((∑ i : Fin n, Z i) ^ 2 - ∑ i : Fin n, (Z i) ^ 2) /
            ((n : ℝ) - 1)) :=
      (sum_rowMean A d Z hn).symm.trans hsumq
    _ = (n : ℝ) *
        ((2 / (n : ℝ)) * (∑ i : Fin n, (A i + d i)) -
          (((∑ i : Fin n, Z i) ^ 2 - ∑ i : Fin n, (Z i) ^ 2) /
            ((n : ℝ) * ((n : ℝ) - 1)))) := by
      field_simp [hn0, h1]

/-- Formula (5): the tuned internal target term cancels in every adjusted row.
No restriction is placed on the cardinality of J. -/
theorem adjustedRow_eq_targetCancellation
    (A d Z : Fin n → ℝ) (hn : 3 ≤ n) (J : Finset (Fin n)) (t δ : ℝ)
    (hZ : ∀ i ∈ J, Z i = t) (hd : ∀ i ∈ J, d i = δ)
    (hδ : δ = ((J.card : ℝ) - 1) * t ^ 2 / ((n : ℝ) - 2)) (i : Fin n) :
    adjustedRow A d Z i =
      A i + backgroundOffset J d i -
        (t * backgroundSum J Z * targetIndicator J i +
          (J.card : ℝ) * t * backgroundFeature J Z i +
          backgroundFeature J Z i * (backgroundSum J Z - backgroundFeature J Z i)) /
          ((n : ℝ) - 2) := by
  classical
  have h2 := target_size_sub_two_ne_zero hn
  have hsum := sum_feature J Z t hZ
  unfold adjustedRow
  rw [hsum]
  by_cases hi : i ∈ J
  · simp [backgroundOffset, backgroundFeature, targetIndicator, hi, hZ i hi, hd i hi]
    rw [hδ]
    field_simp [h2]
    ring
  · simp [backgroundOffset, backgroundFeature, targetIndicator, hi]
    field_simp [h2]
    ring

/-- Formula (6): the full numerator retains the tuned target contribution.
The equality itself needs no positivity assumption on t, δ, or the size of J. -/
theorem uStatistic_eq_targetCancellation
    (A d Z : Fin n → ℝ) (hn : 3 ≤ n) (J : Finset (Fin n)) (t δ : ℝ)
    (hZ : ∀ i ∈ J, Z i = t) (hd : ∀ i ∈ J, d i = δ)
    (hδ : δ = ((J.card : ℝ) - 1) * t ^ 2 / ((n : ℝ) - 2)) :
    uStatistic A d Z =
      (J.card : ℝ) * δ / ((n : ℝ) - 1) +
        (2 / (n : ℝ)) * (∑ i : Fin n, A i) +
        (2 / (n : ℝ)) * (∑ i : Fin n, backgroundOffset J d i) -
        (2 * (J.card : ℝ) * t * backgroundSum J Z) /
          ((n : ℝ) * ((n : ℝ) - 1)) -
        (backgroundSum J Z ^ 2 - backgroundSqSum J Z) /
          ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hn0 := target_size_ne_zero hn
  have h1 := target_size_sub_one_ne_zero hn
  have h2 := target_size_sub_two_ne_zero hn
  rw [uStatistic_eq_sums A d Z hn, Finset.sum_add_distrib,
    sum_offset J d δ hd, sum_feature J Z t hZ, sum_feature_sq J Z t hZ]
  rw [hδ]
  field_simp [hn0, h1, h2]
  ring

end

end Shao.OQ5.P35
