import Shao.OQ5.P35.RowIdentity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators

namespace Shao.OQ5.P41.FiniteBackgroundPerturbation

noncomputable section
def anomaly {n : ℕ} (B : Finset (Fin n)) : Finset (Fin n)
:=
  Finset.univ \ B
def blockPairSum {n : ℕ} (S : Finset (Fin n))
    (r : Fin n → Fin n → ℝ) : ℝ
:=
  ∑ i ∈ S, ∑ j ∈ S, if i < j then r i j else 0
def crossPairSum {n : ℕ} (B : Finset (Fin n))
    (r : Fin n → Fin n → ℝ) : ℝ
:=
  ∑ a ∈ anomaly B, ∑ i ∈ B, r a i
def adjustedRow {n : ℕ} (g : Fin n → ℝ)
    (r : Fin n → Fin n → ℝ) (i : Fin n) : ℝ
:=
  g i + (∑ j ∈ Finset.univ.erase i, r i j) / ((n : ℝ) - 2)
def backgroundRow {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (i : Fin n) : ℝ
:=
  g i + (∑ j ∈ B.erase i, r i j) / ((n : ℝ) - 2)
def blockMean {n : ℕ} (B : Finset (Fin n)) (f : Fin n → ℝ) : ℝ
:=
  (∑ i ∈ B, f i) / (B.card : ℝ)
def blockCenteredEnergy {n : ℕ} (B : Finset (Fin n))
    (f : Fin n → ℝ) : ℝ
:=
  ∑ i ∈ B, (f i - blockMean B f) ^ (2 : ℕ)
def backgroundScale {n : ℕ} (B : Finset (Fin n)) : ℝ
:=
  ((B.card : ℝ) - 2) / ((n : ℝ) - 2)
def backgroundAnchor {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) : ℝ
:=
  blockMean B (adjustedRow g r) -
    Shao.OQ5.P35.unorderedPairSum r / (((n : ℝ) - 1) * ((n : ℝ) - 2))
def backgroundNumerator {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) : ℝ
:=
  ((∑ i ∈ B, g i) +
    ((B.card : ℝ) - 2) * blockPairSum B r /
      (((n : ℝ) - 2) * ((B.card : ℝ) - 1))) / Real.sqrt (B.card : ℝ)
def numeratorShift {n : ℕ} (B : Finset (Fin n))
    (r : Fin n → Fin n → ℝ) : ℝ
:=
  Real.sqrt (n : ℝ) *
    (((anomaly B).card : ℝ) * blockPairSum B r /
        (((n : ℝ) - 2) * ((n : ℝ) - 1) * ((B.card : ℝ) - 1)) +
      (((anomaly B).card : ℝ) - 1) * crossPairSum B r /
        ((B.card : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2)) -
      blockPairSum (anomaly B) r / (((n : ℝ) - 1) * ((n : ℝ) - 2)))
def anomalyWeight {n : ℕ} (B : Finset (Fin n)) (w : Fin n → ℝ) : ℝ
:=
  ∑ a ∈ anomaly B, w a
def backgroundWeightEnergy {n : ℕ} (B : Finset (Fin n))
    (w : Fin n → ℝ) : ℝ
:=
  ∑ i ∈ B, (w i) ^ (2 : ℕ)
def backgroundStudentizer {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) : ℝ
:=
  Real.sqrt (blockCenteredEnergy B (backgroundRow B g r) / ((B.card : ℝ) - 1))
theorem partition_card {n : ℕ} (B : Finset (Fin n)) :
    (anomaly B).card + B.card = n
:= by
  classical
  have hsub : B ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ B
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  simpa only [anomaly, Finset.card_univ, Fintype.card_fin] using hc
theorem background_denominators_and_scale {n : ℕ} (B : Finset (Fin n))
    (hn : 4 ≤ n) (hm : 3 ≤ B.card) :
    0 < (n : ℝ) - 2 ∧ 0 < (B.card : ℝ) - 2 ∧
      0 < (B.card : ℝ) - 1 ∧ 0 < (B.card : ℝ) ∧
      0 ≤ backgroundScale B ∧ backgroundScale B ≤ 1
:= by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM3 : (3 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hm
  have hcard : ((anomaly B).card : ℝ) + (B.card : ℝ) = (n : ℝ) := by
    exact_mod_cast (partition_card B)
  have hK0 : (0 : ℝ) ≤ ((anomaly B).card : ℝ) := Nat.cast_nonneg _
  have hMN : (B.card : ℝ) ≤ (n : ℝ) := by linarith
  have hd : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hm2 : (0 : ℝ) < (B.card : ℝ) - 2 := by linarith
  have hm1 : (0 : ℝ) < (B.card : ℝ) - 1 := by linarith
  have hm0 : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hlam0 : 0 ≤ backgroundScale B := div_nonneg hm2.le hd.le
  have hlam1 : backgroundScale B ≤ 1 := by
    unfold backgroundScale
    apply (div_le_iff₀ hd).2
    linarith
  exact ⟨hd, hm2, hm1, hm0, hlam0, hlam1⟩
theorem block_offDiagonal_sum {n : ℕ} (S : Finset (Fin n))
    (r : Fin n → Fin n → ℝ) (hsym : ∀ i j : Fin n, r i j = r j i) :
    (∑ i ∈ S, ∑ j ∈ S.erase i, r i j) = 2 * blockPairSum S r
:= by
  classical
  have hrow (i : Fin n) (hi : i ∈ S) :
      (∑ j ∈ S.erase i, r i j) = ∑ j ∈ S, if j ≠ i then r i j else 0 := by
    calc
      (∑ j ∈ S.erase i, r i j) =
          ∑ j ∈ S.erase i, if j ≠ i then r i j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [hji]
      _ = ∑ j ∈ S, if j ≠ i then r i j else 0 := by
        rw [Finset.sum_erase_eq_sub hi]
        simp
  have hlower :
      (∑ i ∈ S, ∑ j ∈ S, if j < i then r i j else 0) = blockPairSum S r := by
    unfold blockPairSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i < j
    · simp only [if_pos hij]
      exact hsym j i
    · simp [hij]
  calc
    (∑ i ∈ S, ∑ j ∈ S.erase i, r i j) =
        ∑ i ∈ S, ∑ j ∈ S, if j ≠ i then r i j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i hi
    _ = ∑ i ∈ S, ∑ j ∈ S,
        ((if i < j then r i j else 0) + (if j < i then r i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rcases lt_trichotomy i j with hij | hij | hji
      · simp [hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij)]
      · subst j
        simp
      · simp [hji, ne_of_lt hji, not_lt_of_ge (le_of_lt hji)]
    _ = blockPairSum S r +
        (∑ i ∈ S, ∑ j ∈ S, if j < i then r i j else 0) := by
      simp only [Finset.sum_add_distrib, blockPairSum]
    _ = 2 * blockPairSum S r := by rw [hlower]; ring
theorem unorderedPairSum_partition {n : ℕ} (B : Finset (Fin n))
    (r : Fin n → Fin n → ℝ) (hsym : ∀ i j : Fin n, r i j = r j i) :
    Shao.OQ5.P35.unorderedPairSum r =
      blockPairSum (anomaly B) r + blockPairSum B r + crossPairSum B r
:= by
  classical
  have hdisj : Disjoint (anomaly B) B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiA).2 hiB
  have hunion : anomaly B ∪ B = (Finset.univ : Finset (Fin n)) := by
    ext i
    by_cases hi : i ∈ B <;> simp [anomaly, hi]
  have hsplit (f : Fin n → ℝ) :
      (∑ i : Fin n, f i) = (∑ i ∈ anomaly B, f i) + ∑ i ∈ B, f i := by
    calc
      (∑ i : Fin n, f i) = ∑ i ∈ anomaly B ∪ B, f i := by rw [hunion]
      _ = (∑ i ∈ anomaly B, f i) + ∑ i ∈ B, f i := Finset.sum_union hdisj
  have hcross :
      (∑ i ∈ B, ∑ a ∈ anomaly B, r i a) = crossPairSum B r := by
    unfold crossPairSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro i hi
    exact hsym i a
  have hrowA (i : Fin n) (hi : i ∈ anomaly B) :
      (∑ j ∈ Finset.univ.erase i, r i j) =
        (∑ j ∈ (anomaly B).erase i, r i j) + ∑ j ∈ B, r i j := by
    rw [Finset.sum_erase_eq_sub (by simp), hsplit,
      Finset.sum_erase_eq_sub hi]
    ring
  have hrowB (i : Fin n) (hi : i ∈ B) :
      (∑ j ∈ Finset.univ.erase i, r i j) =
        (∑ a ∈ anomaly B, r i a) + ∑ j ∈ B.erase i, r i j := by
    rw [Finset.sum_erase_eq_sub (by simp), hsplit,
      Finset.sum_erase_eq_sub hi]
    ring
  have hsumA :
      (∑ i ∈ anomaly B, ∑ j ∈ Finset.univ.erase i, r i j) =
        2 * blockPairSum (anomaly B) r + crossPairSum B r := by
    calc
      (∑ i ∈ anomaly B, ∑ j ∈ Finset.univ.erase i, r i j) =
          ∑ i ∈ anomaly B,
            ((∑ j ∈ (anomaly B).erase i, r i j) + ∑ j ∈ B, r i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrowA i hi
      _ = 2 * blockPairSum (anomaly B) r + crossPairSum B r := by
        rw [Finset.sum_add_distrib, block_offDiagonal_sum (anomaly B) r hsym]
        rfl
  have hsumB :
      (∑ i ∈ B, ∑ j ∈ Finset.univ.erase i, r i j) =
        crossPairSum B r + 2 * blockPairSum B r := by
    calc
      (∑ i ∈ B, ∑ j ∈ Finset.univ.erase i, r i j) =
          ∑ i ∈ B, ((∑ a ∈ anomaly B, r i a) + ∑ j ∈ B.erase i, r i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrowB i hi
      _ = crossPairSum B r + 2 * blockPairSum B r := by
        rw [Finset.sum_add_distrib, hcross, block_offDiagonal_sum B r hsym]
  have hs := hsplit (fun i : Fin n => ∑ j ∈ Finset.univ.erase i, r i j)
  rw [hsumA, hsumB] at hs
  rw [Shao.OQ5.P35.offDiagonalSum_eq_two_unordered r hsym] at hs
  linarith only [hs]
theorem background_original_row_sum {n : ℕ} (B : Finset (Fin n))
    (r : Fin n → Fin n → ℝ) (hsym : ∀ i j : Fin n, r i j = r j i) :
    (∑ i ∈ B, ∑ j ∈ Finset.univ.erase i, r i j) =
      2 * blockPairSum B r + crossPairSum B r
:= by
  classical
  have hdisj : Disjoint (anomaly B) B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiA).2 hiB
  have hunion : anomaly B ∪ B = (Finset.univ : Finset (Fin n)) := by
    ext i
    by_cases hi : i ∈ B <;> simp [anomaly, hi]
  have hsplit (f : Fin n → ℝ) :
      (∑ i : Fin n, f i) = (∑ i ∈ anomaly B, f i) + ∑ i ∈ B, f i := by
    calc
      (∑ i : Fin n, f i) = ∑ i ∈ anomaly B ∪ B, f i := by rw [hunion]
      _ = (∑ i ∈ anomaly B, f i) + ∑ i ∈ B, f i := Finset.sum_union hdisj
  have hcross :
      (∑ i ∈ B, ∑ a ∈ anomaly B, r i a) = crossPairSum B r := by
    unfold crossPairSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro i hi
    exact hsym i a
  have hrow (i : Fin n) (hi : i ∈ B) :
      (∑ j ∈ Finset.univ.erase i, r i j) =
        (∑ a ∈ anomaly B, r i a) + ∑ j ∈ B.erase i, r i j := by
    rw [Finset.sum_erase_eq_sub (by simp), hsplit,
      Finset.sum_erase_eq_sub hi]
    ring
  calc
    (∑ i ∈ B, ∑ j ∈ Finset.univ.erase i, r i j) =
        ∑ i ∈ B, ((∑ a ∈ anomaly B, r i a) + ∑ j ∈ B.erase i, r i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i hi
    _ = 2 * blockPairSum B r + crossPairSum B r := by
      rw [Finset.sum_add_distrib, hcross, block_offDiagonal_sum B r hsym]
      ring
theorem adjustedRow_sub_backgroundRow {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (i : Fin n) (hi : i ∈ B) :
    adjustedRow g r i - backgroundRow B g r i =
      (∑ a ∈ anomaly B, r i a) / ((n : ℝ) - 2)
:= by
  classical
  have hdisj : Disjoint (anomaly B) B := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiA).2 hiB
  have hunion : anomaly B ∪ B = (Finset.univ : Finset (Fin n)) := by
    ext i
    by_cases hi : i ∈ B <;> simp [anomaly, hi]
  have hsplit (f : Fin n → ℝ) :
      (∑ i : Fin n, f i) = (∑ i ∈ anomaly B, f i) + ∑ i ∈ B, f i := by
    calc
      (∑ i : Fin n, f i) = ∑ i ∈ anomaly B ∪ B, f i := by rw [hunion]
      _ = (∑ i ∈ anomaly B, f i) + ∑ i ∈ B, f i := Finset.sum_union hdisj
  have hrow :
      (∑ j ∈ Finset.univ.erase i, r i j) =
        (∑ j ∈ B.erase i, r i j) + ∑ a ∈ anomaly B, r i a := by
    rw [Finset.sum_erase_eq_sub (by simp), hsplit,
      Finset.sum_erase_eq_sub hi]
    ring
  unfold adjustedRow backgroundRow
  rw [hrow]
  ring
theorem scaled_background_row_identity {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hn : 4 ≤ n) (hm : 3 ≤ B.card) (i : Fin n) :
    backgroundRow B g r i =
      g i + (∑ j ∈ B.erase i, backgroundScale B * r i j) / ((B.card : ℝ) - 2)
:= by
  have hb := background_denominators_and_scale B hn hm
  have hM2 : (B.card : ℝ) - 2 ≠ 0 := ne_of_gt hb.2.1
  have hN2 : (n : ℝ) - 2 ≠ 0 := ne_of_gt hb.1
  unfold backgroundRow backgroundScale
  rw [← Finset.mul_sum]
  field_simp [hM2, hN2]
  <;> ring
theorem backgroundAnchor_formula {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, r i j = r j i) :
    backgroundAnchor B g r =
      (∑ i ∈ B, g i) / (B.card : ℝ) +
      (2 * blockPairSum B r + crossPairSum B r) /
        ((B.card : ℝ) * ((n : ℝ) - 2)) -
      Shao.OQ5.P35.unorderedPairSum r / (((n : ℝ) - 1) * ((n : ℝ) - 2))
:= by
  have hs :
      (∑ i ∈ B, adjustedRow g r i) =
        (∑ i ∈ B, g i) +
          (2 * blockPairSum B r + crossPairSum B r) / ((n : ℝ) - 2) := by
    unfold adjustedRow
    rw [Finset.sum_add_distrib]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, background_original_row_sum B r hsym]
  unfold backgroundAnchor blockMean
  rw [hs]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
theorem backgroundNumerator_sqrt_scaling {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hn : 4 ≤ n) (hm : 3 ≤ B.card) :
    Real.sqrt ((n : ℝ) / (B.card : ℝ)) * backgroundNumerator B g r =
      Real.sqrt (n : ℝ) / (B.card : ℝ) *
        ((∑ i ∈ B, g i) + ((B.card : ℝ) - 2) * blockPairSum B r /
          (((n : ℝ) - 2) * ((B.card : ℝ) - 1)))
:= by
  have hb := background_denominators_and_scale B hn hm
  have hMpos : (0 : ℝ) < (B.card : ℝ) := hb.2.2.2.1
  have hNpos : (0 : ℝ) < (n : ℝ) := by linarith [hb.1]
  have hMne : (B.card : ℝ) ≠ 0 := ne_of_gt hMpos
  have hsMpos : (0 : ℝ) < Real.sqrt (B.card : ℝ) := Real.sqrt_pos.2 hMpos
  have hsMne : Real.sqrt (B.card : ℝ) ≠ 0 := ne_of_gt hsMpos
  have hratio : (0 : ℝ) ≤ (n : ℝ) / (B.card : ℝ) :=
    div_nonneg hNpos.le hMpos.le
  have hrootSq :
      (Real.sqrt ((n : ℝ) / (B.card : ℝ)) * Real.sqrt (B.card : ℝ)) ^ (2 : ℕ) =
        (Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt hratio, Real.sq_sqrt hMpos.le,
      Real.sq_sqrt hNpos.le]
    field_simp [hMne]
  have hroot0 :
      (0 : ℝ) ≤ Real.sqrt ((n : ℝ) / (B.card : ℝ)) * Real.sqrt (B.card : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hroot :
      Real.sqrt ((n : ℝ) / (B.card : ℝ)) * Real.sqrt (B.card : ℝ) =
        Real.sqrt (n : ℝ) :=
    le_antisymm ((sq_le_sq₀ hroot0 (Real.sqrt_nonneg _)).mp hrootSq.le)
      ((sq_le_sq₀ (Real.sqrt_nonneg _) hroot0).mp hrootSq.ge)
  have hscale (v : ℝ) :
      Real.sqrt ((n : ℝ) / (B.card : ℝ)) * (v / Real.sqrt (B.card : ℝ)) =
        Real.sqrt (n : ℝ) / (B.card : ℝ) * v := by
    calc
      Real.sqrt ((n : ℝ) / (B.card : ℝ)) * (v / Real.sqrt (B.card : ℝ)) =
          (Real.sqrt ((n : ℝ) / (B.card : ℝ)) * Real.sqrt (B.card : ℝ)) *
            v / (Real.sqrt (B.card : ℝ)) ^ (2 : ℕ) := by
        field_simp [hsMne]
        <;> ring
      _ = Real.sqrt (n : ℝ) / (B.card : ℝ) * v := by
        rw [hroot, Real.sq_sqrt hMpos.le]
        ring
  unfold backgroundNumerator
  exact hscale _
theorem background_numerator_perturbation {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, r i j = r j i)
    (hn : 4 ≤ n) (hm : 3 ≤ B.card) :
    Real.sqrt (n : ℝ) * backgroundAnchor B g r =
      Real.sqrt ((n : ℝ) / (B.card : ℝ)) * backgroundNumerator B g r +
        numeratorShift B r
:= by
  have hb := background_denominators_and_scale B hn hm
  have hN2 : (n : ℝ) - 2 ≠ 0 := ne_of_gt hb.1
  have hN1 : (n : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith [hb.1])
  have hM1 : (B.card : ℝ) - 1 ≠ 0 := ne_of_gt hb.2.2.1
  have hM : (B.card : ℝ) ≠ 0 := ne_of_gt hb.2.2.2.1
  have hc : ((anomaly B).card : ℝ) + (B.card : ℝ) = (n : ℝ) := by
    exact_mod_cast (partition_card B)
  have hK : ((anomaly B).card : ℝ) = (n : ℝ) - (B.card : ℝ) := by linarith
  rw [backgroundAnchor_formula B g r hsym,
    backgroundNumerator_sqrt_scaling B g r hn hm,
    unorderedPairSum_partition B r hsym]
  unfold numeratorShift
  rw [hK]
  field_simp [hN2, hN1, hM1, hM]
  <;> ring
theorem block_pair_product_identity {n : ℕ} (S : Finset (Fin n))
    (w : Fin n → ℝ) :
    (∑ i ∈ S, w i) ^ (2 : ℕ) =
      (∑ i ∈ S, (w i) ^ (2 : ℕ)) +
        2 * blockPairSum S (fun i j : Fin n => w i * w j)
:= by
  classical
  have hrow (i : Fin n) (hi : i ∈ S) :
      (∑ j ∈ S, w i * w j) =
        (w i) ^ (2 : ℕ) + ∑ j ∈ S.erase i, w i * w j := by
    rw [Finset.sum_erase_eq_sub hi]
    ring
  calc
    (∑ i ∈ S, w i) ^ (2 : ℕ) = ∑ i ∈ S, ∑ j ∈ S, w i * w j := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ = ∑ i ∈ S, ((w i) ^ (2 : ℕ) + ∑ j ∈ S.erase i, w i * w j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrow i hi
    _ = (∑ i ∈ S, (w i) ^ (2 : ℕ)) +
        2 * blockPairSum S (fun i j : Fin n => w i * w j) := by
      rw [Finset.sum_add_distrib,
        block_offDiagonal_sum S (fun i j : Fin n => w i * w j) (by
          intro i j
          ring)]
theorem anomaly_pair_envelope_bound {n : ℕ} (B : Finset (Fin n))
    (r : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ i : Fin n, 0 ≤ w i)
    (henv : ∀ i j : Fin n, i ≠ j → |r i j| ≤ w i * w j) :
    |blockPairSum (anomaly B) r| ≤ (anomalyWeight B w) ^ (2 : ℕ) / 2
:= by
  classical
  have habs (S : Finset (Fin n)) (f : Fin n → ℝ) :
      |∑ i ∈ S, f i| ≤ ∑ i ∈ S, |f i| := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact le_trans (abs_add_le _ _) (add_le_add_left ih _)
  have hbound :
      |blockPairSum (anomaly B) r| ≤
        blockPairSum (anomaly B) (fun i j : Fin n => w i * w j) := by
    unfold blockPairSum
    calc
      |∑ i ∈ anomaly B, ∑ j ∈ anomaly B, if i < j then r i j else 0| ≤
          ∑ i ∈ anomaly B, |∑ j ∈ anomaly B, if i < j then r i j else 0| :=
        habs _ _
      _ ≤ ∑ i ∈ anomaly B, ∑ j ∈ anomaly B, |if i < j then r i j else 0| := by
        apply Finset.sum_le_sum
        intro i hi
        exact habs _ _
      _ ≤ ∑ i ∈ anomaly B, ∑ j ∈ anomaly B, if i < j then w i * w j else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i < j
        · simp only [if_pos hij]
          exact henv i j (ne_of_lt hij)
        · simp [hij]
  have hid := block_pair_product_identity (anomaly B) w
  have hdiag : (0 : ℝ) ≤ ∑ i ∈ anomaly B, (w i) ^ (2 : ℕ) :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  unfold anomalyWeight
  nlinarith only [hbound, hid, hdiag]
theorem adjustedRow_sub_backgroundRow_bound {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (hn : 4 ≤ n) (hw : ∀ i : Fin n, 0 ≤ w i)
    (henv : ∀ i j : Fin n, i ≠ j → |r i j| ≤ w i * w j)
    (i : Fin n) (hi : i ∈ B) :
    |adjustedRow g r i - backgroundRow B g r i| ≤
      anomalyWeight B w * w i / ((n : ℝ) - 2)
:= by
  classical
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have habs (S : Finset (Fin n)) (f : Fin n → ℝ) :
      |∑ a ∈ S, f a| ≤ ∑ a ∈ S, |f a| := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      exact le_trans (abs_add_le _ _) (add_le_add_left ih _)
  rw [adjustedRow_sub_backgroundRow B g r i hi, abs_div, abs_of_pos hd]
  apply (div_le_div_iff_of_pos_right hd).2
  calc
    |∑ a ∈ anomaly B, r i a| ≤ ∑ a ∈ anomaly B, |r i a| := habs _ _
    _ ≤ ∑ a ∈ anomaly B, w i * w a := by
      apply Finset.sum_le_sum
      intro a ha
      have hai : a ≠ i := by
        intro heq
        subst a
        exact (Finset.mem_sdiff.mp ha).2 hi
      exact henv i a hai.symm
    _ = anomalyWeight B w * w i := by
      unfold anomalyWeight
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      ring
theorem blockCenteredEnergy_variance {n : ℕ} (B : Finset (Fin n))
    (f : Fin n → ℝ) (hB : 0 < B.card) :
    blockCenteredEnergy B f = (∑ i ∈ B, (f i) ^ (2 : ℕ)) -
      (∑ i ∈ B, f i) ^ (2 : ℕ) / (B.card : ℝ)
:= by
  have hMpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB
  have hMne : (B.card : ℝ) ≠ 0 := ne_of_gt hMpos
  have hcross :
      (∑ i ∈ B, 2 * f i * blockMean B f) =
        2 * (∑ i ∈ B, f i) * blockMean B f := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  unfold blockCenteredEnergy
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcross]
  simp only [Finset.sum_const, nsmul_eq_mul]
  unfold blockMean
  field_simp [hMne]
  <;> ring
theorem block_centering_contraction {n : ℕ} (B : Finset (Fin n))
    (f : Fin n → ℝ) (hB : 0 < B.card) :
    blockCenteredEnergy B f ≤ ∑ i ∈ B, (f i) ^ (2 : ℕ)
:= by
  have hMpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB
  rw [blockCenteredEnergy_variance B f hB]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hMpos.le)
theorem block_centered_norm_lipschitz {n : ℕ} (B : Finset (Fin n))
    (f h : Fin n → ℝ) (hB : 0 < B.card) :
    |Real.sqrt (blockCenteredEnergy B f) - Real.sqrt (blockCenteredEnergy B h)| ≤
      Real.sqrt (∑ i ∈ B, (f i - h i) ^ (2 : ℕ))
:= by
  let a : Fin n → ℝ := fun i => f i - blockMean B f
  let b : Fin n → ℝ := fun i => h i - blockMean B h
  let A2 : ℝ := ∑ i ∈ B, (a i) ^ (2 : ℕ)
  let B2 : ℝ := ∑ i ∈ B, (b i) ^ (2 : ℕ)
  let C : ℝ := ∑ i ∈ B, a i * b i
  have hA : 0 ≤ A2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hB2 : 0 ≤ B2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hpoint (i j : Fin n) :
      (a i * b j - a j * b i) ^ (2 : ℕ) =
        (a i) ^ (2 : ℕ) * (b j) ^ (2 : ℕ) +
          (a j) ^ (2 : ℕ) * (b i) ^ (2 : ℕ) -
            2 * (a i * b i) * (a j * b j) := by ring
  have hid :
      (∑ i ∈ B, ∑ j ∈ B, (a i * b j - a j * b i) ^ (2 : ℕ)) =
        2 * (A2 * B2) - 2 * C ^ (2 : ℕ) := by
    dsimp [A2, B2, C]
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hnon :
      (0 : ℝ) ≤ ∑ i ∈ B, ∑ j ∈ B, (a i * b j - a j * b i) ^ (2 : ℕ) :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg _))
  have hCS : C ^ (2 : ℕ) ≤ A2 * B2 := by linarith only [hid, hnon]
  have hroot0 : 0 ≤ Real.sqrt A2 * Real.sqrt B2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hroot2 :
      (Real.sqrt A2 * Real.sqrt B2) ^ (2 : ℕ) = A2 * B2 := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB2]
  have hCab : |C| ≤ Real.sqrt A2 * Real.sqrt B2 := by
    apply (sq_le_sq₀ (abs_nonneg C) hroot0).mp
    rw [sq_abs, hroot2]
    exact hCS
  have hC : C ≤ Real.sqrt A2 * Real.sqrt B2 :=
    le_trans (le_abs_self C) hCab
  have hmean :
      blockMean B (fun i : Fin n => f i - h i) = blockMean B f - blockMean B h := by
    simp only [blockMean, Finset.sum_sub_distrib, sub_div]
  have hdiff (i : Fin n) :
      f i - h i - blockMean B (fun j : Fin n => f j - h j) = a i - b i := by
    rw [hmean]
    dsimp [a, b]
    ring
  have hdiffSq (i : Fin n) :
      (a i - b i) ^ (2 : ℕ) =
        (a i) ^ (2 : ℕ) + (b i) ^ (2 : ℕ) - 2 * (a i * b i) := by ring
  have henergy :
      blockCenteredEnergy B (fun i : Fin n => f i - h i) = A2 + B2 - 2 * C := by
    unfold blockCenteredEnergy
    simp_rw [hdiff, hdiffSq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rfl
  have hcontr := block_centering_contraction B (fun i : Fin n => f i - h i) hB
  rw [henergy] at hcontr
  have hsq :
      (Real.sqrt A2 - Real.sqrt B2) ^ (2 : ℕ) ≤
        ∑ i ∈ B, (f i - h i) ^ (2 : ℕ) := by
    nlinarith only [Real.sq_sqrt hA, Real.sq_sqrt hB2, hC, hcontr]
  have hraw :
      (0 : ℝ) ≤ ∑ i ∈ B, (f i - h i) ^ (2 : ℕ) :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  change |Real.sqrt A2 - Real.sqrt B2| ≤
    Real.sqrt (∑ i ∈ B, (f i - h i) ^ (2 : ℕ))
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hraw]
  exact hsq
theorem row_difference_energy_bound {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (hn : 4 ≤ n) (hw : ∀ i : Fin n, 0 ≤ w i)
    (henv : ∀ i j : Fin n, i ≠ j → |r i j| ≤ w i * w j) :
    (∑ i ∈ B, (adjustedRow g r i - backgroundRow B g r i) ^ (2 : ℕ)) ≤
      (anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) * backgroundWeightEnergy B w
:= by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hell : 0 ≤ anomalyWeight B w :=
    Finset.sum_nonneg (fun a ha => hw a)
  have hbound (i : Fin n) (hi : i ∈ B) :
      (adjustedRow g r i - backgroundRow B g r i) ^ (2 : ℕ) ≤
        (anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) * (w i) ^ (2 : ℕ) := by
    have hh := adjustedRow_sub_backgroundRow_bound B g r w hn hw henv i hi
    have hright : 0 ≤ anomalyWeight B w * w i / ((n : ℝ) - 2) :=
      div_nonneg (mul_nonneg hell (hw i)) hd.le
    have hs := (sq_le_sq₀
      (abs_nonneg (adjustedRow g r i - backgroundRow B g r i)) hright).2 hh
    rw [sq_abs] at hs
    convert hs using 1 <;> ring
  calc
    (∑ i ∈ B, (adjustedRow g r i - backgroundRow B g r i) ^ (2 : ℕ)) ≤
        ∑ i ∈ B,
          (anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) * (w i) ^ (2 : ℕ) :=
      Finset.sum_le_sum hbound
    _ = (anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) *
        backgroundWeightEnergy B w := by
      rw [backgroundWeightEnergy, Finset.mul_sum]
theorem backgroundStudentizer_sqrt_identity {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (hm : 3 ≤ B.card) :
    Real.sqrt ((B.card : ℝ) - 1) * backgroundStudentizer B g r =
      Real.sqrt (blockCenteredEnergy B (backgroundRow B g r))
:= by
  have hM3 : (3 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hm
  have hd : (0 : ℝ) < (B.card : ℝ) - 1 := by linarith
  have hQ : 0 ≤ blockCenteredEnergy B (backgroundRow B g r) :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hquot :
      0 ≤ blockCenteredEnergy B (backgroundRow B g r) / ((B.card : ℝ) - 1) :=
    div_nonneg hQ hd.le
  have hprod0 :
      0 ≤ Real.sqrt ((B.card : ℝ) - 1) *
        Real.sqrt (blockCenteredEnergy B (backgroundRow B g r) / ((B.card : ℝ) - 1)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hs :
      (Real.sqrt ((B.card : ℝ) - 1) *
        Real.sqrt (blockCenteredEnergy B (backgroundRow B g r) / ((B.card : ℝ) - 1))) ^
          (2 : ℕ) = (Real.sqrt (blockCenteredEnergy B (backgroundRow B g r))) ^ (2 : ℕ) := by
    rw [mul_pow, Real.sq_sqrt hd.le, Real.sq_sqrt hquot, Real.sq_sqrt hQ]
    field_simp [ne_of_gt hd]
  unfold backgroundStudentizer
  exact le_antisymm ((sq_le_sq₀ hprod0 (Real.sqrt_nonneg _)).mp hs.le)
    ((sq_le_sq₀ (Real.sqrt_nonneg _) hprod0).mp hs.ge)
theorem background_centered_norm_perturbation {n : ℕ} (B : Finset (Fin n))
    (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (hn : 4 ≤ n) (hm : 3 ≤ B.card) (hw : ∀ i : Fin n, 0 ≤ w i)
    (henv : ∀ i j : Fin n, i ≠ j → |r i j| ≤ w i * w j) :
    |Real.sqrt (blockCenteredEnergy B (adjustedRow g r)) -
        Real.sqrt ((B.card : ℝ) - 1) * backgroundStudentizer B g r| ≤
      anomalyWeight B w * Real.sqrt (backgroundWeightEnergy B w) / ((n : ℝ) - 2)
:= by
  have hB : 0 < B.card := lt_of_lt_of_le (by norm_num : 0 < 3) hm
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hell : 0 ≤ anomalyWeight B w :=
    Finset.sum_nonneg (fun a ha => hw a)
  have hQ : 0 ≤ backgroundWeightEnergy B w :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hratio : 0 ≤ anomalyWeight B w / ((n : ℝ) - 2) := div_nonneg hell hd.le
  have hbound0 :
      0 ≤ (anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) *
        backgroundWeightEnergy B w :=
    mul_nonneg (sq_nonneg _) hQ
  have hright0 :
      0 ≤ anomalyWeight B w * Real.sqrt (backgroundWeightEnergy B w) / ((n : ℝ) - 2) :=
    div_nonneg (mul_nonneg hell (Real.sqrt_nonneg _)) hd.le
  have hsq :
      (Real.sqrt ((anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) *
        backgroundWeightEnergy B w)) ^ (2 : ℕ) =
      (anomalyWeight B w * Real.sqrt (backgroundWeightEnergy B w) / ((n : ℝ) - 2)) ^
        (2 : ℕ) := by
    rw [Real.sq_sqrt hbound0]
    simp only [div_pow, mul_pow, Real.sq_sqrt hQ]
    ring
  have hroot :
      Real.sqrt ((anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) *
        backgroundWeightEnergy B w) =
      anomalyWeight B w * Real.sqrt (backgroundWeightEnergy B w) / ((n : ℝ) - 2) :=
    le_antisymm ((sq_le_sq₀ (Real.sqrt_nonneg _) hright0).mp hsq.le)
      ((sq_le_sq₀ hright0 (Real.sqrt_nonneg _)).mp hsq.ge)
  rw [backgroundStudentizer_sqrt_identity B g r hm]
  calc
    |Real.sqrt (blockCenteredEnergy B (adjustedRow g r)) -
        Real.sqrt (blockCenteredEnergy B (backgroundRow B g r))| ≤
      Real.sqrt (∑ i ∈ B,
        (adjustedRow g r i - backgroundRow B g r i) ^ (2 : ℕ)) :=
      block_centered_norm_lipschitz B (adjustedRow g r) (backgroundRow B g r) hB
    _ ≤ Real.sqrt ((anomalyWeight B w / ((n : ℝ) - 2)) ^ (2 : ℕ) *
        backgroundWeightEnergy B w) :=
      Real.sqrt_le_sqrt (row_difference_energy_bound B g r w hn hw henv)
    _ = anomalyWeight B w * Real.sqrt (backgroundWeightEnergy B w) / ((n : ℝ) - 2) :=
      hroot
end

end Shao.OQ5.P41.FiniteBackgroundPerturbation
