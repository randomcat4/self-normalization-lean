/- Exact frozen unit196 finite studentizer geometry.
Author implementation candidate; not machine checked. -/

import Shao.OQ6.FiniteRows

import Shao.OQ6.CanonicalDoubleGhostRowMoments

import Shao.OQ6.CanonicalDoubleGhostScalarMoments

import Mathlib.Analysis.Real.Sqrt

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

universe u

open scoped BigOperators

open Shao.OQ6.CanonicalDoubleGhostRowMoments (originalRows)

open Shao.OQ6.CanonicalDoubleGhostScalarMoments (originalUpper)

namespace Shao.OQ5.P51

noncomputable section

-- D01

def sampledKernel
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → Fin n → ℝ :=
  fun (i j : Fin n) => g (x i) + g (x j) + r (x i) (x j)

-- D02

def projectionEnergy
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, (g (x i)) ^ (2 : ℕ)) / (n : ℝ)

-- D03

def projectionV
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Real.sqrt (projectionEnergy n g x)

-- D04

def projectionW
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (∑ i : Fin n, g (x i)) / Real.sqrt (n : ℝ)

-- D05

def residualStatisticD
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  originalUpper n r x / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))

-- D06

def residualU
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : Fin n → ℝ :=
  fun i : Fin n => originalRows n r x i / ((n : ℝ) - 2)

-- D07

def residualEnergyJ
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, (residualU n r x i) ^ (2 : ℕ)

-- D08

def centeredSq
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (sampledKernel n g r x) / 4

-- D09

def centeredDelta
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  @ite ℝ (projectionV n g x = 0)
    (Classical.propDecidable (projectionV n g x = 0))
    (0 : ℝ) (centeredSq n g r x / (projectionV n g x) ^ (2 : ℕ) - 1)

-- D10

def projectionGood
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (y : ℝ) : Set (Fin n → Ω) :=
  {x : Fin n → Ω | (1 / 2 : ℝ) ≤ projectionEnergy n g x ∧
    |projectionW n g x| ≤ Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ)) * (4 + projectionV n g x)}

-- D11

def studentizerGeometryScale (K : ℝ) : ℝ :=
  (200 : ℝ) * (1 + K + Real.sqrt K)

-- D12

theorem projectionV_sq
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) :
    (projectionV n g x) ^ (2 : ℕ) = projectionEnergy n g x := by
  unfold projectionV
  apply Real.sq_sqrt
  exact div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg (g (x i))))
    (Nat.cast_nonneg n)

-- D13

theorem residualU_eq_erased_row
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) (i : Fin n) :
    residualU n r x i =
      (∑ j ∈ Finset.univ.erase i, r (x i) (x j)) / ((n : ℝ) - 2) := by
  have hrow : originalRows n r x i =
      ∑ j ∈ Finset.univ.erase i, r (x i) (x j) := by
    unfold originalRows
    simp only [PiLp.toLp_apply]
    rw [← Finset.sum_erase (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => @ite ℝ (i = j) (instDecidableEqFin n i j)
        (0 : ℝ) (r (x i) (x j))) (a := i) (by simp)]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp only [if_neg (Ne.symm hji)]
  unfold residualU
  rw [hrow]

-- D14

theorem residualEnergyJ_eq_rows_norm_sq_div
    (n : ℕ) {Ω : Type u}
    (r : Ω → Ω → ℝ) (x : Fin n → Ω) :
    residualEnergyJ n r x =
      ‖originalRows n r x‖ ^ (2 : ℕ) / ((n : ℝ) - 2) ^ (2 : ℕ) := by
  unfold residualEnergyJ residualU
  simp only [div_pow]
  rw [← Finset.sum_div, EuclideanSpace.real_norm_sq_eq]

-- D15

theorem sampled_uStatistic_formula
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n) :
    Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r x) =
      2 * (∑ i : Fin n, g (x i)) / (n : ℝ) +
        2 * originalUpper n r x / ((n : ℝ) * ((n : ℝ) - 1)) := by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (n : ℝ) ≠ 0 := by linarith
  have hN1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hH : ∀ i j : Fin n,
      sampledKernel n g r x i j = sampledKernel n g r x j i := by
    intro i j
    unfold sampledKernel
    rw [hsym (x i) (x j)]
    ring
  have hR : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, r (x i) (x j)) =
      2 * originalUpper n r x := by
    simpa only [Shao.OQ5.P35.unorderedPairSum, originalUpper] using
      (Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
        (fun (i j : Fin n) => r (x i) (x j))
        (fun i j => hsym (x i) (x j)))
  have hrow (i : Fin n) :
      (∑ j ∈ Finset.univ.erase i, sampledKernel n g r x i j) =
        ((n : ℝ) - 2) * g (x i) + (∑ j : Fin n, g (x j)) +
          (∑ j ∈ Finset.univ.erase i, r (x i) (x j)) := by
    have hsum : (∑ j : Fin n, (g (x i) + g (x j))) =
        (n : ℝ) * g (x i) + (∑ j : Fin n, g (x j)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have herase : (∑ j ∈ Finset.univ.erase i, (g (x i) + g (x j))) =
        ((n : ℝ) - 2) * g (x i) + (∑ j : Fin n, g (x j)) := by
      rw [Finset.sum_erase_eq_sub (by simp), hsum]
      ring
    unfold sampledKernel
    rw [Finset.sum_add_distrib, herase]
  have htotal :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, sampledKernel n g r x i j) =
        2 * ((n : ℝ) - 1) * (∑ i : Fin n, g (x i)) +
          2 * originalUpper n r x := by
    simp_rw [hrow]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hR]
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hpair : Shao.OQ5.P35.unorderedPairSum (sampledKernel n g r x) =
      ((n : ℝ) - 1) * (∑ i : Fin n, g (x i)) + originalUpper n r x := by
    have hd := Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
      (sampledKernel n g r x) hH
    nlinarith only [hd, htotal]
  unfold Shao.OQ6.FiniteRows.uStatistic
  rw [← Shao.OQ5.P35.pairCount_eq_choose n, hpair]
  unfold Shao.OQ5.P35.pairCount
  field_simp [hN0, hN1] <;> ring

-- D16

theorem sampled_centered_row_formula
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (sampledKernel n g r x) i -
        Shao.OQ6.FiniteRows.uStatistic (sampledKernel n g r x) =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
        Shao.OQ5.P35.center (fun j : Fin n => g (x j) + residualU n r x j) i := by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (n : ℝ) ≠ 0 := by linarith
  have hN1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hN2 : (n : ℝ) - 2 ≠ 0 := by linarith
  have hR : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, r (x i) (x j)) =
      2 * originalUpper n r x := by
    simpa only [Shao.OQ5.P35.unorderedPairSum, originalUpper] using
      (Shao.OQ5.P35.offDiagonalSum_eq_two_unordered
        (fun (i j : Fin n) => r (x i) (x j))
        (fun i j => hsym (x i) (x j)))
  have hU : (∑ j : Fin n, residualU n r x j) =
      2 * originalUpper n r x / ((n : ℝ) - 2) := by
    simp_rw [residualU_eq_erased_row]
    rw [← Finset.sum_div, hR]
  have hrow :
      (∑ j ∈ Finset.univ.erase i, sampledKernel n g r x i j) =
        ((n : ℝ) - 2) * g (x i) + (∑ j : Fin n, g (x j)) +
          (∑ j ∈ Finset.univ.erase i, r (x i) (x j)) := by
    have hsum : (∑ j : Fin n, (g (x i) + g (x j))) =
        (n : ℝ) * g (x i) + (∑ j : Fin n, g (x j)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have herase : (∑ j ∈ Finset.univ.erase i, (g (x i) + g (x j))) =
        ((n : ℝ) - 2) * g (x i) + (∑ j : Fin n, g (x j)) := by
      rw [Finset.sum_erase_eq_sub (by simp), hsum]
      ring
    unfold sampledKernel
    rw [Finset.sum_add_distrib, herase]
  rw [Shao.OQ6.FiniteRows.rowMean, hrow,
    sampled_uStatistic_formula n g r x hsym hn]
  unfold Shao.OQ5.P35.center Shao.OQ5.P35.mean
  rw [Finset.sum_add_distrib, hU]
  dsimp only
  rw [residualU_eq_erased_row]
  field_simp [hN0, hN1, hN2] <;> ring

-- D17

theorem centeredSq_eq_center_sum
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n) :
    centeredSq n g r x =
      (∑ i : Fin n,
        (Shao.OQ5.P35.center (fun j : Fin n => g (x j) + residualU n r x j) i) ^ (2 : ℕ)) /
        ((n : ℝ) - 1) := by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hN2 : (n : ℝ) - 2 ≠ 0 := by linarith
  unfold centeredSq Shao.OQ6.FiniteRows.jackknifeSq
  simp_rw [sampled_centered_row_formula n g r x hsym hn]
  simp only [mul_pow, div_pow, ← Finset.mul_sum]
  field_simp [hN1, hN2] <;> ring

-- D18

theorem centeredDelta_eq_zero_of_projectionV_eq_zero
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) (hV : projectionV n g x = 0) :
    centeredDelta n g r x = 0 := by
  unfold centeredDelta
  rw [if_pos hV]

-- D19

theorem centered_denominator_identity
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n)
    (hV : 0 < projectionV n g x) :
    centeredDelta n g r x =
      ((projectionV n g x) ^ (2 : ℕ) - (projectionW n g x) ^ (2 : ℕ) +
          2 * (∑ i : Fin n,
            Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
              Shao.OQ5.P35.center (residualU n r x) i) +
          (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ (2 : ℕ))) /
        (((n : ℝ) - 1) * (projectionV n g x) ^ (2 : ℕ)) := by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0p : (0 : ℝ) < (n : ℝ) := by linarith
  have hN0 : (n : ℝ) ≠ 0 := ne_of_gt hN0p
  have hN1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hroot : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hN0p.le
  have hvariance (z : Fin n → ℝ) :
      (∑ i : Fin n, (Shao.OQ5.P35.center z i) ^ 2) =
        (∑ i : Fin n, (z i) ^ 2) - (∑ i : Fin n, z i) ^ 2 / (n : ℝ) := by
    have hcross :
        (∑ i : Fin n, 2 * z i * ((n : ℝ)⁻¹ * ∑ j : Fin n, z j)) =
          2 * (∑ i : Fin n, z i) * ((n : ℝ)⁻¹ * ∑ j : Fin n, z j) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    unfold Shao.OQ5.P35.center Shao.OQ5.P35.mean
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hcross]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hN0] <;> ring
  have hlinear (i : Fin n) :
      Shao.OQ5.P35.center (fun j : Fin n => g (x j) + residualU n r x j) i =
        Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i +
          Shao.OQ5.P35.center (residualU n r x) i := by
    simp only [Shao.OQ5.P35.center, Shao.OQ5.P35.mean, Finset.sum_add_distrib]
    ring
  have hexpand :
      (∑ i : Fin n,
        (Shao.OQ5.P35.center (fun j : Fin n => g (x j) + residualU n r x j) i) ^ 2) =
      (∑ i : Fin n, (Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i) ^ 2) +
        2 * (∑ i : Fin n,
          Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
            Shao.OQ5.P35.center (residualU n r x) i) +
        (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2) := by
    simp_rw [hlinear, add_sq]
    simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hQ : (∑ i : Fin n, (g (x i)) ^ 2) =
      (n : ℝ) * (projectionV n g x) ^ 2 := by
    rw [projectionV_sq]
    unfold projectionEnergy
    field_simp [hN0] <;> ring
  have hW : (∑ i : Fin n, g (x i)) ^ 2 / (n : ℝ) =
      (projectionW n g x) ^ 2 := by
    unfold projectionW
    rw [div_pow, hroot]
  unfold centeredDelta
  rw [if_neg (ne_of_gt hV), centeredSq_eq_center_sum n g r x hsym hn,
    hexpand, hvariance, hQ, hW]
  field_simp [hN1, ne_of_gt hV] <;> ring

-- D20

theorem centered_geometry
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) (hn : 4 ≤ n) :
    (∑ i : Fin n, (Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i) ^ (2 : ℕ)) ≤
        (n : ℝ) * (projectionV n g x) ^ (2 : ℕ) ∧
      (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ (2 : ℕ)) ≤
        residualEnergyJ n r x ∧
      |∑ i : Fin n,
        Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
          Shao.OQ5.P35.center (residualU n r x) i| ≤
        Real.sqrt (n : ℝ) * projectionV n g x * Real.sqrt (residualEnergyJ n r x) := by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0p : (0 : ℝ) < (n : ℝ) := by linarith
  have hN0 : (n : ℝ) ≠ 0 := ne_of_gt hN0p
  have hvariance (z : Fin n → ℝ) :
      (∑ i : Fin n, (Shao.OQ5.P35.center z i) ^ 2) =
        (∑ i : Fin n, (z i) ^ 2) - (∑ i : Fin n, z i) ^ 2 / (n : ℝ) := by
    have hcross :
        (∑ i : Fin n, 2 * z i * ((n : ℝ)⁻¹ * ∑ j : Fin n, z j)) =
          2 * (∑ i : Fin n, z i) * ((n : ℝ)⁻¹ * ∑ j : Fin n, z j) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    unfold Shao.OQ5.P35.center Shao.OQ5.P35.mean
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hcross]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hN0] <;> ring
  have hcs (a b : Fin n → ℝ) :
      (∑ i : Fin n, a i * b i) ^ 2 ≤
        (∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2) := by
    have hpoint (i j : Fin n) :
        (a i * b j - a j * b i) ^ 2 =
          (a i) ^ 2 * (b j) ^ 2 + (a j) ^ 2 * (b i) ^ 2 -
            2 * (a i * b i) * (a j * b j) := by ring
    have hid : (∑ i : Fin n, ∑ j : Fin n, (a i * b j - a j * b i) ^ 2) =
        2 * ((∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2)) -
          2 * (∑ i : Fin n, a i * b i) ^ 2 := by
      simp_rw [hpoint]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hnon : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (a i * b j - a j * b i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    linarith only [hid, hnon]
  have hQ : (∑ i : Fin n, (g (x i)) ^ 2) =
      (n : ℝ) * (projectionV n g x) ^ 2 := by
    rw [projectionV_sq]
    unfold projectionEnergy
    field_simp [hN0] <;> ring
  have hA :
      (∑ i : Fin n, (Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i) ^ 2) ≤
        (n : ℝ) * (projectionV n g x) ^ 2 := by
    rw [hvariance, hQ]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hN0p.le)
  have hB :
      (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2) ≤
        residualEnergyJ n r x := by
    rw [hvariance]
    unfold residualEnergyJ
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hN0p.le)
  have hA0 :
      0 ≤ ∑ i : Fin n, (Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB0 : 0 ≤ ∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hJ0 : 0 ≤ residualEnergyJ n r x :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hV0 : 0 ≤ projectionV n g x := Real.sqrt_nonneg _
  have hC := hcs (Shao.OQ5.P35.center (fun j : Fin n => g (x j)))
    (Shao.OQ5.P35.center (residualU n r x))
  have hAB := mul_le_mul hA hB hB0 (mul_nonneg hN0p.le (sq_nonneg (projectionV n g x)))
  have hC2 :
      (∑ i : Fin n,
        Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
          Shao.OQ5.P35.center (residualU n r x) i) ^ 2 ≤
        (n : ℝ) * (projectionV n g x) ^ 2 * residualEnergyJ n r x :=
    le_trans hC hAB
  have hroot :
      (Real.sqrt (n : ℝ) * projectionV n g x * Real.sqrt (residualEnergyJ n r x)) ^ 2 =
        (n : ℝ) * (projectionV n g x) ^ 2 * residualEnergyJ n r x := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hN0p.le, Real.sq_sqrt hJ0]
  refine ⟨hA, hB, ?_⟩
  have hr0 : 0 ≤ Real.sqrt (n : ℝ) * projectionV n g x *
      Real.sqrt (residualEnergyJ n r x) := by positivity
  have ha0 := abs_nonneg (∑ i : Fin n,
    Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
      Shao.OQ5.P35.center (residualU n r x) i)
  have ha2 := sq_abs (∑ i : Fin n,
    Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
      Shao.OQ5.P35.center (residualU n r x) i)
  apply (sq_le_sq₀ ha0 hr0).mp
  rw [sq_abs, hroot]
  exact hC2

-- D21

theorem projectionGood_bounds
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (x : Fin n → Ω) (y : ℝ)
    (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y) (hGood : x ∈ projectionGood n g y) :
    0 < projectionV n g x ∧
      (1 / 2 : ℝ) ≤ projectionV n g x ∧
      (projectionW n g x) ^ (2 : ℕ) / (projectionV n g x) ^ (2 : ℕ) ≤
        (81 : ℝ) * y * Real.sqrt (n : ℝ) := by
  rcases hGood with ⟨hE, hW⟩
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hV0 : 0 ≤ projectionV n g x := Real.sqrt_nonneg _
  have hV2 : (1 / 2 : ℝ) ≤ (projectionV n g x) ^ 2 := by
    rw [projectionV_sq]
    exact hE
  have hVp : 0 < projectionV n g x := by nlinarith only [hV0, hV2]
  have hVhalf : (1 / 2 : ℝ) ≤ projectionV n g x := by
    by_contra hnot
    have hlt : projectionV n g x < (1 / 2 : ℝ) := lt_of_not_ge hnot
    have hh := mul_nonneg (sub_nonneg.mpr hlt.le) hV0
    nlinarith only [hV2, hlt, hh]
  have hfour : 4 + projectionV n g x ≤ 9 * projectionV n g x := by linarith
  have hbound : |projectionW n g x| ≤
      9 * (Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ))) * projectionV n g x := by
    calc
      |projectionW n g x| ≤ Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ)) *
          (4 + projectionV n g x) := hW
      _ ≤ Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ)) *
          (9 * projectionV n g x) :=
        mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := by ring
  have hb0 : 0 ≤ 9 * (Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ))) *
      projectionV n g x := by positivity
  have hb2 :
      (9 * (Real.sqrt y * Real.sqrt (Real.sqrt (n : ℝ))) * projectionV n g x) ^ 2 =
        81 * y * Real.sqrt (n : ℝ) * (projectionV n g x) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hy0,
      Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))]
    ring
  have hW2 : (projectionW n g x) ^ 2 ≤
      81 * y * Real.sqrt (n : ℝ) * (projectionV n g x) ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hbound)
      (add_nonneg (abs_nonneg (projectionW n g x)) hb0)
    nlinarith only [sq_abs (projectionW n g x), hb2, hh]
  refine ⟨hVp, hVhalf, ?_⟩
  exact (div_le_iff₀ (sq_pos_of_pos hVp)).2 hW2

-- D22

theorem bounded_studentizer_geometry
    (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (x : Fin n → Ω) (K q y : ℝ)
    (hsym : ∀ a b : Ω, r a b = r b a) (hn : 4 ≤ n)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hy : (1 : ℝ) ≤ y)
    (hF : |originalUpper n r x| ≤ K * (n : ℝ) * q)
    (hRows : ‖originalRows n r x‖ ^ (2 : ℕ) ≤ K * (n : ℝ) ^ (2 : ℕ) * q)
    (hGood : x ∈ projectionGood n g y) :
    residualEnergyJ n r x ≤ 4 * K * q ∧
      |residualStatisticD n r x| / projectionV n g x ≤
        4 * K * q / Real.sqrt (n : ℝ) ∧
      |centeredDelta n g r x| ≤
        164 * y / Real.sqrt (n : ℝ) +
          16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) + 16 * K * q / (n : ℝ) ∧
      |centeredDelta n g r x| ≤
        studentizerGeometryScale K *
          (y / Real.sqrt (n : ℝ) + Real.sqrt (q / (n : ℝ)) + q / (n : ℝ)) := by
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hN1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hN1half : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
  have hqN : 0 ≤ q / (n : ℝ) := div_nonneg hq hN0.le
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hrootN0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hN0
  have hrootN2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hN0.le
  have hrootK2 : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  have hrootqN2 : (Real.sqrt (q / (n : ℝ))) ^ 2 = q / (n : ℝ) :=
    Real.sq_sqrt hqN
  have hgood := projectionGood_bounds n g x y hn hy hGood
  have hV : 0 < projectionV n g x := hgood.1
  have hVhalf : (1 / 2 : ℝ) ≤ projectionV n g x := hgood.2.1
  have hV2 : (1 / 2 : ℝ) ≤ (projectionV n g x) ^ 2 := by
    rw [projectionV_sq]
    exact hGood.1
  have hV2p : 0 < (projectionV n g x) ^ 2 := sq_pos_of_pos hV
  have hden0 : 0 < ((n : ℝ) - 1) * (projectionV n g x) ^ 2 := mul_pos hN1 hV2p
  have hJ0 : 0 ≤ residualEnergyJ n r x :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hrootJ2 : (Real.sqrt (residualEnergyJ n r x)) ^ 2 = residualEnergyJ n r x :=
    Real.sq_sqrt hJ0
  have hratio : (n : ℝ) / ((n : ℝ) - 1) ≤ 2 :=
    (div_le_iff₀ hN1).2 (by linarith)
  have hratio0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) :=
    div_nonneg hN0.le hN1.le
  have hVinv : 1 / projectionV n g x ≤ 2 :=
    (div_le_iff₀ hV).2 (by linarith)
  have hVinv0 : 0 ≤ 1 / projectionV n g x := by positivity
  have hproduct : ((n : ℝ) / ((n : ℝ) - 1)) * (1 / projectionV n g x) ≤ 4 := by
    have hh := mul_le_mul hratio hVinv hVinv0 (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh]
  have hN2square : (n : ℝ) ^ 2 ≤ 4 * ((n : ℝ) - 2) ^ 2 := by
    nlinarith only [hN4, sq_nonneg ((n : ℝ) - 4)]
  have hJ : residualEnergyJ n r x ≤ 4 * K * q := by
    rw [residualEnergyJ_eq_rows_norm_sq_div]
    apply (div_le_iff₀ (sq_pos_of_pos hN2)).2
    have hh := mul_nonneg (mul_nonneg hK hq) (sub_nonneg.mpr hN2square)
    nlinarith only [hRows, hh]
  have hD : |residualStatisticD n r x| / projectionV n g x ≤
      4 * K * q / Real.sqrt (n : ℝ) := by
    have hDabs : |residualStatisticD n r x| / projectionV n g x =
        |originalUpper n r x| /
          (Real.sqrt (n : ℝ) * ((n : ℝ) - 1) * projectionV n g x) := by
      unfold residualStatisticD
      rw [abs_div, abs_of_pos (mul_pos hrootN0 hN1)]
      field_simp [ne_of_gt hV, ne_of_gt hrootN0, ne_of_gt hN1] <;> ring
    calc
      |residualStatisticD n r x| / projectionV n g x = _ := hDabs
      _ ≤ (K * (n : ℝ) * q) /
          (Real.sqrt (n : ℝ) * ((n : ℝ) - 1) * projectionV n g x) :=
        div_le_div_of_nonneg_right hF (by positivity)
      _ = (K * q) * (((n : ℝ) / ((n : ℝ) - 1)) * (1 / projectionV n g x)) /
          Real.sqrt (n : ℝ) := by
        field_simp [ne_of_gt hN1, ne_of_gt hV, ne_of_gt hrootN0] <;> ring
      _ ≤ (K * q) * 4 / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hproduct (mul_nonneg hK hq)) hrootN0.le
      _ = _ := by ring
  have hrootJ0 : 0 ≤ Real.sqrt (residualEnergyJ n r x) / Real.sqrt (n : ℝ) := by positivity
  have hrootJ : Real.sqrt (residualEnergyJ n r x) / Real.sqrt (n : ℝ) ≤
      2 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) := by
    have hleft : (Real.sqrt (residualEnergyJ n r x) / Real.sqrt (n : ℝ)) ^ 2 =
        residualEnergyJ n r x / (n : ℝ) := by
      rw [div_pow, hrootJ2, hrootN2]
    have hright : (2 * Real.sqrt K * Real.sqrt (q / (n : ℝ))) ^ 2 =
        4 * K * (q / (n : ℝ)) := by
      rw [mul_pow, mul_pow, hrootK2, hrootqN2]
      ring
    have hquot : residualEnergyJ n r x / (n : ℝ) ≤ 4 * K * (q / (n : ℝ)) := by
      calc
        residualEnergyJ n r x / (n : ℝ) ≤ (4 * K * q) / (n : ℝ) :=
          div_le_div_of_nonneg_right hJ hN0.le
        _ = _ := by ring
    have hr0 : 0 ≤ 2 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) := by positivity
    apply (sq_le_sq₀ hrootJ0 hr0).mp
    rw [hleft, hright]
    exact hquot
  have hbase : 1 / ((n : ℝ) - 1) ≤ 2 * y / Real.sqrt (n : ℝ) := by
    have hroot1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      by_contra hnot
      have hlt : Real.sqrt (n : ℝ) < 1 := lt_of_not_ge hnot
      have hh := mul_nonneg (sub_nonneg.mpr hlt.le) hrootN0.le
      nlinarith only [hN4, hrootN2, hlt, hh]
    have hrootle : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      nlinarith only [hrootN2,
        mul_nonneg (sub_nonneg.mpr hroot1) (Real.sqrt_nonneg (n : ℝ))]
    calc
      1 / ((n : ℝ) - 1) = ((n : ℝ) / ((n : ℝ) - 1)) / (n : ℝ) := by
        field_simp [ne_of_gt hN0, ne_of_gt hN1] <;> ring
      _ ≤ 2 / (n : ℝ) := div_le_div_of_nonneg_right hratio hN0.le
      _ ≤ 2 / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hrootN0 hrootle
      _ ≤ 2 * y / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right (by linarith : (2 : ℝ) ≤ 2 * y) hrootN0.le
  have hWterm : (projectionW n g x) ^ 2 /
      (((n : ℝ) - 1) * (projectionV n g x) ^ 2) ≤
        162 * y / Real.sqrt (n : ℝ) := by
    calc
      (projectionW n g x) ^ 2 / (((n : ℝ) - 1) * (projectionV n g x) ^ 2) =
          ((projectionW n g x) ^ 2 / (projectionV n g x) ^ 2) / ((n : ℝ) - 1) := by
        field_simp [ne_of_gt hN1, ne_of_gt hV] <;> ring
      _ ≤ (81 * y * Real.sqrt (n : ℝ)) / ((n : ℝ) - 1) :=
        div_le_div_of_nonneg_right hgood.2.2 hN1.le
      _ = (81 * y / Real.sqrt (n : ℝ)) * ((n : ℝ) / ((n : ℝ) - 1)) := by
        field_simp [ne_of_gt hN1, ne_of_gt hrootN0] <;> ring_nf <;> simp only [hrootN2] <;> ring
      _ ≤ (81 * y / Real.sqrt (n : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hcrossTerm : (2 * (Real.sqrt (n : ℝ) * projectionV n g x *
      Real.sqrt (residualEnergyJ n r x))) /
        (((n : ℝ) - 1) * (projectionV n g x) ^ 2) ≤
          16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) := by
    calc
      (2 * (Real.sqrt (n : ℝ) * projectionV n g x * Real.sqrt (residualEnergyJ n r x))) /
          (((n : ℝ) - 1) * (projectionV n g x) ^ 2) =
        2 * (((n : ℝ) / ((n : ℝ) - 1)) * (1 / projectionV n g x)) *
          (Real.sqrt (residualEnergyJ n r x) / Real.sqrt (n : ℝ)) := by
        field_simp [ne_of_gt hN1, ne_of_gt hV, ne_of_gt hrootN0] <;> ring_nf <;> simp only [hrootN2] <;> ring
      _ ≤ 2 * 4 * (Real.sqrt (residualEnergyJ n r x) / Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hproduct (by norm_num)) hrootJ0
      _ = 8 * (Real.sqrt (residualEnergyJ n r x) / Real.sqrt (n : ℝ)) := by ring
      _ ≤ 8 * (2 * Real.sqrt K * Real.sqrt (q / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hrootJ (by norm_num)
      _ = _ := by ring
  have hden : (n : ℝ) ≤ 4 * (((n : ℝ) - 1) * (projectionV n g x) ^ 2) := by
    have hh1 := mul_nonneg (sub_nonneg.mpr hN1half) (sq_nonneg (projectionV n g x))
    have hh2 := mul_nonneg hN0.le (sub_nonneg.mpr hV2)
    nlinarith only [hh1, hh2]
  have hJterm : residualEnergyJ n r x /
      (((n : ℝ) - 1) * (projectionV n g x) ^ 2) ≤ 16 * K * q / (n : ℝ) := by
    apply (div_le_iff₀ hden0).2
    have hprod : (4 * K * q) * (n : ℝ) ≤
        (16 * K * q) * (((n : ℝ) - 1) * (projectionV n g x) ^ 2) := by
      have hh := mul_nonneg (mul_nonneg hK hq) (sub_nonneg.mpr hden)
      nlinarith only [hh]
    have hupper : 4 * K * q ≤ (16 * K * q / (n : ℝ)) *
        (((n : ℝ) - 1) * (projectionV n g x) ^ 2) := by
      convert (le_div_iff₀ hN0).2 hprod using 1 <;> ring
    exact le_trans hJ hupper
  have hgeometry := centered_geometry n g r x hn
  have hB0 : 0 ≤ ∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnum :
      |(projectionV n g x) ^ 2 - (projectionW n g x) ^ 2 +
        2 * (∑ i : Fin n,
          Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
            Shao.OQ5.P35.center (residualU n r x) i) +
        (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2)| ≤
      (projectionV n g x) ^ 2 + (projectionW n g x) ^ 2 +
        2 * |∑ i : Fin n,
          Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
            Shao.OQ5.P35.center (residualU n r x) i| +
        (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2) := by
    have h1 := abs_add_le ((projectionV n g x) ^ 2 - (projectionW n g x) ^ 2)
      (2 * (∑ i : Fin n,
        Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
          Shao.OQ5.P35.center (residualU n r x) i))
    have h2 := abs_add_le ((projectionV n g x) ^ 2 - (projectionW n g x) ^ 2 +
      2 * (∑ i : Fin n,
        Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
          Shao.OQ5.P35.center (residualU n r x) i))
      (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2)
    have h3 := abs_add_le ((projectionV n g x) ^ 2) (-((projectionW n g x) ^ 2))
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h1
    rw [abs_of_nonneg hB0] at h2
    simp only [← sub_eq_add_neg, abs_neg, abs_of_nonneg (sq_nonneg (projectionV n g x)),
      abs_of_nonneg (sq_nonneg (projectionW n g x))] at h3
    linarith only [h1, h2, h3]
  have hnumBound :
      |(projectionV n g x) ^ 2 - (projectionW n g x) ^ 2 +
        2 * (∑ i : Fin n,
          Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
            Shao.OQ5.P35.center (residualU n r x) i) +
        (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2)| ≤
      (projectionV n g x) ^ 2 + (projectionW n g x) ^ 2 +
        2 * (Real.sqrt (n : ℝ) * projectionV n g x * Real.sqrt (residualEnergyJ n r x)) +
        residualEnergyJ n r x := by
    linarith only [hnum, hgeometry.2.1, hgeometry.2.2]
  have hsharp : |centeredDelta n g r x| ≤
      164 * y / Real.sqrt (n : ℝ) +
        16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) + 16 * K * q / (n : ℝ) := by
    calc
      |centeredDelta n g r x| =
        |(projectionV n g x) ^ 2 - (projectionW n g x) ^ 2 +
          2 * (∑ i : Fin n,
            Shao.OQ5.P35.center (fun j : Fin n => g (x j)) i *
              Shao.OQ5.P35.center (residualU n r x) i) +
          (∑ i : Fin n, (Shao.OQ5.P35.center (residualU n r x) i) ^ 2)| /
            (((n : ℝ) - 1) * (projectionV n g x) ^ 2) := by
        rw [centered_denominator_identity n g r x hsym hn hV,
          abs_div, abs_of_pos hden0]
      _ ≤ ((projectionV n g x) ^ 2 + (projectionW n g x) ^ 2 +
          2 * (Real.sqrt (n : ℝ) * projectionV n g x * Real.sqrt (residualEnergyJ n r x)) +
          residualEnergyJ n r x) / (((n : ℝ) - 1) * (projectionV n g x) ^ 2) :=
        div_le_div_of_nonneg_right hnumBound hden0.le
      _ = 1 / ((n : ℝ) - 1) +
          (projectionW n g x) ^ 2 / (((n : ℝ) - 1) * (projectionV n g x) ^ 2) +
          (2 * (Real.sqrt (n : ℝ) * projectionV n g x * Real.sqrt (residualEnergyJ n r x))) /
            (((n : ℝ) - 1) * (projectionV n g x) ^ 2) +
          residualEnergyJ n r x / (((n : ℝ) - 1) * (projectionV n g x) ^ 2) := by
        field_simp [ne_of_gt hN1, ne_of_gt hV] <;> ring
      _ ≤ 2 * y / Real.sqrt (n : ℝ) + 162 * y / Real.sqrt (n : ℝ) +
          16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) + 16 * K * q / (n : ℝ) := by
        linarith only [hbase, hWterm, hcrossTerm, hJterm]
      _ = _ := by ring
  have hscale1 : (164 : ℝ) ≤ studentizerGeometryScale K := by
    unfold studentizerGeometryScale
    nlinarith only [hK, Real.sqrt_nonneg K]
  have hscale2 : 16 * Real.sqrt K ≤ studentizerGeometryScale K := by
    unfold studentizerGeometryScale
    nlinarith only [hK, Real.sqrt_nonneg K]
  have hscale3 : 16 * K ≤ studentizerGeometryScale K := by
    unfold studentizerGeometryScale
    nlinarith only [hK, Real.sqrt_nonneg K]
  refine ⟨hJ, hD, hsharp, ?_⟩
  have ht1 := mul_le_mul_of_nonneg_right hscale1
    (div_nonneg hy0 hrootN0.le)
  have ht2 := mul_le_mul_of_nonneg_right hscale2 (Real.sqrt_nonneg (q / (n : ℝ)))
  have ht3 := mul_le_mul_of_nonneg_right hscale3 hqN
  calc
    |centeredDelta n g r x| ≤ 164 * y / Real.sqrt (n : ℝ) +
        16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) + 16 * K * q / (n : ℝ) := hsharp
    _ ≤ studentizerGeometryScale K * (y / Real.sqrt (n : ℝ)) +
        studentizerGeometryScale K * Real.sqrt (q / (n : ℝ)) +
        studentizerGeometryScale K * (q / (n : ℝ)) := by
      calc
        164 * y / Real.sqrt (n : ℝ) + 16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) +
            16 * K * q / (n : ℝ) =
          164 * (y / Real.sqrt (n : ℝ)) + 16 * Real.sqrt K * Real.sqrt (q / (n : ℝ)) +
            16 * K * (q / (n : ℝ)) := by ring
        _ ≤ _ := add_le_add (add_le_add ht1 ht2) ht3
    _ = _ := by ring

end

end Shao.OQ5.P51
