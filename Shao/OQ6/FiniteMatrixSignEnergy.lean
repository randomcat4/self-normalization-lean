import Shao.OQ6.FiniteHilbertSignMoments
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace Shao.OQ6.FiniteMatrixSignEnergy

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

def column (n : ℕ) (D : Fin n → Fin n → ℝ) (j : Fin n) : EuclideanSpace ℝ (Fin n) := WithLp.toLp (2 : ℝ≥0∞) (V := Fin n → ℝ) (fun i : Fin n => D i j)

def rowAction (n : ℕ) (D : Fin n → Fin n → ℝ) (w : Shao.Path n) : EuclideanSpace ℝ (Fin n) := ∑ j : Fin n, w j • column n D j

def matrixEnergy (n : ℕ) (D : Fin n → Fin n → ℝ) : ℝ := ∑ j : Fin n, (∑ i : Fin n, D i j ^ 2)

def weightEnergy (n : ℕ) (W : Fin n → ℝ) : ℝ := ∑ i : Fin n, W i ^ 2

theorem rowAction_apply (n : ℕ) (D : Fin n → Fin n → ℝ) (w : Shao.Path n) (i : Fin n) : rowAction n D w i = (∑ j : Fin n, w j * D i j) := by
  change (WithLp.ofLp (∑ j : Fin n, w j • column n D j)) i =
    (∑ j : Fin n, w j * D i j)
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
    column, WithLp.ofLp_toLp, smul_eq_mul]

theorem column_energy_eq (n : ℕ) (D : Fin n → Fin n → ℝ) : Shao.OQ6.FiniteHilbertSignMoments.energy n n (column n D) = matrixEnergy n D := by
  unfold Shao.OQ6.FiniteHilbertSignMoments.energy matrixEnergy
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [column, PiLp.toLp_apply] using
    EuclideanSpace.real_norm_sq_eq (column n D j)

theorem matrix_energy_bound (n : ℕ) (D : Fin n → Fin n → ℝ) (W : Fin n → ℝ) (hW : ∀ i : Fin n, 0 ≤ W i) (hD : ∀ i j : Fin n, |D i j| ≤ W i * W j) : matrixEnergy n D ≤ (weightEnergy n W) ^ 2 ∧ Real.sqrt (matrixEnergy n D) ≤ weightEnergy n W := by
  have hS : 0 ≤ weightEnergy n W := by
    unfold weightEnergy
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (W i))
  have hE : matrixEnergy n D ≤ (weightEnergy n W) ^ 2 := by
    calc
      matrixEnergy n D = (∑ j : Fin n, (∑ i : Fin n, D i j ^ 2)) := rfl
      _ ≤ ∑ j : Fin n, (∑ i : Fin n, W i ^ 2 * W j ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro i hi
        calc
          D i j ^ 2 = |D i j| ^ 2 := (sq_abs (D i j)).symm
          _ ≤ (W i * W j) ^ 2 :=
            (sq_le_sq₀ (abs_nonneg (D i j)) (mul_nonneg (hW i) (hW j))).2 (hD i j)
          _ = W i ^ 2 * W j ^ 2 := by ring
      _ = (∑ i : Fin n, W i ^ 2) * (∑ j : Fin n, W j ^ 2) := by
        simp_rw [← Finset.sum_mul]
        rw [← Finset.mul_sum]
      _ = (weightEnergy n W) ^ 2 := by
        simp only [weightEnergy, pow_two]
  constructor
  · exact hE
  · calc
      Real.sqrt (matrixEnergy n D) ≤ Real.sqrt ((weightEnergy n W) ^ 2) :=
        Real.sqrt_le_sqrt hE
      _ = weightEnergy n W := Real.sqrt_sq hS

theorem finite_matrix_sign_moment_bound (n : ℕ) (D : Fin n → Fin n → ℝ) (W : Fin n → ℝ) (q : ℝ) (hW : ∀ i : Fin n, 0 ≤ W i) (hD : ∀ i j : Fin n, |D i j| ≤ W i * W j) (hq : 2 ≤ q) : Real.rpow (Shao.OQ6.FiniteHilbertSignMoments.cubeMean n (fun s : Fin n → Bool => Real.rpow ‖rowAction n D (Shao.OQ6.FiniteHilbertSignMoments.signPath n s)‖ q)) (1 / q) ≤ (2 : ℝ) * Real.sqrt q * weightEnergy n W := by
  have hbase :
      Real.rpow (Shao.OQ6.FiniteHilbertSignMoments.moment n n (column n D) q) (1 / q) ≤
        (2 : ℝ) * Real.sqrt q * Real.sqrt (matrixEnergy n D) := by
    simpa only [Shao.OQ6.FiniteHilbertSignMoments.hilbertConstant, column_energy_eq] using
      Shao.OQ6.FiniteHilbertSignMoments.finite_hilbert_sign_moment_bound
        n n (column n D) q hq
  calc
    Real.rpow (Shao.OQ6.FiniteHilbertSignMoments.cubeMean n
        (fun s : Fin n → Bool =>
          Real.rpow ‖rowAction n D (Shao.OQ6.FiniteHilbertSignMoments.signPath n s)‖ q))
        (1 / q) =
      Real.rpow (Shao.OQ6.FiniteHilbertSignMoments.moment n n (column n D) q) (1 / q) := by
        rfl
    _ ≤ (2 : ℝ) * Real.sqrt q * Real.sqrt (matrixEnergy n D) := hbase
    _ ≤ (2 : ℝ) * Real.sqrt q * weightEnergy n W :=
      mul_le_mul_of_nonneg_left (matrix_energy_bound n D W hW hD).2
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg q))

theorem rademacher_matrix_moment_bound (n : ℕ) (D : Fin n → Fin n → ℝ) (W : Fin n → ℝ) (q : ℝ) (hW : ∀ i : Fin n, 0 ≤ W i) (hD : ∀ i j : Fin n, |D i j| ≤ W i * W j) (hq : 2 ≤ q) : Integrable (fun w : Shao.Path n => Real.rpow ‖rowAction n D w‖ q) (Shao.Probability.BrownianSup.radMeasure n) ∧ Real.rpow (∫ w : Shao.Path n, Real.rpow ‖rowAction n D w‖ q ∂Shao.Probability.BrownianSup.radMeasure n) (1 / q) ≤ (2 : ℝ) * Real.sqrt q * weightEnergy n W := by
  have hbase :=
    Shao.OQ6.FiniteHilbertSignMoments.rademacher_hilbert_moment_bound
      n n (column n D) q hq
  constructor
  · simpa only [Shao.OQ6.FiniteHilbertSignMoments.pathSum, rowAction] using hbase.1
  · calc
      Real.rpow (∫ w : Shao.Path n, Real.rpow ‖rowAction n D w‖ q
          ∂Shao.Probability.BrownianSup.radMeasure n) (1 / q) ≤
        (2 : ℝ) * Real.sqrt q * Real.sqrt (matrixEnergy n D) := by
          simpa only [Shao.OQ6.FiniteHilbertSignMoments.pathSum, rowAction,
            Shao.OQ6.FiniteHilbertSignMoments.hilbertConstant, column_energy_eq] using hbase.2
      _ ≤ (2 : ℝ) * Real.sqrt q * weightEnergy n W :=
        mul_le_mul_of_nonneg_left (matrix_energy_bound n D W hW hD).2
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg q))

end

end Shao.OQ6.FiniteMatrixSignEnergy
