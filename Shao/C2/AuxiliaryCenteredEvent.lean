import Shao.C2.AuxiliaryLowEnergyGaussian

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryCenteredEvent
open scoped BigOperators

theorem auxiliary_centered_path_energy_and_sum
    {n : ℕ} (v : Shao.Path n) (mu : ℝ) :
    Shao.prefixSum (fun i => v i - mu) n = Shao.prefixSum v n - (n : ℝ) * mu ∧
      Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
        Real.sqrt (Shao.energy v) + Real.sqrt (n : ℝ) * |mu| := by
  classical
  have hSum : Shao.prefixSum (fun i => v i - mu) n =
      Shao.prefixSum v n - (n : ℝ) * mu := by
    simp only [Shao.prefixSum_length, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1 : ℝ)) v
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hCauchy
  have hAbs : |Shao.prefixSum v n| ≤
      Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy v) := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
    rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
      Real.sq_sqrt (Shao.energy_nonneg v)]
    simpa only [Shao.prefixSum_length, Shao.energy] using hCauchy
  have hExpansion : Shao.energy (fun i => v i - mu) =
      Shao.energy v - 2 * mu * Shao.prefixSum v n + (n : ℝ) * mu ^ 2 := by
    calc
      Shao.energy (fun i => v i - mu) =
          ∑ i : Fin n, ((v i) ^ 2 - (2 * mu) * v i + mu ^ 2) :=
        Finset.sum_congr rfl (fun i hi => by ring)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Shao.prefixSum_length, Shao.energy]
  have hCross : -2 * mu * Shao.prefixSum v n ≤ 2 * |mu| * |Shao.prefixSum v n| := by
    have hh := neg_le_abs (mu * Shao.prefixSum v n)
    rw [abs_mul] at hh
    linarith
  have hWeighted := mul_le_mul_of_nonneg_left hAbs
    (show 0 ≤ 2 * |mu| by positivity)
  have hSquare : (Real.sqrt (Shao.energy v) + Real.sqrt (n : ℝ) * |mu|) ^ 2 =
      Shao.energy v + 2 * Real.sqrt (Shao.energy v) * (Real.sqrt (n : ℝ) * |mu|) +
        (n : ℝ) * mu ^ 2 := by
    rw [add_sq, Real.sq_sqrt (Shao.energy_nonneg v), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg n), sq_abs]
  have hEnergy : Shao.energy (fun i => v i - mu) ≤
      (Real.sqrt (Shao.energy v) + Real.sqrt (n : ℝ) * |mu|) ^ 2 := by
    rw [hSquare]
    nlinarith
  refine ⟨hSum, ?_⟩
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (show 0 ≤
    Real.sqrt (Shao.energy v) + Real.sqrt (n : ℝ) * |mu| by positivity)).1
  rw [Real.sq_sqrt (Shao.energy_nonneg (fun i => v i - mu))]
  exact hEnergy

theorem auxiliary_centered_weak_event
    {n : ℕ} (v : Shao.Path n) (mu a y : ℝ) (hy : 0 ≤ y)
    (hShift : (Real.sqrt (n : ℝ) + y) * Real.sqrt (n : ℝ) * |mu| ≤
      (a - y) * Real.sqrt (Shao.energy v))
    (hCross : a * Real.sqrt (Shao.energy v) ≤ |Shao.prefixSum v n|) :
    y * Real.sqrt (Shao.energy (fun i => v i - mu)) ≤
      |Shao.prefixSum (fun i => v i - mu) n| := by
  rcases auxiliary_centered_path_energy_and_sum v mu with ⟨hSum, hEnergy⟩
  have hTriangle : |Shao.prefixSum v n| ≤
      |Shao.prefixSum v n - (n : ℝ) * mu| + (n : ℝ) * |mu| := by
    calc
      |Shao.prefixSum v n| =
          |(Shao.prefixSum v n - (n : ℝ) * mu) + (n : ℝ) * mu| := by
        congr 1
        ring
      _ ≤ |Shao.prefixSum v n - (n : ℝ) * mu| + |(n : ℝ) * mu| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le (Shao.prefixSum v n - (n : ℝ) * mu) ((n : ℝ) * mu)
      _ = _ := by rw [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hN : (Real.sqrt (n : ℝ) + y) * Real.sqrt (n : ℝ) * |mu| =
      (n : ℝ) * |mu| + y * Real.sqrt (n : ℝ) * |mu| := by
    calc
      _ = (Real.sqrt (n : ℝ)) ^ 2 * |mu| + y * Real.sqrt (n : ℝ) * |mu| := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hN] at hShift
  have hWeighted := mul_le_mul_of_nonneg_left hEnergy hy
  rw [hSum]
  nlinarith

end Shao.C2.AuxiliaryCenteredEvent
