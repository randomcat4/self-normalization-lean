import Shao.Basic.FinitePath
import Mathlib.Analysis.MeanInequalities

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

theorem self_normalized_high_energy_many_large
    (level B : ℝ) (hlevel : 0 < level) (hB : 0 < B)
    (n : ℕ) (hn : 1 ≤ n) (z : Shao.Path n)
    (htail : level * Real.sqrt (n : ℝ) ≤
      (if Shao.energy z = 0 then 0 else
        (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z)))
    (hhigh : (4 * B ^ 2 / level ^ 2) * (n : ℝ) ≤ Shao.energy z) :
    let Large : Finset (Fin n) := Finset.univ.filter (fun i => B < |z i|)
    (level ^ 2 / 4) * (n : ℝ) ≤ (Large.card : ℝ) := by
  classical
  intro Large
  let Small : Finset (Fin n) := Finset.univ.filter (fun i => |z i| ≤ B)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hEpos : 0 < Shao.energy z :=
    lt_of_lt_of_le (mul_pos (div_pos (by positivity) (sq_pos_of_pos hlevel)) hnpos) hhigh
  have hsE : 0 < Real.sqrt (Shao.energy z) := Real.sqrt_pos.mpr hEpos
  let A : ℝ := level * Real.sqrt (n : ℝ) * Real.sqrt (Shao.energy z)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hRaw : A ≤ ∑ i : Fin n, z i :=
    (le_div_iff₀ hsE).mp (by simpa only [ite_eq_right hEpos.ne'] using htail)
  have hASq : A ^ 2 = level ^ 2 * (n : ℝ) * Shao.energy z := by
    dsimp only [A]
    rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le, Real.sq_sqrt hEpos.le]
  have hHighScale : 4 * B ^ 2 * (n : ℝ) ≤ Shao.energy z * level ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlevel)).mp
    calc
      (4 * B ^ 2 * (n : ℝ)) / level ^ 2 =
          (4 * B ^ 2 / level ^ 2) * (n : ℝ) := by ring
      _ ≤ Shao.energy z := hhigh
  have hABSq : (2 * B * (n : ℝ)) ^ 2 ≤ A ^ 2 := by
    rw [hASq]
    have hh := mul_le_mul_of_nonneg_right hHighScale hnpos.le
    nlinarith only [hh]
  have hAB : 2 * B * (n : ℝ) ≤ A :=
    (sq_le_sq₀ (by positivity) hA).mp hABSq
  have hSmall : (∑ i ∈ Small, z i) ≤ B * (n : ℝ) := by
    dsimp only [Small]
    rw [Finset.sum_filter]
    calc
      (∑ i : Fin n, if |z i| ≤ B then z i else 0) ≤ ∑ _i : Fin n, B := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact (le_abs_self (z i)).trans hi
        · exact hB.le
      _ = B * (n : ℝ) := by simp [mul_comm]
  have hSplit : (∑ i : Fin n, z i) =
      (∑ i ∈ Small, z i) + (∑ i ∈ Large, z i) := by
    dsimp only [Small, Large]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : |z i| ≤ B
    · simp [hi, not_lt_of_ge hi]
    · simp [hi, lt_of_not_ge hi]
  have hBigSum : A / 2 ≤ ∑ i ∈ Large, z i := by
    linarith only [hRaw, hSmall, hSplit, hAB]
  have hBigSquare : (A / 2) ^ 2 ≤ (∑ i ∈ Large, z i) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg hA (by norm_num)) hBigSum 2
  have hLargeEnergy : (∑ i ∈ Large, (z i) ^ 2) ≤ Shao.energy z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    exact sq_nonneg (z i)
  have hCauchy : (∑ i ∈ Large, z i) ^ 2 ≤ (Large.card : ℝ) * Shao.energy z := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Large (fun _ : Fin n => (1 : ℝ)) z
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hLargeEnergy (Nat.cast_nonneg _))
  have hMul : ((level ^ 2 / 4) * (n : ℝ)) * Shao.energy z ≤
      (Large.card : ℝ) * Shao.energy z := by
    have hh := hBigSquare.trans hCauchy
    rw [div_pow, hASq] at hh
    nlinarith only [hh]
  exact (mul_le_mul_iff_left₀ hEpos).mp hMul

end
end Shao.OQ3
