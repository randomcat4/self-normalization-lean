import Shao.OQ3.SampleParabolaTailDomain
import Mathlib.Analysis.MeanInequalities

namespace Shao.OQ3
open scoped BigOperators
noncomputable section

set_option maxHeartbeats 1000000 in
theorem self_normalized_low_energy_many_small_nonzero
    (level eps : ℝ) (hlevel : 0 < level) (heps : 0 < eps)
    (n : ℕ) (hn : 1 ≤ n) (z : Shao.Path n)
    (htail : level * Real.sqrt (n : ℝ) ≤
      (if Shao.energy z = 0 then 0 else
        (∑ i : Fin n, z i) / Real.sqrt (Shao.energy z)))
    (hlow : Shao.energy z ≤ (level ^ 2 * eps ^ 2 / 2) * (n : ℝ)) :
    let Small : Finset (Fin n) := Finset.univ.filter (fun i => z i ≠ 0 ∧ |z i| ≤ eps)
    (level ^ 2 / 2) * (n : ℝ) ≤ (Small.card : ℝ) := by
  classical
  intro Small
  let Active : Finset (Fin n) := Finset.univ.filter (fun i => z i ≠ 0)
  let Large : Finset (Fin n) := Finset.univ.filter (fun i => eps < |z i|)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hEne : Shao.energy z ≠ 0 := by
    intro hz
    have hh : level * Real.sqrt (n : ℝ) ≤ 0 := by simpa [hz] using htail
    exact (not_le_of_gt (mul_pos hlevel hsN)) hh
  have hEpos : 0 < Shao.energy z := lt_of_le_of_ne (Shao.energy_nonneg z) (Ne.symm hEne)
  have hsE : 0 < Real.sqrt (Shao.energy z) := Real.sqrt_pos.mpr hEpos
  have hRaw : (level * Real.sqrt (n : ℝ)) * Real.sqrt (Shao.energy z) ≤ ∑ i : Fin n, z i :=
    (le_div_iff₀ hsE).mp (by simpa only [ite_eq_right hEne] using htail)
  have hSquare := pow_le_pow_left₀
    (mul_nonneg (mul_pos hlevel hsN).le hsE.le) hRaw 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le, Real.sq_sqrt hEpos.le] at hSquare
  have hASum : (∑ i ∈ Active, z i) = ∑ i : Fin n, z i := by
    dsimp only [Active]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hz : z i = 0 <;> simp [hz]
  have hAEnergy : (∑ i ∈ Active, (z i) ^ 2) = Shao.energy z := by
    change (∑ i ∈ Active, (z i) ^ 2) = ∑ i : Fin n, (z i) ^ 2
    dsimp only [Active]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hz : z i = 0 <;> simp [hz]
  have hCauchy : (∑ i : Fin n, z i) ^ 2 ≤ (Active.card : ℝ) * Shao.energy z := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Active (fun _ : Fin n => (1 : ℝ)) z
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    rwa [hASum, hAEnergy] at hh
  have hActive : level ^ 2 * (n : ℝ) ≤ (Active.card : ℝ) :=
    (mul_le_mul_iff_left₀ hEpos).mp (hSquare.trans hCauchy)
  have hLargeSquare : (Large.card : ℝ) * eps ^ 2 ≤ ∑ i ∈ Large, (z i) ^ 2 := by
    calc
      _ = ∑ _i ∈ Large, eps ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hh : eps < |z i| := (Finset.mem_filter.mp hi).2
        simpa only [sq_abs] using (sq_le_sq₀ heps.le (abs_nonneg (z i))).2 hh.le
  have hLargeEnergy : (∑ i ∈ Large, (z i) ^ 2) ≤ Shao.energy z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    exact sq_nonneg (z i)
  have hLarge : (Large.card : ℝ) ≤ level ^ 2 * (n : ℝ) / 2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos heps)).mp
    calc
      _ ≤ Shao.energy z := hLargeSquare.trans hLargeEnergy
      _ ≤ (level ^ 2 * eps ^ 2 / 2) * (n : ℝ) := hlow
      _ = (level ^ 2 * (n : ℝ) / 2) * eps ^ 2 := by ring
  have hUnion : Active = Small ∪ Large := by
    ext i
    simp only [Active, Small, Large, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hi
      by_cases hh : |z i| ≤ eps
      · exact Or.inl ⟨hi, hh⟩
      · exact Or.inr (lt_of_not_ge hh)
    · intro hi
      rcases hi with hi | hi
      · exact hi.1
      · exact abs_pos.mp (lt_trans heps hi)
  have hDisjoint : Disjoint Small Large := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiL
    exact (not_lt_of_ge (Finset.mem_filter.mp hiS).2.2) (Finset.mem_filter.mp hiL).2
  have hCount : Active.card = Small.card + Large.card := by
    rw [hUnion, Finset.card_union_of_disjoint hDisjoint]
  have hCountR : (Active.card : ℝ) = (Small.card : ℝ) + (Large.card : ℝ) := by
    exact_mod_cast hCount
  nlinarith only [hActive, hLarge, hCountR]

end
end Shao.OQ3
