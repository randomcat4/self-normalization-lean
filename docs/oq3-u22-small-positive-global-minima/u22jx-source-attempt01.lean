import Shao.OQ3.SymmetricEightAtomLaw

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem symmetric_eight_atom_positive_energy_support
    (a : Fin 8 → ℝ) (ha : ∀ i, 1 ≤ a i) :
    let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
    let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
      ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
    let B : ℝ := ∑ i : Fin 8, |a i|
    0 < B ∧ (∀ᵐ x ∂mu, 1 ≤ |x| ∧ |x| ≤ B) ∧
      (∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ B ^ 2) ∧ 0 < mu (Set.Ioi 0) := by
  classical
  intro A mu B
  have hbase := symmetric_eight_atom_law_and_phase_gap a
  have hupper : ∀ᵐ x ∂mu, |x| ≤ B := hbase.2.2.2.2.1
  have hsum : |a 0| ≤ B :=
    Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ 0)
  have hB : 0 < B := zero_lt_one.trans_le ((ha 0).trans ((le_abs_self _).trans hsum))
  have hAtomLower : ∀ k : Fin (8 + 8), 1 ≤ |A k| := by
    refine Fin.addCases ?_ ?_
    · intro i
      have hpos : 0 ≤ a i := by linarith [ha i]
      simpa only [A, Fin.append_left, abs_of_nonneg hpos] using ha i
    · intro i
      have hpos : 0 ≤ a i := by linarith [ha i]
      simpa only [A, Fin.append_right, abs_neg, abs_of_nonneg hpos] using ha i
  have hlower : ∀ᵐ x ∂mu, 1 ≤ |x| := by
    apply Measure.ae_sum_iff.mpr
    intro k
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff (isClosed_le continuous_const continuous_abs).measurableSet).mpr
      (hAtomLower k)
  have habs : ∀ᵐ x ∂mu, 1 ≤ |x| ∧ |x| ≤ B := by
    filter_upwards [hlower, hupper] with x hxl hxu
    exact ⟨hxl, hxu⟩
  have henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ B ^ 2 := by
    filter_upwards [habs] with x hx
    constructor
    · have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx.1 2
      simpa only [one_pow, sq_abs] using h
    · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx.2 2
  have hA0 : 0 < A (0 : Fin (8 + 8)) := by
    change 0 < a 0
    linarith [ha 0]
  have hmass : 0 < (ENNReal.ofReal ((1 : ℝ) / 16) •
      Measure.dirac (A (0 : Fin (8 + 8)))) (Set.Ioi 0) := by
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem hA0, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hterm := Measure.le_sum (fun k : Fin (8 + 8) =>
    ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)) (0 : Fin (8 + 8))
  exact ⟨hB, habs, henergy, lt_of_lt_of_le hmass (hterm (Set.Ioi 0))⟩

end
end Shao.OQ3
