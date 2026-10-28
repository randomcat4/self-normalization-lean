import Shao.OQ3.FiniteAtomicJointPhaseGap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem symmetric_eight_atom_law_and_phase_gap
    (a : Fin 8 → ℝ) :
    let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
    let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
      ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
    let B : ℝ := ∑ i : Fin 8, |a i|
    IsProbabilityMeasure mu ∧ Integrable (fun x : ℝ => x) mu ∧
      (∫ x : ℝ, x ∂mu) = 0 ∧ 0 ≤ B ∧ (∀ᵐ x ∂mu, |x| ≤ B) ∧
      ∀ xi eta : ℝ,
        jointCharacteristic mu xi eta = ((1 : ℝ) / 16) •
          ((∑ i : Fin 8, jointPhase xi eta (a i)) +
            ∑ i : Fin 8, jointPhase xi eta (-a i)) ∧
        ∀ i j : Fin (8 + 8),
          ((1 : ℝ) / 1024) *
              ‖jointPhase xi eta (A i) - jointPhase xi eta (A j)‖ ^ 2 ≤
            1 - ‖jointCharacteristic mu xi eta‖ := by
  classical
  intro A mu B
  have hweights : (∑ _ : Fin (8 + 8), ((1 : ℝ) / 16)) = 1 := by norm_num
  obtain ⟨hprob, hPhase⟩ := finite_atomic_joint_phase_gap (8 + 8) A
    (fun _ => (1 : ℝ) / 16) (fun _ => by norm_num) hweights
  have hnorm : Summable (fun k : Fin (8 + 8) =>
      (ENNReal.ofReal ((1 : ℝ) / 16)).toReal * ‖A k‖) :=
    (hasSum_fintype _).summable
  have hL1 : Integrable (fun x : ℝ => x) mu :=
    integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top) hnorm
  have hsumA : (∑ k : Fin (8 + 8), A k) = 0 := by
    rw [Fin.sum_univ_add]
    simp only [A, Fin.append_left, Fin.append_right, Finset.sum_neg_distrib, add_neg_cancel]
  have hmean : (∫ x : ℝ, x ∂mu) = 0 := by
    have h := integral_sum_dirac_eq_tsum (f := fun x : ℝ => x) (x := A)
      (c := fun _ => ENNReal.ofReal ((1 : ℝ) / 16))
        (fun _ => ENNReal.ofReal_ne_top) hnorm
    simpa only [mu, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16),
      tsum_fintype, smul_eq_mul, ← Finset.mul_sum, hsumA, mul_zero] using h
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hAtomBound : ∀ k : Fin (8 + 8), |A k| ≤ B := by
    refine Fin.addCases ?_ ?_
    · intro i
      simp only [A, Fin.append_left]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    · intro i
      simp only [A, Fin.append_right, abs_neg]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  have hbound : ∀ᵐ x ∂mu, |x| ≤ B := by
    apply Measure.ae_sum_iff.mpr
    intro k
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff (isClosed_le continuous_abs continuous_const).measurableSet).mpr
      (hAtomBound k)
  refine ⟨hprob, hL1, hmean, hB, hbound, ?_⟩
  intro xi eta
  refine ⟨?_, ?_⟩
  · rw [(hPhase xi eta).1, Fin.sum_univ_add]
    simp only [A, Fin.append_left, Fin.append_right, ← Finset.smul_sum, smul_add]
  · intro i j
    have h := (hPhase xi eta).2 i j
    change ((1 : ℝ) / 16 * (1 / 16) / 4) *
      ‖jointPhase xi eta (A i) - jointPhase xi eta (A j)‖ ^ 2 ≤
        1 - ‖jointCharacteristic mu xi eta‖ at h
    have hcoefficient : ((1 : ℝ) / 16 * (1 / 16) / 4) = 1 / 1024 := by norm_num
    rw [hcoefficient] at h
    exact h

end
end Shao.OQ3
