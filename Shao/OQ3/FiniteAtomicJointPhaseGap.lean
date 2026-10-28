import Shao.OQ3.FiniteWeightedUnitPhaseGap
import Shao.OQ3.JointNonlattice

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem finite_atomic_joint_phase_gap
    (n : ℕ) (a w : Fin n → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hsum : ∑ k : Fin n, w k = 1) :
    let mu : Measure ℝ := Measure.sum fun k : Fin n =>
      ENNReal.ofReal (w k) • Measure.dirac (a k)
    IsProbabilityMeasure mu ∧ ∀ xi eta : ℝ,
      jointCharacteristic mu xi eta =
        ∑ k : Fin n, w k • jointPhase xi eta (a k) ∧
      ∀ i j : Fin n,
        (w i * w j / 4) * ‖jointPhase xi eta (a i) - jointPhase xi eta (a j)‖ ^ 2 ≤
          1 - ‖jointCharacteristic mu xi eta‖ := by
  classical
  intro mu
  have hs : HasSum w 1 := by simpa only [hsum] using hasSum_fintype w
  have hprob : IsProbabilityMeasure mu := HasSum.isProbabilityMeasure_sum_dirac hw hs
  refine ⟨hprob, ?_⟩
  intro xi eta
  have hChar : jointCharacteristic mu xi eta =
      ∑ k : Fin n, w k • jointPhase xi eta (a k) := by
    simpa only [mu, jointCharacteristic, ENNReal.toReal_ofReal (hw _), tsum_fintype] using
      (integral_sum_dirac_eq_tsum (f := jointPhase xi eta) (x := a)
        (c := fun k => ENNReal.ofReal (w k)) (fun _ => ENNReal.ofReal_ne_top)
          (hasSum_fintype (fun k : Fin n =>
            (ENNReal.ofReal (w k)).toReal * ‖jointPhase xi eta (a k)‖)).summable)
  refine ⟨hChar, ?_⟩
  intro i j
  rw [hChar]
  exact finite_weighted_unit_phase_gap n w hw hsum
    (fun k => jointPhase xi eta (a k)) (fun k => jointPhase_norm xi eta (a k)) i j

end
end Shao.OQ3
