import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Constructions.Pi

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem torus_simultaneous_bad_set_volume (m : ℕ) (q : ℤ) (hq : q ≠ 0) (eps : ℝ) :
    volume {x : Fin m → UnitAddCircle | ∀ j, ‖q • x j‖ ≤ eps} =
        (ENNReal.ofReal (min 1 (2 * eps))) ^ m ∧
      volume {x : Fin m → UnitAddCircle | ∀ j, ‖q • x j‖ ≤ eps} ≤
        (ENNReal.ofReal (2 * eps)) ^ m := by
  let F : (Fin m → UnitAddCircle) → (Fin m → UnitAddCircle) := fun x j => q • x j
  let S : Set (Fin m → UnitAddCircle) :=
    Set.pi Set.univ (fun _ : Fin m => Metric.closedBall (0 : UnitAddCircle) eps)
  have hF : MeasurePreserving F volume volume :=
    volume_preserving_pi (f := fun _ : Fin m => fun z : UnitAddCircle => q • z)
      (fun _ : Fin m => measurePreserving_zsmul (volume : Measure UnitAddCircle) hq)
  have hS : MeasurableSet S := by
    dsimp [S]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_closedBall)
  have hpre : {x : Fin m → UnitAddCircle | ∀ j, ‖q • x j‖ ≤ eps} = F ⁻¹' S := by
    ext x
    simp [F, S, Set.mem_pi, Metric.mem_closedBall, dist_zero_right]
  have hvolume : volume {x : Fin m → UnitAddCircle | ∀ j, ‖q • x j‖ ≤ eps} =
      (ENNReal.ofReal (min 1 (2 * eps))) ^ m := by
    calc
      _ = volume S := by rw [hpre, hF.measure_preimage hS]
      _ = ∏ j : Fin m, volume (Metric.closedBall (0 : UnitAddCircle) eps) := by
        exact volume_pi_pi (fun _ : Fin m => Metric.closedBall (0 : UnitAddCircle) eps)
      _ = _ := by
        simp only [AddCircle.volume_closedBall, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
  refine ⟨hvolume, ?_⟩
  rw [hvolume]
  exact pow_le_pow_left₀ (zero_le _) (ENNReal.ofReal_le_ofReal (min_le_right _ _)) m

end
end Shao.OQ3
