import Shao.OQ3.SymmetricEightAtomLaw

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem symmetric_eight_atom_coordinate_phase_gaps
    (a : Fin 8 → ℝ) :
    let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
    let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
      ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
    ∀ xi eta : ℝ,
      (∀ i : Fin 8,
        ((1 : ℝ) / 1024) * ‖jointPhase (2 * xi) 0 (a i) - 1‖ ^ 2 ≤
          1 - ‖jointCharacteristic mu xi eta‖) ∧
      (∀ i j : Fin 8,
        ((1 : ℝ) / 4096) *
            ‖jointPhase 0 (2 * eta) (a i) - jointPhase 0 (2 * eta) (a j)‖ ^ 2 ≤
          1 - ‖jointCharacteristic mu xi eta‖) := by
  classical
  intro A mu xi eta
  have hAll := (symmetric_eight_atom_law_and_phase_gap a).2.2.2.2.2 xi eta
  have hGap := hAll.2
  have hProduct (x : ℝ) : jointPhase xi eta x * jointPhase xi eta (-x) =
      jointPhase 0 (2 * eta) x := by
    unfold jointPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hOpposite (x : ℝ) : jointPhase xi eta x - jointPhase xi eta (-x) =
      jointPhase xi eta (-x) * (jointPhase (2 * xi) 0 x - 1) := by
    have he : jointPhase xi eta x =
        jointPhase xi eta (-x) * jointPhase (2 * xi) 0 x := by
      unfold jointPhase
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (jointPhase xi eta (-x) * jointPhase (2 * xi) 0 x) -
          jointPhase xi eta (-x) := congrArg (fun z : ℂ => z - jointPhase xi eta (-x)) he
      _ = _ := by ring
  constructor
  · intro i
    have h := hGap (Fin.castAdd 8 i) (Fin.natAdd 8 i)
    simp only [Fin.append_left, Fin.append_right] at h
    rw [hOpposite, norm_mul, jointPhase_norm, one_mul] at h
    exact h
  · intro i j
    have hp := hGap (Fin.castAdd 8 i) (Fin.castAdd 8 j)
    have hn := hGap (Fin.natAdd 8 i) (Fin.natAdd 8 j)
    simp only [Fin.append_left, Fin.append_right] at hp hn
    have hProductBound :
        ‖jointPhase 0 (2 * eta) (a i) - jointPhase 0 (2 * eta) (a j)‖ ≤
          ‖jointPhase xi eta (a i) - jointPhase xi eta (a j)‖ +
            ‖jointPhase xi eta (-a i) - jointPhase xi eta (-a j)‖ := by
      calc
        _ = ‖(jointPhase xi eta (a i) - jointPhase xi eta (a j)) *
              jointPhase xi eta (-a i) + jointPhase xi eta (a j) *
                (jointPhase xi eta (-a i) - jointPhase xi eta (-a j))‖ := by
          rw [← hProduct (a i), ← hProduct (a j)]
          congr 1
          ring
        _ ≤ ‖(jointPhase xi eta (a i) - jointPhase xi eta (a j)) *
              jointPhase xi eta (-a i)‖ + ‖jointPhase xi eta (a j) *
                (jointPhase xi eta (-a i) - jointPhase xi eta (-a j))‖ := norm_add_le _ _
        _ = _ := by
          rw [norm_mul, norm_mul, jointPhase_norm, jointPhase_norm, mul_one, one_mul]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hProductBound 2
    nlinarith [sq_nonneg
      (‖jointPhase xi eta (a i) - jointPhase xi eta (a j)‖ -
        ‖jointPhase xi eta (-a i) - jointPhase xi eta (-a j)‖)]

end
end Shao.OQ3
