import Shao.OQ3.SymmetricEightAtomLaw

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem symmetric_eight_atom_nonlattice_of_weak_cramer
    (a : Fin 8 → ℝ) (c R : ℝ) (hc : 0 < c) (hR : 0 ≤ R) :
    let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
    let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
      ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
    (∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic mu xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8)) →
      ∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic mu xi eta‖ < 1 := by
  classical
  intro A mu hWeak xi eta hne
  have hprob : IsProbabilityMeasure mu := (symmetric_eight_atom_law_and_phase_gap a).1
  letI : IsProbabilityMeasure mu := hprob
  have hle : ‖jointCharacteristic mu xi eta‖ ≤ 1 := jointCharacteristic_norm_le_one mu xi eta
  by_contra hnlt
  have hmod : ‖jointCharacteristic mu xi eta‖ = 1 := le_antisymm hle (not_lt.mp hnlt)
  have hphases (i : Fin (8 + 8)) : jointPhase xi eta (A i) = jointPhase xi eta (A 0) := by
    have h := ((symmetric_eight_atom_law_and_phase_gap a).2.2.2.2.2 xi eta).2 i 0
    rw [hmod] at h
    have hz : ‖jointPhase xi eta (A i) - jointPhase xi eta (A 0)‖ = 0 := by
      nlinarith [norm_nonneg (jointPhase xi eta (A i) - jointPhase xi eta (A 0))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hpow (N : ℕ) (z : ℝ) : jointPhase ((N : ℝ) * xi) ((N : ℝ) * eta) z =
      (jointPhase xi eta z) ^ N := by
    unfold jointPhase
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : (∑ _ : Fin (8 + 8), ((1 : ℝ) / 16)) = 1 := by norm_num
  have hformula := (finite_atomic_joint_phase_gap (8 + 8) A
    (fun _ => (1 : ℝ) / 16) (fun _ => by norm_num) hsum).2
  have hchar (N : ℕ) : ‖jointCharacteristic mu ((N : ℝ) * xi) ((N : ℝ) * eta)‖ = 1 := by
    have heq : jointCharacteristic mu ((N : ℝ) * xi) ((N : ℝ) * eta) =
        (jointPhase xi eta (A 0)) ^ N := by
      calc
        _ = ∑ i : Fin (8 + 8), ((1 : ℝ) / 16) •
            jointPhase ((N : ℝ) * xi) ((N : ℝ) * eta) (A i) :=
          (hformula ((N : ℝ) * xi) ((N : ℝ) * eta)).1
        _ = ∑ _ : Fin (8 + 8), ((1 : ℝ) / 16) • (jointPhase xi eta (A 0)) ^ N := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hpow, hphases i]
        _ = (∑ _ : Fin (8 + 8), ((1 : ℝ) / 16)) • (jointPhase xi eta (A 0)) ^ N := by
          rw [Finset.sum_smul]
        _ = (jointPhase xi eta (A 0)) ^ N := by rw [hsum, one_smul]
    rw [heq, norm_pow, jointPhase_norm, one_pow]
  let rho : ℝ := Real.sqrt (xi ^ 2 + eta ^ 2)
  have hsq : 0 < xi ^ 2 + eta ^ 2 := by
    rcases hne with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg eta]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg xi]
  have hrho : 0 < rho := Real.sqrt_pos.mpr hsq
  obtain ⟨N, hN⟩ := exists_nat_gt (R / rho)
  have hscale : Real.sqrt (((N : ℝ) * xi) ^ 2 + ((N : ℝ) * eta) ^ 2) =
      (N : ℝ) * rho := by
    rw [show ((N : ℝ) * xi) ^ 2 + ((N : ℝ) * eta) ^ 2 =
      (N : ℝ) ^ 2 * (xi ^ 2 + eta ^ 2) by ring]
    rw [Real.sqrt_mul (sq_nonneg (N : ℝ)), Real.sqrt_sq (Nat.cast_nonneg N)]
  have hlarge : R < Real.sqrt (((N : ℝ) * xi) ^ 2 + ((N : ℝ) * eta) ^ 2) := by
    rw [hscale]
    exact (div_lt_iff₀ hrho).mp hN
  have hrad : 0 < Real.sqrt (((N : ℝ) * xi) ^ 2 + ((N : ℝ) * eta) ^ 2) :=
    lt_of_le_of_lt hR hlarge
  have hdec : 0 < c * Real.rpow
      (Real.sqrt (((N : ℝ) * xi) ^ 2 + ((N : ℝ) * eta) ^ 2)) (-(3 : ℝ) / 8) :=
    mul_pos hc (Real.rpow_pos_of_pos hrad _)
  have hcontr := hWeak ((N : ℝ) * xi) ((N : ℝ) * eta) hlarge
  rw [hchar N] at hcontr
  linarith

end
end Shao.OQ3
