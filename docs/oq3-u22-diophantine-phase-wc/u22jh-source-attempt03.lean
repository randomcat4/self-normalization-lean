import Shao.OQ3.SymmetricEightAtomWeakCramer
import Shao.OQ3.CirclePhaseChordLattice

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem symmetric_eight_atom_weak_cramer_of_diophantine_bounds
    (a : Fin 8 → ℝ) (cL cQ TL TQ : ℝ)
    (hcL : 0 < cL) (hcQ : 0 < cQ) (hTL : 0 ≤ TL) (hTQ : 0 ≤ TQ)
    (hLinear : ∀ t : ℝ, TL < |t| → ∃ i : Fin 8, ∀ k : ℤ,
      cL * Real.rpow |t| (-(3 : ℝ) / 16) ≤
        |2 * t * a i - 2 * Real.pi * (k : ℝ)|)
    (hQuadratic : ∀ t : ℝ, TQ < |t| → ∃ j : Fin 7, ∀ k : ℤ,
      cQ * Real.rpow |t| (-(3 : ℝ) / 16) ≤
        |2 * t * (a j.succ) ^ 2 - 2 * t * (a 0) ^ 2 - 2 * Real.pi * (k : ℝ)|) :
    let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
    let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
      ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ xi eta : ℝ,
      R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic mu xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8) := by
  intro A mu
  have hp : 0 < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hSquare (t : ℝ) : (|t| ^ (-(3 : ℝ) / 16)) ^ (2 : ℕ) =
      |t| ^ (-(3 : ℝ) / 8) := by
    have h := (Real.rpow_mul_natCast (abs_nonneg t) (-(3 : ℝ) / 16) 2).symm
    norm_num at h
    exact h
  apply symmetric_eight_atom_weak_cramer_of_coordinate_phase_bounds a
    (((2 / Real.pi) * cL) ^ 2) (((2 / Real.pi) * cQ) ^ 2) TL TQ
    (pow_pos (mul_pos hp hcL) 2) (pow_pos (mul_pos hp hcQ) 2) hTL hTQ
  · intro t ht
    obtain ⟨i, hi⟩ := hLinear t ht
    refine ⟨i, ?_⟩
    have hchord := (circle_phase_chord_nearest_lattice (2 * t * a i) 0).2.2.1
    simp only [sub_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hchord
    have hlower : ((2 / Real.pi) * cL) * Real.rpow |t| (-(3 : ℝ) / 16) ≤
        ‖jointPhase (2 * t) 0 (a i) - 1‖ := by
      calc
        _ = (2 / Real.pi) * (cL * Real.rpow |t| (-(3 : ℝ) / 16)) := by ring
        _ ≤ (2 / Real.pi) *
            |2 * t * a i - 2 * Real.pi *
              (round ((2 * t * a i) / (2 * Real.pi)) : ℤ)| :=
          mul_le_mul_of_nonneg_left (hi _) hp.le
        _ ≤ ‖Complex.exp (((2 * t * a i : ℝ) : ℂ) * Complex.I) - 1‖ := hchord
        _ = _ := by simp only [jointPhase, zero_mul, add_zero]
    have hsq := pow_le_pow_left₀
      (mul_nonneg (mul_nonneg hp.le hcL.le) (Real.rpow_nonneg (abs_nonneg t) _))
      hlower 2
    rw [mul_pow, hSquare] at hsq
    simpa only [Real.rpow_eq_pow] using hsq
  · intro t ht
    obtain ⟨j, hj⟩ := hQuadratic t ht
    refine ⟨j, ?_⟩
    have hchord :=
      (circle_phase_chord_nearest_lattice (2 * t * (a j.succ) ^ 2) (2 * t * (a 0) ^ 2)).2.2.1
    have hlower : ((2 / Real.pi) * cQ) * Real.rpow |t| (-(3 : ℝ) / 16) ≤
        ‖jointPhase 0 (2 * t) (a j.succ) - jointPhase 0 (2 * t) (a 0)‖ := by
      calc
        _ = (2 / Real.pi) * (cQ * Real.rpow |t| (-(3 : ℝ) / 16)) := by ring
        _ ≤ (2 / Real.pi) *
            |2 * t * (a j.succ) ^ 2 - 2 * t * (a 0) ^ 2 - 2 * Real.pi *
              (round ((2 * t * (a j.succ) ^ 2 - 2 * t * (a 0) ^ 2) /
                (2 * Real.pi)) : ℤ)| :=
          mul_le_mul_of_nonneg_left (hj _) hp.le
        _ ≤ ‖Complex.exp (((2 * t * (a j.succ) ^ 2 : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((2 * t * (a 0) ^ 2 : ℝ) : ℂ) * Complex.I)‖ := hchord
        _ = _ := by simp only [jointPhase, zero_mul, zero_add]
    have hsq := pow_le_pow_left₀
      (mul_nonneg (mul_nonneg hp.le hcQ.le) (Real.rpow_nonneg (abs_nonneg t) _))
      hlower 2
    rw [mul_pow, hSquare] at hsq
    simpa only [Real.rpow_eq_pow] using hsq

end
end Shao.OQ3
