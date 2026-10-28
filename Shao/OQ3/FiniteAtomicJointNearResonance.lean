import Shao.OQ3.TorusLargeReturns
import Shao.OQ3.FiniteAtomicJointPhaseGap
import Shao.OQ3.CirclePhaseChordLattice

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem finite_atomic_joint_near_resonance
    (n : ℕ) (a w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i : Fin n, w i = 1) :
    let mu : Measure ℝ := Measure.sum fun i : Fin n =>
      ENNReal.ofReal (w i) • Measure.dirac (a i)
    ∀ R eps : ℝ, 0 < eps → ∃ xi : ℝ, R < xi ∧
      ‖jointCharacteristic mu xi 0 - 1‖ < eps ∧
        1 - eps < ‖jointCharacteristic mu xi 0‖ := by
  classical
  intro mu R eps heps
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let delta : ℝ := eps / (4 * Real.pi)
  have hd : 0 < delta := div_pos heps (mul_pos (by norm_num) Real.pi_pos)
  obtain ⟨B, hB⟩ := exists_nat_gt (R / (2 * Real.pi))
  let x : Fin n → UnitAddCircle := fun i => (a i : UnitAddCircle)
  obtain ⟨k, hk, hx⟩ := exists_large_torus_return n x delta hd B
  let freq : ℝ := (2 * Real.pi) * (k : ℝ)
  have hfreq : R < freq := by
    have hBk : (B : ℝ) < (k : ℝ) := by exact_mod_cast hk
    calc
      R < (B : ℝ) * (2 * Real.pi) := (div_lt_iff₀ hp).mp hB
      _ < (k : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_right hBk hp
      _ = freq := by dsimp [freq]; ring
  have hnear (i : Fin n) : |(k : ℝ) * a i - round ((k : ℝ) * a i)| < delta := by
    have hc := (pi_norm_lt_iff hd).mp hx i
    change ‖k • (a i : UnitAddCircle)‖ < delta at hc
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, UnitAddCircle.norm_eq] at hc
    exact hc
  have hchord (i : Fin n) : ‖jointPhase freq 0 (a i) - 1‖ ≤
      (2 * Real.pi) * |(k : ℝ) * a i - round ((k : ℝ) * a i)| := by
    have h := (circle_phase_chord_nearest_lattice (freq * a i) 0).2.2.2
    have hdiv : (freq * a i - 0) / (2 * Real.pi) = (k : ℝ) * a i := by
      dsimp [freq]
      field_simp <;> ring
    rw [hdiv] at h
    have halg : freq * a i - 0 - 2 * Real.pi * (round ((k : ℝ) * a i) : ℝ) =
        (2 * Real.pi) * ((k : ℝ) * a i - (round ((k : ℝ) * a i) : ℝ)) := by
      dsimp [freq]
      ring
    rw [halg, abs_mul, abs_of_pos hp] at h
    simpa only [jointPhase, zero_mul, add_zero, Complex.ofReal_zero, Complex.exp_zero] using h
  have hscale : (2 * Real.pi) * delta = eps / 2 := by
    dsimp [delta]
    field_simp <;> ring
  have hatom (i : Fin n) : ‖jointPhase freq 0 (a i) - 1‖ ≤ eps / 2 := by
    calc
      _ ≤ (2 * Real.pi) * |(k : ℝ) * a i - round ((k : ℝ) * a i)| := hchord i
      _ ≤ (2 * Real.pi) * delta := mul_le_mul_of_nonneg_left (hnear i).le hp.le
      _ = eps / 2 := hscale
  have hformula := (finite_atomic_joint_phase_gap n a w hw hsum).2
  have hones : (∑ i : Fin n, w i • (1 : ℂ)) = 1 := by
    rw [← Finset.sum_smul, hsum, one_smul]
  have hdiff : jointCharacteristic mu freq 0 - 1 =
      ∑ i : Fin n, w i • (jointPhase freq 0 (a i) - 1) := by
    rw [(hformula freq 0).1]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, hones]
  have hbound : ‖jointCharacteristic mu freq 0 - 1‖ ≤ eps / 2 := by
    calc
      _ = ‖∑ i : Fin n, w i • (jointPhase freq 0 (a i) - 1)‖ := congrArg norm hdiff
      _ ≤ ∑ i : Fin n, ‖w i • (jointPhase freq 0 (a i) - 1)‖ := norm_sum_le _ _
      _ = ∑ i : Fin n, w i * ‖jointPhase freq 0 (a i) - 1‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      _ ≤ ∑ i : Fin n, w i * (eps / 2) := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_left (hatom i) (hw i))
      _ = eps / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  have hreverse : 1 - ‖jointCharacteristic mu freq 0‖ ≤
      ‖jointCharacteristic mu freq 0 - 1‖ := by
    simpa only [norm_one, norm_sub_rev] using
      (norm_sub_norm_le (1 : ℂ) (jointCharacteristic mu freq 0))
  refine ⟨freq, hfreq, ?_, ?_⟩ <;> linarith

end
end Shao.OQ3
