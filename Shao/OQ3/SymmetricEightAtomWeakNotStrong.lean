import Shao.OQ3.SymmetricEightAtomWeakCramerExistence
import Shao.OQ3.SymmetricEightAtomWeakCramerNonlattice
import Shao.OQ3.FiniteAtomicJointNearResonance

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem exists_symmetric_eight_atom_weak_not_strong :
    ∃ a : Fin 8 → ℝ, a 0 = 1 ∧ StrictMono a ∧ (∀ i, 0 < a i) ∧
      let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
      let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
        ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
      Function.Injective A ∧ IsProbabilityMeasure mu ∧ Integrable (fun x : ℝ => x) mu ∧
        (∫ x : ℝ, x ∂mu) = 0 ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂mu, |x| ≤ B) ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic mu xi eta‖ < 1) ∧
        (∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ xi eta : ℝ,
          R < Real.sqrt (xi ^ 2 + eta ^ 2) → ‖jointCharacteristic mu xi eta‖ ≤
            1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8)) ∧
        (∀ R eps : ℝ, 0 < eps → ∃ xi : ℝ, R < xi ∧
          ‖jointCharacteristic mu xi 0 - 1‖ < eps ∧ 1 - eps < ‖jointCharacteristic mu xi 0‖) ∧
        ¬(∃ delta : ℝ, 0 < delta ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ xi eta : ℝ,
          R < Real.sqrt (xi ^ 2 + eta ^ 2) → ‖jointCharacteristic mu xi eta‖ ≤ 1 - delta) := by
  classical
  obtain ⟨a, ha0, hmono, hpos, hlaw⟩ := exists_symmetric_eight_atom_weak_cramer
  let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
  let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
    ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
  obtain ⟨c, hc, R, hR, hW⟩ := hlaw.2.2.2.2
  have hAinj : Function.Injective A := by
    refine Fin.addCases ?_ ?_
    · intro i
      refine Fin.addCases ?_ ?_
      · intro j hij
        have heq : a i = a j := by simpa only [A, Fin.append_left] using hij
        have heqij := hmono.injective heq
        subst j
        rfl
      · intro j hij
        have heq : a i = -a j := by simpa only [A, Fin.append_left, Fin.append_right] using hij
        exfalso
        linarith [hpos i, hpos j]
    · intro i
      refine Fin.addCases ?_ ?_
      · intro j hij
        have heq : -a i = a j := by simpa only [A, Fin.append_left, Fin.append_right] using hij
        exfalso
        linarith [hpos i, hpos j]
      · intro j hij
        have heq : -a i = -a j := by simpa only [A, Fin.append_right] using hij
        have heqij := hmono.injective (neg_injective heq)
        subst j
        rfl
  have hnonlattice : ∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
      ‖jointCharacteristic mu xi eta‖ < 1 :=
    symmetric_eight_atom_nonlattice_of_weak_cramer a c R hc hR hW
  have hnear : ∀ R eps : ℝ, 0 < eps → ∃ xi : ℝ, R < xi ∧
      ‖jointCharacteristic mu xi 0 - 1‖ < eps ∧
        1 - eps < ‖jointCharacteristic mu xi 0‖ :=
    finite_atomic_joint_near_resonance (8 + 8) A (fun _ => (1 : ℝ) / 16)
      (fun _ => by norm_num) (by norm_num)
  have hnotStrong : ¬(∃ delta : ℝ, 0 < delta ∧ ∃ R0 : ℝ, 0 ≤ R0 ∧ ∀ xi eta : ℝ,
      R0 < Real.sqrt (xi ^ 2 + eta ^ 2) → ‖jointCharacteristic mu xi eta‖ ≤ 1 - delta) := by
    rintro ⟨delta, hdelta, R0, hR0, hStrong⟩
    obtain ⟨xi, hxi, _, hmod⟩ := hnear (R0 + 1) (delta / 2) (by positivity)
    have hxipos : 0 < xi := by linarith
    have hrad : R0 < Real.sqrt (xi ^ 2 + (0 : ℝ) ^ 2) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
        Real.sqrt_sq hxipos.le] using (show R0 < xi by linarith)
    have hupper := hStrong xi 0 hrad
    linarith
  refine ⟨a, ha0, hmono, hpos, ?_⟩
  dsimp only
  exact ⟨hAinj, hlaw.1, hlaw.2.1, hlaw.2.2.1, hlaw.2.2.2.1, hnonlattice,
    ⟨c, hc, R, hR, hW⟩, hnear, hnotStrong⟩

end
end Shao.OQ3
