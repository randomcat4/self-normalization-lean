import Shao.OQ3.SymmetricEightAtomWeakNotStrong
import Shao.OQ3.CompactTiltWeakCramer

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem exists_symmetric_eight_atom_compact_tilt_witness :
    ∃ a : Fin 8 → ℝ, a 0 = 1 ∧ StrictMono a ∧ (∀ i, 0 < a i) ∧
      let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
      let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
        ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
      Function.Injective A ∧ IsProbabilityMeasure mu ∧ Integrable (fun x : ℝ => x) mu ∧
        (∫ x : ℝ, x ∂mu) = 0 ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂mu, |x| ≤ B) ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic mu xi eta‖ < 1) ∧
        (∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, 0 ≤ R ∧
          (∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
            ‖jointCharacteristic mu xi eta‖ ≤
              1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8)) ∧
          ∀ K : Set (ℝ × ℝ), IsCompact K → ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
            0 < m ^ 2 * c / 2 ∧ ∀ p ∈ K,
              (ENNReal.ofReal m • mu ≤
                mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
              (∀ xi eta : ℝ, m ^ 2 * (1 - ‖jointCharacteristic mu xi eta‖ ^ 2) ≤
                1 - ‖jointCharacteristic
                  (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ^ 2) ∧
              ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
                ‖jointCharacteristic
                  (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
                    1 - (m ^ 2 * c / 2) *
                      Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-(3 : ℝ) / 8)) ∧
        (∀ R eps : ℝ, 0 < eps → ∃ xi : ℝ, R < xi ∧
          ‖jointCharacteristic mu xi 0 - 1‖ < eps ∧ 1 - eps < ‖jointCharacteristic mu xi 0‖) ∧
        ¬(∃ delta : ℝ, 0 < delta ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ xi eta : ℝ,
          R < Real.sqrt (xi ^ 2 + eta ^ 2) → ‖jointCharacteristic mu xi eta‖ ≤ 1 - delta) := by
  classical
  obtain ⟨a, ha0, hmono, hpos, hlaw⟩ := exists_symmetric_eight_atom_weak_not_strong
  let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
  let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
    ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
  obtain ⟨hAinj, hprob, hint, hmean, hbounded, hnonlattice, hweak, hnear, hnotStrong⟩ := hlaw
  obtain ⟨B, hB, hb⟩ := hbounded
  obtain ⟨c, hc, R, hR, hW⟩ := hweak
  letI : IsProbabilityMeasure mu := hprob
  have hzero : mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2) = mu := by
    simpa only [zero_mul, add_zero] using (Measure.tilted_const mu 0)
  have hbase : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => (0 : ℝ) * x + 0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-((3 : ℝ) / 8)) := by
    simpa only [hzero, neg_div] using hW
  refine ⟨a, ha0, hmono, hpos, ?_⟩
  dsimp only
  refine ⟨hAinj, hprob, hint, hmean, ⟨B, hB, hb⟩, hnonlattice, ?_, hnear, hnotStrong⟩
  refine ⟨c, hc, R, hR, hW, ?_⟩
  intro K hK
  have hcompact := exists_compact_tilted_weakCramer_bound mu B hB hb K hK
    0 0 ((3 : ℝ) / 8) c R hc hbase
  simpa only [hzero, neg_div] using hcompact

end
end Shao.OQ3
