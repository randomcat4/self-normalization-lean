import Shao.OQ3.SymmetricEightAtomCompactTiltWitness
import Shao.OQ3.SymmetricEightAtomPositiveEnergySupport
import Shao.OQ3.BoundedCenteredParabolaSmallPositiveMinimum
import Shao.OQ3.CompactTiltCovarianceSpectrum

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators Topology
noncomputable section

theorem exists_symmetric_eight_atom_small_positive_minimum :
    ∃ a : Fin 8 → ℝ, a 0 = 1 ∧ StrictMono a ∧ (∀ i, 0 < a i) ∧
      let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
      let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
        ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
      letI : IsProbabilityMeasure mu := (symmetric_eight_atom_law_and_phase_gap a).1
      Function.Injective A ∧ IsProbabilityMeasure mu ∧ Integrable (fun x : ℝ => x) mu ∧
        (∫ x : ℝ, x ∂mu) = 0 ∧ (∃ B : ℝ, 0 < B ∧ (∀ᵐ x ∂mu, 1 ≤ |x| ∧ |x| ≤ B) ∧
          (∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ B ^ 2)) ∧ 0 < mu (Set.Ioi 0) ∧
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
          R < Real.sqrt (xi ^ 2 + eta ^ 2) → ‖jointCharacteristic mu xi eta‖ ≤ 1 - delta) ∧
        0 < (parabolaCovariance mu).det ∧
        ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
          ∀ level : ℝ, 0 < level → level < epsilon → ∃ z : ℝ × ℝ,
            0 < z.2 ∧ level * Real.sqrt z.2 ≤ z.1 ∧
              0 ≤ Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ∧
              Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z < ⊤ ∧
              ∀ y : ℝ × ℝ, 0 < y.2 → level * Real.sqrt y.2 ≤ y.1 →
                Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) z ≤
                  Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y := by
  classical
  obtain ⟨a, ha0, hmono, hpos, hlaw⟩ := exists_symmetric_eight_atom_compact_tilt_witness
  let A : Fin (8 + 8) → ℝ := Fin.append a (fun i => -a i)
  let mu : Measure ℝ := Measure.sum fun k : Fin (8 + 8) =>
    ENNReal.ofReal ((1 : ℝ) / 16) • Measure.dirac (A k)
  let B : ℝ := ∑ i : Fin 8, |a i|
  obtain ⟨hAinj, hprob, hint, hmean, _hbounded, hnonlattice, hweak, hnear, hnotStrong⟩ := hlaw
  letI : IsProbabilityMeasure mu := hprob
  have hOne (i : Fin 8) : 1 ≤ a i := by
    rw [← ha0]
    exact hmono.monotone (Fin.zero_le i)
  obtain ⟨hB, habs, henergy, hright⟩ := symmetric_eight_atom_positive_energy_support a hOne
  obtain ⟨c, hc, R, hR, hW, hcompact⟩ := hweak
  have hcov := parabolaCovariance_pos_of_weakCramer mu B hB.le
    (habs.mono fun _ hx => hx.2) ((3 : ℝ) / 8) c R hc
    (by simpa only [neg_div] using hW)
  have hdetpos : 0 < (parabolaCovariance mu).det := hcov.2.2.1
  have hglobal := bounded_centered_parabola_small_positive_global_minimum mu B hB.le
    (habs.mono fun _ hx => hx.2) 1 (B ^ 2) (by norm_num) henergy hmean hdetpos.ne'
  refine ⟨a, ha0, hmono, hpos, ?_⟩
  dsimp only
  exact ⟨hAinj, hprob, hint, hmean, ⟨B, hB, habs, henergy⟩, hright, hnonlattice,
    ⟨c, hc, R, hR, hW, hcompact⟩, hnear, hnotStrong, hdetpos, hglobal⟩

end
end Shao.OQ3
