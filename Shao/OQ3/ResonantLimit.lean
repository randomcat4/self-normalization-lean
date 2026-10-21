import Shao.OQ3.InverseTilt
import Shao.OQ3.JointNonlattice
import Shao.OQ3.ResonanceArithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Escaping resonance for one fixed original probability law

Source: current/oq3/proofs/r1/report.md, lines 259-292.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U6d scope: 9182cd1dc911df4757fd8f80483a045568a0c992096e071c55131fbd9bfdd676.
-/

namespace Shao.OQ3

open MeasureTheory Filter
open scoped Matrix

noncomputable section

theorem jointPhase_resonance_of_scaled_integer (J : ℕ) (x : ℝ)
    (h : ∃ m : ℤ, (2 : ℝ) ^ J * normalValue x = (m : ℝ)) :
  jointPhase (resonanceXi J) (resonanceEta J) x = 1 := by
  obtain ⟨m, hm⟩ := h
  have hres : resonanceXi J * x + resonanceEta J * x ^ 2 =
      (2 * Real.pi) * (m : ℝ) := by
    rw [resonance_phase_normalValue, mul_assoc, hm]
  calc
    jointPhase (resonanceXi J) (resonanceEta J) x =
        jointPhase (resonanceXi J) (resonanceEta J) 0 :=
      (jointPhase_eq_iff_lattice _ _ x 0).mpr ⟨m, by simpa using hres⟩
    _ = 1 := by simp [jointPhase]

theorem fixedAtom_jointPhase_eventually_one (i : AtomicIndex) :
  ∀ᶠ J in Filter.atTop, jointPhase (resonanceXi J) (resonanceEta J) (fixedAtom i) = 1 := by
  filter_upwards [fixedAtom_eventually_scaled_integer i] with J hJ
  exact jointPhase_resonance_of_scaled_integer J (fixedAtom i) hJ

theorem jointPhase_resonance_ae_tendsto (mu : Measure ℝ)
    (hsupp : ∀ᵐ x ∂mu, x ∈ Set.range fixedAtom) :
  ∀ᵐ x ∂mu, Filter.Tendsto
    (fun J => jointPhase (resonanceXi J) (resonanceEta J) x) Filter.atTop (nhds 1) := by
  filter_upwards [hsupp] with x hx
  obtain ⟨i, rfl⟩ := hx
  apply tendsto_const_nhds.congr'
  filter_upwards [fixedAtom_jointPhase_eventually_one i] with J hJ
  exact hJ.symm

theorem jointCharacteristic_resonance_tendsto_one (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hsupp : ∀ᵐ x ∂mu, x ∈ Set.range fixedAtom) :
  Filter.Tendsto (fun J => jointCharacteristic mu (resonanceXi J) (resonanceEta J))
    Filter.atTop (nhds 1) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := mu) (F := fun J x => jointPhase (resonanceXi J) (resonanceEta J) x)
    (f := fun _ => (1 : ℂ)) (fun _ => (1 : ℝ))
    (fun J => (integrable_jointPhase mu (resonanceXi J) (resonanceEta J)).aestronglyMeasurable)
    (integrable_const 1)
    (fun J => Filter.Eventually.of_forall fun x => (jointPhase_norm _ _ x).le)
    (jointPhase_resonance_ae_tendsto mu hsupp)
  simpa [jointCharacteristic, measureReal_def] using hlim

theorem jointCharacteristic_resonance_norm_tendsto_one (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hsupp : ∀ᵐ x ∂mu, x ∈ Set.range fixedAtom) :
  Filter.Tendsto (fun J => ‖jointCharacteristic mu (resonanceXi J) (resonanceEta J)‖)
    Filter.atTop (nhds (1 : ℝ)) := by
  simpa only [norm_one] using (jointCharacteristic_resonance_tendsto_one mu hsupp).norm

theorem exists_source_weakly_nonlattice_family :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ), (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧
    0 < eps ∧ (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (r : ℕ → ℝ), (∀ j, 0 < r j) → Summable r → (∑' j, r j) < eps →
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (∫ x, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
      (∀ᵐ x ∂originalMeasure sourceEll (limitingMass sourceEll p r),
        1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        ‖jointCharacteristic (originalMeasure sourceEll (limitingMass sourceEll p r)) xi eta‖ < 1) ∧
      Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun J => ‖jointCharacteristic
        (originalMeasure sourceEll (limitingMass sourceEll p r)) (resonanceXi J) (resonanceEta J)‖)
        Filter.atTop (nhds (1 : ℝ)) := by
  obtain ⟨p, q, eps, hp, hlo, hhi, heps, hc, hfamily⟩ := exists_source_original_family
  refine ⟨p, q, eps, hp, hlo, hhi, heps, hc, ?_⟩
  intro r hr hs ht
  obtain ⟨hprob, hcenter, hpos, hbounds, _⟩ := hfamily r hr hs ht
  let := hprob
  have hsupp : ∀ᵐ x ∂originalMeasure sourceEll (limitingMass sourceEll p r),
      x ∈ Set.range fixedAtom :=
    (tilted_absolutelyContinuous (atomicMeasure (limitingMass sourceEll p r))
      (fun x => -sourceEll * normalValue x)).ae_le
        (atomicMeasure_ae_range (limitingMass sourceEll p r))
  exact ⟨hprob, hcenter, hbounds,
    fun xi eta hne => jointCharacteristic_norm_lt_one_of_positive_atoms _ hpos xi eta hne,
    resonance_frequency_escape, jointCharacteristic_resonance_norm_tendsto_one _ hsupp⟩

end
end Shao.OQ3
