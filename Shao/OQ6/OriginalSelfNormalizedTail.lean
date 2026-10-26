import Shao.OQ6.PairedSelfNormalizedTail
import Shao.OQ6.OriginalGhostGoodEvent
import Shao.OQ6.OriginalGhostComparison
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

namespace Shao.OQ6.OriginalSelfNormalizedTail

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem original_selfnormalized_tail
    (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1)
    (t : ℝ) (ht : (1 : ℝ) ≤ t) :
    (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
      {x : Fin n → Ω |
        t * (Real.sqrt (Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x) +
          (4 : ℝ) * Real.sqrt (n : ℝ)) <
            |Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x|} ≤
      (4 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
  let M : Measure (Fin n → Ω) := Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
  let P : Measure (Fin n → Ω × Ω) := Shao.OQ6.DoubleGhostSignInvariance.pairedLaw n μ
  let A : Set (Fin n → Ω) := {x : Fin n → Ω | t * (Real.sqrt (Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x) + (4 : ℝ) * Real.sqrt (n : ℝ)) < |Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x|}
  let B : Set (Fin n → Ω) := Shao.OQ6.OriginalGhostGoodEvent.goodEvent n g
  let D : Set (Fin n → Ω × Ω) := Shao.OQ6.PairedSelfNormalizedTail.pairedTailEvent n g t
  let F : ((Fin n → Ω) × (Fin n → Ω)) → (Fin n → Ω × Ω) := Shao.OQ6.CanonicalDoubleGhostRowMoments.pairSamples n
  letI hMProbability : IsProbabilityMeasure M := by
    dsimp only [M, Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw]
    infer_instance
  have hB : MeasurableSet B ∧ (1 : ℝ) / (2 : ℝ) ≤ M.real B := by
    exact Shao.OQ6.OriginalGhostGoodEvent.original_ghost_good_event
      n μ g hg hg2 hgmean hgsecond
  have hD : MeasurableSet D := by
    exact Shao.OQ6.PairedSelfNormalizedTail.measurableSet_pairedTailEvent n g hg t
  have hF : MeasurePreserving F (M.prod M) P := by
    exact Shao.OQ6.CanonicalDoubleGhostRowMoments.pairSamples_measurePreserving n μ
  have hAB : A ×ˢ B ⊆ F ⁻¹' D := by
    intro p hp
    exact Shao.OQ6.OriginalGhostComparison.ghost_good_vector_tail_comparison n
      (fun i : Fin n => g (p.1 i)) (fun i : Fin n => g (p.2 i))
      t ht hp.1 hp.2.1 hp.2.2
  have hrectangle : (M.prod M).real (A ×ˢ B) = M.real A * M.real B := by
    exact measureReal_prod_prod (μ := M) (ν := M) A B
  have hpreimage : (M.prod M).real (F ⁻¹' D) = P.real D := by
    simpa only [hF.map_eq] using
      (map_measureReal_apply (μ := M.prod M) hF.measurable hD).symm
  have hmono : (M.prod M).real (A ×ˢ B) ≤ (M.prod M).real (F ⁻¹' D) := by
    exact measureReal_mono hAB
  have ht0 : (0 : ℝ) ≤ t := by
    nlinarith [ht]
  have hpaired : P.real D ≤ (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
    exact Shao.OQ6.PairedSelfNormalizedTail.paired_selfnormalized_tail n μ g hg t ht0
  have hproduct : M.real A * M.real B ≤ (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
    calc
      M.real A * M.real B = (M.prod M).real (A ×ˢ B) := hrectangle.symm
      _ ≤ (M.prod M).real (F ⁻¹' D) := hmono
      _ = P.real D := hpreimage
      _ ≤ (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := hpaired
  have hA0 : (0 : ℝ) ≤ M.real A := by
    exact measureReal_nonneg (μ := M) (s := A)
  have hBdiff : (0 : ℝ) ≤ M.real B - (1 : ℝ) / (2 : ℝ) := by
    nlinarith [hB.2]
  have hmul0 : (0 : ℝ) ≤ M.real A * (M.real B - (1 : ℝ) / (2 : ℝ)) := by
    exact mul_nonneg hA0 hBdiff
  have hfinal : M.real A ≤ (4 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
    nlinarith [hproduct, hmul0]
  exact hfinal

end

end Shao.OQ6.OriginalSelfNormalizedTail
