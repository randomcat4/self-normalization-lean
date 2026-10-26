import Shao.OQ6.OriginalLowEnergyTail
import Shao.OQ6.OriginalNormalizedUpperTail

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

namespace Shao.OQ6.OriginalGoodEventProbability

noncomputable section

/-!
The literal p51 S3 (S10) good event and its (S11) complement payment.
The upper-tail input retains the source attribution to Shao--Zhou (92)
and its self-normalized inequality dependencies; this module assembles
qualified inputs and does not claim a new proof of that external result.
Only the complement probability component is addressed here.
-/

def normalizedGoodEvent
    (n : ℕ) {Ω : Type*} (g : Ω → ℝ) (y : ℝ) : Set (Fin n → Ω) := {x : Fin n → Ω |
  (1 / 2 : ℝ) ≤ Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x / (n : ℝ) ∧
    |Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x / Real.sqrt (n : ℝ)| ≤
      Real.sqrt y * Real.rpow (n : ℝ) ((1 : ℝ) / 4) *
        ((4 : ℝ) + Real.sqrt
          (Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x / (n : ℝ)))}

theorem original_good_event_complement_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgmean : (∫ o : Ω, g o ∂μ) = 0)
    (hgsecond : (∫ o : Ω, (g o) ^ (2 : ℕ) ∂μ) = 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 0 < n → ∀ (y : ℝ), (1 : ℝ) ≤ y →
      (Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ).real
        (normalizedGoodEvent n g y)ᶜ ≤
          Real.exp (-c * (n : ℝ)) +
            (4 : ℝ) * Real.exp (-(y * Real.sqrt (n : ℝ)) / (2 : ℝ)) := by
  classical
  rcases Shao.OQ6.OriginalLowEnergyTail.original_low_energy_exponential
    μ g hg hg2 hgsecond with ⟨c, hc, hLowAll⟩
  refine ⟨c, hc, ?_⟩
  intro n hn y hy
  let M : Measure (Fin n → Ω) := Shao.OQ6.CanonicalDoubleGhostRowMoments.sampleLaw n μ
  let E : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => Shao.OQ6.OriginalGhostGoodEvent.sampleEnergy n g x
  let S : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => Shao.OQ6.OriginalGhostGoodEvent.sampleSum n g x
  let r : ℝ := Real.sqrt (n : ℝ)
  let q : ℝ := Real.rpow (n : ℝ) ((1 : ℝ) / 4)
  let T : (Fin n → Ω) → ℝ := fun x : Fin n → Ω => Real.sqrt y * q * ((4 : ℝ) + Real.sqrt (E x / (n : ℝ)))
  let G : Set (Fin n → Ω) := normalizedGoodEvent n g y
  let A : Set (Fin n → Ω) := {x : Fin n → Ω | E x < (n : ℝ) / (2 : ℝ)}
  let B : Set (Fin n → Ω) := {x : Fin n → Ω | T x < |S x / r|}
  have hNpos : 0 < (n : ℝ) := by
    exact Nat.cast_pos.mpr hn
  have hLowPoint : ∀ x : Fin n → Ω, E x / (n : ℝ) < (1 / 2 : ℝ) ↔ E x < (n : ℝ) / (2 : ℝ) := by
    intro x
    rw [div_lt_iff₀ hNpos]
    rw [show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / (2 : ℝ) by ring]
  have hComplementPoint : ∀ x : Fin n → Ω, x ∈ Gᶜ ↔ x ∈ A ∪ B := by
    intro x
    change ¬ ((1 / 2 : ℝ) ≤ E x / (n : ℝ) ∧ |S x / r| ≤ T x) ↔
      E x < (n : ℝ) / (2 : ℝ) ∨ T x < |S x / r|
    rw [not_and_or, not_le, not_le, hLowPoint x]
  have hComplementEq : Gᶜ = A ∪ B := by
    exact Set.ext hComplementPoint
  have hMeasureEq : M.real Gᶜ = M.real (A ∪ B) := by
    exact congrArg (fun U : Set (Fin n → Ω) => M.real U) hComplementEq
  have hLow : M.real A ≤ Real.exp (-c * (n : ℝ)) := by
    exact hLowAll n
  have hUpper : M.real B ≤ (4 : ℝ) * Real.exp (-(y * r) / (2 : ℝ)) := by
    exact Shao.OQ6.OriginalNormalizedUpperTail.original_normalized_upper_tail
      n hn μ g hg hg2 hgmean hgsecond y hy
  have hUnion : M.real (A ∪ B) ≤ M.real A + M.real B := by
    exact measureReal_union_le (μ := M) A B
  have hPayment : M.real Gᶜ ≤ Real.exp (-c * (n : ℝ)) + (4 : ℝ) * Real.exp (-(y * r) / (2 : ℝ)) := by
    calc
      M.real Gᶜ = M.real (A ∪ B) := hMeasureEq
      _ ≤ M.real A + M.real B := hUnion
      _ ≤ Real.exp (-c * (n : ℝ)) + (4 : ℝ) * Real.exp (-(y * r) / (2 : ℝ)) :=
        add_le_add hLow hUpper
  exact hPayment

end

end Shao.OQ6.OriginalGoodEventProbability
