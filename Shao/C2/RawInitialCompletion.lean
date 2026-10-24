import Shao.C2.CompletionScaling
import Shao.C2.CompletionMeasurability
import Shao.C2.TruncatedScalarBudget

open scoped NNReal
noncomputable section
namespace Shao.C2.RawInitialCompletion
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw

def rawInitial (ν : Measure BridgeNoise) (x : ℝ) {n : ℕ} (z : Shao.Path n) : ℝ :=
  if 0 < Shao.energy z then
    intervalCompletion ν (x * Real.sqrt (Shao.energy z)) 0 (Shao.energy z) (Shao.prefixSum z n)
  else 0

theorem rawInitial_eq_normalized (n : ℕ) (ν : Measure BridgeNoise) (x : ℝ) (z : Shao.Path n) :
    rawInitial ν x z = if 0 < Shao.energy z then
      intervalCompletion ν x 0 1 (Shao.C1.normalizedEndpoint z) else 0 := by
  unfold rawInitial
  split_ifs with hQ
  · rw [CompletionScaling.initial_raw_completion_eq_normalized ν x (Shao.energy z)
      (Shao.prefixSum z n) hQ, Shao.C1.normalizedEndpoint_of_energy_pos z hQ]
  · rfl

set_option maxHeartbeats 1000000 in
theorem measurable_rawInitial (n : ℕ) (ν : Measure BridgeNoise) [SFinite ν] (x : ℝ) :
    Measurable (rawInitial ν x : Shao.Path n → ℝ) := by
  have hp : Measurable (fun z : Shao.Path n =>
      ((x * Real.sqrt (Shao.energy z), (0, (Shao.energy z, Shao.prefixSum z n))) :
        CompletionMeasurability.CompletionParameters)) :=
    (Shao.measurable_energyWall x).prodMk (measurable_const.prodMk
      (Shao.measurable_energy.prodMk (Shao.measurable_prefixSum n)))
  unfold rawInitial
  exact Measurable.ite (measurableSet_lt measurable_const Shao.measurable_energy)
    ((CompletionMeasurability.measurable_intervalCompletion_parameters ν).comp hp)
    measurable_const

theorem rawInitial_bounds (n : ℕ) (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (x : ℝ) (z : Shao.Path n) :
    0 ≤ rawInitial ν x z ∧ rawInitial ν x z ≤ 1 := by
  unfold rawInitial
  split_ifs
  · exact (completion_bounds ν _ _ _ _).2.2.2.2
  · exact ⟨le_rfl, zero_le_one⟩

theorem integrable_rawInitial_and_joint (n : ℕ)
    (ν : Measure BridgeNoise) [IsProbabilityMeasure ν]
    (P : Measure (Shao.Path n)) [IsProbabilityMeasure P] (x v : ℝ) :
    Integrable (rawInitial ν x) P ∧
      Integrable (fun z => if Shao.C1.normalizedEndpoint z ≤ v then rawInitial ν x z else 0) P := by
  have hm := measurable_rawInitial n ν x
  have hj : Measurable (fun z : Shao.Path n =>
      if Shao.C1.normalizedEndpoint z ≤ v then rawInitial ν x z else 0) :=
    Measurable.ite (measurableSet_le Shao.C1.measurable_normalizedEndpoint measurable_const)
      hm measurable_const
  constructor
  · refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (rawInitial_bounds n ν x z).1]
      exact (rawInitial_bounds n ν x z).2
  · refine (integrable_const (1 : ℝ)).mono' hj.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun z => by
      split_ifs
      · rw [Real.norm_eq_abs, abs_of_nonneg (rawInitial_bounds n ν x z).1]
        exact (rawInitial_bounds n ν x z).2
      · simp

theorem raw_initial_marginal_error_of_cdf
    {ΩB : Type*} [MeasurableSpace ΩB]
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ u : ℝ,
      |P.real {z | Shao.C1.normalizedEndpoint z ≤ u} -
        (gaussianReal 0 1).real (Set.Iic u)| ≤ δ)
    (x : ℝ) :
    |(∫ z, rawInitial (bridgeLaw B PB) x z ∂P) -
      PB.real {ω | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < x}| ≤ 4 * δ := by
  simpa only [rawInitial_eq_normalized] using
    FiniteInitialCompletion.finite_initial_marginal_error_of_cdf n P B PB hB δ hδ hCDF x

theorem raw_initial_joint_error_of_cdf
    {ΩB : Type*} [MeasurableSpace ΩB]
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ u : ℝ,
      |P.real {z | Shao.C1.normalizedEndpoint z ≤ u} -
        (gaussianReal 0 1).real (Set.Iic u)| ≤ δ)
    (x v : ℝ) :
    |(∫ z, (if Shao.C1.normalizedEndpoint z ≤ v then rawInitial (bridgeLaw B PB) x z else 0) ∂P) -
      PB.real {ω | (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < x) ∧ B 1 ω ≤ v}| ≤ 4 * δ := by
  have he (z : Shao.Path n) :
      (if 0 < Shao.energy z then
        (if Shao.C1.normalizedEndpoint z ≤ v then
          intervalCompletion (bridgeLaw B PB) x 0 1 (Shao.C1.normalizedEndpoint z) else 0) else 0) =
      (if Shao.C1.normalizedEndpoint z ≤ v then rawInitial (bridgeLaw B PB) x z else 0) := by
    rw [rawInitial_eq_normalized]
    split_ifs <;> rfl
  simpa only [he] using
    FiniteInitialCompletion.finite_initial_joint_error_of_cdf n P B PB hB δ hδ hCDF x v

theorem iid_raw_initial_errors_of_truncated_scalar_input
    {ΩB : Type*} [MeasurableSpace ΩB]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB)
    (hScalar : ∀ u : ℝ,
      |(Measure.pi (fun _ : Fin n => ν)).real
          {z | Shao.C1.normalizedEndpoint z ≤ u} -
        (gaussianReal 0 1).real (Set.Iic u)| ≤
          (51 / 5 : ℝ) * TruncatedScalarBudget.scalarGamma2 ν n +
            25 * TruncatedScalarBudget.scalarGamma3 ν n)
    (x v : ℝ) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
    (|(∫ z, rawInitial (bridgeLaw B PB) x z ∂P) -
      PB.real {ω | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < x}| ≤
        200 * Shao.truncationBudget ν n 0) ∧
    (|(∫ z, (if Shao.C1.normalizedEndpoint z ≤ v then rawInitial (bridgeLaw B PB) x z else 0) ∂P) -
      PB.real {ω | (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < x) ∧ B 1 ω ≤ v}| ≤
        200 * Shao.truncationBudget ν n 0) := by
  have he (z : Shao.Path n) :
      (if 0 < Shao.energy z then
        (if Shao.C1.normalizedEndpoint z ≤ v then
          intervalCompletion (bridgeLaw B PB) x 0 1 (Shao.C1.normalizedEndpoint z) else 0) else 0) =
      (if Shao.C1.normalizedEndpoint z ≤ v then rawInitial (bridgeLaw B PB) x z else 0) := by
    rw [rawInitial_eq_normalized]
    split_ifs <;> rfl
  have h := TruncatedScalarBudget.iid_initial_errors_of_truncated_scalar_input
    ν n hn h2 hmean hnorm B PB hB hScalar x v
  constructor
  · simpa only [rawInitial_eq_normalized] using h.1
  · simpa only [he] using h.2

end Shao.C2.RawInitialCompletion
