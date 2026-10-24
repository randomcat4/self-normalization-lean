import Shao.C2.InitialCompletionError
import Shao.Probability.MeasurablePath

open scoped NNReal
noncomputable section
namespace Shao.C2.FiniteInitialCompletion
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw Shao.C2.EndpointCDFTransfer

theorem atom_le_two_cdf
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (x : ℝ) (hρx : ρ {x} = 0) :
    μ.real {x} ≤ 2 * δ := by
  have hc := hCDF x
  have ho := lower_set_discrepancy μ ρ δ hδ hCDF (Set.Iio x) (IsLowerSet.Iio x)
  have heρ : ρ.real (Set.Iio x) = ρ.real (Set.Iic x) :=
    measureReal_congr (Iio_ae_eq_Iic' hρx)
  rw [heρ] at ho
  have hi : Set.Iic x ∩ Set.Iio x = Set.Iio x :=
    Set.inter_eq_right.mpr Set.Iio_subset_Iic_self
  have hs : Set.Iic x \ Set.Iio x = {x} := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Iic, Set.mem_Iio, Set.mem_singleton_iff]
    constructor
    · intro h
      exact le_antisymm h.1 (le_of_not_gt h.2)
    · intro h
      subst y
      exact ⟨le_rfl, lt_irrefl x⟩
  have hsum := measureReal_inter_add_sdiff (μ := μ) (s := Set.Iic x) (measurableSet_Iio (a := x))
  rw [hi, hs] at hsum
  have hu := (abs_le.mp hc).2
  have hl := (abs_le.mp ho).1
  linarith

theorem normalized_energy_zero_le_cdf
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ,
      |P.real {z | Shao.C1.normalizedEndpoint z ≤ x} -
        (gaussianReal 0 1).real (Set.Iic x)| ≤ δ) :
    P.real {z | Shao.energy z = 0} ≤ 2 * δ := by
  let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
  have hW : Measurable W := Shao.C1.measurable_normalizedEndpoint
  let μ := P.map W
  letI : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hW.aemeasurable).mpr inferInstance
  have hLaw : HasLaw W μ P := ⟨hW.aemeasurable, rfl⟩
  have hCDF' (x : ℝ) : |μ.real (Set.Iic x) - (gaussianReal 0 1).real (Set.Iic x)| ≤ δ := by
    have hx := hLaw.measureReal_eq (measurableSet_Iic (a := x))
    change P.real {z | W z ≤ x} = μ.real (Set.Iic x) at hx
    rw [← hx]
    exact hCDF x
  have hN : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  letI := hN
  have hatom := atom_le_two_cdf μ (gaussianReal 0 1) δ hδ hCDF' 0 (measure_singleton 0)
  have he := hLaw.measureReal_eq (measurableSet_singleton (0 : ℝ))
  change P.real {z | W z = 0} = μ.real {0} at he
  calc
    _ ≤ P.real {z | W z = 0} := measureReal_mono
      (fun z hz => Shao.C1.normalizedEndpoint_of_energy_eq_zero z hz) (by finiteness)
    _ = μ.real {0} := he
    _ ≤ 2 * δ := hatom

theorem finite_initial_marginal_error_of_cdf
    {ΩB : Type*} [MeasurableSpace ΩB]
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ,
      |P.real {z | Shao.C1.normalizedEndpoint z ≤ x} -
        (gaussianReal 0 1).real (Set.Iic x)| ≤ δ)
    (a : ℝ) :
    |(∫ z, (if 0 < Shao.energy z then
        intervalCompletion (bridgeLaw B PB) a 0 1 (Shao.C1.normalizedEndpoint z) else 0) ∂P) -
      PB.real {ω | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a}| ≤ 4 * δ := by
  have h := InitialCompletionError.initial_marginal_error_of_cdf P Shao.C1.normalizedEndpoint
    Shao.energy Shao.C1.measurable_normalizedEndpoint.aemeasurable Shao.measurable_energy
    (Filter.Eventually.of_forall Shao.energy_nonneg) B PB hB δ hδ hCDF a
  exact h.trans (by linarith [normalized_energy_zero_le_cdf n P δ hδ hCDF])

theorem finite_initial_joint_error_of_cdf
    {ΩB : Type*} [MeasurableSpace ΩB]
    (n : ℕ) (P : Measure (Shao.Path n)) [IsProbabilityMeasure P]
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB) (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ,
      |P.real {z | Shao.C1.normalizedEndpoint z ≤ x} -
        (gaussianReal 0 1).real (Set.Iic x)| ≤ δ)
    (a v : ℝ) :
    |(∫ z, (if 0 < Shao.energy z then
        (if Shao.C1.normalizedEndpoint z ≤ v then
          intervalCompletion (bridgeLaw B PB) a 0 1 (Shao.C1.normalizedEndpoint z) else 0) else 0) ∂P) -
      PB.real {ω | (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v}| ≤ 4 * δ := by
  have h := InitialCompletionError.initial_joint_error_of_cdf P Shao.C1.normalizedEndpoint
    Shao.energy Shao.C1.measurable_normalizedEndpoint.aemeasurable Shao.measurable_energy
    (Filter.Eventually.of_forall Shao.energy_nonneg) B PB hB δ hδ hCDF a v
  exact h.trans (by linarith [normalized_energy_zero_le_cdf n P δ hδ hCDF])

end Shao.C2.FiniteInitialCompletion
