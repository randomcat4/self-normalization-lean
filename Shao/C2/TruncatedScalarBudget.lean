import Shao.C2.FiniteInitialCompletion
import Shao.Probability.TruncationIntegrals

open scoped NNReal
noncomputable section
namespace Shao.C2.TruncatedScalarBudget
open MeasureTheory ProbabilityTheory Set
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw Shao.C2.FiniteInitialCompletion

def scalarGamma2 (ν : Measure ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * ∫ z : ℝ, (if (1 / 2 : ℝ) < |z| then z ^ 2 else 0) ∂ν

def scalarGamma3 (ν : Measure ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * ∫ z : ℝ, (if |z| ≤ (1 / 2 : ℝ) then |z| ^ 3 else 0) ∂ν

theorem scalar_gammas_nonneg (ν : Measure ℝ) (n : ℕ) :
    0 ≤ scalarGamma2 ν n ∧ 0 ≤ scalarGamma3 ν n := by
  constructor
  · apply mul_nonneg (Nat.cast_nonneg n)
    exact integral_nonneg fun z => by split_ifs <;> positivity
  · apply mul_nonneg (Nat.cast_nonneg n)
    exact integral_nonneg fun z => by split_ifs <;> positivity

theorem scalar_gamma_sum_le_budget (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    scalarGamma2 ν n + scalarGamma3 ν n ≤ 2 * Shao.truncationBudget ν n 0 := by
  have hd := Shao.truncationBudget_decomposition ν n h2 1 (by norm_num)
  norm_num only [one_add_one_eq_two, Nat.reducePow, one_div] at hd
  change Shao.truncationBudget ν n 1 = 8 * scalarGamma3 ν n + 4 * scalarGamma2 ν n at hd
  have hs := (Shao.truncationBudget_scale_one_le ν n h2 0 2 (by norm_num)).2
  norm_num at hs
  have hg := scalar_gammas_nonneg ν n
  linarith

theorem scalar_weighted_error_le_budget (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) :
    (51 / 5 : ℝ) * scalarGamma2 ν n + 25 * scalarGamma3 ν n ≤
      50 * Shao.truncationBudget ν n 0 := by
  have hg := scalar_gammas_nonneg ν n
  have hs := scalar_gamma_sum_le_budget ν n h2
  linarith

theorem iid_initial_errors_of_truncated_scalar_input
    {ΩB : Type*} [MeasurableSpace ΩB]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (hn : 0 < n)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hB : IsBrownianReal B PB)
    (hScalar : ∀ x : ℝ,
      |(Measure.pi (fun _ : Fin n => ν)).real
          {z | Shao.C1.normalizedEndpoint z ≤ x} -
        (gaussianReal 0 1).real (Set.Iic x)| ≤
          (51 / 5 : ℝ) * scalarGamma2 ν n + 25 * scalarGamma3 ν n)
    (a v : ℝ) :
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
    (|(∫ z, (if 0 < Shao.energy z then
        intervalCompletion (bridgeLaw B PB) a 0 1 (Shao.C1.normalizedEndpoint z) else 0) ∂P) -
      PB.real {ω | ∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a}| ≤
        200 * Shao.truncationBudget ν n 0) ∧
    (|(∫ z, (if 0 < Shao.energy z then
        (if Shao.C1.normalizedEndpoint z ≤ v then
          intervalCompletion (bridgeLaw B PB) a 0 1 (Shao.C1.normalizedEndpoint z) else 0) else 0) ∂P) -
      PB.real {ω | (∀ t : BridgeTime, |B ⟨(t : ℝ), t.property.1⟩ ω| < a) ∧ B 1 ω ≤ v}| ≤
        200 * Shao.truncationBudget ν n 0) := by
  let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
  let δ : ℝ := 50 * Shao.truncationBudget ν n 0
  have hδ : 0 ≤ δ := mul_nonneg (by norm_num) (Shao.truncationBudget_nonneg ν n h2 0)
  have hc (x : ℝ) :
      |P.real {z | Shao.C1.normalizedEndpoint z ≤ x} -
        (gaussianReal 0 1).real (Set.Iic x)| ≤ δ :=
    (hScalar x).trans (scalar_weighted_error_le_budget ν n h2)
  constructor
  · have h := finite_initial_marginal_error_of_cdf n P B PB hB δ hδ hc a
    dsimp [δ] at h
    nlinarith
  · have h := finite_initial_joint_error_of_cdf n P B PB hB δ hδ hc a v
    dsimp [δ] at h
    nlinarith

end Shao.C2.TruncatedScalarBudget
