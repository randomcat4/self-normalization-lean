# Unit229 Stage1 declaration candidate

Status: `CANDIDATE_ONLY_AWAITING_LEAD_FREEZE`. This file proposes a type and its exact surrounding text. It is not an implemented Lean module, a proof, a source qualification, or a machine-check receipt. Only the OQ56 lead may freeze the declaration and authorize implementation.

Tentative module: `Shao.OQ6.NormalizedStrictMomentBudgets`.
One proposed public theorem: `actual_source_z_strict_truncated_moment_budgets`.

The intended statement is the following preamble and head, without a proof assignment or body:

```lean
import Shao.OQ6.NormalizedAnalyticCostLimits

set_option autoImplicit false

namespace Shao.OQ6.NormalizedStrictMomentBudgets

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem actual_source_z_strict_truncated_moment_budgets
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω : Ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω : Ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (z : ℝ) (hz : 1 ≤ z)
    (cBudget : ℝ) (hcBudget : 0 < cBudget) :
    let η : ℕ → Fin n → Ω → ℝ := fun (k : ℕ) =>
      Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let Fz : ℝ → ℝ := fun (t : ℝ) => (z * t) ^ 2 * min |z * t| 1
    let δ0 : Fin n → ℝ := fun (i : Fin n) => ∫ ω : Ω, Fz (ξ i ω) ∂ν
    let δη : ℕ → Fin n → ℝ := fun (k : ℕ) (i : Fin n) =>
      ∫ ω : Ω, Fz (η k i ω) ∂ν
    let L0 : ℝ := ∑ i : Fin n, δ0 i
    let Lη : ℕ → ℝ := fun (k : ℕ) => ∑ i : Fin n, δη k i
    (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) →
    L0 < cBudget * z ^ 2 →
    (∀ i : Fin n, Integrable (fun (ω : Ω) => Fz (ξ i ω)) ν) ∧
    (∀ (k : ℕ) (i : Fin n), Integrable (fun (ω : Ω) => Fz (η k i ω)) ν) ∧
    (∀ i : Fin n,
      Filter.Tendsto (fun (k : ℕ) => δη k i) Filter.atTop (nhds (δ0 i))) ∧
    Filter.Tendsto Lη Filter.atTop (nhds L0) ∧
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2)
```

After a later authorized proof body, the exact closing text would be:

```lean
end

end Shao.OQ6.NormalizedStrictMomentBudgets
```

The two implications after all six deterministic lets are new, explicit, conditional strict-margin hypotheses of this helper. They do not assert that the preceding normalization hypotheses, unit228, a published constant, or the original model supplies either margin. `hz` and `hcBudget` visibly retain the requested source regime even though the limit-neighborhood step can hold in a wider scalar regime.

The conclusion deliberately retains genuine integrability and both limit levels, then supplies a single tail threshold. It adds no optional nonnegativity fields: the integrand is already pointwise nonnegative by its displayed formula, and no extra nonnegativity result is needed to transfer the strict upper budgets. There are no public definitions, additional theorems, bundled normalization/tilt fields, callback parameters, or auxiliary propositions in this candidate.

The existential threshold is under every fixed carrier, measure, n, original family, approximation sequence, error sequence, z, cBudget, and both strict margins. It is common to every coordinate only for this fixed finite `Fin n`. No threshold uniform in n, z, cBudget, models or approximation sequences is asserted.
