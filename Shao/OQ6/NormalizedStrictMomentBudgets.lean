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
:= by
  classical
  dsimp only
  let η : ℕ → Fin n → Ω → ℝ := fun (k : ℕ) =>
    Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
  let Fz : ℝ → ℝ := fun (t : ℝ) => (z * t) ^ 2 * min |z * t| 1
  let δ0 : Fin n → ℝ := fun (i : Fin n) => ∫ ω : Ω, Fz (ξ i ω) ∂ν
  let δη : ℕ → Fin n → ℝ := fun (k : ℕ) (i : Fin n) =>
    ∫ ω : Ω, Fz (η k i ω) ∂ν
  let L0 : ℝ := ∑ i : Fin n, δ0 i
  let Lη : ℕ → ℝ := fun (k : ℕ) => ∑ i : Fin n, δη k i
  intro hδ0 hL0
  change (∀ i : Fin n, δ0 i < (1 / 2 : ℝ)) at hδ0
  change L0 < cBudget * z ^ 2 at hL0
  rcases Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
      ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr z with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hδ0int, hδηint, _, _, _, _,
      hδlim, hLlim, _⟩
  change (∀ i : Fin n, Integrable (fun (ω : Ω) => Fz (ξ i ω)) ν) at hδ0int
  change (∀ (k : ℕ) (i : Fin n),
    Integrable (fun (ω : Ω) => Fz (η k i ω)) ν) at hδηint
  change (∀ i : Fin n,
    Filter.Tendsto (fun (k : ℕ) => δη k i) Filter.atTop (nhds (δ0 i))) at hδlim
  change Filter.Tendsto Lη Filter.atTop (nhds L0) at hLlim
  have hδevent : ∀ i : Fin n,
      ∀ᶠ k : ℕ in Filter.atTop, δη k i < (1 / 2 : ℝ) := by
    intro i
    exact (hδlim i).eventually (eventually_lt_nhds (hδ0 i))
  have hAllevent : ∀ᶠ k : ℕ in Filter.atTop,
      ∀ i : Fin n, δη k i < (1 / 2 : ℝ) :=
    Filter.eventually_all.2 hδevent
  have hLevent : ∀ᶠ k : ℕ in Filter.atTop, Lη k < cBudget * z ^ 2 :=
    hLlim.eventually (eventually_lt_nhds hL0)
  have htail : ∀ᶠ k : ℕ in Filter.atTop,
      (∀ i : Fin n, δη k i < (1 / 2 : ℝ)) ∧ Lη k < cBudget * z ^ 2 :=
    hAllevent.and hLevent
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 htail
  exact ⟨hδ0int, hδηint, hδlim, hLlim, k0, hk0⟩

end

end Shao.OQ6.NormalizedStrictMomentBudgets
