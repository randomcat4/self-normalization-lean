-- STAGE1 DECLARATION HEAD ONLY. Proposed, not frozen or implemented.
-- This file intentionally has no proof body and is not a compilable module.
-- No Lean, server, or axiom command has been run by this author.
-- Proposed target: Shao/OQ6/UnperturbedDeletedWeightedCostBridge.lean
import Shao.OQ6.LiteralDeletedWeightedCosts

set_option autoImplicit false
universe u

namespace Shao.OQ6.UnperturbedDeletedWeightedCostBridge
noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem actual_unperturbed_deleted_weighted_cost_bridge
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) (n : ℕ) (z K : ℝ) (hK : 0 ≤ K)
    (η : ℕ → Fin n → Ω → ℝ)
    (hη : ∀ (k : ℕ) (i : Fin n), Measurable (η k i))
    (Anew : ℕ → Ω → ℝ) (Adelete : Fin n → Ω → ℝ)
    (B : Ω → ℝ) (Bdelete Hdelete : Fin n → Ω → ℝ)
    (hAnew : ∀ k : ℕ, Measurable (Anew k))
    (hAdelete : ∀ i : Fin n, Measurable (Adelete i))
    (hHdelete : ∀ i : Fin n,
      Measurable (Hdelete i) ∧ Integrable (Hdelete i) ν ∧
        ∀ ω : Ω, 0 ≤ Hdelete i ω)
    (ε : ℕ → ℝ)
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ))) :
    let Mdelete : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => K * ε k * Hdelete i ω
    let AdeleteNew : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => Adelete i ω + Mdelete k i ω
    let ℓη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => z * η k i ω - (z * η k i ω) ^ 2 / 2
    let Sηminus : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => ∑ j ∈ Finset.univ.erase i, ℓη k j ω
    let capη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => min |z * η k i ω| 1
    let deletedTestη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => capη k i ω *
        (|Anew k ω - AdeleteNew k i ω| + z * |B ω - Bdelete i ω|)
    let deletedTestUnperturbedη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => capη k i ω *
        (|Anew k ω - Adelete i ω| + z * |B ω - Bdelete i ω|)
    let weightedDeletedη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => deletedTestη k i ω * Real.exp (Sηminus k i ω)
    let weightedDeletedUnperturbedη : ℕ → Fin n → Ω → ℝ :=
      fun k i ω => deletedTestUnperturbedη k i ω * Real.exp (Sηminus k i ω)
    let Edel : ℝ := Real.exp ((n : ℝ) / 2)
    let Qdel : Fin n → Ω → ℝ := fun i ω => Edel * (K * Hdelete i ω)
    let mHdelete : Fin n → ℝ := fun i => ∫ ω, Hdelete i ω ∂ν
    let Cdel : Fin n → ℝ := fun i => Edel * (K * mHdelete i)
    (∀ (k : ℕ) (i : Fin n), Integrable (weightedDeletedη k i) ν) →
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      0 ≤ capη k i ω ∧ capη k i ω ≤ 1 ∧
      0 < Real.exp (Sηminus k i ω) ∧
      Real.exp (Sηminus k i ω) ≤ Edel) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω =
        capη k i ω *
          (|Anew k ω - Adelete i ω| - |Anew k ω - AdeleteNew k i ω|) *
            Real.exp (Sηminus k i ω)) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
        capη k i ω * |Mdelete k i ω| * Real.exp (Sηminus k i ω) ∧
      |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ≤
        |ε k| * Qdel i ω) ∧
    (∀ i : Fin n, Integrable (Qdel i) ν ∧
      (∫ ω, Qdel i ω ∂ν) = Cdel i ∧ 0 ≤ Cdel i) ∧
    (∀ (k : ℕ) (i : Fin n),
      Measurable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) ∧
      Integrable (fun ω => weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω) ν ∧
      Integrable (fun ω => |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω|) ν ∧
      Integrable (weightedDeletedUnperturbedη k i) ν ∧
      (∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν) ≤
        |ε k| * Cdel i ∧
      |(∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∫ ω, weightedDeletedη k i ω ∂ν)| ≤ |ε k| * Cdel i) ∧
    (∀ i : Fin n,
      Filter.Tendsto
        (fun k : ℕ => ∫ ω, |weightedDeletedUnperturbedη k i ω - weightedDeletedη k i ω| ∂ν)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (fun k : ℕ => (∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
          (∫ ω, weightedDeletedη k i ω ∂ν))
        Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ k : ℕ,
      |(∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν)| ≤
          |ε k| * ∑ i : Fin n, Cdel i) ∧
    Filter.Tendsto
      (fun k : ℕ => (∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) -
        (∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν))
      Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ (I0 sourceCost0 : ℝ) (Iη : ℕ → ℝ) (fullη : ℕ → Ω → ℝ),
      let sourceCostη : ℕ → ℝ := fun k =>
        ((∫ ω, fullη k ω ∂ν) +
          ∑ i : Fin n, ∫ ω, weightedDeletedη k i ω ∂ν) / Iη k
      let unperturbedSourceCostη : ℕ → ℝ := fun k =>
        ((∫ ω, fullη k ω ∂ν) +
          ∑ i : Fin n, ∫ ω, weightedDeletedUnperturbedη k i ω ∂ν) / Iη k
      0 < I0 →
      Filter.Tendsto Iη Filter.atTop (nhds I0) →
      Filter.Tendsto sourceCostη Filter.atTop (nhds sourceCost0) →
      Filter.Tendsto (fun k : ℕ => unperturbedSourceCostη k - sourceCostη k)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto unperturbedSourceCostη Filter.atTop (nhds sourceCost0))

end
end Shao.OQ6.UnperturbedDeletedWeightedCostBridge
