# Frozen interfaces: balanced block and canonical edges

The catalogs below contain exact definition bodies and theorem types, intentionally without proofs. Complete implementations reside in the two Lean modules. No extra public declarations or changed assumptions are accepted. Unit33 freeze SHA7b6de979a5ded92483d679a6c8c3fb98377cec90d22041aab423c7de624e8559; Unit34 freeze SHA61d6d0d1de93b795da25ab2506cfd2a42ebaee22864941b67e3e3eef504b94c8. Both catalogs were independently source-translated before implementation.

## Shao/OQ5/P45/BalancedBlock.lean

```lean
import Shao.OQ6.FiniteRows
import Shao.OQ5.P35.TargetCancellation

set_option autoImplicit false

namespace Shao.OQ5.P45

noncomputable section

open scoped BigOperators

variable {n : ℕ}

/-- The positive-residual kernel of p45 (1). -/
def positiveKernel (G Z : Fin n → ℝ) (i j : Fin n) : ℝ :=
  G i + G j + Z i * Z j

/-- The adjusted row b in p45 (2), with the original real denominator. -/
def adjustedRow (G Z : Fin n → ℝ) (i : Fin n) : ℝ :=
  G i + Z i * ((∑ j : Fin n, Z j) - Z i) / ((n : ℝ) - 2)

/-- The deterministic information from the balanced target configuration. -/
def BalancedTarget (A G Z : Fin n → ℝ) (J : Finset (Fin n))
    (t d : ℝ) : Prop :=
  (∀ i ∈ J, G i = A i + d) ∧
  (∀ i ∈ J, (Z i) ^ 2 = t ^ 2) ∧
  (∑ i ∈ J, Z i) = 0 ∧
  d = t ^ 2 / ((n : ℝ) - 2)

theorem positiveKernel_symmetric (G Z : Fin n → ℝ) (i j : Fin n) :
    positiveKernel G Z i j = positiveKernel G Z j i

theorem centered_rowMean (G Z : Fin n → ℝ) (hn : 3 ≤ n) (i : Fin n) :
    Shao.OQ6.FiniteRows.rowMean (positiveKernel G Z) i -
        Shao.OQ6.FiniteRows.uStatistic (positiveKernel G Z) =
      (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
        Shao.OQ5.P35.center (adjustedRow G Z) i

theorem jackknifeSq_eq_centeredRow (G Z : Fin n → ℝ) (hn : 3 ≤ n) :
    Shao.OQ6.FiniteRows.jackknifeSq (positiveKernel G Z) =
      (4 / ((n : ℝ) - 1)) *
        ∑ i : Fin n, (Shao.OQ5.P35.center (adjustedRow G Z) i) ^ 2

theorem adjustedRow_eq_target (A G Z : Fin n → ℝ) (hn : 3 ≤ n)
    (J : Finset (Fin n)) (t d : ℝ)
    (hblock : BalancedTarget A G Z J t d) (i : Fin n) (hi : i ∈ J) :
    adjustedRow G Z i =
      A i + Z i * Shao.OQ5.P35.backgroundSum J Z / ((n : ℝ) - 2)

theorem adjustedRow_eq_background (G Z : Fin n → ℝ) (hn : 3 ≤ n)
    (J : Finset (Fin n)) (hbalance : (∑ j ∈ J, Z j) = 0)
    (i : Fin n) (hi : i ∉ J) :
    adjustedRow G Z i =
      G i + Z i * (Shao.OQ5.P35.backgroundSum J Z - Z i) /
        ((n : ℝ) - 2)

theorem uStatistic_eq_balancedBlock (A G Z : Fin n → ℝ) (hn : 3 ≤ n)
    (J : Finset (Fin n)) (t d : ℝ)
    (hblock : BalancedTarget A G Z J t d) :
    Shao.OQ6.FiniteRows.uStatistic (positiveKernel G Z) =
      (J.card : ℝ) * d / ((n : ℝ) - 1) +
        (2 / (n : ℝ)) * (∑ i ∈ J, A i) +
        (2 / (n : ℝ)) * (∑ i : Fin n, if i ∈ J then 0 else G i) +
        (Shao.OQ5.P35.backgroundSum J Z ^ 2 -
            Shao.OQ5.P35.backgroundSqSum J Z) /
          ((n : ℝ) * ((n : ℝ) - 1))
```

## Shao/OQ5/P50/CanonicalEdges.lean

```lean
open MeasureTheory ProbabilityTheory

namespace Shao.OQ5.P50

noncomputable section

theorem pairKernel_memLp_two
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (i j : ι) (hij : i ≠ j) :
    MemLp (fun ω => r (X i ω, X j ω)) 2 μ

theorem integral_pairKernel_sq
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (i j : ι) (hij : i ≠ j) :
    (∫ ω, r (X i ω, X j ω) ^ 2 ∂μ) =
      ∫ ab, r ab ^ 2 ∂(ν.prod ν)

theorem integral_pairKernel_eq_zero
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (hcan : ∀ᵐ a ∂ν, (∫ b, r (a, b) ∂ν) = 0)
    (i j : ι) (hij : i ≠ j) :
    (∫ ω, r (X i ω, X j ω) ∂μ) = 0

theorem sharedEdgeProduct_integrable
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (hr : Measurable r) (i j k : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Integrable (fun ω => r (X i ω, X j ω) * r (X i ω, X k ω)) μ

theorem integral_sharedEdgeProduct_eq_zero
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure E} [IsProbabilityMeasure ν]
    {X : ι → Ω → E} {r : E × E → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : E → E) μ ν)
    (hr2 : MemLp r 2 (ν.prod ν))
    (hr : Measurable r)
    (hcan : ∀ᵐ a ∂ν, (∫ b, r (a, b) ∂ν) = 0)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∫ ω, r (X i ω, X j ω) * r (X i ω, X k ω) ∂μ) = 0

end
end Shao.OQ5.P50
```

The public surface is3definitions+11theorems. Probability-law/exponential-moment/tail/operator assertions outside the listed types remain separate obligations. All original finite-statistic denominators and background contributions are retained; canonical-edge integrals use the actual population product law and explicit distinct indices.
