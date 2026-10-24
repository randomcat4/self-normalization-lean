# OQ6 finite tilted moments and actual quadratic adapter

This package preserves the exact pre-implementation declarations for units139 and140. The independent author/reviewer separation, original successful objects, warning dispositions and source scope are recorded in proof-review.md and server-checks.json. Unit141 is excluded. All original research root groups remain OPEN.

## Unit139 — original frozen contract

# Unit139 exact frozen actual finite-product moments

Frozen beforeimplementation: two publictypes, zero publicdefinitions. Both statements cover alln andderiveactualcompleteobservation coordinatepullbacks, orientations, genuineintegrability andexactorderededgepaircounts; no targetfinite-nmomentpremise. Conditionalonexact138qualification forlaterserveracceptance. No rootclosure; p54repairs/m_i^-1/Shao–Zhou attributionpreserved.

```lean
import Shao.OQ6.CanonicalTilt
import Shao.OQ6.QuantitativeOverlap
import Shao.OQ6.ResidualDeletion
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.FiniteTiltedMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem unordered_pair_sum_second_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => ρ)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    let D : ℝ :=
      ∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))
    IsProbabilityMeasure ρ ∧
      IsProbabilityMeasure P ∧
      MemLp F 2 P ∧
      Integrable (fun ξ => F ξ ^ 2) P ∧
      (∫ ξ : Fin n → Ω, F ξ ^ 2 ∂P) =
        (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B +
          6 * (n.choose 4 : ℝ) * D ∧
      (∫ ξ : Fin n → Ω, F ξ ^ 2 ∂P) ≤
        ((n.choose 2 : ℝ) * K ^ 2 +
          6 * (n.choose 3 : ℝ) * K * ε ^ 2 +
          6 * (n.choose 4 : ℝ) * ε ^ 4) * s ^ 2

theorem row_square_sum_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => ρ)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k => r (ξ j) (ξ k)) i
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, ψ ξ i ^ 2
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    IsProbabilityMeasure ρ ∧
      IsProbabilityMeasure P ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 P) ∧
      Integrable Λsq P ∧
      (∫ ξ : Fin n → Ω, Λsq ξ ∂P) =
        2 * (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B ∧
      (∫ ξ : Fin n → Ω, Λsq ξ ∂P) ≤
        (2 * (n.choose 2 : ℝ) * K ^ 2 +
          6 * (n.choose 3 : ℝ) * K * ε ^ 2) * s ^ 2

end

end Shao.OQ6.FiniteTiltedMoments
```

All originalroots OPEN.

## Unit140 — original frozen contract

# Unit140 frozen exact source-facing declaration

Frozen beforeimplementation. Onepublictheorem/zeropublicdefinitions. Exact raw4307Bheader SHAf373bf2b2521c63915bd8ab41bae8f261ef4392c566d538d569be2fe92504c59 is copied unchanged from candidate99d8a3b5 after full independentdeclaration/paperCORRECT reviewb7bed4b6d284bc0f97d77f18ec0835f271674f3bee1869e47e2fb3f7962054a0 and mainintakea825a2c21f3ea540503ee72cc899ea93d28b59b7432d2236122e6163d9ba1fb8. Unit139 is now scopedqualified 77d18efd2d4cd40003d7d4579705825d29a32ec0d1e74082c6edab51a700ed0b atsourceb0a34e401746e2b4637a4ff317f3b082de9b302b1fb0f04995afa9cbd2dcf2b7 /object631b9718c2c0aa67c6e611e4831adb3202b7d21ce3885bdd14cd265d814b4a95; no oldproducerreplays.

Source: originalp39actualnormalizedh→g/r/s, fullquadraticobservationdensity/actualm^n/productlaw, p39(10)actualfinitebudgetsconstant14exp2. Remainingweighted11–14/partial m_i inverse/cost/HG/RS1RS2/p54probabilityduties and alloriginalrootsOPEN.

~~~lean
import Shao.OQ6.QuadraticTilt
import Shao.OQ6.ObservationProductTilt
import Shao.OQ6.FiniteTiltedMoments
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.ActualQuadraticTiltMoments

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem actual_quadratic_source_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 0 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, φ (ξ j)
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k => r (ξ j) (ξ k)) i
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, ψ ξ i ^ 2
    let A : ℝ :=
      ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)
    let B : ℝ :=
      ∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))
    let D : ℝ :=
      ∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))
    Measurable g ∧ MemLp g 2 μ ∧ (∫ o, g o ∂μ) = 0 ∧
      (∫ o, g o ^ 2 ∂μ) = 1 ∧
      Measurable (fun z : Ω × Ω => r z.1 z.2) ∧
      MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ) ∧
      (∀ o y, r o y = r y o) ∧
      (∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0) ∧
      0 ≤ v ∧ 1 ≤ s ∧ v ≤ s ^ 2 ∧
      Integrable w μ ∧ (1 / 2 : ℝ) ≤ m ∧ m ≤ (3 / 2 : ℝ) ∧
      Measurable L ∧ Integrable L μ ∧
      (∀ o, 0 < L o ∧ L o ≤ 2 * C) ∧
      (∫ o, L o ∂μ) = 1 ∧
      Integrable (fun o => (L o - 1) ^ 2) μ ∧
      (∫ o, (L o - 1) ^ 2 ∂μ) ≤ 4 * C ^ 2 * a ^ 2 ∧
      μ.tilted φ = ρ ∧ IsProbabilityMeasure ρ ∧
      Integrable (fun ξ => Real.exp (S ξ)) P₀ ∧
      (∫ ξ, Real.exp (S ξ) ∂P₀) = m ^ n ∧ 0 < m ^ n ∧
      (∀ ξ, Real.exp (S ξ) / m ^ n =
        ∏ j : Fin n, L (ξ j)) ∧
      Pₐ = P₀.withDensity
        (fun ξ => ENNReal.ofReal (∏ j : Fin n, L (ξ j))) ∧
      Pₐ = Measure.pi (fun _ : Fin n => ρ) ∧
      IsProbabilityMeasure Pₐ ∧
      MemLp F 2 Pₐ ∧ Integrable (fun ξ => F ξ ^ 2) Pₐ ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 Pₐ) ∧
      Integrable Λsq Pₐ ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) =
        (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B +
          6 * (n.choose 4 : ℝ) * D ∧
      (∫ ξ, Λsq ξ ∂Pₐ) =
        2 * (n.choose 2 : ℝ) * A +
          6 * (n.choose 3 : ℝ) * B ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 *
        (4 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
          96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 *
        (8 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (2 * C ^ 2 + 8 * C ^ 3 * x ^ 2 + 4 * C ^ 4 * x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ s ^ 2 * (n : ℝ) ^ 2 *
        (4 * C ^ 2 + 8 * C ^ 3 * x ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤
        14 * C ^ 4 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x ^ 2)

end

end Shao.OQ6.ActualQuadraticTiltMoments
~~~

NoLeanimplementation, probe orcheck isperformedbythisfreeze. Authorlocalonly; source/object/allactualtypes/values/generated/transitiveaxioms independentgatesmandatorybeforeacceptance.
