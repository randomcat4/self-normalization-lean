# Frozen canonical-tilt and observation-overlap contracts

These six public theorem types were frozen before implementation. They concern full observation spaces, genuine integrability and the exact measures displayed below. They do not assert finite-sample counts, source costs or original probability roots. The original p53/OQ6/RS2 roots remain OPEN.

## Unit 136 — Shao.OQ6.CanonicalTilt

Source SHA256 `6d7709cf90b9e746251155221788e634e3ded8ede2700cc34bdf86355165fa23`; object SHA256 `d731862ea0297daeb0d82e07e4c1b94d44c91e1515f0d73c2d211690b2132a48`.

```lean
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.CanonicalTilt

noncomputable section

open MeasureTheory

theorem pair_contraction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond : (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let δ : Ω → ℝ := fun o => L o - 1
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    IsProbabilityMeasure ρ ∧
      1 ≤ K ∧
      MemLp L 2 μ ∧ MemLp δ 2 μ ∧
      MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (ρ.prod ρ) ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2) (ρ.prod ρ) ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2 ^ 2) (ρ.prod ρ) ∧
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(ρ.prod ρ)) ≤ K ^ 2 * s ^ 2 ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2 * L z.1 * L z.2) (μ.prod μ) ∧
      Integrable (fun z : Ω × Ω => r z.1 z.2 * δ z.1 * δ z.2) (μ.prod μ) ∧
      (∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)) =
        (∫ z : Ω × Ω, r z.1 z.2 * δ z.1 * δ z.2 ∂(μ.prod μ)) ∧
      |∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)| ≤ s * ε ^ 2

theorem section_contraction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond : (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L)
    (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let δ : Ω → ℝ := fun o => L o - 1
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
    let f : Ω → ℝ := fun o => ∫ y, r o y * L y ∂μ
    Measurable R ∧ Integrable R μ ∧
      (∫ o, R o ∂μ) = (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ∧
      (∫ o, R o ∂μ) ≤ s ^ 2 ∧
      Measurable f ∧ MemLp f 2 μ ∧ MemLp f 2 ρ ∧
      Integrable (fun o => f o ^ 2) μ ∧
      Integrable (fun o => f o ^ 2) ρ ∧
      (∫ o, f o ^ 2 ∂ρ) ≤ K * ε ^ 2 * s ^ 2 ∧
      (∀ᵐ o ∂μ,
        MemLp (r o) 2 μ ∧ MemLp (r o) 2 ρ ∧
        Integrable (r o) μ ∧ Integrable (r o) ρ ∧
        Integrable (fun y => r o y ^ 2) μ ∧
        Integrable (fun y => r o y ^ 2) ρ ∧
        Integrable (fun y => r o y * L y) μ ∧
        Integrable (fun y => r o y * δ y) μ ∧
        (∫ y, r o y ∂ρ) = f o ∧
        f o = (∫ y, r o y * δ y ∂μ) ∧
        |f o| ^ 2 ≤ ε ^ 2 * R o ∧
        (∫ y, r o y ^ 2 ∂ρ) ≤ K * R o)

end

end Shao.OQ6.CanonicalTilt
```

## Unit 137 — Shao.OQ6.CanonicalOverlap

Source SHA256 `4b1f2cb7a8bb561f8f50c07bb8db90aac757c3c82ed97c2838374a6d14ba8ee3`; object SHA256 `04ca730649d1da34a6723e1c9c0c07dafef0ad53a44945f4ef1eefb5a0e90005`.

```lean
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.CanonicalOverlap

noncomputable section

open MeasureTheory

theorem shared_observation_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun p : Ω × Ω => r p.1 p.2))
    (hr2 : MemLp (fun p : Ω × Ω => r p.1 p.2) 2 (ρ.prod ρ)) :
    Measurable (fun x : Ω => ∫ y : Ω, r x y ∂ρ) ∧
      MemLp (fun x : Ω => ∫ y : Ω, r x y ∂ρ) 2 ρ ∧
      Integrable
        (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
        (ρ.prod (ρ.prod ρ)) ∧
      (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) =
        ∫ x : Ω, (∫ y : Ω, r x y ∂ρ) ^ 2 ∂ρ

theorem disjoint_observation_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (hr1 : Integrable (fun p : Ω × Ω => r p.1 p.2) (ρ.prod ρ)) :
    Integrable
        (fun d : (Ω × Ω) × (Ω × Ω) =>
          r d.1.1 d.1.2 * r d.2.1 d.2.2)
        ((ρ.prod ρ).prod (ρ.prod ρ)) ∧
      (∫ d : (Ω × Ω) × (Ω × Ω),
          r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) =
        (∫ p : Ω × Ω, r p.1 p.2 ∂(ρ.prod ρ)) ^ 2

end

end Shao.OQ6.CanonicalOverlap
```

## Unit 138 — Shao.OQ6.QuantitativeOverlap

Source SHA256 `1ed84756da1ab6dde82b3cf76c091c985d9891830bad401d92fade979384f4d3`; object SHA256 `13d76fd341a85c70a98b4968a65c48c3c32af32e4526c4aa3d100d46906976ef`.

```lean
import Shao.OQ6.CanonicalTilt
import Shao.OQ6.CanonicalOverlap
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Shao.OQ6.QuantitativeOverlap

noncomputable section

open MeasureTheory

theorem shared_tilted_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o)
    (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let f : Ω → ℝ := fun o => ∫ y, r o y * L y ∂μ
    ρ ≪ μ ∧
      MemLp f 2 ρ ∧
      (∀ᵐ o ∂ρ,
        Integrable (r o) ρ ∧ (∫ y, r o y ∂ρ) = f o) ∧
      Integrable
        (fun t : Ω × (Ω × Ω) => r t.1 t.2.1 * r t.1 t.2.2)
        (ρ.prod (ρ.prod ρ)) ∧
      (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) = (∫ o, f o ^ 2 ∂ρ) ∧
      0 ≤ (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) ∧
      (∫ t : Ω × (Ω × Ω), r t.1 t.2.1 * r t.1 t.2.2
        ∂(ρ.prod (ρ.prod ρ))) ≤ K * ε ^ 2 * s ^ 2

theorem disjoint_tilted_moment_bound
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
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2) :
    let ρ : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    Integrable
        (fun d : (Ω × Ω) × (Ω × Ω) =>
          r d.1.1 d.1.2 * r d.2.1 d.2.2)
        ((ρ.prod ρ).prod (ρ.prod ρ)) ∧
      (∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) =
        (∫ z : Ω × Ω, r z.1 z.2 ∂(ρ.prod ρ)) ^ 2 ∧
      0 ≤ (∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) ∧
      (∫ d : (Ω × Ω) × (Ω × Ω),
        r d.1.1 d.1.2 * r d.2.1 d.2.2
        ∂((ρ.prod ρ).prod (ρ.prod ρ))) ≤ s ^ 2 * ε ^ 4

end

end Shao.OQ6.QuantitativeOverlap
```
