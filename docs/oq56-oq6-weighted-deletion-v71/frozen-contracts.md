# Weighted deletion moments and capped section energy

This milestone formalizes the local analytic deletion calculations of p39(11)--(13) for the actual normalized source h, together with the supporting capped conditional-energy contraction. Public binders and all lets, and each private helper declaration, were frozen before implementation. Exact finite second moments suffice; no higher kernel moment or pointwise domination is assumed. The complement calculation includes original n=3/deleted size2. The original full m^n normalizer, extra m^-1 partial-law factor and original sqrt(n)(n-1) coefficient are retained.

The p39(14) total analytic cost, actual D2 envelope, actual bad-event probabilities, H/G, RS1/RS2, clipping, physical Studentizer zero/positivity and final Gaussian limits remain separate. All original C12/OQ3/OQ4/OQ56 roots are OPEN. The p54 corrections and the Shao--Zhou external probability-engine attribution remain intact. The unified124 mechanism is not a prerequisite.

## Public weighted deletion declaration

```lean
theorem actual_quadratic_weighted_deletion_bounds
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
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let I : ℝ := m ^ n
    let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (∑ j ∈ Finset.univ.erase i, φ (ξ j)) / I
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, ψdel ξ i j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let cross : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    (∀ ξ i, Λsq ξ - Λdelsq ξ i = ψ ξ i ^ 2 + cross ξ i +
      ∑ j ∈ Finset.univ.erase i, r (ξ i) (ξ j) ^ 2) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤
          4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 /
            Real.sqrt (n : ℝ) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |cross ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |cross ξ i| ∂P₀) ≤
          16 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) ∧
      (∀ i : Fin n, Integrable
        (fun ξ => R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|) P₀) ∧
      (∑ i : Fin n,
        ∫ ξ, R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i| ∂P₀) ≤
          24 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2
```

## Private group A

```lean
private theorem wd_insert_fubini
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (n : ℕ) (i : Fin n) :
    let J := {j : Fin n // j ≠ i}
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then μ else ρ)
    let ins : Ω × (J → Ω) → Fin n → Ω := fun z j =>
      if hji : j = i then z.1 else z.2 ⟨j, hji⟩
    MeasurePreserving ins (μ.prod P) H ∧
      (∀ f : (Fin n → Ω) → ℝ, Integrable f H →
        Integrable (fun z : Ω × (J → Ω) => f (ins z)) (μ.prod P) ∧
        (∫ ξ, f ξ ∂H) =
          ∫ o, (∫ Y, f (ins (o, Y)) ∂P) ∂μ)

private theorem wd_deleted_row_reindex
    {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (r : Ω → Ω → ℝ)
    (n : ℕ) (i : Fin n)
    (e : Fin (n - 1) ≃ {j : Fin n // j ≠ i}) :
    let J := {j : Fin n // j ≠ i}
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let Pdel : Measure (Fin (n - 1) → Ω) :=
      Measure.pi (fun _ : Fin (n - 1) => ρ)
    let reindex : (J → Ω) → Fin (n - 1) → Ω :=
      fun Y k => Y (e k)
    let T : (J → Ω) → J → ℝ := fun Y j =>
      ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
    let E : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    MeasurePreserving reindex P Pdel ∧
      (∀ Y : J → Ω,
        (∑ j : J, T Y j ^ 2) =
          ∑ k : Fin (n - 1),
            Shao.OQ6.ResidualDeletion.rowSum
              (fun u v => r (reindex Y u) (reindex Y v)) k ^ 2) ∧
      (∀ ξ : Fin n → Ω,
        (∑ j : Fin n,
          Shao.OQ6.ResidualDeletion.rowSum
            (Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i) j ^ 2) =
          ∑ j : J, T (fun k => ξ k) j ^ 2)
```

## Private group B

```lean
private theorem wd_product_row_second
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (f : Ω → ℝ) (hf : Measurable f) (hf2 : MemLp f 2 ρ) :
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let S : (J → Ω) → ℝ := fun Y => ∑ j : J, f (Y j)
    let E : (J → Ω) → ℝ := fun Y => ∑ j : J, f (Y j) ^ 2
    MemLp S 2 P ∧ Integrable (fun Y => S Y ^ 2) P ∧
      Integrable E P ∧
      (∫ Y, S Y ^ 2 ∂P) =
        (Fintype.card J : ℝ) * (∫ y, f y ^ 2 ∂ρ) +
        (Fintype.card J : ℝ) * ((Fintype.card J : ℝ) - 1) *
          (∫ y, f y ∂ρ) ^ 2 ∧
      (∫ Y, E Y ∂P) =
        (Fintype.card J : ℝ) * (∫ y, f y ^ 2 ∂ρ)

private theorem wd_conditional_row_moments
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
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) (i : Fin n) :
    let J := {j : Fin n // j ≠ i}
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let R : Ω → ℝ := fun o => ∫ y, r o y ^ 2 ∂μ
    let S : Ω → (J → Ω) → ℝ := fun o Y => ∑ j : J, r o (Y j)
    let E : Ω → (J → Ω) → ℝ := fun o Y => ∑ j : J, r o (Y j) ^ 2
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      Measurable R ∧ Integrable R μ ∧ (∀ o, 0 ≤ R o) ∧
      (∫ o, R o ∂μ) ≤ s ^ 2 ∧
      (∀ᵐ o ∂μ,
        MemLp (S o) 2 P ∧ Integrable (fun Y => S o Y ^ 2) P ∧
        Integrable (E o) P ∧
        (∫ Y, S o Y ^ 2 ∂P) ≤
          ((n - 1 : ℕ) : ℝ) *
            (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2) * R o ∧
        (∫ Y, E o Y ∂P) ≤ ((n - 1 : ℕ) : ℝ) * K * R o)

private theorem wd_deleted_row_moment
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
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (n : ℕ) (i : Fin n)
    (e : Fin (n - 1) ≃ {j : Fin n // j ≠ i}) :
    let J := {j : Fin n // j ≠ i}
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P : Measure (J → Ω) := Measure.pi (fun _ : J => ρ)
    let T : (J → Ω) → J → ℝ := fun Y j =>
      ∑ k ∈ Finset.univ.erase j, r (Y j) (Y k)
    let M : (J → Ω) → ℝ := fun Y => ∑ j : J, T Y j ^ 2
    IsProbabilityMeasure ρ ∧ IsProbabilityMeasure P ∧
      (∀ j : J, MemLp (fun Y => T Y j) 2 P) ∧
      Integrable M P ∧
      (∫ Y, M Y ∂P) ≤
        (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
          6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
```

## Private group C

```lean
private theorem wd_vector_integral_cauchy
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (U V : Ω → J → ℝ)
    (hU : ∀ j : J, MemLp (fun o => U o j) 2 ν)
    (hV : ∀ j : J, MemLp (fun o => V o j) 2 ν) :
    let A : Ω → ℝ := fun o => ∑ j : J, U o j ^ 2
    let B : Ω → ℝ := fun o => ∑ j : J, V o j ^ 2
    let dot : Ω → ℝ := fun o => ∑ j : J, U o j * V o j
    Integrable dot ν ∧
      (∫ o, |dot o| ∂ν) ≤
        Real.sqrt (∫ o, A o ∂ν) * Real.sqrt (∫ o, B o ∂ν)

private theorem wd_mixed_row_cross_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (r : Ω → Ω → ℝ)
    (hr : Measurable (fun z : Ω × Ω => r z.1 z.2))
    (hr2 : MemLp (fun z : Ω × Ω => r z.1 z.2) 2 (μ.prod μ))
    (hrsymm : ∀ o y, r o y = r y o)
    (hrcan : ∀ᵐ o ∂μ, (∫ y, r o y ∂μ) = 0)
    (s : ℝ) (hs : 0 ≤ s)
    (hrsecond :
      (∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)) ≤ s ^ 2)
    (L : Ω → ℝ) (hL : Measurable L) (K : ℝ)
    (hLnonneg : ∀ o, 0 ≤ L o) (hLle : ∀ o, L o ≤ K)
    (hLmass : (∫ o, L o ∂μ) = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hδsecond : (∫ o, (L o - 1) ^ 2 ∂μ) ≤ ε ^ 2)
    (a : ℝ) (ha : 0 ≤ a)
    (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    let ρ : Measure Ω := μ.withDensity (fun o => ENNReal.ofReal (L o))
    let H : Measure (Fin n → Ω) := Measure.pi
      (fun j : Fin n => if j = i then μ else ρ)
    let cap : (Fin n → Ω) → ℝ := fun ξ => min |a * g (ξ i)| 1
    let E : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (E ξ) j
    let ψdel : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (E ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, ψdel ξ j ^ 2
    let cross : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j ∈ Finset.univ.erase i,
        2 * r (ξ i) (ξ j) * (ψ ξ j - r (ξ i) (ξ j))
    let Bdel : ℝ :=
      (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
        6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
    IsProbabilityMeasure H ∧
      Integrable (fun ξ => cap ξ * |ψ ξ i|) H ∧
      (∫ ξ, cap ξ * |ψ ξ i| ∂H) ≤
        a * s * Real.sqrt
          (((n - 1 : ℕ) : ℝ) * (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2)) ∧
      Integrable (fun ξ => cap ξ * |cross ξ|) H ∧
      (∫ ξ, cap ξ * |cross ξ| ∂H) ≤
        2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel) ∧
      Integrable (fun ξ => cap ξ * |Λsq ξ - Λdelsq ξ|) H ∧
      (∫ ξ, cap ξ * |Λsq ξ - Λdelsq ξ| ∂H) ≤
        s ^ 2 * ((n - 1 : ℕ) : ℝ) *
          (2 * K + ((n - 2 : ℕ) : ℝ) * ε ^ 2) +
        2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel)
```

## Private group D

```lean
private theorem wd_scalar_deletion_bounds
    (C s : ℝ) (hC : 1 ≤ C) (hs : 0 ≤ s)
    (n : ℕ) (hn : 3 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let K : ℝ := 2 * C
    let ε : ℝ := 2 * C * a
    let Bdel : ℝ :=
      (2 * ((n - 1).choose 2 : ℝ) * K ^ 2 +
        6 * ((n - 1).choose 3 : ℝ) * K * ε ^ 2) * s ^ 2
    (n : ℝ) * 2 *
        (a * s * Real.sqrt
          (((n - 1 : ℕ) : ℝ) * (K + ((n - 2 : ℕ) : ℝ) * ε ^ 2)) /
          (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))) ≤
      4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 / Real.sqrt (n : ℝ) ∧
    (n : ℝ) * 2 *
        (2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel)) ≤
      16 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * x * (1 + x) ∧
    (n : ℝ) * 2 *
        (s ^ 2 * ((n - 1 : ℕ) : ℝ) *
          (2 * K + ((n - 2 : ℕ) : ℝ) * ε ^ 2) +
          2 * a * s * Real.sqrt (((n - 1 : ℕ) : ℝ) * K * Bdel)) ≤
      24 * C ^ 2 * s ^ 2 * (n : ℝ) ^ 2 * (1 + x) ^ 2
```

# Frozen source-bound capped-energy helper

This complete declaration and every let are frozen before implementation.
It pays exactly the capped conditional-energy contraction in p39 section4(11).
The generic inputs will be derived from actual140 and mu-AE section_contraction;
they are not additional assumptions in the final142 theorem. No higher moment
is introduced. All original roots remain OPEN. Any additional declaration must
be separately frozen before its implementation.

```lean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Shao.OQ6.CappedSectionEnergy

noncomputable section

open MeasureTheory

theorem capped_sqrt_energy_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (R : Ω → ℝ) (hR : Measurable R)
    (hRnonneg : ∀ o, 0 ≤ R o) (hRint : Integrable R μ)
    (s : ℝ) (hs : 0 ≤ s)
    (hRsecond : (∫ o, R o ∂μ) ≤ s ^ 2)
    (a : ℝ) (ha : 0 ≤ a) :
    let cap : Ω → ℝ := fun o => min |a * g o| 1
    Integrable (fun o => cap o * Real.sqrt (R o)) μ ∧
      (∫ o, cap o * Real.sqrt (R o) ∂μ) ≤ a * s

end

end Shao.OQ6.CappedSectionEnergy
```
