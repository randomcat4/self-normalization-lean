# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean", "sha256": "bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef", "bytes": 47126, "mtime_ns": "1792382595000000000"}}

contexts lines60-60

```lean
open Function Set MeasureTheory.OuterMeasure Filter MeasurableSpace Encodable
```

contexts lines62-62

```lean
open scoped Topology ENNReal
```

contexts lines66-66

```lean
variable {ι ι' : Type*} {α : ι → Type*}
```

contexts lines68-68

```lean
namespace MeasureTheory
```

contexts lines70-70

```lean
variable [Fintype ι] {m : ∀ i, OuterMeasure (α i)}
```

contexts lines100-100

```lean
namespace OuterMeasure
```

contexts lines123-123

```lean
end OuterMeasure
```

contexts lines125-125

```lean
namespace Measure
```

contexts lines127-127

```lean
variable [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
```

contexts lines129-129

```lean
section Tprod
```

contexts lines131-131

```lean
open List
```

contexts lines133-133

```lean
variable {δ : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]
```

contexts lines169-169

```lean
end Tprod
```

contexts lines171-171

```lean
section Encodable
```

contexts lines173-173

```lean
open List
```

contexts lines175-175

```lean
variable [Encodable ι]
```

contexts lines177-177

```lean
open scoped Classical in
```

contexts lines193-193

```lean
end Encodable
```

contexts lines232-232

```lean
variable {μ}
```

contexts lines285-285

```lean
variable (μ)
```

ranges lines1-90

```lean
/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Logic.Encodable.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

import Mathlib.Algebra.BigOperators.Fin

/-!
# Indexed product measures

In this file we define and prove properties about finite products of measures
(and at some point, countable products of measures).

## Main definition

* `MeasureTheory.Measure.pi`: The product of finitely many σ-finite measures.
  Given `μ : (i : ι) → Measure (α i)` for `[Fintype ι]` it has type `Measure ((i : ι) → α i)`.

To apply Fubini's theorem or Tonelli's theorem along some subset, we recommend using the marginal
construction `MeasureTheory.lmarginal` and (todo) `MeasureTheory.marginal`. This allows you to
apply these theorems without any bookkeeping with measurable equivalences.

## Implementation Notes

We define `MeasureTheory.OuterMeasure.pi`, the product of finitely many outer measures, as the
maximal outer measure `n` with the property that `n (pi univ s) ≤ ∏ i, m i (s i)`,
where `pi univ s` is the product of the sets `{s i | i : ι}`.

We then show that this induces a product of measures, called `MeasureTheory.Measure.pi`.
For a collection of σ-finite measures `μ` and a collection of measurable sets `s` we show that
`Measure.pi μ (pi univ s) = ∏ i, m i (s i)`. To do this, we follow the following steps:
* We know that there is some ordering on `ι`, given by an element of `[Countable ι]`.
* Using this, we have an equivalence `MeasurableEquiv.piMeasurableEquivTProd` between
  `∀ i, α i` and an iterated product of `α i`, called `List.tprod α l` for some list `l`.
* On this iterated product we can easily define a product measure `MeasureTheory.Measure.tprod`
  by iterating `MeasureTheory.Measure.prod`
* Using the previous two steps we construct `MeasureTheory.Measure.pi'` on `(i : ι) → α i` for
  countable `ι`.
* We know that `MeasureTheory.Measure.pi'` sends products of sets to products of measures, and
  since `MeasureTheory.Measure.pi` is the maximal such measure (or at least, it comes from an outer
  measure which is the maximal such outer measure), we get the same rule for
  `MeasureTheory.Measure.pi`.

## Tags

finitary product measure

-/

@[expose] public section

noncomputable section

open Function Set MeasureTheory.OuterMeasure Filter MeasurableSpace Encodable

open scoped Topology ENNReal

universe u v

variable {ι ι' : Type*} {α : ι → Type*}

namespace MeasureTheory

variable [Fintype ι] {m : ∀ i, OuterMeasure (α i)}

/-- An upper bound for the measure in a finite product space.
  It is defined by taking the image of the set under all projections, and taking the product
  of the measures of these images.
  For measurable boxes it is equal to the correct measure. -/
def piPremeasure (m : ∀ i, OuterMeasure (α i)) (s : Set (∀ i, α i)) : ℝ≥0∞ :=
  ∏ i, m i (eval i '' s)

theorem piPremeasure_pi {s : ∀ i, Set (α i)} (hs : (pi univ s).Nonempty) :
    piPremeasure m (pi univ s) = ∏ i, m i (s i) := by simp [hs, piPremeasure]

theorem piPremeasure_pi' {s : ∀ i, Set (α i)} : piPremeasure m (pi univ s) = ∏ i, m i (s i) := by
  cases isEmpty_or_nonempty ι
  · simp [piPremeasure]
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩
    simpa [h, Finset.card_univ, zero_pow Fintype.card_ne_zero, @eq_comm _ (0 : ℝ≥0∞),
      Finset.prod_eq_zero_iff, piPremeasure]
  · simp [h, piPremeasure]
```

ranges lines290-316

```lean
@[simp]
theorem pi_pi [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  have : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi, pi'_pi]

nonrec theorem pi_univ [∀ i, SigmaFinite (μ i)] : Measure.pi μ univ = ∏ i, μ i univ := by
  rw [← pi_univ, pi_pi μ]

@[simp] lemma pi_singleton [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i) :
    Measure.pi μ {f} = ∏ i, μ i {f i} := by
  simpa [Set.univ_pi_singleton, -pi_pi] using pi_pi μ fun i ↦ {f i}

instance pi.instIsFiniteMeasure [∀ i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (Measure.pi μ) :=
  ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ ↦ measure_lt_top (μ i) _)⟩

instance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, IsFiniteMeasure (volume : Measure (α i))] :
    IsFiniteMeasure (volume : Measure (∀ i, α i)) :=
  pi.instIsFiniteMeasure _

instance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) :=
  ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]
theorem pi_pi_finset [∀ i, IsProbabilityMeasure (μ i)] (f : (i : ι) → Set (α i)) (s : Finset ι) :
```

