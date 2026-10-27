# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean", "sha256": "00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b", "bytes": 10640, "mtime_ns": "1792382595000000000"}}

contexts lines22-22

```lean
namespace MeasureTheory
```

contexts lines24-24

```lean
open Set Measure Filter Function ENNReal
```

contexts lines26-26

```lean
variable {α β : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {s : Set α}
```

contexts lines28-28

```lean
section IsZeroOrProbabilityMeasure
```

contexts lines59-59

```lean
end IsZeroOrProbabilityMeasure
```

contexts lines61-61

```lean
section IsProbabilityMeasure
```

ranges lines1-80

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.UnitInterval

/-!
# Classes for probability measures

We introduce the following typeclasses for measures:

* `IsZeroOrProbabilityMeasure μ`: `μ univ = 0 ∨ μ univ = 1`;
* `IsProbabilityMeasure μ`: `μ univ = 1`.
-/

public section

namespace MeasureTheory

open Set Measure Filter Function ENNReal

variable {α β : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {s : Set α}

section IsZeroOrProbabilityMeasure

/-- A measure `μ` is zero or a probability measure if `μ univ = 0` or `μ univ = 1`. This class
of measures appears naturally when conditioning on events, and many results which are true for
probability measures hold more generally over this class. -/
class IsZeroOrProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 0 ∨ μ univ = 1

lemma isZeroOrProbabilityMeasure_iff : IsZeroOrProbabilityMeasure μ ↔ μ univ = 0 ∨ μ univ = 1 :=
  ⟨fun _ ↦ IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk⟩

lemma prob_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} : μ s ≤ 1 := by
  apply (measure_mono (subset_univ _)).trans
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h <;> simp [h]

@[simp]
lemma measureReal_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} :
    μ.real s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)

@[simp]
theorem one_le_prob_iff {μ : Measure α} [IsZeroOrProbabilityMeasure μ] : 1 ≤ μ s ↔ μ s = 1 :=
  ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩

instance (priority := 100) IsZeroOrProbabilityMeasure.toIsFiniteMeasure (μ : Measure α)
    [IsZeroOrProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨prob_le_one.trans_lt one_lt_top⟩

instance : IsZeroOrProbabilityMeasure (0 : Measure α) :=
  ⟨Or.inl rfl⟩

end IsZeroOrProbabilityMeasure

section IsProbabilityMeasure

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class IsProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 1

export MeasureTheory.IsProbabilityMeasure (measure_univ)

attribute [simp] IsProbabilityMeasure.measure_univ

lemma isProbabilityMeasure_iff : IsProbabilityMeasure μ ↔ μ univ = 1 :=
  ⟨fun _ ↦ measure_univ, IsProbabilityMeasure.mk⟩

instance (priority := 100) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsZeroOrProbabilityMeasure μ :=
  ⟨Or.inr measure_univ⟩

theorem nonempty_of_isProbabilityMeasure (μ : Measure α) [IsProbabilityMeasure μ] : Nonempty α := by
  by_contra! maybe_empty
  have : μ Set.univ = 0 := by
```

