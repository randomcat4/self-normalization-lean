# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean", "sha256": "a8ef0ba0a9b953a5aae9fb16188cd7ad93e0e8d5767c564d02e9f2e8c57eedf2", "bytes": 31964, "mtime_ns": "1792382595000000000"}}

contexts lines21-21

```lean
open scoped NNReal Topology
```

contexts lines22-22

```lean
open Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal
```

contexts lines24-24

```lean
variable {α β δ ι : Type*}
```

contexts lines26-26

```lean
namespace MeasureTheory
```

contexts lines28-29

```lean
variable {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ ν ν₁ ν₂ : Measure α}
  {s t : Set α}
```

contexts lines31-31

```lean
section IsFiniteMeasure
```

ranges lines1-58

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Classes for finite measures

We introduce the following typeclasses for measures:

* `IsFiniteMeasure μ`: `μ univ < ∞`;
* `IsLocallyFiniteMeasure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`.
-/

@[expose] public section

open scoped NNReal Topology
open Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal

variable {α β δ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ ν ν₁ ν₂ : Measure α}
  {s t : Set α}

section IsFiniteMeasure

/-- A measure `μ` is called finite if `μ univ < ∞`. -/
@[mk_iff]
class IsFiniteMeasure (μ : Measure α) : Prop where
  measure_univ_lt_top : μ univ < ∞

lemma not_isFiniteMeasure_iff : ¬IsFiniteMeasure μ ↔ μ univ = ∞ := by simp [isFiniteMeasure_iff]

lemma isFiniteMeasure_restrict : IsFiniteMeasure (μ.restrict s) ↔ μ s ≠ ∞ := by
  simp [isFiniteMeasure_iff, lt_top_iff_ne_top]

instance Restrict.isFiniteMeasure (μ : Measure α) [hs : Fact (μ s < ∞)] :
    IsFiniteMeasure (μ.restrict s) :=
  ⟨by simpa using hs.elim⟩

@[simp]
theorem measure_lt_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s < ∞ :=
  (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top

instance isFiniteMeasureRestrict (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.restrict s) := ⟨by simp⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem measure_ne_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ :=
  ne_of_lt (measure_lt_top μ s)

theorem measure_compl_le_add_of_le_add [IsFiniteMeasure μ] (hs : MeasurableSet s)
```

