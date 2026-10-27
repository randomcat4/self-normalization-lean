# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean", "sha256": "8cafe2d83ca194225b37f331c01ed08219f58541b6de0aa0d20a6866fa048935", "bytes": 15859, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Algebra.Notation.Indicator
```

contexts lines9-9

```lean
public import Mathlib.Data.Int.Cast.Pi
```

contexts lines10-10

```lean
public import Mathlib.Data.Nat.Cast.Basic
```

contexts lines11-11

```lean
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
```

contexts lines12-12

```lean
public import Mathlib.Order.SupClosed
```

contexts lines48-48

```lean
open Set
```

contexts lines50-50

```lean
open scoped MeasureTheory
```

contexts lines54-54

```lean
variable {α β γ : Type*} {ι : Sort uι} {s : Set α}
```

contexts lines56-56

```lean
namespace MeasurableSpace
```

contexts lines58-58

```lean
section Functors
```

contexts lines60-60

```lean
variable {m m₁ m₂ : MeasurableSpace α} {m' : MeasurableSpace β} {f : α → β} {g : β → α}
```

contexts lines162-162

```lean
end Functors
```

contexts lines177-177

```lean
end MeasurableSpace
```

contexts lines179-179

```lean
section MeasurableFunctions
```

contexts lines181-181

```lean
open MeasurableSpace
```

contexts lines249-249

```lean
variable {f g : α → β}
```

contexts lines251-251

```lean
section TypeclassMeasurableSpace
```

contexts lines253-253

```lean
variable [MeasurableSpace α] [MeasurableSpace β]
```

ranges lines230-255

```lean
    Measurable[mα ⊔ mα'] f :=
  h.mono le_sup_right le_rfl

theorem measurable_id'' {m mα : MeasurableSpace α} (hm : m ≤ mα) : @Measurable α α mα m id :=
  measurable_id.mono le_rfl hm

theorem measurable_from_top [MeasurableSpace β] {f : α → β} : Measurable[⊤] f := fun _ _ => trivial

theorem measurable_generateFrom [MeasurableSpace α] {s : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ s, MeasurableSet (f ⁻¹' t)) : @Measurable _ _ _ (generateFrom s) f :=
  Measurable.of_le_map <| generateFrom_le h

theorem measurableSet_generateFrom_of_mem_supClosure {s : Set (Set α)} {t : Set α}
    (ht : t ∈ supClosure s) : MeasurableSet[generateFrom s] t := by
  rcases ht with ⟨P, hP, PC, rfl⟩
  rw [Finset.sup'_eq_sup, Finset.sup_id_set_eq_sUnion]
  exact MeasurableSet.sUnion (Finset.countable_toSet P)
    (fun s hs ↦ measurableSet_generateFrom (PC hs))

variable {f g : α → β}

section TypeclassMeasurableSpace

variable [MeasurableSpace α] [MeasurableSpace β]

@[nontriviality]
```

