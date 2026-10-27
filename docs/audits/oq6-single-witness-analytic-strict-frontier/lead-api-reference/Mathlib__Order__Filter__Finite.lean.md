# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Order/Filter/Finite.lean", "sha256": "b26d5f2f5e115eb5733aef6a27f4607628921704d5e17c9935c2861733c44017", "bytes": 17713, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Data.Set.Finite.Lattice
```

contexts lines9-9

```lean
public import Mathlib.Order.CompleteLattice.Finset
```

contexts lines10-10

```lean
public import Mathlib.Order.Filter.Basic
```

contexts lines18-18

```lean
public section
```

contexts lines20-20

```lean
open Function Set Order
```

contexts lines21-21

```lean
open scoped symmDiff
```

contexts lines25-25

```lean
namespace Filter
```

contexts lines27-27

```lean
variable {α : Type u} {f : Filter α} {s : Set α}
```

contexts lines51-51

```lean
end Filter
```

contexts lines54-54

```lean
namespace Filter
```

contexts lines56-56

```lean
variable {α : Type u} {β : Type v} {ι : Sort x}
```

contexts lines58-58

```lean
section Lattice
```

contexts lines60-60

```lean
variable {f g : Filter α} {s t : Set α}
```

contexts lines242-242

```lean
end Lattice
```

ranges lines244-269

```lean
/-! ### Eventually and Frequently -/

@[simp]
theorem eventually_all {ι : Sort*} [Finite ι] {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, ofPred_forall] using iInter_mem

@[simp]
theorem eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, ofPred_forall] using biInter_mem hI

protected alias _root_.Set.Finite.eventually_all := eventually_all_finite

@[simp] theorem eventually_all_finset {ι} (I : Finset ι) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x :=
  I.finite_toSet.eventually_all

protected alias _root_.Finset.eventually_all := eventually_all_finset

@[simp]
theorem frequently_exists {ι : Sort*} [Finite ι] {l} {p : ι → α → Prop} :
    (∃ᶠ x in l, ∃ i, p i x) ↔ ∃ i, ∃ᶠ x in l, p i x := by
  rw [← not_iff_not]
  simp

```

