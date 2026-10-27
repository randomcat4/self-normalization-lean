# Exact pinned nat-cast filter API reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Archimedean.lean", "sha256": "0ba4137bb8d0837d43b1140379163e3cdf89e88675c26807c51f5e801ad31df3", "bytes": 12631, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Algebra.Order.Archimedean.Basic
```

contexts lines9-9

```lean
public import Mathlib.Order.Filter.AtTopBot.Group
```

contexts lines10-10

```lean
public import Mathlib.Order.Filter.CountablyGenerated
```

contexts lines12-12

```lean
import Mathlib.Algebra.Order.Group.Basic
```

contexts lines23-23

```lean
public section
```

contexts lines26-26

```lean
variable {α R : Type*}
```

contexts lines28-28

```lean
open Filter Set Function
```

ranges lines41-57

```lean
    Tendsto (fun x : ℕ+ => f x) atTop l ↔ Tendsto f atTop l := by
  exact tendsto_comp_val_Ioi_atTop

theorem tendsto_natCast_atTop_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] :
    Tendsto ((↑) : ℕ → R) atTop atTop :=
  Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge

lemma tendsto_PNat_val_atTop_atTop : Tendsto PNat.val atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ h ↦ h) fun a ↦ ⟨Nat.succPNat a, Nat.le_succ a⟩

theorem Filter.Eventually.natCast_atTop [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x : R) in atTop, p x) : ∀ᶠ (n : ℕ) in atTop, p n :=
  tendsto_natCast_atTop_atTop.eventually h

@[simp] theorem Int.comap_cast_atTop [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
```

