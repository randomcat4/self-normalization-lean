# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean", "sha256": "7b467c049ee486339022e2d65a13ee22c37df2625fabeb2c92c0190c7c8aeb1c", "bytes": 18146, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Order.Filter.AtTopBot.Tendsto
```

contexts lines9-9

```lean
public import Mathlib.Order.Filter.Bases.Basic
```

contexts lines10-10

```lean
public import Mathlib.Order.Nat
```

contexts lines12-12

```lean
import Mathlib.Tactic.Subsingleton
```

contexts lines20-20

```lean
public section
```

contexts lines24-24

```lean
variable {ι ι' α β : Type*}
```

contexts lines26-26

```lean
open Set
```

contexts lines28-28

```lean
namespace Filter
```

contexts lines30-30

```lean
section IsDirected
```

contexts lines31-31

```lean
variable [Preorder α] [IsDirectedOrder α] {p : α → Prop}
```

contexts lines64-64

```lean
variable [Nonempty α]
```

ranges lines77-102

```lean
  atTop_basis.mem_iff.trans <| exists_congr fun _ => iff_of_eq (true_and _)

@[to_dual (attr := simp)]
lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b, a ≤ b → p b := mem_atTop_sets

@[to_dual]
theorem frequently_atTop : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b, a ≤ b ∧ p b :=
  atTop_basis.frequently_iff.trans <| by simp

@[to_dual]
alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop

-- `to_dual` cannot translate `forall_ge_iff`
lemma exists_eventually_atTop {r : α → β → Prop} :
    (∃ b, ∀ᶠ a in atTop, r a b) ↔ ∀ᶠ a₀ in atTop, ∃ b, ∀ a, a₀ ≤ a → r a b := by
  simp_rw [eventually_atTop, ← exists_comm (α := α)]
  exact exists_congr fun a ↦ .symm <| forall_ge_iff <| Monotone.exists fun _ _ _ hb H n hn ↦
    H n (hb.trans hn)

@[to_dual existing]
lemma exists_eventually_atBot {α : Type*} [Preorder α] [IsCodirectedOrder α] [Nonempty α]
    {r : α → β → Prop} : (∃ b, ∀ᶠ a in atBot, r a b) ↔ ∀ᶠ a₀ in atBot, ∃ b, ∀ a ≤ a₀, r a b :=
  exists_eventually_atTop (α := αᵒᵈ)

@[to_dual]
theorem map_atTop_eq {f : α → β} : atTop.map f = ⨅ a, 𝓟 (f '' { a' | a ≤ a' }) :=
```

