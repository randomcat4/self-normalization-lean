# Exact pinned generated standard API producer source

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Topology/Algebra/Order/Group.lean", "sha256": "89d8872ab941b5690b6530710748a851eb398313f2eb18f477e2f3833f5c9cbb", "bytes": 5833, "mtime_ns": "1792382595000000000"}}

Exact lines 1-74 (full prefix includes imports and all binder contexts)

```lean
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Order.LeftRightNhds

import Mathlib.Algebra.Order.Group.Basic

/-!
# Topology on a linear ordered commutative group

In this file we prove that a linear ordered commutative group with order topology
is a topological group.
We also prove continuity of `abs : G → G` and provide convenience lemmas like `ContinuousAt.abs`.
-/

public section


open Set Filter Function

open scoped Topology

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
  [OrderTopology G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toIsTopologicalGroup :
    IsTopologicalGroup G where
  continuous_mul := by
    simp only [continuous_iff_continuousAt, Prod.forall, ContinuousAt,
      LinearOrderedCommGroup.tendsto_nhds]
    intro a b ε hε
    rcases dense_or_discrete 1 ε with ⟨δ, hδ₁, hδε⟩ | ⟨-, hε_min⟩
    · filter_upwards [(eventually_mabs_div_lt _ hδ₁).prod_nhds
        (eventually_mabs_div_lt _ (one_lt_div'.mpr hδε))]
      rintro ⟨c, d⟩ ⟨hc, hd⟩
      calc
        |c * d / (a * b)|ₘ = |(c / a) * (d / b)|ₘ := by rw [div_mul_div_comm]
        _ ≤ |c / a|ₘ * |d / b|ₘ := mabs_mul_le ..
        _ < δ * (ε / δ) := mul_lt_mul_of_lt_of_lt hc hd
        _ = ε := mul_div_cancel ..
    · have (x : G) : ∀ᶠ y in 𝓝 x, y = x :=
        (eventually_mabs_div_lt _ hε).mono fun y hy ↦ mabs_div_le_one.mp <| hε_min _ hy
      filter_upwards [(this _).prod_nhds (this _)]
      simp [hε]
  continuous_inv := continuous_iff_continuousAt.2 fun a ↦
    LinearOrderedCommGroup.tendsto_nhds.2 fun ε ε0 ↦
      (eventually_mabs_div_lt a ε0).mono fun x hx ↦ by rwa [inv_div_inv, mabs_div_comm]

@[to_additive (attr := continuity)]
theorem continuous_mabs : Continuous (mabs : G → G) :=
  continuous_id.max continuous_inv

section Tendsto

variable {α : Type*} {l : Filter α} {f : α → G}

@[to_additive]
protected theorem Filter.Tendsto.mabs {a : G} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun x => |f x|ₘ) l (𝓝 |a|ₘ) :=
  (continuous_mabs.tendsto _).comp h

@[to_additive (attr := simp)]
theorem comap_mabs_nhds_one : comap mabs (𝓝 (1 : G)) = 𝓝 1 := by
  simp [nhds_eq_iInf_mabs_div]

@[to_additive]
theorem tendsto_one_iff_mabs_tendsto_one (f : α → G) :
```
