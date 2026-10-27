# Exact pinned generated standard API producer source

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/Topology/Order/OrderClosed.lean", "sha256": "011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e", "bytes": 31585, "mtime_ns": "1792382595000000000"}}

Exact lines 1-245 (full prefix includes imports and all binder contexts)

```lean
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Order-closed topologies

In this file we introduce 3 typeclass mixins that relate topology and order structures:

- `ClosedIicTopology` says that all the intervals $(-∞, a]$ (formally, `Set.Iic a`)
  are closed sets;
- `ClosedIciTopology` says that all the intervals $[a, +∞)$ (formally, `Set.Ici a`)
  are closed sets;
- `OrderClosedTopology` says that the set of points `(x, y)` such that `x ≤ y`
  is closed in the product topology.

The last predicate implies the first two.

We prove many basic properties of such topologies.

## Main statements

This file contains the proofs of the following facts.
For exact requirements
(`OrderClosedTopology` vs `ClosedIciTopology` vs `ClosedIicTopology`,
`Preorder` vs `PartialOrder` vs `LinearOrder`, etc.)
see their statements.

### Open / closed sets

* `isOpen_lt` : if `f` and `g` are continuous functions, then `{x | f x < g x}` is open;
* `isOpen_Iio`, `isOpen_Ioi`, `isOpen_Ioo` : open intervals are open;
* `isClosed_le` : if `f` and `g` are continuous functions, then `{x | f x ≤ g x}` is closed;
* `isClosed_Iic`, `isClosed_Ici`, `isClosed_Icc` : closed intervals are closed;
* `frontier_le_subset_eq`, `frontier_lt_subset_eq` : frontiers of both `{x | f x ≤ g x}`
  and `{x | f x < g x}` are included by `{x | f x = g x}`;

### Convergence and inequalities

* `le_of_tendsto_of_tendsto` : if `f` converges to `a`, `g` converges to `b`, and eventually
  `f x ≤ g x`, then `a ≤ b`
* `le_of_tendsto`, `ge_of_tendsto` : if `f` converges to `a` and eventually `f x ≤ b`
  (resp., `b ≤ f x`), then `a ≤ b` (resp., `b ≤ a`); we also provide primed versions
  that assume the inequalities to hold for all `x`.
* `monotone_of_frequently_monotone_of_tendsto`, `antitone_of_frequently_antitone_of_tendsto` : the
  pointwise limit of frequently monotone or antitone functions is monotone or antitone.

### Min, max, `sSup` and `sInf`

* `Continuous.min`, `Continuous.max`: pointwise `min`/`max` of two continuous functions is
  continuous.
* `Tendsto.min`, `Tendsto.max` : if `f` tends to `a` and `g` tends to `b`, then their pointwise
  `min`/`max` tend to `min a b` and `max a b`, respectively.
-/

public section

open Set Filter TopologicalSpace
open OrderDual (toDual)
open scoped Topology

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- If `α` is a topological space and a preorder, `ClosedIicTopology α` means that `Iic a` is
closed for all `a : α`. -/
class ClosedIicTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `(-∞, a]` is closed. -/
  isClosed_Iic (a : α) : IsClosed (Iic a)

/-- If `α` is a topological space and a preorder, `ClosedIciTopology α` means that `Ici a` is
closed for all `a : α`. -/
@[to_dual existing]
class ClosedIciTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `[a, +∞)` is closed. -/
  isClosed_Ici (a : α) : IsClosed (Ici a)

/-- A topology on a set which is both a topological space and a preorder is _order-closed_ if the
set of points `(x, y)` with `x ≤ y` is closed in the product space. We introduce this as a mixin.
This property is satisfied for the order topology on a linear order, but it can be satisfied more
generally, and suffices to derive many interesting properties relating order and topology. -/
class OrderClosedTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- The set `{ (x, y) | x ≤ y }` is a closed set. -/
  protected isClosed_le' : IsClosed { p : α × α | p.1 ≤ p.2 }

instance [TopologicalSpace α] [h : FirstCountableTopology α] : FirstCountableTopology αᵒᵈ := h
instance [TopologicalSpace α] [h : SecondCountableTopology α] : SecondCountableTopology αᵒᵈ := h
instance [TopologicalSpace α] [h : SeparableSpace α] : SeparableSpace αᵒᵈ := h

theorem Dense.orderDual [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    Dense (OrderDual.ofDual ⁻¹' s) :=
  hs

section General
variable [TopologicalSpace α] [Preorder α] {s : Set α}

@[to_dual]
protected lemma BddAbove.of_closure : BddAbove (closure s) → BddAbove s :=
  BddAbove.mono subset_closure

end General

section ClosedIicTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {f : β → α} {a b : α} {s : Set α}

@[to_dual (attr := closedness .)]
theorem isClosed_Iic : IsClosed (Iic a) :=
  ClosedIicTopology.isClosed_Iic a

@[to_dual]
instance : ClosedIciTopology αᵒᵈ where
  isClosed_Ici _ := isClosed_Iic (α := α)

@[to_dual (attr := simp, closedness =)]
theorem closure_Iic (a : α) : closure (Iic a) = Iic a :=
  isClosed_Iic.closure_eq

@[to_dual ge_of_tendsto_of_frequently]
theorem le_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : ∃ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_frequently_of_tendsto h lim

@[to_dual ge_of_tendsto]
theorem le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_tendsto lim h

@[to_dual ge_of_tendsto']
theorem le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ c, f c ≤ b) : a ≤ b :=
  le_of_tendsto lim (Eventually.of_forall h)

@[to_dual (attr := simp)]
lemma upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperBounds s :=
  ext fun a ↦ by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]

@[to_dual (attr := simp)]
lemma bddAbove_closure : BddAbove (closure s) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_closure]

@[to_dual]
protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure

@[to_dual (attr := simp) disjoint_nhds_atTop_iff]
theorem disjoint_nhds_atBot_iff : Disjoint (𝓝 a) atBot ↔ ¬IsBot a := by
  constructor
  · intro hd hbot
    rw [hbot.atBot_eq, disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsBot, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Iic_mem_atBot b)
    exact isClosed_Iic.isOpen_compl.mem_nhds hb

@[to_dual]
theorem IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] (hle : ∀ i, f i ≤ a)
    (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a :=
  ⟨forall_mem_range.mpr hle, fun _c hc ↦ le_of_tendsto' hlim fun i ↦ hc <| mem_range_self i⟩

end Preorder

section NoBotOrder

variable [Preorder α] [NoBotOrder α] [TopologicalSpace α] [ClosedIicTopology α] {a : α}
  {l : Filter β} [NeBot l] {f : β → α}

@[to_dual disjoint_nhds_atTop]
theorem disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot := by simp

@[to_dual (attr := simp) nhds_inf_atTop]
theorem nhds_inf_atBot (a : α) : 𝓝 a ⊓ atBot = ⊥ := (disjoint_nhds_atBot a).eq_bot

@[to_dual]
theorem not_tendsto_nhds_of_tendsto_atBot (hf : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a) :=
  hf.not_tendsto (disjoint_nhds_atBot a).symm

@[to_dual]
theorem not_tendsto_atBot_of_tendsto_nhds (hf : Tendsto f l (𝓝 a)) : ¬Tendsto f l atBot :=
  hf.not_tendsto (disjoint_nhds_atBot a)

end NoBotOrder

theorem iSup_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [Filter.NeBot F]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι → α} (hle : ∀ i, f i ≤ a) (hlim : Filter.Tendsto f F (𝓝 a)) :
    ⨆ i, f i = a :=
  have := F.nonempty_of_neBot
  (IsLUB.range_of_tendsto hle hlim).ciSup_eq

theorem iUnion_Iic_eq_Iio_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι → α} (hlt : ∀ i, f i < a) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Iic (f i) = Iio a := by
  have obs : a ∉ range f := by
    rw [mem_range]
    rintro ⟨i, rfl⟩
    exact (hlt i).false
  rw [← biUnion_range, (IsLUB.range_of_tendsto (le_of_lt <| hlt ·) hlim).biUnion_Iic_eq_Iio obs]

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] [TopologicalSpace β]
  {a b c : α} {f : α → β}

@[to_dual]
theorem isOpen_Ioi : IsOpen (Ioi a) := by
  rw [← compl_Iic]
  exact isClosed_Iic.isOpen_compl

@[to_dual (attr := simp)]
theorem interior_Ioi : interior (Ioi a) = Ioi a :=
  isOpen_Ioi.interior_eq

@[to_dual]
theorem Ioi_mem_nhds (h : a < b) : Ioi a ∈ 𝓝 b := IsOpen.mem_nhds isOpen_Ioi h

@[to_dual eventually_lt_nhds]
theorem eventually_gt_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b < x := Ioi_mem_nhds hab

@[to_dual]
theorem Ici_mem_nhds (h : a < b) : Ici a ∈ 𝓝 b :=
  mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self

@[to_dual eventually_le_nhds]
theorem eventually_ge_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b ≤ x := Ici_mem_nhds hab

@[to_dual eventually_lt_const]
theorem Filter.Tendsto.eventually_const_lt {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Filter.Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u < f a :=
  h.eventually <| eventually_gt_nhds hv

@[to_dual eventually_le_const]
theorem Filter.Tendsto.eventually_const_le {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u ≤ f a :=
  h.eventually <| eventually_ge_nhds hv

```
