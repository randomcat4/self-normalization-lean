# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean", "sha256": "d9e37392e603459e76d9799dd8cc59d62a514a0c79716098d0352e1455f7c200", "bytes": 37803, "mtime_ns": "1792382595000000000"}}


precedingContexts lines53-53

```lean
variable {α : Type*}
```

precedingContexts lines92-92

```lean
section Mul
```

precedingContexts lines94-95

```lean
variable {M α β : Type*} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α → M} {μ : Measure α}
```

precedingContexts lines152-152

```lean
end Mul
```

precedingContexts lines177-177

```lean
section Pow
```

precedingContexts lines179-180

```lean
variable {β γ α : Type*} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [MeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}
```

precedingContexts lines209-209

```lean
end Pow
```

precedingContexts lines243-243

```lean
section Div
```

precedingContexts lines245-246

```lean
variable {G α β : Type*} [MeasurableSpace G] [Div G] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α → G} {μ : Measure α}
```

precedingContexts lines316-316

```lean
end Div
```

precedingContexts lines343-343

```lean
section Inv
```

precedingContexts lines345-346

```lean
variable {G α : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}
```

precedingContexts lines380-380

```lean
end Inv
```

precedingContexts lines503-503

```lean
section SMul
```

precedingContexts lines504-505

```lean
variable {M X α β : Type*} [MeasurableSpace X] [SMul M X]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : α → M} {g : α → X}
```

precedingContexts lines507-507

```lean
section MeasurableConstSMul
```

precedingContexts lines508-508

```lean
variable [MeasurableConstSMul M X]
```

precedingContexts lines531-531

```lean
end MeasurableConstSMul
```

precedingContexts lines533-533

```lean
variable [MeasurableSpace M]
```

precedingContexts lines556-556

```lean
variable [MeasurableSMul M X]
```

precedingContexts lines598-598

```lean
end SMul
```

precedingContexts lines600-600

```lean
section IterateMulAct
```

precedingContexts lines602-602

```lean
variable {α : Type*} {_ : MeasurableSpace α} {f : α → α}
```

precedingContexts lines621-621

```lean
end IterateMulAct
```

precedingContexts lines623-623

```lean
section MulAction
```

precedingContexts lines624-624

```lean
variable {G G₀ M β α : Type*} [MeasurableSpace β] [MeasurableSpace α] {f : α → β} {μ : Measure α}
```

precedingContexts lines626-626

```lean
section Group
```

precedingContexts lines627-627

```lean
variable {G : Type*} [Group G] [MulAction G β] [MeasurableConstSMul G β]
```

precedingContexts lines638-638

```lean
end Group
```

precedingContexts lines640-640

```lean
section Monoid
```

precedingContexts lines641-641

```lean
variable [Monoid M] [MulAction M β]
```

precedingContexts lines643-643

```lean
section MeasurableConstSMul
```

precedingContexts lines644-644

```lean
variable [MeasurableConstSMul M β]
```

precedingContexts lines662-662

```lean
end MeasurableConstSMul
```

precedingContexts lines664-664

```lean
section MeasurableSMul
```

precedingContexts lines665-665

```lean
variable [MeasurableSpace M] [MeasurableSMul M β]
```

precedingContexts lines675-675

```lean
end MeasurableSMul
```

precedingContexts lines676-676

```lean
end Monoid
```

precedingContexts lines678-678

```lean
section GroupWithZero
```

precedingContexts lines679-679

```lean
variable [GroupWithZero G₀] [MulAction G₀ β] [MeasurableConstSMul G₀ β]
```

precedingContexts lines689-689

```lean
end GroupWithZero
```

precedingContexts lines690-690

```lean
end MulAction
```

precedingContexts lines697-697

```lean
section Opposite
```

precedingContexts lines752-752

```lean
end Opposite
```

precedingContexts lines759-759

```lean
section Monoid
```

precedingContexts lines761-762

```lean
variable {M α : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}
```

precedingContexts lines795-795

```lean
end Monoid
```

precedingContexts lines797-797

```lean
section CommMonoid
```

precedingContexts lines799-800

```lean
variable {M ι α β : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : ι → α → M}
```

ranges lines1-95

```lean
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Typeclasses for measurability of operations

In this file we define classes `MeasurableMul` etc. and prove dot-style lemmas
(`Measurable.mul`, `AEMeasurable.mul` etc). For binary operations we define two typeclasses:

- `MeasurableMul` says that both left and right multiplication are measurable;
- `MeasurableMul₂` says that `fun p : α × α => p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableMul₂`
etc. require `α` to have a second countable topology.

We define separate classes for `MeasurableDiv`/`MeasurableSub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `ContinuousMul` to `MeasurableMul` see file
`MeasureTheory.BorelSpace`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operation) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## TODO

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `MeasurablePow` to `MeasurableSMul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `MeasurableSMul`.)
-/

public section

open MeasureTheory
open scoped Pointwise

universe u v
variable {α : Type*}

/-!
### Binary operations: `(· + ·)`, `(· * ·)`, `(· - ·)`, `(· / ·)`
-/


/-- We say that a type has `MeasurableAdd` if `(c + ·)` and `(· + c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· + ·)` see `MeasurableAdd₂`. -/
class MeasurableAdd (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable (c + ·) := by intro; fun_prop
  measurable_add_const : ∀ c : M, Measurable (· + c) := by intro; fun_prop

export MeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type has `MeasurableAdd₂` if `uncurry (· + ·)` is a measurable function.
For a typeclass assuming measurability of `(c + ·)` and `(· + c)` see `MeasurableAdd`. -/
class MeasurableAdd₂ (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2

export MeasurableAdd₂ (measurable_add)

/-- We say that a type has `MeasurableMul` if `(c * ·)` and `(· * c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `MeasurableMul₂`. -/
@[to_additive]
class MeasurableMul (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable (c * ·) := by intro; fun_prop
  measurable_mul_const : ∀ c : M, Measurable (· * c) := by intro; fun_prop

export MeasurableMul (measurable_const_mul measurable_mul_const)

/-- We say that a type has `MeasurableMul₂` if `uncurry (· * ·)` is a measurable function.
For a typeclass assuming measurability of `(c * ·)` and `(· * c)` see `MeasurableMul`. -/
@[to_additive MeasurableAdd₂]
class MeasurableMul₂ (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2

export MeasurableMul₂ (measurable_mul)

section Mul

variable {M α β : Type*} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α → M} {μ : Measure α}
```

ranges lines735-838

```lean
/-- If a scalar is central, then its right action is measurable when its left action is. -/
nonrec instance MeasurableSMul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul₂ M α] : MeasurableSMul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2 by
      simp_rw [op_smul_eq_smul]
      exact (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩

@[to_additive]
instance measurableSMul_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableSMul Mᵐᵒᵖ M where
  measurable_smul_const x := measurable_mul_unop.const_mul x

@[to_additive]
instance measurableSMul₂_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableSMul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

-- TODO: `fun_prop` cannot use lemmas with a condition quantifying over the function
@[to_additive (attr := fun_prop)]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  induction l with
  | nil => exact measurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
theorem List.aemeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  induction l with
  | nil => exact aemeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
theorem List.measurable_fun_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod hl

@[to_additive (attr := fun_prop)]
theorem List.aemeasurable_fun_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aemeasurable_prod hl

end Monoid

section CommMonoid

variable {M ι α β : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : ι → α → M}

@[to_additive (attr := fun_prop)]
theorem Multiset.measurable_prod (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
theorem Multiset.aemeasurable_prod (l : Multiset (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aemeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
theorem Multiset.measurable_fun_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod hs

@[to_additive (attr := fun_prop)]
theorem Multiset.aemeasurable_fun_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aemeasurable_prod hs

@[to_additive (attr := fun_prop)]
theorem Finset.measurable_fun_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a ↦ ∏ i ∈ s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

@[to_additive (attr := fun_prop)]
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a ↦ ∏ i ∈ s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

/-- Compositional version of `Finset.measurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Finset.measurable_sum` for use by `fun_prop`. -/]
```
