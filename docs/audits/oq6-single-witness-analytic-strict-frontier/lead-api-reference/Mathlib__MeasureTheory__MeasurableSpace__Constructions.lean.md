# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean", "sha256": "03bdd1fd16c69f61acf8ae50d684f54c9b565d03c6fa880fc338fcbd3bbebadb", "bytes": 49519, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Data.Finset.Update
```

contexts lines9-9

```lean
public import Mathlib.Data.Prod.TProd
```

contexts lines10-10

```lean
public import Mathlib.Data.Set.UnionLift
```

contexts lines11-11

```lean
public import Mathlib.GroupTheory.Coset.Defs
```

contexts lines12-12

```lean
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
```

contexts lines13-13

```lean
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
```

contexts lines14-14

```lean
public import Mathlib.Order.Disjointed
```

contexts lines27-27

```lean
open Set Function MeasureTheory
```

contexts lines31-31

```lean
variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}
```

contexts lines60-60

```lean
section ULift
```

contexts lines61-61

```lean
variable [MeasurableSpace α]
```

contexts lines74-74

```lean
end ULift
```

contexts lines76-76

```lean
section Nat
```

contexts lines78-78

```lean
variable {mα : MeasurableSpace α}
```

contexts lines123-123

```lean
end Nat
```

contexts lines125-125

```lean
section Quotient
```

contexts lines127-127

```lean
variable [MeasurableSpace α] [MeasurableSpace β]
```

contexts lines180-180

```lean
end Quotient
```

contexts lines182-182

```lean
section Subtype
```

contexts lines188-188

```lean
section
```

contexts lines190-190

```lean
variable [MeasurableSpace α]
```

contexts lines201-201

```lean
end
```

contexts lines203-203

```lean
variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}
```

contexts lines290-290

```lean
end Subtype
```

contexts lines292-292

```lean
section Atoms
```

contexts lines294-294

```lean
variable [MeasurableSpace β]
```

contexts lines365-365

```lean
end Atoms
```

contexts lines367-367

```lean
section Prod
```

contexts lines387-387

```lean
variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
```

contexts lines568-568

```lean
end Prod
```

contexts lines570-570

```lean
section Pi
```

contexts lines572-572

```lean
variable {X : δ → Type*} [MeasurableSpace α]
```

contexts lines577-577

```lean
variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]
```

ranges lines576-601

```lean

variable [∀ a, MeasurableSpace (X a)] [MeasurableSpace γ]

theorem measurable_pi_iff {g : α → ∀ a, X a} : Measurable g ↔ ∀ a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a :=
  measurable_pi_iff.1 measurable_id a

theorem MeasurableSpace.comap_le_comap_pi {g : (a : δ) → β → X a} (a : δ) :
    .comap (g a) inferInstance ≤ pi.comap (fun b c ↦ g c b) := by
  simpa only [pi, comap_iSup] using le_iSup_of_le a <| by measurability

theorem Measurable.eval {a : δ} {g : α → ∀ a, X a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg

@[fun_prop]
theorem Measurable.of_eval {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf

@[deprecated (since := "2026-08-20")] alias measurable_pi_lambda := Measurable.of_eval

```

ranges lines581-606

```lean
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
theorem measurable_pi_apply (a : δ) : Measurable fun f : ∀ a, X a => f a :=
  measurable_pi_iff.1 measurable_id a

theorem MeasurableSpace.comap_le_comap_pi {g : (a : δ) → β → X a} (a : δ) :
    .comap (g a) inferInstance ≤ pi.comap (fun b c ↦ g c b) := by
  simpa only [pi, comap_iSup] using le_iSup_of_le a <| by measurability

theorem Measurable.eval {a : δ} {g : α → ∀ a, X a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg

@[fun_prop]
theorem Measurable.of_eval {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf

@[deprecated (since := "2026-08-20")] alias measurable_pi_lambda := Measurable.of_eval

lemma MeasurableSpace.comap_process_pi (X : (a : δ) → β → X a) :
    MeasurableSpace.comap (fun b a ↦ X a b) inferInstance =
      ⨆ a, MeasurableSpace.comap (X a) inferInstance := by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl
```

