# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean", "sha256": "d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759", "bytes": 57371, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
```

contexts lines9-9

```lean
public import Mathlib.MeasureTheory.Function.LpOrder
```

contexts lines10-10

```lean
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
```

contexts lines43-43

```lean
open ENNReal Filter MeasureTheory NNReal Set TopologicalSpace
```

contexts lines45-45

```lean
open scoped Topology
```

contexts lines47-47

```lean
variable {α β γ δ ε ε' : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]
```

contexts lines48-49

```lean
variable [NormedAddCommGroup β] [NormedAddCommGroup γ]
  [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
```

contexts lines51-51

```lean
namespace MeasureTheory
```

contexts lines309-309

```lean
section
```

contexts lines311-311

```lean
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
```

contexts lines349-349

```lean
end
```

contexts lines351-351

```lean
section
```

contexts lines353-353

```lean
variable {α' : Type*} [MeasurableSpace α']
```

contexts lines369-369

```lean
end
```

contexts lines403-403

```lean
section ESeminormedAddMonoid
```

contexts lines405-405

```lean
variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddMonoid ε']
```

contexts lines407-407

```lean
variable (α ε') in
```

ranges lines378-403

```lean
  simp_rw [← memLp_one_iff_integrable]
  exact f.memLp_map_measure_iff

theorem MeasurePreserving.integrable_comp {ν : Measure δ} {g : δ → ε} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : AEStronglyMeasurable g ν) :
    Integrable (g ∘ f) μ ↔ Integrable g ν := by
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm

theorem MeasurePreserving.integrable_comp_of_integrable {ν : Measure δ} {g : δ → ε} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : Integrable g ν) :
    Integrable (g ∘ f) μ :=
  hf.integrable_comp hg.aestronglyMeasurable |>.mpr hg

theorem MeasurePreserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : MeasurePreserving f μ ν)
    (h₂ : MeasurableEmbedding f) {g : δ → ε} : Integrable (g ∘ f) μ ↔ Integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

theorem lintegral_edist_lt_top {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

section ESeminormedAddMonoid
```

ranges lines384-409

```lean
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm

theorem MeasurePreserving.integrable_comp_of_integrable {ν : Measure δ} {g : δ → ε} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : Integrable g ν) :
    Integrable (g ∘ f) μ :=
  hf.integrable_comp hg.aestronglyMeasurable |>.mpr hg

theorem MeasurePreserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : MeasurePreserving f μ ν)
    (h₂ : MeasurableEmbedding f) {g : δ → ε} : Integrable (g ∘ f) μ ↔ Integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

theorem lintegral_edist_lt_top {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

section ESeminormedAddMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

variable (α ε') in
@[to_fun (attr := fun_prop, simp) integrable_fun_zero]
theorem integrable_zero (μ : Measure α) : Integrable (0 : α → ε') μ := by
```

