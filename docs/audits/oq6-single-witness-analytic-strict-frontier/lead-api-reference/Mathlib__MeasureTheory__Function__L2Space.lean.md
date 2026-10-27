# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean", "sha256": "c5737e32b9b1e2a6a0d04b411244ed90d0fcf25aab0449b51865d39182eb4593", "bytes": 13817, "mtime_ns": "1792382595000000000"}}

contexts lines8-8

```lean
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
```

contexts lines9-9

```lean
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
```

contexts lines10-10

```lean
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
```

contexts lines11-11

```lean
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
```

contexts lines28-28

```lean
public section
```

contexts lines32-32

```lean
open TopologicalSpace MeasureTheory MeasureTheory.Lp Filter
```

contexts lines34-34

```lean
open scoped NNReal ENNReal MeasureTheory InnerProductSpace
```

contexts lines36-36

```lean
namespace MeasureTheory
```

contexts lines38-38

```lean
section
```

contexts lines40-40

```lean
variable {α F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]
```

contexts lines57-57

```lean
end
```

contexts lines59-59

```lean
section InnerProductSpace
```

contexts lines61-61

```lean
variable {α : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
```

contexts lines62-62

```lean
variable {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
```

ranges lines49-74

```lean
  · simp
  · rw [div_eq_mul_inv, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem memLp_two_iff_integrable_sq {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ := by
  convert! memLp_two_iff_integrable_sq_norm hf using 3
  simp

end

section InnerProductSpace

variable {α : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
variable {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

theorem MemLp.const_inner (c : E) {f : α → E} (hf : MemLp f p μ) : MemLp (fun a => ⟪c, f a⟫) p μ :=
  hf.of_le_mul (AEStronglyMeasurable.inner aestronglyMeasurable_const hf.aestronglyMeasurable)
    (Eventually.of_forall fun _ => norm_inner_le_norm _ _)

theorem MemLp.inner_const {f : α → E} (hf : MemLp f p μ) (c : E) : MemLp (fun a => ⟪f a, c⟫) p μ :=
  hf.of_le_mul (c := ‖c‖)
    (AEStronglyMeasurable.inner hf.aestronglyMeasurable aestronglyMeasurable_const)
    (Eventually.of_forall fun x => by rw [mul_comm]; exact norm_inner_le_norm _ _)

```

