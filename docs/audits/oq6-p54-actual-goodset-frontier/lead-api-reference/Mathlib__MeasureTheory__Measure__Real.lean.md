# Exact pinned standard API source reference

{"mathlibHEAD": "807d3836b165983210ee2ecf3cd28f239436949c", "source": {"physical_path": "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq56/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Real.lean", "sha256": "1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d", "bytes": 24359, "mtime_ns": "1792382595000000000"}}


ranges lines1-145

```lean
/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measures as real-valued functions

Given a measure `μ`, we have defined `μ.real` as the function sending a set `s` to `(μ s).toReal`.
In this file, we develop a basic API around this notion.

We essentially copy relevant lemmas from the files `MeasureSpaceDef.lean`, `NullMeasurable.lean` and
`MeasureSpace.lean`, and adapt them by replacing in their name `measure` with `measureReal`.

Many lemmas require an assumption that some set has finite measure. These assumptions are written
in the form `(h : μ s ≠ ∞ := by finiteness)`, where `finiteness` is a tactic for goals of
the form `≠ ∞`.

There are certainly many missing lemmas. The missing ones should be added as they are needed.

There are no lemmas on infinite sums, as summability issues are really
more painful with reals than nonnegative extended reals. They should probably be added in the long
run.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal NNReal Function symmDiff

namespace MeasureTheory

variable {α β ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t t₁ t₂ u : Set α}

theorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s = 0 ↔ μ s = 0 := by
  rw [Measure.real, ENNReal.toReal_eq_zero_iff]
  exact or_iff_left h

theorem measureReal_ne_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s ≠ 0 ↔ μ s ≠ 0 := by
  simp [measureReal_eq_zero_iff, h]

@[simp] theorem measureReal_zero : (0 : Measure α).real = 0 := rfl

theorem measureReal_zero_apply (s : Set α) : (0 : Measure α).real s = 0 := rfl

@[simp] theorem measureReal_nonneg : 0 ≤ μ.real s := ENNReal.toReal_nonneg

@[simp] theorem measureReal_empty : μ.real ∅ = 0 := by simp [Measure.real]

@[simp]
theorem measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ :=
  ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (by finiteness)

theorem measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ ≠ 0 :=
  measureReal_univ_pos.ne'

@[simp]
theorem ofReal_measureReal (h : μ s ≠ ∞ := by finiteness) : ENNReal.ofReal (μ.real s) = μ s := by
  simp [measureReal_def, h]

theorem nonempty_of_measureReal_ne_zero (h : μ.real s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' ↦ h <| h'.symm ▸ measureReal_empty

@[simp] theorem measureReal_ennreal_smul_apply (c : ℝ≥0∞) :
    (c • μ).real s = c.toReal * μ.real s := by
  simp [Measure.real]

@[simp] theorem measureReal_nnreal_smul_apply (c : ℝ≥0) :
    (c • μ).real s = c * μ.real s := by
  simp [measureReal_def]

theorem map_measureReal_apply_of_aemeasurable [MeasurableSpace β] {f : α → β}
    (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).real s = μ.real (f ⁻¹' s) := by
  simp_rw [measureReal_def, map_apply_of_aemeasurable hf hs]

theorem map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s) :=
  map_measureReal_apply_of_aemeasurable hf.aemeasurable hs

@[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ ≤ μ.real s₂ :=
  ENNReal.toReal_mono h₂ (measure_mono h)

theorem measureReal_eq_measureReal_iff {m : MeasurableSpace β} {ν : Measure β} {t : Set β}
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : ν t ≠ ∞ := by finiteness) :
    μ.real s = ν.real t ↔ μ s = ν t := by
  simp [measureReal_def, ENNReal.toReal_eq_toReal_iff' h₁ h₂]

theorem measureReal_restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply₀ ht]

@[simp]
theorem measureReal_restrict_apply (ht : MeasurableSet t) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply ht]

theorem measureReal_restrict_apply_univ (s : Set α) : (μ.restrict s).real univ = μ.real s := by
  simp

@[simp]
theorem measureReal_restrict_apply' (hs : MeasurableSet s) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply' hs]

theorem measureReal_restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t ∩ s) := by
  simp only [restrict_apply₀' hs]

@[simp]
theorem measureReal_restrict_apply_self (s : Set α) : (μ.restrict s).real s = μ.real s := by
  simp [measureReal_def]

theorem measureReal_mono_null (h : s₁ ⊆ s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ = 0 := by
  rw [measureReal_eq_zero_iff h'₂] at h₂
  simp [Measure.real, measure_mono_null h h₂]

theorem measureReal_le_measureReal_union_left (h : μ t ≠ ∞ := by finiteness) :
    μ.real s ≤ μ.real (s ∪ t) := by
  rcases eq_top_or_lt_top (μ s) with hs | hs
  · simp [Measure.real, hs]
  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne

theorem measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :
    μ.real t ≤ μ.real (s ∪ t) := by
  rw [union_comm]
  exact measureReal_le_measureReal_union_left h

theorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by
  rcases eq_top_or_lt_top (μ (s₁ ∪ s₂)) with h | h
  · simp only [Measure.real, h, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have A : μ s₁ ≠ ∞ := measure_ne_top_of_subset subset_union_left h.ne
    have B : μ s₂ ≠ ∞ := measure_ne_top_of_subset subset_union_right h.ne
    simp only [Measure.real, ← ENNReal.toReal_add A B]
    exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)

```
