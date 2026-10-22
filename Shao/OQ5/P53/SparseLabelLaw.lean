import Shao.OQ5.P53.SparseMassLimits
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace Shao.OQ5.P53

def sparseLabelMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure ℕ :=
  Measure.sum fun j : ℕ => ENNReal.ofReal (sparseLabelMass α x N j) • Measure.dirac j

theorem sparseLabelMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseLabelMeasure α x N) := by
  intro α x N
  exact HasSum.isProbabilityMeasure_sum_dirac
    (fun j => sparseLabelMass_nonneg α x N j) (hasSum_sparseLabelMass α x N)

theorem sparseLabelMeasure_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparseLabelMeasure α x N {j} = ENNReal.ofReal (sparseLabelMass α x N j) := by
  intro α x N j
  exact Measure.sum_smul_dirac_singleton

theorem sparseLabelMeasure_real_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparseLabelMeasure α x N).real {j} = sparseLabelMass α x N j := by
  intro α x N j
  rw [measureReal_def, sparseLabelMeasure_singleton]
  exact ENNReal.toReal_ofReal (sparseLabelMass_nonneg α x N j)

private theorem label_prior_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparsePriorMass α x N j := by
  unfold sparsePriorMass
  exact Finset.sum_nonneg fun k _ => sparseLabelMass_nonneg α x N k

theorem sparseLabelMeasure_Iio :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparseLabelMeasure α x N (Set.Iio j) = ENNReal.ofReal (sparsePriorMass α x N j) := by
  intro α x N j
  have hset : (Finset.range j : Set ℕ) = Set.Iio j := by
    ext k
    simp only [Finset.mem_coe, Finset.mem_range, Set.mem_Iio]
  calc
    sparseLabelMeasure α x N (Set.Iio j) =
        ∑ k ∈ Finset.range j, sparseLabelMeasure α x N {k} := by
      rw [← hset]
      exact (sum_measure_singleton (μ := sparseLabelMeasure α x N)
        (s := Finset.range j)).symm
    _ = ∑ k ∈ Finset.range j, ENNReal.ofReal (sparseLabelMass α x N k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact sparseLabelMeasure_singleton α x N k
    _ = ENNReal.ofReal (sparsePriorMass α x N j) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun k _ => sparseLabelMass_nonneg α x N k)).symm

theorem sparseLabelMeasure_real_Iio :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparseLabelMeasure α x N).real (Set.Iio j) = sparsePriorMass α x N j := by
  intro α x N j
  rw [measureReal_def, sparseLabelMeasure_Iio]
  exact ENNReal.toReal_ofReal (label_prior_nonneg α x N j)

private theorem label_real_Ici (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    (sparseLabelMeasure α x N).real (Set.Ici j) = sparseHighMass α x N j := by
  let : IsProbabilityMeasure (sparseLabelMeasure α x N) :=
    sparseLabelMeasure_probability α x N
  have hcompl : (Set.Iio j : Set ℕ)ᶜ = Set.Ici j := by
    ext k
    simp only [Set.mem_compl_iff, Set.mem_Iio, Set.mem_Ici, not_lt]
  have hm : MeasurableSet (Set.Iio j : Set ℕ) := by trivial
  have hsum := probReal_add_probReal_compl
    (μ := sparseLabelMeasure α x N) (s := Set.Iio j) hm
  rw [hcompl, sparseLabelMeasure_real_Iio,
    sparsePriorMass_eq_one_sub_highMass α x N j hj] at hsum
  linarith

theorem sparseLabelMeasure_Ici :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  1 ≤ j →
  sparseLabelMeasure α x N (Set.Ici j) = ENNReal.ofReal (sparseHighMass α x N j) := by
  intro α x N j hj
  let : IsProbabilityMeasure (sparseLabelMeasure α x N) :=
    sparseLabelMeasure_probability α x N
  calc
    sparseLabelMeasure α x N (Set.Ici j) =
        ENNReal.ofReal ((sparseLabelMeasure α x N).real (Set.Ici j)) :=
      (ENNReal.ofReal_toReal
        (measure_ne_top (sparseLabelMeasure α x N) (Set.Ici j))).symm
    _ = ENNReal.ofReal (sparseHighMass α x N j) :=
      congrArg ENNReal.ofReal (label_real_Ici α x N j hj)

theorem sparseLabelMeasure_real_Ici :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  1 ≤ j →
  (sparseLabelMeasure α x N).real (Set.Ici j) = sparseHighMass α x N j := by
  intro α x N j hj
  exact label_real_Ici α x N j hj

theorem integrable_sparseLabelMeasure_iff :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ → ℝ),
  Integrable f (sparseLabelMeasure α x N) ↔
    Summable (fun j : ℕ => sparseLabelMass α x N j * ‖f j‖) := by
  intro α x N f
  have hw :
      (fun j : ℕ => (ENNReal.ofReal (sparseLabelMass α x N j)).toReal * ‖f j‖) =
        (fun j : ℕ => sparseLabelMass α x N j * ‖f j‖) := by
    funext j
    rw [ENNReal.toReal_ofReal (sparseLabelMass_nonneg α x N j)]
  change Integrable f
      (Measure.sum fun j : ℕ => ENNReal.ofReal (sparseLabelMass α x N j) •
        Measure.dirac j) ↔
    Summable (fun j : ℕ => sparseLabelMass α x N j * ‖f j‖)
  rw [← hw]
  exact integrable_sum_dirac_iff (fun _ => ENNReal.ofReal_ne_top)

theorem integral_sparseLabelMeasure :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ → ℝ),
  Integrable f (sparseLabelMeasure α x N) →
  (∫ j, f j ∂(sparseLabelMeasure α x N)) =
    ∑' j : ℕ, sparseLabelMass α x N j * f j := by
  intro α x N f hf
  calc
    (∫ j, f j ∂(sparseLabelMeasure α x N)) =
        ∑' j : ℕ, (sparseLabelMeasure α x N).real {j} • f j :=
      integral_countable hf
    _ = ∑' j : ℕ, sparseLabelMass α x N j * f j := by
      apply tsum_congr
      intro j
      rw [sparseLabelMeasure_real_singleton]
      rfl

theorem tendsto_sparseLabelMeasure_high_mass_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Ici j))
    atTop (nhds 0) := by
  intro α x N
  have heq :
      (fun j : ℕ => sparseHighMass α x N j) =ᶠ[atTop]
        (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Ici j)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    exact (sparseLabelMeasure_real_Ici α x N j hj).symm
  exact Filter.Tendsto.congr' heq (tendsto_sparseHighMass_zero α x N)

theorem tendsto_sparseLabelMeasure_high_mass_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  Tendsto (fun j : ℕ => (N j : ℝ) *
    (sparseLabelMeasure α x N).real (Set.Ici j))
    atTop (nhds 0) := by
  intro α x N hN
  have heq :
      (fun j : ℕ => (N j : ℝ) * sparseHighMass α x N j) =ᶠ[atTop]
        (fun j : ℕ => (N j : ℝ) *
          (sparseLabelMeasure α x N).real (Set.Ici j)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    exact congrArg (fun a : ℝ => (N j : ℝ) * a)
      (sparseLabelMeasure_real_Ici α x N j hj).symm
  exact Filter.Tendsto.congr' heq (tendsto_sparseHighMass_cost_zero α x N hN)

theorem tendsto_sparseLabelMeasure_low_mass_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Iio j))
    atTop (nhds 1) := by
  intro α x N
  have heq :
      (fun j : ℕ => sparsePriorMass α x N j) =ᶠ[atTop]
        (fun j : ℕ => (sparseLabelMeasure α x N).real (Set.Iio j)) :=
    Filter.Eventually.of_forall fun j => (sparseLabelMeasure_real_Iio α x N j).symm
  exact Filter.Tendsto.congr' heq (tendsto_sparsePriorMass_one α x N)

theorem tendsto_sparseLabelMeasure_background_power_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  SparseSelectionCore α x N →
  Tendsto (fun j : ℕ => ((sparseLabelMeasure α x N).real (Set.Iio j)) ^ (2 * (N j - 2)))
    atTop (nhds 1) := by
  intro α x N hN
  have heq :
      (fun j : ℕ => (sparsePriorMass α x N j) ^ (2 * (N j - 2))) =ᶠ[atTop]
        (fun j : ℕ => ((sparseLabelMeasure α x N).real (Set.Iio j)) ^
          (2 * (N j - 2))) := by
    filter_upwards [] with j
    rw [sparseLabelMeasure_real_Iio]
  exact Filter.Tendsto.congr' heq
    (tendsto_sparsePriorMass_background_power_one α x N hN)

end Shao.OQ5.P53
