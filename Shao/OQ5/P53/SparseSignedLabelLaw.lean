import Shao.OQ5.P53.SparseLabelLaw
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

namespace Shao.OQ5.P53

def sparseSignedLabelMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : Measure (ℕ × Bool) :=
  (sparseLabelMeasure α x N).prod
    (Measure.sum (fun b : Bool => (1 / 2 : ℝ≥0∞) • Measure.dirac b))

private def signedLabelFairMeasure : Measure Bool :=
  Measure.sum (fun b : Bool => (1 / 2 : ℝ≥0∞) • Measure.dirac b)

private theorem signedLabelFairMeasure_probability :
    IsProbabilityMeasure signedLabelFairMeasure := by
  have hs : Summable (fun _ : Bool => (1 / 2 : ℝ≥0∞)) := Summable.of_finite
  have ht : (∑' _ : Bool, (1 / 2 : ℝ≥0∞)) = 1 := by
    rw [tsum_bool]
    exact ENNReal.add_halves 1
  have htotal : HasSum (fun _ : Bool => (1 / 2 : ℝ≥0∞)) 1 := by
    simpa only [ht] using hs.hasSum
  exact htotal.isProbabilityMeasure_sum_dirac_ennreal

private theorem signedLabelFairMeasure_singleton (b : Bool) :
    signedLabelFairMeasure {b} = (1 / 2 : ℝ≥0∞) := by
  exact Measure.sum_smul_dirac_singleton

theorem sparseSignedLabelMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  IsProbabilityMeasure (sparseSignedLabelMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseLabelMeasure α x N) :=
    sparseLabelMeasure_probability α x N
  let : IsProbabilityMeasure signedLabelFairMeasure := signedLabelFairMeasure_probability
  change IsProbabilityMeasure ((sparseLabelMeasure α x N).prod signedLabelFairMeasure)
  infer_instance

theorem sparseSignedLabelMeasure_singleton :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool),
  sparseSignedLabelMeasure α x N {(j, b)} = ENNReal.ofReal (sparseLabelMass α x N j / 2) := by
  intro α x N j b
  let : IsProbabilityMeasure signedLabelFairMeasure := signedLabelFairMeasure_probability
  have hset : ({(j, b)} : Set (ℕ × Bool)) = ({j} : Set ℕ) ×ˢ ({b} : Set Bool) := by
    ext z
    rcases z with ⟨k, c⟩
    simp
  change (sparseLabelMeasure α x N).prod signedLabelFairMeasure {(j, b)} = _
  rw [hset, Measure.prod_prod, sparseLabelMeasure_singleton,
    signedLabelFairMeasure_singleton]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num [div_eq_mul_inv]

theorem sparseSignedLabelMeasure_first :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map Prod.fst = sparseLabelMeasure α x N := by
  intro α x N
  let : IsProbabilityMeasure signedLabelFairMeasure := signedLabelFairMeasure_probability
  have hfair : signedLabelFairMeasure Set.univ = 1 :=
    signedLabelFairMeasure_probability.measure_univ
  change ((sparseLabelMeasure α x N).prod signedLabelFairMeasure).map Prod.fst = _
  rw [Measure.map_fst_prod, hfair, one_smul]

theorem sparseSignedLabelMeasure_sign :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  (sparseSignedLabelMeasure α x N).map Prod.snd =
    (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true := by
  intro α x N
  let : IsProbabilityMeasure signedLabelFairMeasure := signedLabelFairMeasure_probability
  have hlabel : sparseLabelMeasure α x N Set.univ = 1 :=
    (sparseLabelMeasure_probability α x N).measure_univ
  change ((sparseLabelMeasure α x N).prod signedLabelFairMeasure).map Prod.snd = _
  rw [Measure.map_snd_prod, hlabel, one_smul, signedLabelFairMeasure, Measure.sum_bool]
  exact add_comm _ _

theorem sparseSignedLabelMeasure_eq_sum :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  sparseSignedLabelMeasure α x N =
    Measure.sum (fun j : ℕ => Measure.sum (fun b : Bool =>
      ENNReal.ofReal (sparseLabelMass α x N j / 2) • Measure.dirac (j, b))) := by
  intro α x N
  rw [Measure.sum_sum]
  apply Measure.ext_of_singleton
  rintro ⟨j, b⟩
  change sparseSignedLabelMeasure α x N {(j, b)} =
    (Measure.sum (fun z : ℕ × Bool =>
      ENNReal.ofReal (sparseLabelMass α x N z.1 / 2) • Measure.dirac z)) {(j, b)}
  rw [sparseSignedLabelMeasure_singleton, Measure.sum_smul_dirac_singleton]

theorem sparseSignedLabelMeasure_indep_coordinates :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  ProbabilityTheory.IndepFun (Prod.fst : ℕ × Bool → ℕ) (Prod.snd : ℕ × Bool → Bool)
    (sparseSignedLabelMeasure α x N) := by
  intro α x N
  let : IsProbabilityMeasure (sparseLabelMeasure α x N) :=
    sparseLabelMeasure_probability α x N
  let : IsProbabilityMeasure signedLabelFairMeasure := signedLabelFairMeasure_probability
  change ProbabilityTheory.IndepFun (Prod.fst : ℕ × Bool → ℕ)
    (Prod.snd : ℕ × Bool → Bool) ((sparseLabelMeasure α x N).prod signedLabelFairMeasure)
  exact ProbabilityTheory.indepFun_prod
    (μ := sparseLabelMeasure α x N) (ν := signedLabelFairMeasure)
    (X := fun j : ℕ => j) (Y := fun b : Bool => b) measurable_id measurable_id

private def signedLabelSliceMeasure (m : ℝ) (j : ℕ) : Measure (ℕ × Bool) :=
  Measure.sum (fun b : Bool => ENNReal.ofReal (m / 2) • Measure.dirac (j, b))

private theorem signedLabelSliceMeasure_integrable (m : ℝ) (j : ℕ)
    (f : ℕ × Bool → ℝ) : Integrable f (signedLabelSliceMeasure m j) := by
  exact (integrable_sum_dirac_iff (f := f) (x := fun b : Bool => (j, b))
    (c := fun _ : Bool => ENNReal.ofReal (m / 2))
    (fun _ : Bool => ENNReal.ofReal_ne_top)).2
    (Summable.of_finite : Summable (fun b : Bool =>
      (ENNReal.ofReal (m / 2)).toReal * ‖f (j, b)‖))

private theorem signedLabelSliceMeasure_integral (m : ℝ) (j : ℕ)
    (f : ℕ × Bool → ℝ) (hm : 0 ≤ m) :
    (∫ z, f z ∂(signedLabelSliceMeasure m j)) =
      (m / 2) * (f (j, false) + f (j, true)) := by
  change (∫ z, f z ∂(Measure.sum (fun b : Bool =>
    ENNReal.ofReal (m / 2) • Measure.dirac (j, b)))) = _
  rw [integral_sum_dirac_eq_tsum (f := f) (x := fun b : Bool => (j, b))
    (c := fun _ : Bool => ENNReal.ofReal (m / 2))
    (fun _ : Bool => ENNReal.ofReal_ne_top)
    (Summable.of_finite : Summable (fun b : Bool =>
      (ENNReal.ofReal (m / 2)).toReal * ‖f (j, b)‖)), tsum_bool]
  simp only [ENNReal.toReal_ofReal (div_nonneg hm (by norm_num : (0 : ℝ) ≤ 2))]
  change (m / 2) * f (j, false) + (m / 2) * f (j, true) =
    (m / 2) * (f (j, false) + f (j, true))
  ring

theorem integrable_sparseSignedLabelMeasure_iff :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ × Bool → ℝ),
  Integrable f (sparseSignedLabelMeasure α x N) ↔
    Summable (fun j : ℕ => (sparseLabelMass α x N j / 2) *
      (‖f (j, false)‖ + ‖f (j, true)‖)) := by
  intro α x N f
  rw [sparseSignedLabelMeasure_eq_sum]
  change Integrable f (Measure.sum (fun j : ℕ =>
    signedLabelSliceMeasure (sparseLabelMass α x N j) j)) ↔ _
  have hnorm : (fun j : ℕ =>
      ∫ z, ‖f z‖ ∂(signedLabelSliceMeasure (sparseLabelMass α x N j) j)) =
      (fun j : ℕ => (sparseLabelMass α x N j / 2) *
        (‖f (j, false)‖ + ‖f (j, true)‖)) := by
    funext j
    exact signedLabelSliceMeasure_integral (sparseLabelMass α x N j) j
      (fun z => ‖f z‖) (sparseLabelMass_nonneg α x N j)
  rw [integrable_sum_measure_iff, hnorm]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨fun j => signedLabelSliceMeasure_integrable (sparseLabelMass α x N j) j f, h⟩

theorem integral_sparseSignedLabelMeasure :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (f : ℕ × Bool → ℝ),
  Integrable f (sparseSignedLabelMeasure α x N) →
  (∫ z, f z ∂(sparseSignedLabelMeasure α x N)) =
    ∑' j : ℕ, (sparseLabelMass α x N j / 2) * (f (j, false) + f (j, true)) := by
  intro α x N f hf
  rw [sparseSignedLabelMeasure_eq_sum] at hf ⊢
  rw [integral_sum_measure hf]
  apply tsum_congr
  intro j
  exact signedLabelSliceMeasure_integral (sparseLabelMass α x N j) j f
    (sparseLabelMass_nonneg α x N j)

end Shao.OQ5.P53
