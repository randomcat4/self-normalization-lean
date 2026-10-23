import Shao.OQ5.P53.SparseSampleStatistics
import Shao.OQ5.P53.SparseRealSample

/-!
# Positivity of the actual p53 centered-row studentizer

The complete nested product law is regrouped into the independent uniform
noise vector and the two complete signed-label vectors. With these labels
fixed, each adjusted row is its own noise coordinate plus a label-only
constant. Equality of two distinct rows is therefore a measurable null event.
No moment or sparse-selection hypothesis is needed for this structural fact.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))
local notation "SignedLabel" => (ℕ × Bool)
local notation "noiseLaw" => Shao.OQ5.P35.noiseLaw

private def labelRow (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (i : Fin n) (c : (Fin n → SignedLabel) × (Fin n → SignedLabel)) : ℝ :=
  sparseSignedShift α x N (c.1 i) +
    (∑ k ∈ Finset.univ.erase i,
      sparseSignedAmplitude α x N (c.2 i) * sparseSignedAmplitude α x N (c.2 k)) /
      ((n : ℝ) - 2)

private def groupedRow (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ}
    (gc : (Fin n → ℝ) × ((Fin n → SignedLabel) × (Fin n → SignedLabel)))
    (i : Fin n) : ℝ :=
  gc.1 i + labelRow α x N i gc.2

private def regroupSample (n : ℕ) (ω : Fin n → SparseObs) :
    (Fin n → ℝ) × ((Fin n → SignedLabel) × (Fin n → SignedLabel)) :=
  (fun i => (ω i).1.1, (fun i => (ω i).1.2, fun i => (ω i).2))

private theorem measurable_labelRow (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (i : Fin n) : Measurable (labelRow α x N i) := by
  classical
  have hsum : Measurable
      (fun c : (Fin n → SignedLabel) × (Fin n → SignedLabel) =>
        ∑ k ∈ Finset.univ.erase i,
          sparseSignedAmplitude α x N (c.2 i) * sparseSignedAmplitude α x N (c.2 k)) := by
    apply Finset.measurable_sum
    intro k _
    exact ((measurable_sparseSignedAmplitude α x N).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
      ((measurable_sparseSignedAmplitude α x N).comp
        ((measurable_pi_apply k).comp measurable_snd))
  exact ((measurable_sparseSignedShift α x N).comp
    ((measurable_pi_apply i).comp measurable_fst)).add (hsum.div_const _)

private theorem measurable_groupedRow (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (i : Fin n) :
    Measurable (fun gc : (Fin n → ℝ) ×
      ((Fin n → SignedLabel) × (Fin n → SignedLabel)) => groupedRow α x N gc i) :=
  ((measurable_pi_apply i).comp measurable_fst).add
    ((measurable_labelRow α x N n i).comp measurable_snd)

private theorem adjustedRow_regroup (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (ω : Fin n → SparseObs) (i : Fin n) :
    sparseSampleAdjustedRow α x N ω i = groupedRow α x N (regroupSample n ω) i := by
  classical
  change ((ω i).1.1 + sparseSignedShift α x N (ω i).1.2) +
      (∑ k ∈ Finset.univ.erase i,
        sparseSignedAmplitude α x N (ω i).2 * sparseSignedAmplitude α x N (ω k).2) /
        ((n : ℝ) - 2) =
    (ω i).1.1 + (sparseSignedShift α x N (ω i).1.2 +
      (∑ k ∈ Finset.univ.erase i,
        sparseSignedAmplitude α x N (ω i).2 * sparseSignedAmplitude α x N (ω k).2) /
        ((n : ℝ) - 2))
  ring

private theorem regroupSample_preserving (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) :
    MeasurePreserving (regroupSample n)
      (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
      ((Measure.pi (fun _ : Fin n => noiseLaw)).prod
        ((Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N)).prod
          (Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N)))) := by
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  let : IsProbabilityMeasure (sparseGBaseMeasure α x N) :=
    sparseGBaseMeasure_probability α x N
  have houter := measurePreserving_arrowProdEquivProdArrow
    (ℝ × SignedLabel) SignedLabel (Fin n)
    (fun _ => sparseGBaseMeasure α x N) (fun _ => sparseSignedLabelMeasure α x N)
  have hinner := measurePreserving_arrowProdEquivProdArrow
    ℝ SignedLabel (Fin n) (fun _ => noiseLaw)
    (fun _ => sparseSignedLabelMeasure α x N)
  have hid : MeasurePreserving (id : (Fin n → SignedLabel) → (Fin n → SignedLabel))
      (Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N))
      (Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N)) :=
    ⟨measurable_id, Measure.map_id⟩
  have hmiddle := hinner.prod hid
  have hassoc := measurePreserving_prodAssoc
    (Measure.pi (fun _ : Fin n => noiseLaw))
    (Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N))
    (Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N))
  exact hassoc.comp (hmiddle.comp houter)

private theorem noise_affine_null {n : ℕ} (i k : Fin n) (hik : i ≠ k) (s t : ℝ) :
    (Measure.pi (fun _ : Fin n => noiseLaw)) {g | g i + s = g k + t} = 0 := by
  let ν := Measure.pi (fun _ : Fin n => noiseLaw)
  have hpair : Measure.map (fun g : Fin n → ℝ => (g i, g k)) ν =
      (noiseLaw).prod noiseLaw := by
    have hi : iIndepFun (fun a : Fin n => fun g : Fin n → ℝ => g a) ν :=
      iIndepFun_pi (μ := fun _ : Fin n => noiseLaw)
        (X := fun _ (a : ℝ) => a) (fun _ => measurable_id.aemeasurable)
    have hp := (hi.indepFun hik).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply k).aemeasurable
    have hmi : Measure.map (fun g : Fin n → ℝ => g i) ν = noiseLaw :=
      (measurePreserving_eval (fun _ : Fin n => noiseLaw) i).map_eq
    have hmk : Measure.map (fun g : Fin n → ℝ => g k) ν = noiseLaw :=
      (measurePreserving_eval (fun _ : Fin n => noiseLaw) k).map_eq
    rw [hmi, hmk] at hp
    exact hp
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 + s = p.2 + t} :=
    measurableSet_eq_fun (measurable_fst.add_const s) (measurable_snd.add_const t)
  have hz : ((noiseLaw).prod noiseLaw) {p : ℝ × ℝ | p.1 + s = p.2 + t} = 0 := by
    rw [Measure.prod_apply_symm hm]
    have hf : (fun y : ℝ => noiseLaw ((fun a => (a, y)) ⁻¹'
        {p : ℝ × ℝ | p.1 + s = p.2 + t})) = fun _ => 0 := by
      funext y
      have he : ((fun a => (a, y)) ⁻¹'
          {p : ℝ × ℝ | p.1 + s = p.2 + t}) = {y + t - s} := by
        ext a
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor <;> intro h <;> linarith
      rw [he]
      exact Shao.OQ5.P35.noiseLaw_absolutelyContinuous Real.volume_singleton
    rw [hf]
    simp
  rw [← hpair, Measure.map_apply
    ((measurable_pi_apply i).prodMk (measurable_pi_apply k)) hm] at hz
  exact hz

private theorem grouped_equality_null (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    {n : ℕ} (i k : Fin n) (hik : i ≠ k) :
    ((Measure.pi (fun _ : Fin n => noiseLaw)).prod
      ((Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N)).prod
        (Measure.pi (fun _ : Fin n => sparseSignedLabelMeasure α x N))))
      {gc | groupedRow α x N gc i = groupedRow α x N gc k} = 0 := by
  let : IsProbabilityMeasure (sparseSignedLabelMeasure α x N) :=
    sparseSignedLabelMeasure_probability α x N
  have hm : MeasurableSet
      {gc : (Fin n → ℝ) × ((Fin n → SignedLabel) × (Fin n → SignedLabel)) |
        groupedRow α x N gc i = groupedRow α x N gc k} :=
    measurableSet_eq_fun (measurable_groupedRow α x N n i)
      (measurable_groupedRow α x N n k)
  rw [Measure.prod_apply_symm hm]
  have hf : (fun c : (Fin n → SignedLabel) × (Fin n → SignedLabel) =>
      (Measure.pi (fun _ : Fin n => noiseLaw))
        ((fun g => (g, c)) ⁻¹' {gc | groupedRow α x N gc i = groupedRow α x N gc k})) =
      fun _ => 0 := by
    funext c
    change (Measure.pi (fun _ : Fin n => noiseLaw))
      {g | g i + labelRow α x N i c = g k + labelRow α x N k c} = 0
    exact noise_affine_null i k hik _ _
  rw [hf]
  simp

theorem sparseSampleStudentizerSq_zero_null :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n →
  (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
    {ω : Fin n → SparseObs | sparseSampleStudentizerSq α x N ω = 0} = 0 := by
  intro α x N n hn
  let i : Fin n := ⟨0, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  have hik : i ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    simp [i, k] at hval
  let E : Set ((Fin n → ℝ) × ((Fin n → SignedLabel) × (Fin n → SignedLabel))) :=
    {gc | groupedRow α x N gc i = groupedRow α x N gc k}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (measurable_groupedRow α x N n i)
      (measurable_groupedRow α x N n k)
  have hG := regroupSample_preserving α x N n
  have hz : (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
      (regroupSample n ⁻¹' E) = 0 := by
    rw [← Measure.map_apply hG.measurable hE, hG.map_eq]
    exact grouped_equality_null α x N i k hik
  apply measure_mono_null _ hz
  intro ω hω
  change groupedRow α x N (regroupSample n ω) i = groupedRow α x N (regroupSample n ω) k
  rw [← adjustedRow_regroup α x N n ω i, ← adjustedRow_regroup α x N n ω k]
  exact sparseSampleStudentizerSq_eq_zero_imp_adjustedRow_eq α x N n hn ω hω i k

theorem sparseSampleStudentizer_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n →
  ∀ᵐ ω : Fin n → SparseObs ∂Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N),
    0 < sparseSampleStudentizer α x N ω := by
  intro α x N n hn
  have hz : ∀ᵐ ω : Fin n → SparseObs
      ∂Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N),
      sparseSampleStudentizerSq α x N ω ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not] using sparseSampleStudentizerSq_zero_null α x N n hn)
  filter_upwards [hz] with ω hω
  exact Real.sqrt_pos.2
    (lt_of_le_of_ne (sparseSampleStudentizerSq_nonneg α x N n hn ω) (Ne.symm hω))

theorem sparseSampleStudentizer_prefix_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n →
  ∀ᵐ ω : ℕ → SparseObs ∂sparsePopulationSampleMeasure α x N,
    0 < sparseSampleStudentizer α x N (fun i : Fin n => ω i.val) := by
  intro α x N n hn
  have hmp : MeasurePreserving
      (fun ω : ℕ → SparseObs => fun i : Fin n => ω i.val)
      (sparsePopulationSampleMeasure α x N)
      (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)) :=
    ⟨Measurable.of_eval (fun i => measurable_pi_apply i.val),
      sparsePopulationSample_prefix_law α x N n⟩
  exact hmp.quasiMeasurePreserving.ae (sparseSampleStudentizer_pos_ae α x N n hn)

theorem sparseSampleStudentizer_cond_prefix_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ E : Set (ℕ → SparseObs),
  ∀ᵐ ω : ℕ → SparseObs ∂ProbabilityTheory.cond (sparsePopulationSampleMeasure α x N) E,
    0 < sparseSampleStudentizer α x N (fun i : Fin n => ω i.val) := by
  intro α x N n hn E
  exact (ProbabilityTheory.cond_absolutelyContinuous
    (μ := sparsePopulationSampleMeasure α x N) (s := E)).ae_le
      (sparseSampleStudentizer_prefix_pos_ae α x N n hn)

end Shao.OQ5.P53
