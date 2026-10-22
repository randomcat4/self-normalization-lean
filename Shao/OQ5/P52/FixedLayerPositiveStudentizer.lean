import Shao.OQ5.P52.FixedLayerErasedMixture
import Shao.OQ5.P52.FixedLayerSampleStatistics

/-!
# True square-root Studentizer for the original full observation law

The centered denominator is positive almost surely at every fixed n >= 3.
The proof groups the complete category vectors and independent noises, and
uses measurable null sections of one affine noise equality. The residual
and its absolute-convergence mask retain their actual category-only bodies.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))
local notation "Categories" => (ℕ → Fin 3)
local notation "noiseLaw" => Shao.OQ5.P50.layerNoiseLaw
local notation "categoriesLaw" =>
  Shao.OQ5.P50.layerCategoryProductLaw fixedLayerP fixedLayerQ

attribute [local instance] Shao.OQ5.P50.layerNoiseLaw_isProbabilityMeasure
attribute [local instance] fixedObservationLaw_isProbabilityMeasure

private theorem categories_probability : IsProbabilityMeasure categoriesLaw :=
  Shao.OQ5.P50.layerCategoryProductLaw_isProbabilityMeasure fixedLayerP fixedLayerQ
    (fun j => (fixedLayerP_bounds j).1.le)
    (fun j => (fixedLayerQ_bounds j).1.le)
    (fun j => (fixedLayerP_add_Q_lt_one j).le)

attribute [local instance] categories_probability

def fixedSampleStudentizer {n : ℕ} (x : Fin n → LayerObs) : ℝ :=
  Real.sqrt (fixedSampleStudentizerSq x)

theorem fixedSampleStudentizer_nonneg
    {n : ℕ} (x : Fin n → LayerObs) :
    0 ≤ fixedSampleStudentizer x :=
  Real.sqrt_nonneg _

theorem fixedSampleStudentizer_sq
    (n : ℕ) (hn : 3 ≤ n) (x : Fin n → LayerObs) :
    (fixedSampleStudentizer x) ^ 2 = fixedSampleStudentizerSq x :=
  Real.sq_sqrt (fixedSampleStudentizerSq_nonneg n hn x)

private def categoryRow {n : ℕ} (i : Fin n) (c : Fin n → Categories) : ℝ :=
  fixedErasedResidualRow i (fun k => (0, c k))

private def groupedRow {n : ℕ}
    (gc : (Fin n → ℝ) × (Fin n → Categories)) (i : Fin n) : ℝ :=
  gc.1 i + categoryRow i gc.2 / ((n : ℝ) - 2)

private theorem residualRow_categories {n : ℕ} (x : Fin n → LayerObs) (i : Fin n) :
    fixedErasedResidualRow i x = categoryRow i (fun k => (x k).2) := rfl

private theorem measurable_categoryRow (n : ℕ) (i : Fin n) :
    Measurable (categoryRow i) := by
  classical
  unfold categoryRow fixedErasedResidualRow
  apply Finset.measurable_sum
  intro k _
  exact measurable_fixedResidualKernel.comp
    ((measurable_const.prodMk (measurable_pi_apply i)).prodMk
      (measurable_const.prodMk (measurable_pi_apply k)))

private theorem measurable_groupedRow (n : ℕ) (i : Fin n) :
    Measurable (fun gc : (Fin n → ℝ) × (Fin n → Categories) => groupedRow gc i) :=
  ((measurable_pi_apply i).comp measurable_fst).add
    (((measurable_categoryRow n i).comp measurable_snd).div_const _)

private theorem zero_square_imp_row_eq (n : ℕ) (hn : 3 ≤ n)
    (x : Fin n → LayerObs) (hzero : fixedSampleStudentizerSq x = 0) (i k : Fin n) :
    (x i).1 + fixedErasedResidualRow i x / ((n : ℝ) - 2) =
      (x k).1 + fixedErasedResidualRow k x / ((n : ℝ) - 2) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [fixedSampleStudentizerSq_eq_centered_residual_rows n hn x] at hzero
  have hp : (4 / ((n : ℝ) - 1)) ≠ 0 :=
    ne_of_gt (div_pos (by norm_num) (by linarith))
  have hs : (∑ i : Fin n, (Shao.OQ5.P35.center
      (fun k : Fin n => (x k).1 + fixedErasedResidualRow k x / ((n : ℝ) - 2)) i) ^ 2) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hp
  have hall := (Finset.sum_sq_eq_zero_iff Finset.univ
    (Shao.OQ5.P35.center
      (fun k : Fin n => (x k).1 + fixedErasedResidualRow k x / ((n : ℝ) - 2)))).mp hs
  have hi := hall i (Finset.mem_univ i)
  have hk := hall k (Finset.mem_univ k)
  unfold Shao.OQ5.P35.center at hi hk
  linarith

private theorem noise_affine_null {n : ℕ} (i k : Fin n) (hik : i ≠ k) (s t : ℝ) :
    (Measure.pi (fun _ : Fin n => noiseLaw)) {g | g i + s = g k + t} = 0 := by
  let ν := Measure.pi (fun _ : Fin n => noiseLaw)
  have hpair : Measure.map (fun g : Fin n → ℝ => (g i, g k)) ν =
      (noiseLaw).prod noiseLaw := by
    have hi : iIndepFun (fun a : Fin n => fun g : Fin n → ℝ => g a) ν :=
      iIndepFun_pi (μ := fun _ : Fin n => noiseLaw)
        (X := fun _ (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)
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
    have hf : (fun y : ℝ => noiseLaw ((fun x => (x, y)) ⁻¹'
        {p : ℝ × ℝ | p.1 + s = p.2 + t})) = fun _ => 0 := by
      funext y
      have he : ((fun x => (x, y)) ⁻¹'
          {p : ℝ × ℝ | p.1 + s = p.2 + t}) = {y + t - s} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor <;> intro h <;> linarith
      rw [he]
      exact (ProbabilityTheory.cond_absolutelyContinuous
        (μ := (volume : Measure ℝ)) (s := Set.Icc (-1 : ℝ) 1)) Real.volume_singleton
    rw [hf]
    simp
  rw [← hpair, Measure.map_apply
    ((measurable_pi_apply i).prodMk (measurable_pi_apply k)) hm] at hz
  exact hz

private theorem grouped_equality_null {n : ℕ} (i k : Fin n) (hik : i ≠ k) :
    ((Measure.pi (fun _ : Fin n => noiseLaw)).prod
      (Measure.pi (fun _ : Fin n => categoriesLaw)))
      {gc | groupedRow gc i = groupedRow gc k} = 0 := by
  have hm : MeasurableSet
      {gc : (Fin n → ℝ) × (Fin n → Categories) | groupedRow gc i = groupedRow gc k} :=
    measurableSet_eq_fun (measurable_groupedRow n i) (measurable_groupedRow n k)
  rw [Measure.prod_apply_symm hm]
  have hf : (fun c : Fin n → Categories =>
      (Measure.pi (fun _ : Fin n => noiseLaw))
        ((fun g => (g, c)) ⁻¹' {gc | groupedRow gc i = groupedRow gc k})) =
      fun _ => 0 := by
    funext c
    change (Measure.pi (fun _ : Fin n => noiseLaw))
      {g | g i + categoryRow i c / ((n : ℝ) - 2) =
        g k + categoryRow k c / ((n : ℝ) - 2)} = 0
    exact noise_affine_null i k hik _ _
  rw [hf]
  simp

private theorem finite_square_zero_null (n : ℕ) (hn : 3 ≤ n) :
    (Measure.pi (fun _ : Fin n => fixedObservationLaw))
      {x | fixedSampleStudentizerSq x = 0} = 0 := by
  let i : Fin n := ⟨0, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  have hik : i ≠ k := by
    intro h
    have hval := congrArg Fin.val h
    simp [i, k] at hval
  let G := MeasurableEquiv.arrowProdEquivProdArrow ℝ Categories (Fin n)
  have hG : MeasurePreserving G
      (Measure.pi (fun _ : Fin n => fixedObservationLaw))
      ((Measure.pi (fun _ : Fin n => noiseLaw)).prod
        (Measure.pi (fun _ : Fin n => categoriesLaw))) := by
    exact measurePreserving_arrowProdEquivProdArrow ℝ Categories (Fin n)
      (fun _ => noiseLaw) (fun _ => categoriesLaw)
  let E : Set ((Fin n → ℝ) × (Fin n → Categories)) :=
    {gc | groupedRow gc i = groupedRow gc k}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (measurable_groupedRow n i) (measurable_groupedRow n k)
  have hz : (Measure.pi (fun _ : Fin n => fixedObservationLaw)) (G ⁻¹' E) = 0 := by
    rw [← Measure.map_apply hG.measurable hE, hG.map_eq]
    exact grouped_equality_null i k hik
  apply measure_mono_null _ hz
  intro x hx
  change groupedRow (G x) i = groupedRow (G x) k
  exact zero_square_imp_row_eq n hn x hx i k

theorem fixedSampleStudentizer_pos_ae
    (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ x : Fin n → LayerObs
      ∂Measure.pi (fun _ : Fin n => fixedObservationLaw),
      0 < fixedSampleStudentizer x := by
  have hz : ∀ᵐ x : Fin n → LayerObs
      ∂Measure.pi (fun _ : Fin n => fixedObservationLaw), fixedSampleStudentizerSq x ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not] using finite_square_zero_null n hn)
  filter_upwards [hz] with x hx
  exact Real.sqrt_pos.2
    (lt_of_le_of_ne (fixedSampleStudentizerSq_nonneg n hn x) (Ne.symm hx))

theorem fixedSampleStudentizer_prefix_pos_ae
    (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ω : ℕ → LayerObs ∂fixedSampleLaw,
      0 < fixedSampleStudentizer
        (fun i : Fin n => fixedSampleCoordinate i.val ω) := by
  have hmp : MeasurePreserving
      (fun ω : ℕ → LayerObs => fun i : Fin n => fixedSampleCoordinate i.val ω)
      fixedSampleLaw (Measure.pi (fun _ : Fin n => fixedObservationLaw)) :=
    ⟨Measurable.of_eval (fun i => measurable_fixedSampleCoordinate i.val),
      map_fixedSamplePrefix n⟩
  exact hmp.quasiMeasurePreserving.ae (fixedSampleStudentizer_pos_ae n hn)

theorem fixedSampleStudentizer_fixedLayerRareEvent_cond_pos_ae (j : ℕ) :
    ∀ᵐ ω : ℕ → LayerObs
      ∂ProbabilityTheory.cond fixedSampleLaw (fixedLayerRareEvent j),
      0 < fixedSampleStudentizer
        (fun i : Fin (fixedLayerN j) => fixedSampleCoordinate i.val ω) := by
  exact (ProbabilityTheory.cond_absolutelyContinuous
    (μ := fixedSampleLaw) (s := fixedLayerRareEvent j)).ae_le
      (fixedSampleStudentizer_prefix_pos_ae (fixedLayerN j)
        (le_trans (by decide : 3 ≤ 8) (fixedLayerN_ge_eight j)))

end
end Shao.OQ5.P52
