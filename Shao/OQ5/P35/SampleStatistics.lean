import Shao.OQ5.P35.RareEvents
import Shao.OQ5.P35.KernelMoments
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Actual sample statistics and positivity of the p35 Studentizer

The statistics use the one fixed infinite sample law and every centered row
coordinate of the original jackknife normalization.  Positivity is proved for
each fixed n ≥ 3 by grouping all decoded categories and independent noises,
then excluding an affine equality of two continuous noise coordinates.
Source: original p35 §§1–2 and §7, formula (18).
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def finiteSample (n : ℕ) (ω : ℕ → ℝ) (i : Fin n) : ℝ :=
  sampleCoordinate i.val ω

def sampleMatrix (n : ℕ) (ω : ℕ → ℝ) (i j : Fin n) : ℝ :=
  populationKernel (finiteSample n ω i) (finiteSample n ω j)

def sampleU (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (pairCount n)⁻¹ * unorderedPairSum (sampleMatrix n ω)

def sampleRowMean (n : ℕ) (ω : ℕ → ℝ) (i : Fin n) : ℝ :=
  ((n : ℝ) - 1)⁻¹ * ∑ j ∈ Finset.univ.erase i, sampleMatrix n ω i j

def jackknifeSq (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (4 * ((n : ℝ) - 1) / ((n : ℝ) - 2) ^ 2) *
    ∑ i : Fin n, (sampleRowMean n ω i - sampleU n ω) ^ 2

def sampleStudentizer (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  Real.sqrt (jackknifeSq n ω)

def sampleStatistic (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  if 0 < sampleStudentizer n ω then
    Real.sqrt (n : ℝ) * (sampleU n ω - populationMean) / sampleStudentizer n ω
  else 0

theorem measurable_finiteSample (n : ℕ) : Measurable (finiteSample n) :=
  Measurable.of_eval (fun i => measurable_sampleCoordinate i.val)

theorem measurable_sampleMatrix (n : ℕ) (i j : Fin n) :
    Measurable (fun ω => sampleMatrix n ω i j) :=
  measurable_populationKernel.comp
    ((measurable_sampleCoordinate i.val).prodMk (measurable_sampleCoordinate j.val))

theorem measurable_sampleU (n : ℕ) : Measurable (sampleU n) := by
  classical
  unfold sampleU unorderedPairSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases h : i < j
  · simpa only [h, ite_true] using measurable_sampleMatrix n i j
  · simp only [h, ite_false]
    exact measurable_const

theorem measurable_sampleRowMean (n : ℕ) (i : Fin n) :
    Measurable (fun ω => sampleRowMean n ω i) := by
  classical
  unfold sampleRowMean
  exact (Finset.measurable_sum _ (fun j _ => measurable_sampleMatrix n i j)).const_mul _

theorem measurable_jackknifeSq (n : ℕ) : Measurable (jackknifeSq n) := by
  unfold jackknifeSq
  exact (Finset.measurable_sum _ (fun i _ =>
    ((measurable_sampleRowMean n i).sub (measurable_sampleU n)).pow_const 2)).const_mul _

theorem measurable_sampleStudentizer (n : ℕ) : Measurable (sampleStudentizer n) :=
  (measurable_jackknifeSq n).sqrt

theorem measurable_sampleStatistic (n : ℕ) : Measurable (sampleStatistic n) := by
  unfold sampleStatistic
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_sampleStudentizer n))
    ((((measurable_sampleU n).sub measurable_const).const_mul _).div
      (measurable_sampleStudentizer n)) measurable_const

theorem sampleU_eq_uStatistic (n : ℕ) (ω : ℕ → ℝ) :
    sampleU n ω = uStatistic (fun i : Fin n => decodeNoise (finiteSample n ω i))
      (fun i => observationOffset (finiteSample n ω i))
      (fun i => observationFeature (finiteSample n ω i)) := rfl

theorem sampleRowMean_eq_rowMean (n : ℕ) (ω : ℕ → ℝ) (i : Fin n) :
    sampleRowMean n ω i = rowMean (fun i : Fin n => decodeNoise (finiteSample n ω i))
      (fun i => observationOffset (finiteSample n ω i))
      (fun i => observationFeature (finiteSample n ω i)) i := rfl

theorem jackknifeSq_eq_studentizerSq (n : ℕ) (ω : ℕ → ℝ) :
    jackknifeSq n ω = studentizerSq (fun i : Fin n => decodeNoise (finiteSample n ω i))
      (fun i => observationOffset (finiteSample n ω i))
      (fun i => observationFeature (finiteSample n ω i)) := rfl

theorem jackknifeSq_nonneg (n : ℕ) (hn : 3 ≤ n) (ω : ℕ → ℝ) :
    0 ≤ jackknifeSq n ω := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold jackknifeSq
  exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (by linarith))
    (sq_nonneg _)) (Finset.sum_nonneg (fun i _ => sq_nonneg _))

private theorem map_finiteSample (n : ℕ) :
    Measure.map (finiteSample n) sampleLaw = Measure.pi (fun _ : Fin n => realLaw) := by
  have hi : iIndepFun (fun i : Fin n => sampleCoordinate i.val) sampleLaw :=
    iIndepFun.precomp Fin.val_injective iIndepFun_sampleCoordinate
  change Measure.map (fun ω (i : Fin n) => sampleCoordinate i.val ω) sampleLaw = _
  rw [hi.map_fun_eq_pi_map (fun i : Fin n => (measurable_sampleCoordinate i.val).aemeasurable)]
  simp only [map_sampleCoordinate]

theorem map_sampleGroupedDecoded (n : ℕ) :
    Measure.map
      (fun ω => ((fun i : Fin n => sampleCategory i.val ω),
        (fun i : Fin n => decodeNoise (sampleCoordinate i.val ω)))) sampleLaw =
      (Measure.pi (fun _ : Fin n => categoryMeasure)).prod
        (Measure.pi (fun _ : Fin n => noiseLaw)) := by
  let D : (Fin n → ℝ) → Fin n → ℕ × ℝ :=
    fun x i => (decodeCategory (x i), decodeNoise (x i))
  have hD : Measurable D := Measurable.of_eval (fun i =>
    (measurable_decodeCategory.comp (measurable_pi_apply i)).prodMk
      (measurable_decodeNoise.comp (measurable_pi_apply i)))
  have hpi : Measure.map D (Measure.pi (fun _ : Fin n => realLaw)) =
      Measure.pi (fun _ : Fin n => observationPairLaw) := by
    have : IsProbabilityMeasure
        (Measure.map (fun x => (decodeCategory x, decodeNoise x)) realLaw) := by
      rw [map_decode_realLaw]
      infer_instance
    simpa only [D, map_decode_realLaw] using
      (Measure.pi_map_pi (μ := fun _ : Fin n => realLaw)
        (f := fun _ x => (decodeCategory x, decodeNoise x))
        (fun _ => (measurable_decodeCategory.prodMk measurable_decodeNoise).aemeasurable))
  have hG := measurePreserving_arrowProdEquivProdArrow ℕ ℝ (Fin n)
    (fun _ => categoryMeasure) (fun _ => noiseLaw)
  calc
    _ = Measure.map (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℝ (Fin n))
        (Measure.map D (Measure.map (finiteSample n) sampleLaw)) := by
      rw [Measure.map_map hD (measurable_finiteSample n),
        Measure.map_map hG.measurable (hD.comp (measurable_finiteSample n))]
      rfl
    _ = _ := by rw [map_finiteSample, hpi]; exact hG.map_eq

theorem studentizerSq_eq_zero_imp_adjustedRow_eq {n : ℕ}
    (A d Z : Fin n → ℝ) (hn : 3 ≤ n)
    (hzero : studentizerSq A d Z = 0) (i j : Fin n) :
    adjustedRow A d Z i = adjustedRow A d Z j := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [studentizerSq_eq_centeredRow A d Z hn] at hzero
  have hp : (4 / ((n : ℝ) - 1)) ≠ 0 := ne_of_gt (div_pos (by norm_num) (by linarith))
  have hs : (∑ i, center (adjustedRow A d Z) i ^ 2) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hp
  have hall := (Finset.sum_sq_eq_zero_iff Finset.univ (center (adjustedRow A d Z))).mp hs
  have hi := hall i (Finset.mem_univ i)
  have hj := hall j (Finset.mem_univ j)
  unfold center at hi hj
  linarith

private theorem noise_affine_null {n : ℕ} (i j : Fin n) (hij : i ≠ j) (s t : ℝ) :
    (Measure.pi (fun _ : Fin n => noiseLaw)) {a | a i + s = a j + t} = 0 := by
  let ν := Measure.pi (fun _ : Fin n => noiseLaw)
  have hpair : Measure.map (fun a : Fin n → ℝ => (a i, a j)) ν =
      noiseLaw.prod noiseLaw := by
    have hi : iIndepFun (fun k : Fin n => fun a : Fin n → ℝ => a k) ν :=
      iIndepFun_pi (μ := fun _ : Fin n => noiseLaw)
        (X := fun _ (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)
    have hp := (hi.indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    have hmi : Measure.map (fun a : Fin n → ℝ => a i) ν = noiseLaw :=
      (measurePreserving_eval (fun _ : Fin n => noiseLaw) i).map_eq
    have hmj : Measure.map (fun a : Fin n → ℝ => a j) ν = noiseLaw :=
      (measurePreserving_eval (fun _ : Fin n => noiseLaw) j).map_eq
    rw [hmi, hmj] at hp
    exact hp
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 + s = p.2 + t} :=
    measurableSet_eq_fun (measurable_fst.add_const s) (measurable_snd.add_const t)
  have hz : (noiseLaw.prod noiseLaw) {p : ℝ × ℝ | p.1 + s = p.2 + t} = 0 := by
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
      exact noiseLaw_absolutelyContinuous (Real.volume_singleton)
    rw [hf]
    simp
  rw [← hpair, Measure.map_apply
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) hm] at hz
  exact hz

private theorem measurable_groupedAdjustedRow (n : ℕ) (i : Fin n) :
    Measurable (fun ca : (Fin n → ℕ) × (Fin n → ℝ) =>
      adjustedRow ca.2 (fun k => categoryOffset (ca.1 k))
        (fun k => categoryFeature (ca.1 k)) i) := by
  have hd (k : Fin n) : Measurable (fun ca : (Fin n → ℕ) × (Fin n → ℝ) =>
      categoryOffset (ca.1 k)) :=
    (measurable_of_countable categoryOffset).comp ((measurable_pi_apply k).comp measurable_fst)
  have hZ (k : Fin n) : Measurable (fun ca : (Fin n → ℕ) × (Fin n → ℝ) =>
      categoryFeature (ca.1 k)) :=
    (measurable_of_countable categoryFeature).comp ((measurable_pi_apply k).comp measurable_fst)
  unfold adjustedRow
  exact (((measurable_pi_apply i).comp measurable_snd).add (hd i)).sub
    (((hZ i).mul ((Finset.measurable_sum _ (fun k _ => hZ k)).sub (hZ i))).div_const _)

private theorem groupedAdjustedRow_equality_null {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ((Measure.pi (fun _ : Fin n => categoryMeasure)).prod
      (Measure.pi (fun _ : Fin n => noiseLaw)))
      {ca | adjustedRow ca.2 (fun k => categoryOffset (ca.1 k))
          (fun k => categoryFeature (ca.1 k)) i =
        adjustedRow ca.2 (fun k => categoryOffset (ca.1 k))
          (fun k => categoryFeature (ca.1 k)) j} = 0 := by
  apply Measure.measure_prod_null_of_ae_null
    (measurableSet_eq_fun (measurable_groupedAdjustedRow n i)
      (measurable_groupedAdjustedRow n j))
  apply Filter.Eventually.of_forall
  intro c
  let d : Fin n → ℝ := fun k => categoryOffset (c k)
  let Z : Fin n → ℝ := fun k => categoryFeature (c k)
  have he : (Prod.mk c ⁻¹' {ca : (Fin n → ℕ) × (Fin n → ℝ) |
      adjustedRow ca.2 (fun k => categoryOffset (ca.1 k))
        (fun k => categoryFeature (ca.1 k)) i =
      adjustedRow ca.2 (fun k => categoryOffset (ca.1 k))
        (fun k => categoryFeature (ca.1 k)) j}) =
      {a | a i + (d i - Z i * ((∑ k, Z k) - Z i) / ((n : ℝ) - 2)) =
        a j + (d j - Z j * ((∑ k, Z k) - Z j) / ((n : ℝ) - 2))} := by
    ext a
    change (a i + d i - Z i * ((∑ k, Z k) - Z i) / ((n : ℝ) - 2) =
      a j + d j - Z j * ((∑ k, Z k) - Z j) / ((n : ℝ) - 2)) ↔
      (a i + (d i - Z i * ((∑ k, Z k) - Z i) / ((n : ℝ) - 2)) =
      a j + (d j - Z j * ((∑ k, Z k) - Z j) / ((n : ℝ) - 2)))
    constructor <;> intro h <;> linarith
  change (Measure.pi (fun _ : Fin n => noiseLaw)) _ = 0
  rw [he]
  exact noise_affine_null i j hij _ _

theorem measure_jackknifeSq_zero (n : ℕ) (hn : 3 ≤ n) :
    sampleLaw {ω | jackknifeSq n ω = 0} = 0 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
  let G : (ℕ → ℝ) → (Fin n → ℕ) × (Fin n → ℝ) :=
    fun ω => ((fun k => sampleCategory k.val ω),
      (fun k => decodeNoise (sampleCoordinate k.val ω)))
  have hG : Measurable G :=
    (Measurable.of_eval (fun k : Fin n => measurable_sampleCategory k.val)).prodMk
      (Measurable.of_eval (fun k : Fin n =>
        measurable_decodeNoise.comp (measurable_sampleCoordinate k.val)))
  let E : Set ((Fin n → ℕ) × (Fin n → ℝ)) :=
    {ca | adjustedRow ca.2 (fun k => categoryOffset (ca.1 k))
        (fun k => categoryFeature (ca.1 k)) i =
      adjustedRow ca.2 (fun k => categoryOffset (ca.1 k))
        (fun k => categoryFeature (ca.1 k)) j}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (measurable_groupedAdjustedRow n i) (measurable_groupedAdjustedRow n j)
  have hz : sampleLaw (G ⁻¹' E) = 0 := by
    rw [← Measure.map_apply hG hE, map_sampleGroupedDecoded]
    exact groupedAdjustedRow_equality_null i j hij
  apply measure_mono_null _ hz
  intro ω hω
  have hs := studentizerSq_eq_zero_imp_adjustedRow_eq
    (fun k : Fin n => decodeNoise (finiteSample n ω k))
    (fun k => observationOffset (finiteSample n ω k))
    (fun k => observationFeature (finiteSample n ω k)) hn
    ((jackknifeSq_eq_studentizerSq n ω).symm.trans hω) i j
  exact hs

theorem ae_jackknifeSq_pos (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ω ∂sampleLaw, 0 < jackknifeSq n ω := by
  have hz : ∀ᵐ ω ∂sampleLaw, jackknifeSq n ω ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not] using measure_jackknifeSq_zero n hn)
  filter_upwards [hz] with ω hω
  exact lt_of_le_of_ne (jackknifeSq_nonneg n hn ω) (Ne.symm hω)

theorem ae_sampleStudentizer_pos (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ω ∂sampleLaw, 0 < sampleStudentizer n ω := by
  filter_upwards [ae_jackknifeSq_pos n hn] with ω hω
  exact Real.sqrt_pos.2 hω

theorem measure_sampleStudentizer_pos (n : ℕ) (hn : 3 ≤ n) :
    sampleLaw {ω | 0 < sampleStudentizer n ω} = 1 := by
  exact (mem_ae_iff_prob_eq_one
    (measurableSet_lt measurable_const (measurable_sampleStudentizer n))).mp
      (ae_sampleStudentizer_pos n hn)

end

end Shao.OQ5.P35
