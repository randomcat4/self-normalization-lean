import Shao.OQ5.P35.RareEvents
import Shao.Probability.ConditionalIID

/-!
# Actual decoded sample law after fixing category positions

Source: original p35, section4 lines116-130. The left hand conditional
measure is always the normalized restriction of the single fixed sampleLaw.
The joint law retains all category/noise independence after fixing J.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The category and noise decoded from one actual observation coordinate. -/
def sampleDecoded (i : ℕ) (ω : ℕ → ℝ) : ℕ × ℝ :=
  (sampleCategory i ω, decodeNoise (sampleCoordinate i ω))

/-- The prescribed category set at each fixed target or background position. -/
def categoryPatternSet {n : ℕ} (j : ℕ) (J : Finset (Fin n)) (i : Fin n) : Set ℕ :=
  if i ∈ J then {j} else Set.Iio j

/-- The genuine normalized restriction giving the background category law. -/
def backgroundCategoryLaw (j : ℕ) : Measure ℕ :=
  cond categoryMeasure (Set.Iio j)

theorem measurable_sampleDecoded (i : ℕ) : Measurable (sampleDecoded i) :=
  (measurable_sampleCategory i).prodMk
    (measurable_decodeNoise.comp (measurable_sampleCoordinate i))

theorem map_sampleDecoded (i : ℕ) :
    Measure.map (sampleDecoded i) sampleLaw = observationPairLaw := by
  calc
    Measure.map (sampleDecoded i) sampleLaw =
        Measure.map (fun x => (decodeCategory x, decodeNoise x))
          (Measure.map (sampleCoordinate i) sampleLaw) := by
      rw [Measure.map_map (measurable_decodeCategory.prodMk measurable_decodeNoise)
        (measurable_sampleCoordinate i)]
      rfl
    _ = observationPairLaw := by rw [map_sampleCoordinate, map_decode_realLaw]

theorem iIndepFun_sampleDecoded : iIndepFun sampleDecoded sampleLaw := by
  exact iIndepFun_sampleCoordinate.comp
    (fun _ x => (decodeCategory x, decodeNoise x))
    (fun _ => measurable_decodeCategory.prodMk measurable_decodeNoise)

private theorem below_category_ne_zero (j : ℕ) (hj : 1 ≤ j) :
    categoryMeasure (Set.Iio j) ≠ 0 := by
  intro hz
  have hq := (categoryBelowMass_bounds j hj).1
  have hzero : categoryBelowMass j = 0 := by
    simp [categoryBelowMass, measureReal_def, hz]
  linarith

theorem backgroundCategoryLaw_isProbability (j : ℕ) (hj : 1 ≤ j) :
    IsProbabilityMeasure (backgroundCategoryLaw j) :=
  cond_isProbabilityMeasure (below_category_ne_zero j hj)

private theorem pattern_category_ne_zero {n : ℕ} (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) (i : Fin n) :
    categoryMeasure (categoryPatternSet j J i) ≠ 0 := by
  classical
  by_cases hi : i ∈ J
  · simp only [categoryPatternSet, hi, ite_true, categoryMeasure_singleton]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (categoryMass_pos j))
  · simpa [categoryPatternSet, hi] using below_category_ne_zero j hj

theorem categoryPatternLaw_isProbability {n : ℕ} (j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) (i : Fin n) :
    IsProbabilityMeasure (cond categoryMeasure (categoryPatternSet j J i)) :=
  cond_isProbabilityMeasure (pattern_category_ne_zero j hj J i)

theorem fixedCategoryEvent_ne_zero (n j : ℕ) (hj : 1 ≤ j) (J : Finset (Fin n)) :
    sampleLaw (fixedCategoryEvent n j J) ≠ 0 := by
  have hq : 0 < categoryBelowMass j :=
    lt_of_lt_of_le (by norm_num) (categoryBelowMass_bounds j hj).1
  have hp : 0 < sampleLaw.real (fixedCategoryEvent n j J) := by
    rw [fixedCategoryEvent_probability]
    exact mul_pos (pow_pos (categoryMass_pos j) _) (pow_pos hq _)
  intro hz
  simp [measureReal_def, hz] at hp

theorem conditionalPairLaw_factorization (S : Set ℕ) (_hS : MeasurableSet S)
    (_hS0 : categoryMeasure S ≠ 0) :
    cond observationPairLaw (S ×ˢ (Set.univ : Set ℝ)) =
      (cond categoryMeasure S).prod noiseLaw := by
  clear _hS _hS0
  unfold ProbabilityTheory.cond observationPairLaw
  rw [Measure.prod_prod, measure_univ, mul_one,
    ← Measure.restrict_prod_eq_prod_univ, Measure.prod_smul_left]

theorem fixedCategoryEvent_cond_isProbability (n j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) :
    IsProbabilityMeasure (cond sampleLaw (fixedCategoryEvent n j J)) :=
  cond_isProbabilityMeasure (fixedCategoryEvent_ne_zero n j hj J)

private theorem fixedCategoryEvent_eq_decoded_inter (n j : ℕ) (J : Finset (Fin n)) :
    fixedCategoryEvent n j J =
      ⋂ i : Fin n, sampleDecoded i.val ⁻¹'
        (categoryPatternSet j J i ×ˢ (Set.univ : Set ℝ)) := by
  classical
  ext ω
  simp only [fixedCategoryEvent, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ J <;> simp [categoryPatternSet, sampleDecoded, hi]

theorem decoded_cond_fixed_joint_map (n j : ℕ) (hj : 1 ≤ j)
    (J : Finset (Fin n)) :
    Measure.map (fun ω (i : Fin n) => sampleDecoded i.val ω)
        (cond sampleLaw (fixedCategoryEvent n j J)) =
      Measure.pi (fun i : Fin n =>
        (cond categoryMeasure (categoryPatternSet j J i)).prod noiseLaw) := by
  classical
  have hB : ∀ i : Fin n,
      MeasurableSet (categoryPatternSet j J i ×ˢ (Set.univ : Set ℝ)) := by
    intro i
    have hS : MeasurableSet (categoryPatternSet j J i) := by
      by_cases hi : i ∈ J <;> simp [categoryPatternSet, hi]
    exact hS.prod MeasurableSet.univ
  have hA : sampleLaw (⋂ i : Fin n, sampleDecoded i.val ⁻¹'
      (categoryPatternSet j J i ×ˢ (Set.univ : Set ℝ))) ≠ 0 := by
    rw [← fixedCategoryEvent_eq_decoded_inter]
    exact fixedCategoryEvent_ne_zero n j hj J
  rw [fixedCategoryEvent_eq_decoded_inter]
  have h := Shao.Probability.indep_cond_joint_map_eq_pi
    (fun i : Fin n => measurable_sampleDecoded i.val)
    (iIndepFun_sampleDecoded.precomp Fin.val_injective)
    (fun i : Fin n => categoryPatternSet j J i ×ˢ (Set.univ : Set ℝ)) hB hA
  rw [h]
  congr 1
  funext i
  rw [map_sampleDecoded]
  apply conditionalPairLaw_factorization
  · by_cases hi : i ∈ J <;> simp [categoryPatternSet, hi]
  · exact pattern_category_ne_zero j hj J i

end

end Shao.OQ5.P35
