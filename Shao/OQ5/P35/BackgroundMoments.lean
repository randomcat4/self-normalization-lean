import Shao.OQ5.P35.ConditionalSample
import Shao.OQ5.P35.KernelMoments
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual background-category moments for p35 formula (10)

Every integral uses the normalized restriction of the fixed category law.
The truncated feature retains its nonzero negative mean.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem background_mass_pos (j : ℕ) (hj : 1 ≤ j) :
    0 < categoryBelowMass j :=
  lt_of_lt_of_le (by norm_num) (categoryBelowMass_bounds j hj).1

private theorem background_mass_ne_zero (j : ℕ) (hj : 1 ≤ j) :
    categoryMeasure (Set.Iio j) ≠ 0 := by
  intro hz
  have h := background_mass_pos j hj
  simp [categoryBelowMass, measureReal_def, hz] at h

private theorem integrable_background (f : ℕ → ℝ)
    (hf : Integrable f categoryMeasure) (j : ℕ) (hj : 1 ≤ j) :
    Integrable f (backgroundCategoryLaw j) := by
  unfold backgroundCategoryLaw ProbabilityTheory.cond
  exact hf.integrableOn.smul_measure
    (ENNReal.inv_ne_top.mpr (background_mass_ne_zero j hj))

theorem integrable_backgroundCategoryFeature (j : ℕ) (hj : 1 ≤ j) :
    Integrable categoryFeature (backgroundCategoryLaw j) :=
  integrable_background _ integrable_categoryFeature j hj

theorem integrable_backgroundCategoryFeature_sq (j : ℕ) (hj : 1 ≤ j) :
    Integrable (fun c => categoryFeature c ^ 2) (backgroundCategoryLaw j) :=
  integrable_background _ integrable_categoryFeature_sq j hj

private theorem integrable_offset : Integrable categoryOffset categoryMeasure := by
  simpa only [pow_one] using integrable_categoryOffset_pow 1 (by norm_num)

theorem integrable_backgroundCategoryOffset (j : ℕ) (hj : 1 ≤ j) :
    Integrable categoryOffset (backgroundCategoryLaw j) :=
  integrable_background _ integrable_offset j hj

theorem integrable_backgroundCategoryOffset_sq (j : ℕ) (hj : 1 ≤ j) :
    Integrable (fun c => categoryOffset c ^ 2) (backgroundCategoryLaw j) :=
  integrable_background _ (integrable_categoryOffset_pow 2 (by norm_num)) j hj

private theorem background_integral_mul (f : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) :
    categoryBelowMass j * (∫ c, f c ∂backgroundCategoryLaw j) =
      ∫ c in Set.Iio j, f c ∂categoryMeasure := by
  rw [backgroundCategoryLaw, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    smul_eq_mul]
  change categoryBelowMass j * ((categoryBelowMass j)⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (background_mass_pos j hj).ne', one_mul]

private theorem category_below_integral_sum (f : ℕ → ℝ)
    (hf : Integrable f categoryMeasure) (j : ℕ) :
    (∫ c in Set.Iio j, f c ∂categoryMeasure) =
      ∑ c ∈ Finset.range j, categoryMass c * f c := by
  have hset : (Set.Iio j : Set ℕ) = (Finset.range j : Set ℕ) := by
    ext c
    simp
  rw [hset, setIntegral_finset _ hf.integrableOn]
  simp only [categoryMeasure_real_singleton, smul_eq_mul]

private theorem category_weight_summable (f : ℕ → ℝ)
    (hf : Integrable f categoryMeasure) (h0 : ∀ c, 0 ≤ f c) :
    Summable (fun c => categoryMass c * f c) := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 _)] using
    (integrable_categoryMeasure_iff f).mp hf

private theorem category_tail_integral_tsum (f : ℕ → ℝ)
    (hf : Integrable f categoryMeasure) (h0 : ∀ c, 0 ≤ f c) (j : ℕ) :
    (∫ c in Set.Ici j, f c ∂categoryMeasure) =
      ∑' c : ℕ, categoryMass (c + j) * f (c + j) := by
  have hs := category_weight_summable f hf h0
  have hsum := hs.sum_add_tsum_nat_add j
  rw [← integral_categoryMeasure f hf] at hsum
  have hsplit := integral_add_compl (s := Set.Iio j) measurableSet_Iio hf
  rw [Set.compl_Iio, category_below_integral_sum f hf j] at hsplit
  linarith

private theorem category_value_nonneg (c : ℕ) : 0 ≤ categoryValue c := by
  unfold categoryValue
  split_ifs <;> positivity

private theorem category_value_tail (j : ℕ) (hj : 1 ≤ j) :
    (∫ c in Set.Ici j, categoryValue c ∂categoryMeasure) =
      (512 / 511 : ℝ) * (1 / 512 : ℝ) ^ j := by
  rw [category_tail_integral_tsum _ integrable_categoryValue category_value_nonneg]
  have hterm (c : ℕ) :
      categoryMass (c + j) * categoryValue (c + j) = (1 / 512 : ℝ) ^ (c + j) := by
    have hc : c + j ≠ 0 := by omega
    simp only [categoryMass, categoryValue, hc, ite_false, ← mul_pow]
    norm_num
  simp_rw [hterm]
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 512)
    (by norm_num : (1 / 512 : ℝ) < 1)).mul_right ((1 / 512 : ℝ) ^ j)
  have ht := h.tsum_eq
  simp only [← pow_add] at ht
  norm_num at ht
  exact ht

private theorem category_mass_tail (j : ℕ) (hj : 1 ≤ j) :
    categoryMeasure.real (Set.Ici j) =
      (16384 / 16383 : ℝ) * (1 / 16384 : ℝ) ^ j := by
  have h := measureReal_add_measureReal_compl (μ := categoryMeasure)
    (s := Set.Iio j) measurableSet_Iio
  rw [Set.compl_Iio] at h
  change categoryBelowMass j + _ = _ at h
  rw [categoryBelowMass_eq j hj] at h
  simp only [probReal_univ] at h
  linarith

theorem backgroundCategoryFeature_mean_exact (j : ℕ) (hj : 1 ≤ j) :
    categoryBelowMass j * (∫ c, categoryFeature c ∂backgroundCategoryLaw j) =
      -(512 / 511 : ℝ) * (1 / 512 : ℝ) ^ j +
        (16384 / (511 * 16383) : ℝ) * (1 / 16384 : ℝ) ^ j := by
  rw [background_integral_mul _ j hj]
  have hsplit := integral_add_compl (s := Set.Iio j) measurableSet_Iio
    integrable_categoryFeature
  rw [Set.compl_Iio, integral_categoryFeature] at hsplit
  have htail :
      (∫ c in Set.Ici j, categoryFeature c ∂categoryMeasure) =
        (512 / 511 : ℝ) * (1 / 512 : ℝ) ^ j -
          (16384 / (511 * 16383) : ℝ) * (1 / 16384 : ℝ) ^ j := by
    change (∫ c in Set.Ici j, categoryValue c - featureMean ∂categoryMeasure) = _
    rw [integral_sub integrable_categoryValue.integrableOn
      (integrable_const featureMean), category_value_tail j hj,
      setIntegral_const, category_mass_tail j hj]
    simp only [smul_eq_mul, featureMean]
    ring
  linarith

theorem backgroundCategoryFeature_mean_neg (j : ℕ) (hj : 1 ≤ j) :
    (∫ c, categoryFeature c ∂backgroundCategoryLaw j) < 0 := by
  have hpow : (1 / 16384 : ℝ) ^ j ≤ (1 / 512 : ℝ) ^ j :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hpos : 0 < (1 / 512 : ℝ) ^ j := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpow
    (by norm_num : (0 : ℝ) ≤ 16384 / (511 * 16383))
  have hid := backgroundCategoryFeature_mean_exact j hj
  have hneg : categoryBelowMass j *
      (∫ c, categoryFeature c ∂backgroundCategoryLaw j) < 0 := by
    nlinarith
  by_contra hn
  have hm : 0 ≤ ∫ c, categoryFeature c ∂backgroundCategoryLaw j := le_of_not_gt hn
  exact (not_lt_of_ge (mul_nonneg (background_mass_pos j hj).le hm)) hneg

private theorem offsetMean_category :
    offsetMean = ∫ c, categoryOffset c ∂categoryMeasure := by
  simpa only [offsetMean, pow_one] using integral_observationOffset_pow 1 (by norm_num)

private theorem offsetMean_nonneg : 0 ≤ offsetMean := by
  rw [offsetMean_category]
  exact integral_nonneg categoryOffset_nonneg

private theorem category_mass_offset_le (c : ℕ) (hc : 1 ≤ c) :
    categoryMass c * categoryOffset c ≤ 2 * (1 / 1024 : ℝ) ^ c := by
  have hm : categoryMass c * categoryScale c ^ 2 = (1 / 1024 : ℝ) ^ c := by
    simp only [categoryMass, show c ≠ 0 by omega, ite_false, categoryScale]
    rw [← pow_mul, Nat.mul_comm c 2, pow_mul, ← mul_pow]
    norm_num
  calc
    _ ≤ categoryMass c * (2 * categoryScale c ^ 2) :=
      mul_le_mul_of_nonneg_left (categoryOffset_le c) (categoryMass_nonneg c)
    _ = 2 * (categoryMass c * categoryScale c ^ 2) := by ring
    _ = _ := by rw [hm]

private theorem category_offset_tail_le (j : ℕ) (hj : 1 ≤ j) :
    (∫ c in Set.Ici j, categoryOffset c ∂categoryMeasure) ≤
      4 * (1 / 1024 : ℝ) ^ j := by
  rw [category_tail_integral_tsum _ integrable_offset categoryOffset_nonneg]
  have hs := category_weight_summable categoryOffset integrable_offset categoryOffset_nonneg
  have hshift : Summable (fun c : ℕ => categoryMass (c + j) * categoryOffset (c + j)) :=
    (summable_nat_add_iff j).mpr hs
  have hgeom := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 1024)
    (by norm_num : (1 / 1024 : ℝ) < 1)).mul_right (2 * (1 / 1024 : ℝ) ^ j)
  have hgeom' : HasSum (fun c : ℕ => 2 * (1 / 1024 : ℝ) ^ (c + j))
      ((2048 / 1023 : ℝ) * (1 / 1024 : ℝ) ^ j) := by
    convert hgeom using 1
    · funext c
      rw [pow_add]
      ring
    · norm_num
      ring
  calc
    _ ≤ ∑' c : ℕ, 2 * (1 / 1024 : ℝ) ^ (c + j) :=
      hshift.tsum_le_tsum (fun c => category_mass_offset_le (c + j) (by omega))
        hgeom'.summable
    _ = (2048 / 1023 : ℝ) * (1 / 1024 : ℝ) ^ j := hgeom'.tsum_eq
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

private theorem background_missing_mass_le (j : ℕ) (hj : 1 ≤ j) :
    1 - categoryBelowMass j ≤ 2 * (1 / 1024 : ℝ) ^ j := by
  have hp : (1 / 16384 : ℝ) ^ j ≤ (1 / 1024 : ℝ) ^ j :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) j
  rw [categoryBelowMass_eq j hj]
  calc
    _ = (16384 / 16383 : ℝ) * (1 / 16384 : ℝ) ^ j := by ring
    _ ≤ (16384 / 16383 : ℝ) * (1 / 1024 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

private theorem background_offset_bias_le (j : ℕ) (hj : 1 ≤ j) :
    |(∫ c, categoryOffset c ∂backgroundCategoryLaw j) - offsetMean| ≤
      (4 * offsetMean + 8) * (1 / 1024 : ℝ) ^ j := by
  have hq := (categoryBelowMass_bounds j hj)
  have hqhalf : (1 / 2 : ℝ) ≤ categoryBelowMass j := by linarith [hq.1]
  have ht0 : 0 ≤ ∫ c in Set.Ici j, categoryOffset c ∂categoryMeasure :=
    integral_nonneg categoryOffset_nonneg
  have hsplit := integral_add_compl (s := Set.Iio j) measurableSet_Iio integrable_offset
  rw [Set.compl_Iio, ← offsetMean_category, ← background_integral_mul _ j hj] at hsplit
  have hid : categoryBelowMass j *
      ((∫ c, categoryOffset c ∂backgroundCategoryLaw j) - offsetMean) =
      offsetMean * (1 - categoryBelowMass j) -
        (∫ c in Set.Ici j, categoryOffset c ∂categoryMeasure) := by
    nlinarith
  have ha : categoryBelowMass j *
      |(∫ c, categoryOffset c ∂backgroundCategoryLaw j) - offsetMean| ≤
      offsetMean * (1 - categoryBelowMass j) +
        (∫ c in Set.Ici j, categoryOffset c ∂categoryMeasure) := by
    calc
      _ = |categoryBelowMass j *
          ((∫ c, categoryOffset c ∂backgroundCategoryLaw j) - offsetMean)| := by
        rw [abs_mul, abs_of_nonneg (background_mass_pos j hj).le]
      _ = _ := congrArg abs hid
      _ ≤ _ := by
        simpa only [abs_of_nonneg (mul_nonneg offsetMean_nonneg (sub_nonneg.mpr hq.2.le)),
          abs_of_nonneg ht0] using
          abs_sub (offsetMean * (1 - categoryBelowMass j))
            (∫ c in Set.Ici j, categoryOffset c ∂categoryMeasure)
  have hb := mul_le_mul_of_nonneg_left (background_missing_mass_le j hj) offsetMean_nonneg
  have ht := category_offset_tail_le j hj
  have hm := mul_nonneg (sub_nonneg.mpr hqhalf)
    (abs_nonneg ((∫ c, categoryOffset c ∂backgroundCategoryLaw j) - offsetMean))
  nlinarith

theorem backgroundCategoryMoments_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (∫ c, categoryFeature c ^ 2 ∂backgroundCategoryLaw j) ≤ C ∧
      (∫ c, categoryOffset c ^ 2 ∂backgroundCategoryLaw j) ≤ C ∧
      |∫ c, categoryFeature c ∂backgroundCategoryLaw j| ≤ C * (1 / 512 : ℝ) ^ j ∧
      |(∫ c, categoryOffset c ∂backgroundCategoryLaw j) - offsetMean| ≤
        C * (1 / 1024 : ℝ) ^ j := by
  let D2 : ℝ := ∫ c, categoryOffset c ^ 2 ∂categoryMeasure
  have hD2 : 0 ≤ D2 := integral_nonneg (fun c => sq_nonneg _)
  let C : ℝ := 2 * featureVariance + 2 * D2 + 4 * offsetMean + 16
  have hC1 : 2 * featureVariance ≤ C := by dsimp [C]; linarith [offsetMean_nonneg]
  have hC2 : 2 * D2 ≤ C := by dsimp [C]; linarith [offsetMean_nonneg, featureVariance_pos]
  have hC4 : 4 ≤ C := by dsimp [C]; linarith [offsetMean_nonneg, featureVariance_pos]
  have hCB : 4 * offsetMean + 8 ≤ C := by dsimp [C]; linarith [featureVariance_pos]
  refine ⟨C, by linarith, ?_⟩
  intro j hj
  have hqhalf : (1 / 2 : ℝ) ≤ categoryBelowMass j := by
    linarith [(categoryBelowMass_bounds j hj).1]
  have hF0 : 0 ≤ ∫ c, categoryFeature c ^ 2 ∂backgroundCategoryLaw j :=
    integral_nonneg (fun c => sq_nonneg _)
  have hD0 : 0 ≤ ∫ c, categoryOffset c ^ 2 ∂backgroundCategoryLaw j :=
    integral_nonneg (fun c => sq_nonneg _)
  have hF := setIntegral_le_integral (s := Set.Iio j) integrable_categoryFeature_sq
    (ae_of_all _ (fun c => sq_nonneg (categoryFeature c)))
  rw [integral_categoryFeature_sq, ← background_integral_mul _ j hj] at hF
  have hD := setIntegral_le_integral (s := Set.Iio j)
    (integrable_categoryOffset_pow 2 (by norm_num))
    (ae_of_all _ (fun c => sq_nonneg (categoryOffset c)))
  rw [← background_integral_mul _ j hj] at hD
  change categoryBelowMass j * _ ≤ D2 at hD
  have hFM : (∫ c, categoryFeature c ^ 2 ∂backgroundCategoryLaw j) ≤ 2 * featureVariance := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqhalf) hF0]
  have hDM : (∫ c, categoryOffset c ^ 2 ∂backgroundCategoryLaw j) ≤ 2 * D2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqhalf) hD0]
  refine ⟨hFM.trans hC1, hDM.trans hC2, ?_, ?_⟩
  · have hid := backgroundCategoryFeature_mean_exact j hj
    have hn := backgroundCategoryFeature_mean_neg j hj
    have hp : 0 ≤ (1 / 16384 : ℝ) ^ j := by positivity
    have hpa : 0 ≤ (1 / 512 : ℝ) ^ j := by positivity
    have hm := mul_nonneg (sub_nonneg.mpr hqhalf)
      (abs_nonneg (∫ c, categoryFeature c ∂backgroundCategoryLaw j))
    have hmean : |∫ c, categoryFeature c ∂backgroundCategoryLaw j| ≤
        4 * (1 / 512 : ℝ) ^ j := by
      rw [abs_of_neg hn] at hm ⊢
      nlinarith
    exact hmean.trans (mul_le_mul_of_nonneg_right hC4 hpa)
  · exact (background_offset_bias_le j hj).trans
      (mul_le_mul_of_nonneg_right hCB (by positivity))

end

end Shao.OQ5.P35
