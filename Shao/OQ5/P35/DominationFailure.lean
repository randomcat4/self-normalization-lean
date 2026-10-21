import Shao.OQ5.P35.ProjectionMoments

/-!
# Positive-probability failure of domination for the fixed p35 kernel

Source: `current/oq56/inputs02/p35.md`, §3 final paragraph. The projection
variance is its actual raw second moment. The witness is a positive Cartesian
category block under the actual product law, rather than the real diagonal.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

open MeasureTheory

noncomputable section

def categorySupportBlock (j : ℕ) : Set ℝ :=
  {x | decodeCategory x = j ∧ decodeNoise x ∈ Set.Icc (-1 : ℝ) 1}

def dominationFailureEvent (c0 : ℝ) : Set (ℝ × ℝ) :=
  {xy | c0 * ((∫ x, populationProjection x ^ 2 ∂realLaw) +
      populationProjection xy.1 ^ 2 + populationProjection xy.2 ^ 2) <
    populationKernel xy.1 xy.2 ^ 2}

theorem measurableSet_categorySupportBlock (j : ℕ) :
    MeasurableSet (categorySupportBlock j) := by
  change MeasurableSet ((decodeCategory ⁻¹' {j}) ∩
    (decodeNoise ⁻¹' Set.Icc (-1 : ℝ) 1))
  exact (measurable_decodeCategory (measurableSet_singleton j)).inter
    (measurable_decodeNoise measurableSet_Icc)

theorem measure_categorySupportBlock (j : ℕ) :
    realLaw (categorySupportBlock j) = ENNReal.ofReal (categoryMass j) := by
  have hnoise : ∀ᵐ x ∂realLaw, decodeNoise x ∈ Set.Icc (-1 : ℝ) 1 := by
    apply ae_of_ae_map measurable_decodeNoise.aemeasurable
    rw [map_noise_realLaw]
    exact noiseLaw_ae_mem
  have hae : categorySupportBlock j =ᵐ[realLaw] {x | decodeCategory x = j} := by
    filter_upwards [hnoise] with x hx
    simp only [categorySupportBlock, Set.mem_ofPred_eq, hx, and_true]
  calc
    realLaw (categorySupportBlock j) = realLaw {x | decodeCategory x = j} :=
      measure_congr hae
    _ = (Measure.map decodeCategory realLaw) {j} := by
      rw [Measure.map_apply measurable_decodeCategory (measurableSet_singleton j)]
      rfl
    _ = ENNReal.ofReal (categoryMass j) := by
      rw [map_category_realLaw, categoryMeasure_singleton]

theorem measure_categorySupportBlock_prod (j : ℕ) :
    (realLaw.prod realLaw) (categorySupportBlock j ×ˢ categorySupportBlock j) =
      ENNReal.ofReal (categoryMass j) ^ 2 := by
  rw [Measure.prod_prod, measure_categorySupportBlock, pow_two]

theorem measurableSet_dominationFailureEvent (c0 : ℝ) :
    MeasurableSet (dominationFailureEvent c0) := by
  have hg : Measurable populationProjection :=
    (measurable_decodeNoise.add measurable_observationOffset).sub_const offsetMean
  have hden : Measurable (fun xy : ℝ × ℝ =>
      c0 * ((∫ x, populationProjection x ^ 2 ∂realLaw) +
        populationProjection xy.1 ^ 2 + populationProjection xy.2 ^ 2)) :=
    ((measurable_const.add ((hg.comp measurable_fst).pow_const 2)).add
      ((hg.comp measurable_snd).pow_const 2)).const_mul c0
  exact measurableSet_lt hden (measurable_populationKernel.pow_const 2)

private theorem feature_sq_lower (m : ℕ) :
    categoryScale (m + 1) ^ 5 / 4 ≤ categoryFeature (m + 1) ^ 2 := by
  have hv := categoryValue_succ_ge m
  have hh : categoryValue (m + 1) / 2 ≤ categoryFeature (m + 1) := by
    unfold categoryFeature featureMean
    linarith
  have hs := pow_le_pow_left₀
    (show 0 ≤ categoryValue (m + 1) / 2 by linarith) hh 2
  calc
    categoryScale (m + 1) ^ 5 / 4 = (categoryValue (m + 1) / 2) ^ 2 := by
      rw [← categoryValue_sq_succ]
      ring
    _ ≤ categoryFeature (m + 1) ^ 2 := hs

private theorem small_terms_le (m : ℕ) :
    2 + 4 * categoryScale (m + 1) ^ 2 ≤ categoryScale (m + 1) ^ 5 / 8 := by
  have hk := categoryScale_succ_ge m
  have hk2 : (16 : ℝ) ≤ categoryScale (m + 1) ^ 2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hk 2
    norm_num at hp
    exact hp
  have hk3 : (64 : ℝ) ≤ categoryScale (m + 1) ^ 3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hk 3
    norm_num at hp
    exact hp
  have hm : 64 * categoryScale (m + 1) ^ 2 ≤ categoryScale (m + 1) ^ 5 := by
    calc
      64 * categoryScale (m + 1) ^ 2 ≤
          categoryScale (m + 1) ^ 3 * categoryScale (m + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hk3 (sq_nonneg _)
      _ = categoryScale (m + 1) ^ 5 := by ring
  nlinarith

private theorem kernel_sq_lower (m : ℕ) {x y : ℝ}
    (hx : x ∈ categorySupportBlock (m + 1))
    (hy : y ∈ categorySupportBlock (m + 1)) :
    categoryScale (m + 1) ^ 10 / 64 ≤ populationKernel x y ^ 2 := by
  rcases hx with ⟨hcx, hax⟩
  rcases hy with ⟨hcy, hay⟩
  have heq : populationKernel x y = decodeNoise x + decodeNoise y +
      2 * categoryOffset (m + 1) - categoryFeature (m + 1) ^ 2 := by
    simp only [populationKernel, observationOffset, observationFeature, hcx, hcy, pow_two]
    ring
  have hneg : populationKernel x y ≤ -categoryScale (m + 1) ^ 5 / 8 := by
    rw [heq]
    have hd := categoryOffset_le (m + 1)
    have ht := feature_sq_lower m
    have hsmall := small_terms_le m
    linarith [hax.2, hay.2]
  have hk0 : 0 ≤ categoryScale (m + 1) := le_trans (by norm_num) (categoryScale_one_le _)
  have hp : 0 ≤ categoryScale (m + 1) ^ 5 / 8 := by positivity
  have hle : categoryScale (m + 1) ^ 5 / 8 ≤ -populationKernel x y := by linarith
  calc
    categoryScale (m + 1) ^ 10 / 64 = (categoryScale (m + 1) ^ 5 / 8) ^ 2 := by ring
    _ ≤ (-populationKernel x y) ^ 2 := pow_le_pow_left₀ hp hle 2
    _ = populationKernel x y ^ 2 := by ring

private theorem projection_sq_upper (j : ℕ) {x : ℝ}
    (hx : x ∈ categorySupportBlock j) :
    populationProjection x ^ 2 ≤
      3 * (1 + 4 * categoryScale j ^ 4 + offsetMean ^ 2) := by
  rcases hx with ⟨hcx, hax⟩
  have ha2 : decodeNoise x ^ 2 ≤ 1 := by
    have hprod := mul_nonneg (show 0 ≤ decodeNoise x + 1 by linarith [hax.1])
      (show 0 ≤ 1 - decodeNoise x by linarith [hax.2])
    nlinarith
  have hd2 : categoryOffset j ^ 2 ≤ 4 * categoryScale j ^ 4 := by
    calc
      categoryOffset j ^ 2 ≤ (2 * categoryScale j ^ 2) ^ 2 :=
        pow_le_pow_left₀ (categoryOffset_nonneg j) (categoryOffset_le j) 2
      _ = 4 * categoryScale j ^ 4 := by ring
  have hg : populationProjection x = decodeNoise x + categoryOffset j - offsetMean := by
    simp only [populationProjection, observationOffset, hcx]
  rw [hg]
  nlinarith [sq_nonneg (decodeNoise x - categoryOffset j),
    sq_nonneg (decodeNoise x + offsetMean), sq_nonneg (categoryOffset j + offsetMean)]

private theorem denominator_upper (j : ℕ) {x y : ℝ}
    (hx : x ∈ categorySupportBlock j) (hy : y ∈ categorySupportBlock j) :
    (∫ z, populationProjection z ^ 2 ∂realLaw) +
        populationProjection x ^ 2 + populationProjection y ^ 2 ≤
      ((∫ z, populationProjection z ^ 2 ∂realLaw) + 30 + 6 * offsetMean ^ 2) *
        categoryScale j ^ 4 := by
  have hxg := projection_sq_upper j hx
  have hyg := projection_sq_upper j hy
  have hk4 : 1 ≤ categoryScale j ^ 4 := one_le_pow₀ (categoryScale_one_le j)
  have hB : 0 ≤ (∫ z, populationProjection z ^ 2 ∂realLaw) + 6 + 6 * offsetMean ^ 2 := by
    have hs := integral_populationProjection_sq_pos
    positivity
  calc
    (∫ z, populationProjection z ^ 2 ∂realLaw) +
        populationProjection x ^ 2 + populationProjection y ^ 2 ≤
      ((∫ z, populationProjection z ^ 2 ∂realLaw) + 6 + 6 * offsetMean ^ 2) +
        24 * categoryScale j ^ 4 := by linarith
    _ ≤ ((∫ z, populationProjection z ^ 2 ∂realLaw) + 6 + 6 * offsetMean ^ 2) *
        categoryScale j ^ 4 + 24 * categoryScale j ^ 4 :=
      by
        have hb := mul_le_mul_of_nonneg_left hk4 hB
        linarith only [hb]
    _ = ((∫ z, populationProjection z ^ 2 ∂realLaw) + 30 + 6 * offsetMean ^ 2) *
        categoryScale j ^ 4 := by ring

theorem exists_categorySupportBlock_violation (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ j : ℕ, 0 < j ∧
      categorySupportBlock j ×ˢ categorySupportBlock j ⊆ dominationFailureEvent c0 := by
  let D : ℝ := (∫ z, populationProjection z ^ 2 ∂realLaw) + 30 + 6 * offsetMean ^ 2
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (64 * c0 * D)
    (by norm_num : (1 : ℝ) < 4 ^ 6)
  have hkg : 64 * c0 * D < categoryScale (m + 1) ^ 6 := by
    have hnext := hm.trans_le
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4 ^ 6) (Nat.le_succ m))
    simpa only [categoryScale, ← pow_mul, Nat.mul_comm] using hnext
  refine ⟨m + 1, by omega, ?_⟩
  intro xy hxy
  rcases hxy with ⟨hx, hy⟩
  change c0 * ((∫ z, populationProjection z ^ 2 ∂realLaw) +
    populationProjection xy.1 ^ 2 + populationProjection xy.2 ^ 2) <
      populationKernel xy.1 xy.2 ^ 2
  have hden := denominator_upper (m + 1) hx hy
  have hsq := kernel_sq_lower m hx hy
  have hkpos : 0 < categoryScale (m + 1) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (categoryScale_one_le _)
  have hstrict : c0 * (D * categoryScale (m + 1) ^ 4) <
      categoryScale (m + 1) ^ 10 / 64 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
    calc
      c0 * (D * categoryScale (m + 1) ^ 4) * 64 =
          (64 * c0 * D) * categoryScale (m + 1) ^ 4 := by ring
      _ < categoryScale (m + 1) ^ 6 * categoryScale (m + 1) ^ 4 :=
        mul_lt_mul_of_pos_right hkg (pow_pos hkpos 4)
      _ = categoryScale (m + 1) ^ 10 := by ring
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hden hc0.le) hstrict) hsq

theorem measure_dominationFailureEvent_pos (c0 : ℝ) (hc0 : 0 < c0) :
    0 < (realLaw.prod realLaw) (dominationFailureEvent c0) := by
  obtain ⟨j, _hj, hsub⟩ := exists_categorySupportBlock_violation c0 hc0
  have hp : 0 < (realLaw.prod realLaw) (categorySupportBlock j ×ˢ categorySupportBlock j) := by
    rw [measure_categorySupportBlock_prod]
    exact pos_iff_ne_zero.mpr
      (pow_ne_zero 2 (ne_of_gt (ENNReal.ofReal_pos.mpr (categoryMass_pos j))))
  exact lt_of_lt_of_le hp (measure_mono hsub)

end
end Shao.OQ5.P35
