import Shao.OQ5.P35.KernelMoments

/-!
# Moment premises of the actual p35 projection

Source: current/oq56/inputs02/p35.md §3. The independent category/noise joint
law is used only for their mixed moment. The offset and feature are not assumed
independent, and no feature moment beyond the second is used.
-/

set_option autoImplicit false

namespace Shao.OQ5.P35

noncomputable section

open MeasureTheory

private theorem integrable_noise_offset :
    Integrable (fun x => decodeNoise x * observationOffset x) realLaw := by
  have hd : Integrable categoryOffset categoryMeasure := by
    simpa only [pow_one] using integrable_categoryOffset_pow 1 (by norm_num)
  have hprod : Integrable (fun ca : ℕ × ℝ => ca.2 * categoryOffset ca.1)
      observationPairLaw := by
    simpa only [observationPairLaw, mul_comm] using hd.mul_prod integrable_noiseLaw_id
  have hmp : MeasurePreserving (fun x => (decodeCategory x, decodeNoise x))
      realLaw observationPairLaw :=
    ⟨measurable_decodeCategory.prodMk measurable_decodeNoise, map_decode_realLaw⟩
  exact hmp.integrable_comp_of_integrable hprod

private theorem integral_noise_offset :
    (∫ x, decodeNoise x * observationOffset x ∂realLaw) = 0 := by
  have hd : Integrable categoryOffset categoryMeasure := by
    simpa only [pow_one] using integrable_categoryOffset_pow 1 (by norm_num)
  have hprod : Integrable (fun ca : ℕ × ℝ => ca.2 * categoryOffset ca.1)
      observationPairLaw := by
    simpa only [observationPairLaw, mul_comm] using hd.mul_prod integrable_noiseLaw_id
  have hfm : AEStronglyMeasurable (fun ca : ℕ × ℝ => ca.2 * categoryOffset ca.1)
      (Measure.map (fun x => (decodeCategory x, decodeNoise x)) realLaw) := by
    rw [map_decode_realLaw]
    exact hprod.aestronglyMeasurable
  have hmap := integral_map
    (measurable_decodeCategory.prodMk measurable_decodeNoise).aemeasurable hfm
  rw [map_decode_realLaw] at hmap
  calc
    (∫ x, decodeNoise x * observationOffset x ∂realLaw) =
        ∫ ca : ℕ × ℝ, ca.2 * categoryOffset ca.1 ∂observationPairLaw := hmap.symm
    _ = ∫ ca : ℕ × ℝ, categoryOffset ca.1 * ca.2 ∂categoryMeasure.prod noiseLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
    _ = (∫ c, categoryOffset c ∂categoryMeasure) * ∫ a : ℝ, a ∂noiseLaw :=
      integral_prod_mul (μ := categoryMeasure) (ν := noiseLaw) categoryOffset (fun a : ℝ => a)
    _ = 0 := by rw [integral_noiseLaw_id, mul_zero]

private theorem integrable_noise_centeredOffset :
    Integrable (fun x => decodeNoise x * (observationOffset x - offsetMean)) realLaw := by
  have h := integrable_noise_offset.sub (integrable_decodeNoise.mul_const offsetMean)
  apply h.congr
  exact Filter.Eventually.of_forall (fun _ => by simp only [Pi.sub_apply]; ring)

private theorem integral_noise_centeredOffset :
    (∫ x, decodeNoise x * (observationOffset x - offsetMean) ∂realLaw) = 0 := by
  have hfun : (fun x => decodeNoise x * (observationOffset x - offsetMean)) =
      (fun x => decodeNoise x * observationOffset x - decodeNoise x * offsetMean) := by
    funext x
    ring
  rw [hfun, integral_sub integrable_noise_offset (integrable_decodeNoise.mul_const offsetMean),
    integral_noise_offset, integral_mul_const, integral_decodeNoise]
  ring

private theorem integrable_centeredOffset_sq :
    Integrable (fun x => (observationOffset x - offsetMean) ^ 2) realLaw := by
  have hd2 := integrable_observationOffset_pow 2 (by norm_num)
  have h := (hd2.sub (integrable_observationOffset.const_mul (2 * offsetMean))).add
    (integrable_const (offsetMean ^ 2))
  apply h.congr
  exact Filter.Eventually.of_forall (fun _ => by simp only [Pi.sub_apply, Pi.add_apply]; ring)

theorem integrable_populationProjection : Integrable populationProjection realLaw :=
  (integrable_decodeNoise.add integrable_observationOffset).sub (integrable_const offsetMean)

theorem integral_populationProjection : (∫ x, populationProjection x ∂realLaw) = 0 := by
  change (∫ x, decodeNoise x + observationOffset x - offsetMean ∂realLaw) = 0
  have hs : Integrable (fun x => decodeNoise x + observationOffset x) realLaw :=
    integrable_decodeNoise.add integrable_observationOffset
  rw [integral_sub hs (integrable_const offsetMean), integral_add integrable_decodeNoise integrable_observationOffset,
    integral_decodeNoise, integral_const, probReal_univ, one_smul]
  simp only [offsetMean, zero_add, sub_self]

private theorem projection_sq_expand :
    (fun x => populationProjection x ^ 2) =
      (fun x => decodeNoise x ^ 2 +
        2 * (decodeNoise x * (observationOffset x - offsetMean)) +
        (observationOffset x - offsetMean) ^ 2) := by
  funext x
  unfold populationProjection
  ring

theorem integrable_populationProjection_sq :
    Integrable (fun x => populationProjection x ^ 2) realLaw := by
  rw [projection_sq_expand]
  exact (integrable_decodeNoise_sq.add
    (integrable_noise_centeredOffset.const_mul 2)).add integrable_centeredOffset_sq

private theorem nonneg_add_cube_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

private theorem nonneg_add_three_cube_le (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 3 ≤ 16 * (a ^ 3 + b ^ 3 + c ^ 3) := by
  have h1 := nonneg_add_cube_le a b ha hb
  have h2 := nonneg_add_cube_le (a + b) c (add_nonneg ha hb) hc
  nlinarith [pow_nonneg hc 3]

theorem integrable_populationProjection_abs_cube :
    Integrable (fun x => |populationProjection x| ^ 3) realLaw := by
  have hd3 : Integrable (fun x => |observationOffset x| ^ 3) realLaw := by
    simpa only [observationOffset, abs_of_nonneg (categoryOffset_nonneg _)] using
      integrable_observationOffset_pow 3 (by norm_num)
  have hdom := ((integrable_decodeNoise_abs_pow 3 (by norm_num)).add hd3).add
    (integrable_const (|offsetMean| ^ 3))
  apply (hdom.const_mul 16).mono'
  · have hg : Measurable populationProjection :=
      (measurable_decodeNoise.add measurable_observationOffset).sub_const offsetMean
    exact ((continuous_abs.measurable.comp hg).pow_const 3).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
    simp only [Pi.add_apply]
    have habs : |populationProjection x| ≤
        |decodeNoise x| + |observationOffset x| + |offsetMean| := by
      unfold populationProjection
      calc
        |decodeNoise x + observationOffset x - offsetMean| ≤
            |decodeNoise x + observationOffset x| + |-offsetMean| := by
          simpa only [Real.norm_eq_abs, sub_eq_add_neg] using
            norm_add_le (decodeNoise x + observationOffset x) (-offsetMean)
        _ ≤ |decodeNoise x| + |observationOffset x| + |offsetMean| := by
          rw [abs_neg]
          have hadd : |decodeNoise x + observationOffset x| ≤
              |decodeNoise x| + |observationOffset x| := by
            simpa only [Real.norm_eq_abs] using
              norm_add_le (decodeNoise x) (observationOffset x)
          linarith
    exact (pow_le_pow_left₀ (abs_nonneg _) habs 3).trans
      (nonneg_add_three_cube_le _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _))

theorem integral_populationProjection_sq_ge :
    (1 / 3 : ℝ) ≤ ∫ x, populationProjection x ^ 2 ∂realLaw := by
  have hs : Integrable (fun x => decodeNoise x ^ 2 +
      2 * (decodeNoise x * (observationOffset x - offsetMean))) realLaw :=
    integrable_decodeNoise_sq.add (integrable_noise_centeredOffset.const_mul 2)
  rw [projection_sq_expand, integral_add hs integrable_centeredOffset_sq,
    integral_add integrable_decodeNoise_sq (integrable_noise_centeredOffset.const_mul 2),
    integral_const_mul, integral_decodeNoise_sq, integral_noise_centeredOffset]
  have hnonneg : 0 ≤ ∫ x, (observationOffset x - offsetMean) ^ 2 ∂realLaw :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

theorem integral_populationProjection_sq_pos :
    0 < ∫ x, populationProjection x ^ 2 ∂realLaw :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3) integral_populationProjection_sq_ge

end

end Shao.OQ5.P35
