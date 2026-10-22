import Shao.OQ4.EnergyLinearTiltCentering
import Shao.OQ4.KilledPathLaw
import Shao.Probability.FiniteIID
import Mathlib.MeasureTheory.Integral.Pi

/-! The actual energy-tilted finite path identity, including empty paths. -/

namespace Shao.OQ4

open MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem finitePi_withDensity_lintegral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℝ → ENNReal) (hd : Measurable d) [IsProbabilityMeasure (ν.withDensity d)]
    (n : ℕ) (F : Shao.Path n → ENNReal) (hF : Measurable F) :
    (∫⁻ a, F a ∂Measure.pi (fun _ : Fin n => ν.withDensity d)) =
      ∫⁻ a, (∏ i, d (a i)) * F a ∂Measure.pi (fun _ : Fin n => ν) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rw [Measure.pi_of_empty (fun _ : Fin 0 => ν.withDensity d),
      Measure.pi_of_empty (fun _ : Fin 0 => ν)]
  | succ n ih =>
    have hc : Measurable (fun p : ℝ × Shao.Path n =>
        (Fin.cons p.1 p.2 : Shao.Path (n + 1))) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using measurable_fst
      · exact (measurable_pi_apply j).comp measurable_snd
    have hD : Measurable (fun b : Shao.Path n => ∏ i, d (b i)) :=
      Finset.measurable_prod _ (fun i _ => hd.comp (measurable_pi_apply i))
    have hH : Measurable (fun p : ℝ × Shao.Path n =>
        (∏ i, d (p.2 i)) * F (Fin.cons p.1 p.2)) :=
      (hD.comp measurable_snd).mul (hF.comp hc)
    have hG : Measurable (fun x : ℝ => ∫⁻ b : Shao.Path n,
        (∏ i, d (b i)) * F (Fin.cons x b) ∂Measure.pi (fun _ : Fin n => ν)) :=
      hH.lintegral_prod_right
    calc
      _ = ∫⁻ x, ∫⁻ b, F (Fin.cons x b)
          ∂Measure.pi (fun _ : Fin n => ν.withDensity d) ∂ν.withDensity d :=
        path_pi_lintegral_cons (ν.withDensity d) n F hF
      _ = ∫⁻ x, ∫⁻ b : Shao.Path n, (∏ i, d (b i)) * F (Fin.cons x b)
          ∂Measure.pi (fun _ : Fin n => ν) ∂ν.withDensity d := by
        apply lintegral_congr
        intro x
        exact ih _ (hF.comp (hc.comp (measurable_const.prodMk measurable_id)))
      _ = ∫⁻ x, d x * (∫⁻ b : Shao.Path n, (∏ i, d (b i)) * F (Fin.cons x b)
          ∂Measure.pi (fun _ : Fin n => ν)) ∂ν :=
        lintegral_withDensity_eq_lintegral_mul ν hd hG
      _ = ∫⁻ x, ∫⁻ b : Shao.Path n, d x * ((∏ i, d (b i)) * F (Fin.cons x b))
          ∂Measure.pi (fun _ : Fin n => ν) ∂ν := by
        apply lintegral_congr
        intro x
        exact (lintegral_const_mul (d x)
          (hD.mul (hF.comp (hc.comp (measurable_const.prodMk measurable_id))))).symm
      _ = ∫⁻ a, (∏ i, d (a i)) * F a ∂Measure.pi (fun _ : Fin (n + 1) => ν) := by
        have hDp : Measurable (fun a : Shao.Path (n + 1) => ∏ i, d (a i)) :=
          Finset.measurable_prod Finset.univ (fun i _ => hd.comp (measurable_pi_apply i))
        rw [path_pi_lintegral_cons ν n (fun a => (∏ i, d (a i)) * F a) (hDp.mul hF)]
        apply lintegral_congr
        intro x
        apply lintegral_congr
        intro b
        simp [Fin.prod_univ_succ, mul_assoc]

/-- Finite products of the actual density measures have the product density. -/
theorem finitePi_withDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d : ℝ → ENNReal) (hd : Measurable d) [IsProbabilityMeasure (ν.withDensity d)]
    (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν.withDensity d) =
      (Measure.pi (fun _ : Fin n => ν)).withDensity (fun a => ∏ i, d (a i)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hD : Measurable (fun a : Shao.Path n => ∏ i, d (a i)) :=
    Finset.measurable_prod Finset.univ (fun i _ => hd.comp (measurable_pi_apply i))
  calc
    _ = ∫⁻ a, (∏ i, d (a i)) * F a ∂Measure.pi (fun _ : Fin n => ν) :=
      finitePi_withDensity_lintegral ν d hd n F hF
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hD hF).symm

/-- The source's centered energy exponential is cut off only by the actual closed event. -/
noncomputable def energyPathIntegrand {n : ℕ} (h s : ℝ) (a : Shao.Path n) : ℝ :=
  by
    classical
    exact if a ∈ Shao.closedStrip h then
      Real.exp (s * (Shao.energy a - (n : ℝ)) / h ^ 2) else 0

theorem energyPathIntegrand_nonneg {n : ℕ} (h s : ℝ) (a : Shao.Path n) :
    0 ≤ energyPathIntegrand h s a := by
  unfold energyPathIntegrand
  split_ifs <;> positivity

theorem energyPathIntegrand_measurable {n : ℕ} (h s : ℝ) (hh : 0 ≤ h) :
    Measurable (energyPathIntegrand (n := n) h s) := by
  have hA : MeasurableSet (Shao.closedStrip (n := n) h) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n h hh]
    exact measurableSet_shiftedClosedSurvival n h 0
  exact Measurable.ite hA
    (((Shao.measurable_energy.sub_const (n : ℝ)).const_mul s).div_const (h ^ 2)).exp
    measurable_const

private theorem energyPath_energy_le {n : ℕ} (h : ℝ)
    (a : Shao.Path n) (ha : a ∈ Shao.closedStrip h) :
    Shao.energy a ≤ 4 * (n : ℝ) * h ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin n, 4 * h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Shao.abs_coordinate_le_two_mul_of_mem_closedStrip a h ha i
      have hi2 := pow_le_pow_left₀ (abs_nonneg (a i)) hi 2
      nlinarith [sq_abs (a i)]
    _ = _ := by simp; ring

/-- A global finite envelope uses the energy bound only inside the closed event. -/
theorem energyPathIntegrand_le {n : ℕ} (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h)
    (hs : |s| ≤ T) (a : Shao.Path n) :
    energyPathIntegrand h s a ≤
      Real.exp (-s * (n : ℝ) / h ^ 2) * Real.exp (4 * T * (n : ℝ)) := by
  have hh0 : 0 < h := by linarith
  have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh0
  by_cases ha : a ∈ Shao.closedStrip h
  · have hq0 : 0 ≤ Shao.energy a / h ^ 2 := div_nonneg (Shao.energy_nonneg a) hh2.le
    have hq4 : Shao.energy a / h ^ 2 ≤ 4 * (n : ℝ) := by
      apply (div_le_iff₀ hh2).2
      exact energyPath_energy_le h a ha
    have hsT : s ≤ T := (le_abs_self s).trans hs
    have harg : s * Shao.energy a / h ^ 2 ≤ 4 * T * (n : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hsT hq0
      have h2 := mul_le_mul_of_nonneg_left hq4 hT
      calc
        _ = s * (Shao.energy a / h ^ 2) := by ring
        _ ≤ T * (Shao.energy a / h ^ 2) := h1
        _ ≤ T * (4 * (n : ℝ)) := h2
        _ = _ := by ring
    rw [energyPathIntegrand, ite_eq_left ha]
    calc
      _ = Real.exp (-s * (n : ℝ) / h ^ 2) * Real.exp (s * Shao.energy a / h ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _)
  · simp only [energyPathIntegrand, ite_eq_right ha]
    positivity

/-- True integrability needs no untruncated exponential moment. -/
theorem energyPathIntegrand_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T) :
    Integrable (energyPathIntegrand (n := n) h s) (Measure.pi (fun _ : Fin n => ν)) := by
  apply Integrable.of_bound
    (energyPathIntegrand_measurable h s (by linarith)).aestronglyMeasurable
    (Real.exp (-s * (n : ℝ) / h ^ 2) * Real.exp (4 * T * (n : ℝ)))
  exact Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_of_nonneg (energyPathIntegrand_nonneg h s a)]
    exact energyPathIntegrand_le T h s hT hh hs a

/-- The actual finite product of the actual normalized energy laws. -/
theorem energyPathLaw_withDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s) =
      (Measure.pi (fun _ : Fin n => ν)).withDensity
        (fun a => ENNReal.ofReal (∏ i, energyWeight h s (a i) / energyNormalizer ν h s)) := by
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have : IsProbabilityMeasure
      (ν.withDensity (fun x => ENNReal.ofReal (energyWeight h s x / energyNormalizer ν h s))) :=
    energyTiltedLaw_isProbabilityMeasure ν T h s hT hh hs hSq hsecond
  change Measure.pi (fun _ : Fin n => ν.withDensity
    (fun x => ENNReal.ofReal (energyWeight h s x / energyNormalizer ν h s))) = _
  rw [finitePi_withDensity ν _ (energyTiltedLaw_density_measurable ν h s) n]
  congr 1
  funext a
  exact (ENNReal.ofReal_prod_of_nonneg fun i _ =>
    div_nonneg (energyWeight_nonneg h s (a i)) hZ.le).symm

private theorem energyPath_density_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T) :
    Integrable (fun a : Shao.Path n =>
      ∏ i, energyWeight h s (a i) / energyNormalizer ν h s)
      (Measure.pi (fun _ : Fin n => ν)) := by
  have hw := (energyWeight_integrable ν T h s hT (by linarith) hs).div_const
    (energyNormalizer ν h s)
  exact Integrable.fintype_prod (fun _ : Fin n => hw)

/-- Event mass is converted to a real integral only after true integrability is supplied. -/
theorem energyPathLaw_real_apply (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (A : Set (Shao.Path n)) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real A =
      ∫ a in A, (∏ i, energyWeight h s (a i) / energyNormalizer ν h s)
        ∂Measure.pi (fun _ : Fin n => ν) := by
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hi := energyPath_density_integrable ν n T h s hT hh hs
  have hp (a : Shao.Path n) :
      0 ≤ ∏ i, energyWeight h s (a i) / energyNormalizer ν h s :=
    Finset.prod_nonneg (fun i _ => div_nonneg (energyWeight_nonneg h s (a i)) hZ.le)
  rw [energyPathLaw_withDensity ν n T h s hT hh hs hSq hsecond,
    measureReal_def, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hi.restrict (Filter.Eventually.of_forall hp),
    ENNReal.toReal_ofReal (integral_nonneg hp)]

private theorem energyPath_closed_density (ν : Measure ℝ) (n : ℕ) (h s : ℝ)
    (hZ : 0 < energyNormalizer ν h s) (a : Shao.Path n) (ha : a ∈ Shao.closedStrip h) :
    (energyNormalizer ν h s) ^ n *
        (∏ i, energyWeight h s (a i) / energyNormalizer ν h s) =
      Real.exp (s * Shao.energy a / h ^ 2) := by
  have hwprod : (∏ i, energyWeight h s (a i)) = Real.exp (s * Shao.energy a / h ^ 2) := by
    calc
      _ = ∏ i : Fin n, Real.exp (s * (a i) ^ 2 / h ^ 2) := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [energyWeight, Shao.abs_coordinate_le_two_mul_of_mem_closedStrip a h ha i,
          ite_true]
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        change (∑ i : Fin n, s * (a i) ^ 2 / h ^ 2) = s * (∑ i : Fin n, (a i) ^ 2) / h ^ 2
        rw [← Finset.sum_div, ← Finset.mul_sum]
  calc
    _ = ∏ i, energyWeight h s (a i) := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      field_simp
    _ = _ := hwprod

/-- Exact source identity, with true integrability and no division by survival probability. -/
theorem energyPathLaw_integral (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1) :
    Integrable (energyPathIntegrand (n := n) h s) (Measure.pi (fun _ : Fin n => ν)) ∧
      (∫ a, energyPathIntegrand h s a ∂Measure.pi (fun _ : Fin n => ν)) =
        Real.exp (-s * (n : ℝ) / h ^ 2) * (energyNormalizer ν h s) ^ n *
          (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) := by
  classical
  refine ⟨energyPathIntegrand_integrable ν n T h s hT hh hs, ?_⟩
  have hZ := energyTiltedLaw_normalizer_pos ν T h s hT hh hs hSq hsecond
  have hA : MeasurableSet (Shao.closedStrip (n := n) h) := by
    rw [← shiftedClosedSurvival_eq_closedStrip n h (by linarith : 0 ≤ h)]
    exact measurableSet_shiftedClosedSurvival n h 0
  have hp (a : Shao.Path n) : energyPathIntegrand h s a =
      (Real.exp (-s * (n : ℝ) / h ^ 2) * (energyNormalizer ν h s) ^ n) *
        (Shao.closedStrip h).indicator
          (fun b => ∏ i, energyWeight h s (b i) / energyNormalizer ν h s) a := by
    by_cases ha : a ∈ Shao.closedStrip h
    · simp only [energyPathIntegrand, ha, ite_true, Set.indicator_of_mem ha]
      calc
        _ = Real.exp (-s * (n : ℝ) / h ^ 2) * Real.exp (s * Shao.energy a / h ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ = _ := by rw [mul_assoc, energyPath_closed_density ν n h s hZ a ha]
    · simp [energyPathIntegrand, ha]
  calc
    _ = ∫ a, (Real.exp (-s * (n : ℝ) / h ^ 2) * (energyNormalizer ν h s) ^ n) *
        (Shao.closedStrip h).indicator
          (fun b => ∏ i, energyWeight h s (b i) / energyNormalizer ν h s) a
        ∂Measure.pi (fun _ : Fin n => ν) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hp
    _ = _ := by
      rw [integral_const_mul, integral_indicator hA,
        ← energyPathLaw_real_apply ν n T h s hT hh hs hSq hsecond (Shao.closedStrip h) hA]

/-- The genuine finite iid joint law transfers integrability and the exact same energy integral. -/
theorem energyPathLaw_integral_iid {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (T h s : ℝ) (hT : 0 ≤ T) (hh : 1 ≤ h) (hs : |s| ≤ T)
    (hSq : Integrable (fun x : ℝ => x ^ 2) ν) (hsecond : (∫ x : ℝ, x ^ 2 ∂ν) = 1)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X p)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) p ν) :
    Integrable (fun ω => energyPathIntegrand h s (Shao.Probability.samplePath X ω)) p ∧
      (∫ ω, energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂p) =
        Real.exp (-s * (n : ℝ) / h ^ 2) * (energyNormalizer ν h s) ^ n *
          (Measure.pi (fun _ : Fin n => energyTiltedLaw ν h s)).real (Shao.closedStrip h) := by
  have hY := Shao.Probability.measurable_samplePath hX
  have hmap := Shao.Probability.iid_samplePath_map_eq_pi hX hIndep hLaw
  have hF := energyPathIntegrand_measurable (n := n) h s (by linarith : 0 ≤ h)
  obtain ⟨hfi, hidentity⟩ := energyPathLaw_integral ν n T h s hT hh hs hSq hsecond
  constructor
  · have hmi : Integrable (energyPathIntegrand (n := n) h s)
        (Measure.map (Shao.Probability.samplePath X) p) := by
      rwa [hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable hY.aemeasurable).1 hmi
  · calc
      _ = ∫ a, energyPathIntegrand h s a
          ∂Measure.map (Shao.Probability.samplePath X) p :=
        (integral_map hY.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [hmap]; exact hidentity

end Shao.OQ4
