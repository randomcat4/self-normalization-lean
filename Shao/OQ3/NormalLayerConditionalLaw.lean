import Shao.OQ3.FundamentalFourierAsymptotic
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace Shao.OQ3

open MeasureTheory Filter
open scoped BigOperators Matrix

noncomputable section

def normalLayerConditionalLaw (mu : Measure ℝ) (q a d : ℝ) (n : ℕ) : Measure ℝ :=
  if (Measure.pi (fun _ : Fin n => mu)) {z : Shao.Path n | normalDeviation q z = d} = 0 then
    Measure.dirac 0
  else
    Measure.map (fun z : Shao.Path n => ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ))
      (ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => mu))
        {z : Shao.Path n | normalDeviation q z = d})

private theorem normalLayerSet_measurable (q d : ℝ) (n : ℕ) :
    MeasurableSet {z : Shao.Path n | normalDeviation q z = d} := by
  have hM : Continuous (fun z : Shao.Path n => normalDeviation q z) := by
    unfold normalDeviation normalValue
    fun_prop
  exact (isClosed_eq hM continuous_const).measurableSet

private theorem normalLayerStatistic_continuous (a : ℝ) (n : ℕ) :
    Continuous (fun z : Shao.Path n => ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ)) := by
  fun_prop

theorem normalLayerCharacteristic_zero_eq_mass (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a d : ℝ) (n : ℕ) :
    normalLayerCharacteristic mu q a d 0 n =
      ((((Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d}) : ℝ) : ℂ) := by
  have _hint := normalLayerIntegrand_integrable mu q a d 0 n
  unfold normalLayerCharacteristic normalLayerIntegrand
  simp only [zero_mul, zero_div, Complex.ofReal_zero, Complex.exp_zero]
  rw [integral_indicator_const 1 (normalLayerSet_measurable q d n)]
  simp only [Complex.real_smul, mul_one]

theorem normalLayerConditionalLaw_isProbabilityMeasure (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (q a d : ℝ) (n : ℕ) :
    IsProbabilityMeasure (normalLayerConditionalLaw mu q a d n) := by
  have _hT := (normalLayerStatistic_continuous a n).measurable
  unfold normalLayerConditionalLaw
  split_ifs with hzero
  · infer_instance
  · let := ProbabilityTheory.cond_isProbabilityMeasure hzero
    infer_instance

theorem charFun_normalLayerConditionalLaw (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a d : ℝ) (n : ℕ)
    (hpos : (Measure.pi (fun _ : Fin n => mu))
      {z : Shao.Path n | normalDeviation q z = d} ≠ 0) (s : ℝ) :
    charFun (normalLayerConditionalLaw mu q a d n) s =
      normalLayerCharacteristic mu q a d s n / normalLayerCharacteristic mu q a d 0 n := by
  let nu : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let A : Set (Shao.Path n) := {z : Shao.Path n | normalDeviation q z = d}
  let T : Shao.Path n → ℝ := fun z => ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ)
  have hA : MeasurableSet A := normalLayerSet_measurable q d n
  have hT : Measurable T := (normalLayerStatistic_continuous a n).measurable
  have hfinite : nu A ≠ ⊤ := measure_ne_top nu A
  have hmasspos : 0 < (nu A).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨pos_iff_ne_zero.mpr hpos, lt_top_iff_ne_top.mpr hfinite⟩
  have _hden : normalLayerCharacteristic mu q a d 0 n ≠ 0 := by
    rw [normalLayerCharacteristic_zero_eq_mass]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hmasspos)
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := nu) hpos
  have hphase : Integrable (fun z : Shao.Path n => Complex.exp
      (((s * ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I)) nu := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun z => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hrestrict := hphase.integrableOn (s := A)
  have _hcond : Integrable (fun z : Shao.Path n => Complex.exp
      (((s * ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I))
      (ProbabilityTheory.cond nu A) := hrestrict.smul_measure (ENNReal.inv_ne_top.mpr hpos)
  have _hmap : Integrable (fun x : ℝ => Complex.exp (((s * x : ℝ) : ℂ) * Complex.I))
      (Measure.map T (ProbabilityTheory.cond nu A)) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ fun x => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hbranch : normalLayerConditionalLaw mu q a d n =
      Measure.map T (ProbabilityTheory.cond nu A) := by
    simp only [normalLayerConditionalLaw, hpos, ite_false]
    rfl
  rw [hbranch, charFun_apply_real,
    integral_map hT.aemeasurable (by fun_prop)]
  have hfun : (fun z : Shao.Path n => Complex.exp ((s : ℂ) * (T z : ℂ) * Complex.I)) =
      (fun z : Shao.Path n => Complex.exp
        (((s * ((∑ i, z i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    funext z
    dsimp [T]
    congr 1
    push_cast
    ring
  rw [hfun, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    ← integral_indicator hA]
  change (nu A).toReal⁻¹ • normalLayerCharacteristic mu q a d s n = _
  rw [normalLayerCharacteristic_zero_eq_mass, Complex.real_smul, Complex.ofReal_inv]
  simp only [measureReal_def, div_eq_mul_inv]
  ring

theorem eventually_stage_normalLayer_mass_pos (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    ∀ᶠ n : ℕ in atTop, 0 < (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = d n} := by
  let C : ℝ := (dyadicMesh J / (2 * Real.pi)) *
    Real.sqrt (2 * Real.pi / normalVariance mu)
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (div_pos hmesh (by positivity)) (Real.sqrt_pos.2 (div_pos (by positivity) hS))
  have hraw := stage_normalLayerCharacteristic_scaled_tendsto mu J q a hb hq ha hS hD
    hrange hpos 0 d hd hlayer
  have hrawC : Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      normalLayerCharacteristic mu q a (d n) 0 n) atTop (nhds (C : ℂ)) := by
    simpa [C] using hraw
  have hreal : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d n}) atTop (nhds C) := by
    have hre := (Complex.continuous_re.tendsto _).comp hrawC
    simpa only [Function.comp_def, normalLayerCharacteristic_zero_eq_mass,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using hre
  filter_upwards [hreal.eventually (Ioi_mem_nhds hC)] with n hn
  by_contra hmass
  have hprod := mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg (n : ℝ)) (not_lt.mp hmass)
  exact (not_le_of_gt hn) hprod

theorem stage_normalLayerConditionalLaw_charFun_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (s : ℝ) (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    Tendsto (fun n : ℕ => charFun (normalLayerConditionalLaw mu q a (d n) n) s)
      atTop (nhds (Complex.exp ((-(transverseVariance mu * s ^ 2) / 2 : ℝ) : ℂ))) := by
  let C : ℝ := (dyadicMesh J / (2 * Real.pi)) *
    Real.sqrt (2 * Real.pi / normalVariance mu)
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (div_pos hmesh (by positivity)) (Real.sqrt_pos.2 (div_pos (by positivity) hS))
  have hCne : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hs : Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      normalLayerCharacteristic mu q a (d n) s n)
      atTop (nhds (((C * Real.exp (-(transverseVariance mu * s ^ 2) / 2) : ℝ) : ℂ))) := by
    simpa only [C, mul_assoc] using
      stage_normalLayerCharacteristic_scaled_tendsto mu J q a hb hq ha hS hD hrange hpos s d hd hlayer
  have h0 : Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      normalLayerCharacteristic mu q a (d n) 0 n) atTop (nhds (C : ℂ)) := by
    simpa [C] using
      stage_normalLayerCharacteristic_scaled_tendsto mu J q a hb hq ha hS hD hrange hpos 0 d hd hlayer
  have hquot := hs.div h0 hCne
  have hmass := eventually_stage_normalLayer_mass_pos mu J q a hb hq ha hS hD hrange hpos d hd hlayer
  have heq : (fun n : ℕ =>
      (((Real.sqrt (n : ℝ) : ℝ) : ℂ) * normalLayerCharacteristic mu q a (d n) s n) /
        (((Real.sqrt (n : ℝ) : ℝ) : ℂ) * normalLayerCharacteristic mu q a (d n) 0 n)) =ᶠ[atTop]
      (fun n : ℕ => charFun (normalLayerConditionalLaw mu q a (d n) n) s) := by
    filter_upwards [hmass, eventually_ge_atTop (1 : ℕ)] with n hm hn
    have hmass0 : (Measure.pi (fun _ : Fin n => mu))
        {z : Shao.Path n | normalDeviation q z = d n} ≠ 0 :=
      ne_of_gt (ENNReal.toReal_pos_iff.mp hm).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hroot : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hnpos).ne'
    have hden : normalLayerCharacteristic mu q a (d n) 0 n ≠ 0 := by
      rw [normalLayerCharacteristic_zero_eq_mass]
      exact Complex.ofReal_ne_zero.mpr hm.ne'
    rw [charFun_normalLayerConditionalLaw mu q a (d n) n hmass0 s]
    apply (div_eq_div_iff (mul_ne_zero hroot hden) hden).2
    ring
  have hvalue : (((C * Real.exp (-(transverseVariance mu * s ^ 2) / 2) : ℝ) : ℂ)) /
      (C : ℂ) = Complex.exp ((-(transverseVariance mu * s ^ 2) / 2 : ℝ) : ℂ) := by
    apply (div_eq_iff hCne).2
    rw [← Complex.ofReal_exp]
    push_cast
    ring
  simpa only [hvalue] using hquot.congr' heq

end
end Shao.OQ3
