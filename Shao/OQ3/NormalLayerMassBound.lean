import Shao.OQ3.NormalLayerConditionalLaw
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
open MeasureTheory Filter
open scoped BigOperators Matrix
noncomputable section

private theorem normal_power_norm_continuous (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖) :=
  (((centeredNormalTangentCharacteristic_continuous mu q a).comp
    (continuous_id.prodMk continuous_const)).pow n).norm

private theorem central_norm_integral_eq_scaled (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a delta : ℝ) (hdelta : 0 < delta) (n : ℕ) (hn : 1 ≤ n) :
    (∫ v : ℝ, ‖centralFourierIntegrand mu q a delta 0 (fun _ => 0) n v‖
      ∂(volume : Measure ℝ)) =
      Real.sqrt (n : ℝ) *
        ∫ t : ℝ in Set.Icc (-delta) delta,
          ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  let f : ℝ → ℝ := fun t => ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖
  have hfc : Continuous f := normal_power_norm_continuous mu q a n
  have _hbase : IntegrableOn f (Set.Icc (-delta) delta) (volume : Measure ℝ) :=
    hfc.integrableOn_Icc
  have _hscaled : IntegrableOn (fun v : ℝ => f (v / Real.sqrt (n : ℝ)))
      (Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ)))
      (volume : Measure ℝ) :=
    (hfc.comp (show Continuous (fun v : ℝ => v / Real.sqrt (n : ℝ)) by fun_prop)).integrableOn_Icc
  have hfun : (fun v : ℝ => ‖centralFourierIntegrand mu q a delta 0 (fun _ => 0) n v‖) =
      (Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ))).indicator
        (fun v : ℝ => f (v / Real.sqrt (n : ℝ))) := by
    funext v
    by_cases hv : v ∈ Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ))
    · simp only [centralFourierIntegrand, Set.indicator_of_mem hv]
      simp [f, div_eq_mul_inv, mul_comm]
    · simp only [centralFourierIntegrand, Set.indicator_of_notMem hv, norm_zero]
  have hab : -delta * Real.sqrt (n : ℝ) ≤ delta * Real.sqrt (n : ℝ) := by
    nlinarith [mul_pos hdelta hr]
  have hleft : (-delta * Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) = -delta :=
    mul_div_cancel_right₀ _ hr.ne'
  have hright : (delta * Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) = delta :=
    mul_div_cancel_right₀ _ hr.ne'
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_comp_div f hr.ne',
    hleft, hright, intervalIntegral.integral_of_le (by linarith : -delta ≤ delta),
    ← integral_Icc_eq_integral_Ioc, smul_eq_mul]

theorem exists_stage_normal_power_norm_integral_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) ≤ C := by
  let H := Real.pi / dyadicMesh J
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hH : 0 < H := div_pos Real.pi_pos hmesh
  obtain ⟨delta0, c, hdelta0, hc, hlocal⟩ :=
    exists_centeredNormalTangentCharacteristic_scaled_domination mu hb q a hq ha hS hD
  let delta := min delta0 (H / 2)
  have hdelta : 0 < delta := lt_min hdelta0 (by positivity)
  have hdeltaH : delta < H := (min_le_right delta0 (H / 2)).trans_lt (by linarith)
  have hdelta0le : delta ≤ delta0 := min_le_left _ _
  let B := Set.Icc (-H) H
  let A := Set.Icc (-delta) delta
  let E := B \ A
  let K := Set.Icc (-H) (-delta) ∪ Set.Icc delta H
  let G : ℝ := ∫ v : ℝ, Real.exp (-c * v ^ 2) ∂(volume : Measure ℝ)
  have hG : 0 ≤ G := integral_nonneg fun _ => (Real.exp_pos _).le
  have hK : IsCompact K := isCompact_Icc.union isCompact_Icc
  have hzero : (0 : ℝ) ∉ K := by
    rintro (hz | hz)
    · have := hz.2; linarith
    · have := hz.1; linarith
  have hband : ∀ t ∈ K, |t| ≤ Real.pi / dyadicMesh J := by
    intro t ht
    apply abs_le.mpr
    rcases ht with ht | ht
    · exact ⟨ht.1, by dsimp [H] at hdeltaH; linarith [ht.2]⟩
    · exact ⟨by dsimp [H] at hdeltaH; linarith [ht.1], ht.2⟩
  have hEK : E ⊆ K := by
    intro t ht
    change t ∈ B ∧ t ∉ Set.Icc (-delta) delta at ht
    by_cases htneg : t ≤ -delta
    · exact Or.inl ⟨ht.1.1, htneg⟩
    · apply Or.inr
      refine ⟨?_, ht.1.2⟩
      by_contra hbad
      exact ht.2 ⟨by linarith, by linarith⟩
  have hsub : A ⊆ B := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hEfinite : (volume : Measure ℝ) E < ⊤ :=
    (measure_mono (show E ⊆ B from Set.sdiff_subset)).trans_lt
      (isCompact_Icc : IsCompact B).measure_lt_top
  obtain ⟨eta, rho, heta, hrho, hrho1, hcontract⟩ :=
    stage_far_arc_uniform mu J q a hrange hpos K hK hzero hband
  have hfull (n : ℕ) : IntegrableOn
      (fun t : ℝ => ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖) B
      (volume : Measure ℝ) := (normal_power_norm_continuous mu q a n).integrableOn_Icc
  have hfar_integrable (n : ℕ) : IntegrableOn
      (fun t : ℝ => ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖) E
      (volume : Measure ℝ) := (hfull n).mono_set Set.sdiff_subset
  have hfar (n : ℕ) : (∫ t : ℝ in E,
      ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) ≤
      volume.real E * rho ^ n := by
    have hh := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
      hEfinite (f := fun t : ℝ => ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖)
      (C := rho ^ n) (fun t ht => by
        rw [norm_norm, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hcontract t (hEK ht) 0 (by simpa using heta)).le n)
    have hnonneg : 0 ≤ ∫ t : ℝ in E,
        ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ) :=
      integral_nonneg fun _ => norm_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, mul_comm] using hh
  have hnrho := tendsto_self_mul_const_pow_of_lt_one hrho.le hrho1
  have hrhopow := tendsto_pow_atTop_nhds_zero_of_lt_one hrho.le hrho1
  have hmajor : Tendsto (fun n : ℕ => volume.real E * ((n : ℝ) * rho ^ n + rho ^ n))
      atTop (nhds 0) := by
    simpa only [zero_add, mul_zero] using (hnrho.add hrhopow).const_mul (volume.real E)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      volume.real E * ((n : ℝ) * rho ^ n + rho ^ n) < 1 :=
    hmajor.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨G + 1, by linarith, ?_⟩
  filter_upwards [hlocal 0, hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hsn hn1
  have hcentral : Real.sqrt (n : ℝ) *
      (∫ t : ℝ in A, ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖
        ∂(volume : Measure ℝ)) ≤ G := by
    rw [← central_norm_integral_eq_scaled mu q a delta hdelta n hn1]
    apply integral_mono (centralFourierIntegrand_integrable mu q a delta 0 (fun _ => 0) n).norm
      (integrable_exp_neg_mul_sq hc)
    intro v
    by_cases hv : v ∈ Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ))
    · simp only [centralFourierIntegrand, Set.indicator_of_mem hv, norm_mul,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      apply hn v
      have habs : |v| ≤ delta * Real.sqrt (n : ℝ) := by
        apply abs_le.mpr
        simpa only [Set.mem_Icc, neg_mul] using hv
      exact habs.trans (mul_le_mul_of_nonneg_right hdelta0le (Real.sqrt_nonneg _))
    · simp only [centralFourierIntegrand, Set.indicator_of_notMem hv, norm_zero]
      exact (Real.exp_pos _).le
  have hfar_scaled : Real.sqrt (n : ℝ) *
      (∫ t : ℝ in E, ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖
        ∂(volume : Measure ℝ)) ≤ 1 := by
    have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (n : ℝ)]⟩
    calc
      _ ≤ Real.sqrt (n : ℝ) * (volume.real E * rho ^ n) :=
        mul_le_mul_of_nonneg_left (hfar n) (Real.sqrt_nonneg _)
      _ ≤ ((n : ℝ) + 1) * (volume.real E * rho ^ n) :=
        mul_le_mul_of_nonneg_right hroot (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hrho.le n))
      _ = volume.real E * ((n : ℝ) * rho ^ n + rho ^ n) := by ring
      _ ≤ 1 := hsn.le
  have hdecomp : (∫ t : ℝ in B,
      ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) =
      (∫ t : ℝ in A, ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖
        ∂(volume : Measure ℝ)) +
      ∫ t : ℝ in E, ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖
        ∂(volume : Measure ℝ) := by
    change _ = _ + ∫ t : ℝ in B \ A,
      ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)
    rw [setIntegral_sdiff measurableSet_Icc (hfull n) hsub]
    ring
  have htotal : Real.sqrt (n : ℝ) * (∫ t : ℝ in B,
      ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) ≤ G + 1 := by
    rw [hdecomp, mul_add]
    exact add_le_add hcentral hfar_scaled
  simpa only [B, H, neg_div] using htotal

private theorem normal_layer_mass_zero_off_grid (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (J : ℕ) (q d : ℝ) (n : ℕ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hoff : ¬ ∃ k : ℤ, d + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    (Measure.pi (fun _ : Fin n => mu)) {z : Shao.Path n | normalDeviation q z = d} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hcoords (i : Fin n) : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => mu),
      z i ∈ Set.range (fun j : Fin 4 ⊕ Fin J =>
        stageAtom (fun k : Fin J => addedAtom k.val) j) :=
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually hrange
  have hall := ae_all_iff.mpr hcoords
  filter_upwards [hall] with z hz
  intro hzd
  have heq : normalDeviation q z = d := hzd
  obtain ⟨k, hk⟩ := stage_sample_normal_layer q n J z hz
  apply hoff
  exact ⟨k, by linarith⟩

theorem exists_stage_normal_layer_mass_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ d : ℝ,
      Real.sqrt (n : ℝ) * (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d} ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_stage_normal_power_norm_integral_bound mu J q a hb hq ha hS hD hrange hpos
  let k : ℝ := dyadicMesh J / (2 * Real.pi)
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hk : 0 < k := div_pos hmesh (mul_pos (by norm_num) Real.pi_pos)
  have hgrid : ∀ᵐ x ∂mu, ∃ m : ℤ, normalValue x = dyadicMesh J * (m : ℝ) := by
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact stageAtom_normalValue_lattice J i
  refine ⟨k * C, mul_pos hk hC, ?_⟩
  filter_upwards [hbound] with n hn
  intro d
  by_cases hlayer : ∃ m : ℤ, d + (n : ℝ) * q = dyadicMesh J * (m : ℝ)
  · have hFourier := normal_layer_Fourier_identity mu q a (dyadicMesh J) d 0 hmesh hgrid n hlayer
    have hmass : 0 ≤ (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d} := ENNReal.toReal_nonneg
    have hbody : Continuous (fun t : ℝ =>
        Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
          centeredNormalTangentCharacteristic mu q a t 0 ^ n) := by
      apply Continuous.mul
      · fun_prop
      · exact ((centeredNormalTangentCharacteristic_continuous mu q a).comp
          (continuous_id.prodMk continuous_const)).pow n
    have _hbody_integrable : IntegrableOn (fun t : ℝ =>
        Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
          centeredNormalTangentCharacteristic mu q a t 0 ^ n)
        (Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J))
        (volume : Measure ℝ) := hbody.integrableOn_Icc
    have hmass_bound : (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d} ≤ k *
        ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ) := by
      calc
        _ = ‖normalLayerCharacteristic mu q a d 0 n‖ := by
          rw [normalLayerCharacteristic_zero_eq_mass, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hmass]
        _ = k * ‖∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
              centeredNormalTangentCharacteristic mu q a t 0 ^ n ∂(volume : Measure ℝ)‖ := by
          rw [hFourier, norm_mul]
          simp only [mul_zero, Complex.norm_real, Real.norm_eq_abs]
          change |k| * _ = k * _
          rw [abs_of_pos hk]
        _ ≤ k * ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            ‖Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
              centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
        _ = _ := by simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc
      _ ≤ Real.sqrt (n : ℝ) * (k *
          ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) :=
        mul_le_mul_of_nonneg_left hmass_bound (Real.sqrt_nonneg _)
      _ = k * (Real.sqrt (n : ℝ) *
          ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            ‖centeredNormalTangentCharacteristic mu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) := by ring
      _ ≤ k * C := mul_le_mul_of_nonneg_left hn hk.le
  · have hz := normal_layer_mass_zero_off_grid mu J q d n hrange hlayer
    simp only [measureReal_def, hz, ENNReal.toReal_zero, mul_zero]
    exact (mul_pos hk hC).le

end
end Shao.OQ3
