import Shao.OQ3.CentralFourierIntegral
import Shao.OQ3.NormalLayerFourier
import Mathlib.Analysis.SpecificLimits.Normed

namespace Shao.OQ3

open MeasureTheory Filter
open scoped BigOperators Matrix

noncomputable section

private def fundamentalBody (mu : Measure ℝ) (q a s : ℝ) (d : ℕ → ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((-(t * d n) : ℝ) : ℂ) * Complex.I) *
    centeredNormalTangentCharacteristic mu q a t ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n

private theorem fundamentalBody_continuous (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a s : ℝ) (d : ℕ → ℝ) (n : ℕ) :
    Continuous (fundamentalBody mu q a s d n) := by
  have hchar := (centeredNormalTangentCharacteristic_continuous mu q a).comp
    (show Continuous (fun t : ℝ => (t, (Real.sqrt (n : ℝ))⁻¹ * s)) by fun_prop)
  unfold fundamentalBody
  apply Continuous.mul
  · fun_prop
  · exact hchar.pow n

private theorem centralFourierIntegral_eq_scaled (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a delta s : ℝ) (hdelta : 0 < delta) (d : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ v : ℝ, centralFourierIntegrand mu q a delta s d n v ∂(volume : Measure ℝ)) =
      ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        ∫ t : ℝ in Set.Icc (-delta) delta,
          fundamentalBody mu q a s d n t ∂(volume : Measure ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have _hbase : IntegrableOn (fundamentalBody mu q a s d n)
      (Set.Icc (-delta) delta) (volume : Measure ℝ) :=
    (fundamentalBody_continuous mu q a s d n).integrableOn_Icc
  have _hscaled : IntegrableOn (fun v : ℝ =>
      fundamentalBody mu q a s d n (v / Real.sqrt (n : ℝ)))
      (Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ)))
      (volume : Measure ℝ) :=
    ((fundamentalBody_continuous mu q a s d n).comp
      (show Continuous (fun v : ℝ => v / Real.sqrt (n : ℝ)) by fun_prop)).integrableOn_Icc
  have hfun : (fun v : ℝ =>
      Complex.exp (((-(v * d n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
        centeredNormalTangentCharacteristic mu q a ((Real.sqrt (n : ℝ))⁻¹ * v)
          ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n) =
      (fun v : ℝ => fundamentalBody mu q a s d n (v / Real.sqrt (n : ℝ))) := by
    funext v
    dsimp [fundamentalBody]
    apply congrArg₂ (· * ·)
    · congr 1
      push_cast
      ring
    · congr 2
      ring
  have hab : -delta * Real.sqrt (n : ℝ) ≤ delta * Real.sqrt (n : ℝ) := by
    nlinarith [mul_pos hdelta hr]
  have hleft : (-delta * Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) = -delta :=
    mul_div_cancel_right₀ _ hr.ne'
  have hright : (delta * Real.sqrt (n : ℝ)) / Real.sqrt (n : ℝ) = delta :=
    mul_div_cancel_right₀ _ hr.ne'
  unfold centralFourierIntegrand
  rw [integral_indicator measurableSet_Icc, hfun, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_div (fundamentalBody mu q a s d n) hr.ne',
    hleft, hright, intervalIntegral.integral_of_le (by linarith : -delta ≤ delta),
    ← integral_Icc_eq_integral_Ioc, Complex.real_smul]

theorem exists_centralFourierIntegral_tendsto_below (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) (H : ℝ) (hH : 0 < H) :
    ∃ delta : ℝ, 0 < delta ∧ delta < H ∧ ∀ (s : ℝ) (d : ℕ → ℝ),
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
        Tendsto (fun n : ℕ =>
          ∫ v : ℝ, centralFourierIntegrand mu q a delta s d n v ∂(volume : Measure ℝ))
          atTop (nhds (((Real.sqrt (2 * Real.pi / normalVariance mu) *
            Real.exp (-(transverseVariance mu * s ^ 2) / 2)) : ℝ) : ℂ)) := by
  obtain ⟨delta0, c, hdelta0, hc, hlocal⟩ :=
    exists_centeredNormalTangentCharacteristic_scaled_domination mu hb q a hq ha hS hD
  let delta := min delta0 (H / 2)
  have hdelta : 0 < delta := lt_min hdelta0 (by positivity)
  have hsmall : delta < H := (min_le_right delta0 (H / 2)).trans_lt (by linarith)
  have hle : delta ≤ delta0 := min_le_left _ _
  refine ⟨delta, hdelta, hsmall, ?_⟩
  intro s d hd
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (centralFourierIntegrand mu q a delta s d n) (volume : Measure ℝ) :=
    Eventually.of_forall fun n =>
      (centralFourierIntegrand_integrable mu q a delta s d n).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ v : ℝ ∂(volume : Measure ℝ),
      ‖centralFourierIntegrand mu q a delta s d n v‖ ≤ Real.exp (-c * v ^ 2) := by
    filter_upwards [hlocal s] with n hn
    exact ae_of_all _ fun v => by
      by_cases hv : v ∈ Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ))
      · simp only [centralFourierIntegrand, Set.indicator_of_mem hv, norm_mul,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        apply hn v
        have habs : |v| ≤ delta * Real.sqrt (n : ℝ) := by
          apply abs_le.mpr
          simpa only [Set.mem_Icc, neg_mul] using hv
        exact habs.trans (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _))
      · simp only [centralFourierIntegrand, Set.indicator_of_notMem hv, norm_zero]
        exact (Real.exp_pos _).le
  have hlim : ∀ᵐ v : ℝ ∂(volume : Measure ℝ),
      Tendsto (fun n : ℕ => centralFourierIntegrand mu q a delta s d n v)
        atTop (nhds (Complex.exp ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ))) :=
    ae_of_all _ fun v => centralFourierIntegrand_tendsto mu hb q a hq ha delta hdelta s d hd v
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun v : ℝ => Real.exp (-c * v ^ 2)) hmeas hbound (integrable_exp_neg_mul_sq hc) hlim
  have hvalue : (∫ v : ℝ, Complex.exp ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ)
      ∂(volume : Measure ℝ)) =
      (((Real.sqrt (2 * Real.pi / normalVariance mu) *
        Real.exp (-(transverseVariance mu * s ^ 2) / 2)) : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_exp]
    rw [integral_complex_ofReal, integral_normalTangentGaussian mu hb hS s]
  simpa only [hvalue] using hconv

theorem stage_fundamentalFourierIntegral_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (s : ℝ) (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) :
    Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
        Complex.exp (((-(t * d n) : ℝ) : ℂ) * Complex.I) *
          centeredNormalTangentCharacteristic mu q a t
            ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n ∂(volume : Measure ℝ)))
      atTop (nhds (((Real.sqrt (2 * Real.pi / normalVariance mu) *
        Real.exp (-(transverseVariance mu * s ^ 2) / 2)) : ℝ) : ℂ)) := by
  let H := Real.pi / dyadicMesh J
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hH : 0 < H := div_pos Real.pi_pos hmesh
  obtain ⟨delta, hdelta, hdeltaH, hcentral⟩ :=
    exists_centralFourierIntegral_tendsto_below mu hb q a hq ha hS hD H hH
  let B := Set.Icc (-H) H
  let E := B \ Set.Icc (-delta) delta
  let K := Set.Icc (-H) (-delta) ∪ Set.Icc delta H
  have hK : IsCompact K := isCompact_Icc.union isCompact_Icc
  have hzero : (0 : ℝ) ∉ K := by
    rintro (hz | hz)
    · have := hz.2
      linarith
    · have := hz.1
      linarith
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
      apply ht.2
      exact ⟨by linarith, by linarith⟩
  have hsub : Set.Icc (-delta) delta ⊆ B := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfull (n : ℕ) : IntegrableOn (fundamentalBody mu q a s d n) B
      (volume : Measure ℝ) :=
    (fundamentalBody_continuous mu q a s d n).integrableOn_Icc
  have _hfar_integrable (n : ℕ) : IntegrableOn (fundamentalBody mu q a s d n) E
      (volume : Measure ℝ) := (hfull n).mono_set Set.sdiff_subset
  have hEfinite : (volume : Measure ℝ) E < ⊤ :=
    (measure_mono (show E ⊆ B from Set.sdiff_subset)).trans_lt
      (isCompact_Icc : IsCompact B).measure_lt_top
  obtain ⟨eta, rho, heta, hrho, hrho1, hcontract⟩ :=
    stage_far_arc_uniform mu J q a hrange hpos K hK hzero hband
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hfreq : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ * s) atTop (nhds 0) := by
    simpa only [Function.comp_def, zero_mul] using (tendsto_inv_atTop_zero.comp hsqrt).mul_const s
  have hfreqabs : Tendsto (fun n : ℕ => |(Real.sqrt (n : ℝ))⁻¹ * s|) atTop (nhds 0) := by
    simpa only [abs_zero] using hfreq.abs
  have hsmall : ∀ᶠ n : ℕ in atTop, |(Real.sqrt (n : ℝ))⁻¹ * s| < eta :=
    hfreqabs.eventually (Iio_mem_nhds heta)
  have hnorm : ∀ᶠ n : ℕ in atTop,
      ‖∫ t : ℝ in E, fundamentalBody mu q a s d n t ∂(volume : Measure ℝ)‖ ≤
        volume.real E * rho ^ n := by
    filter_upwards [hsmall] with n hn
    have hbound (t : ℝ) (ht : t ∈ E) : ‖fundamentalBody mu q a s d n t‖ ≤ rho ^ n := by
      dsimp [fundamentalBody]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcontract t (hEK ht) _ hn).le n
    simpa only [mul_comm] using
      (norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) hEfinite hbound)
  have hnrho := tendsto_self_mul_const_pow_of_lt_one hrho.le hrho1
  have hrhopow := tendsto_pow_atTop_nhds_zero_of_lt_one hrho.le hrho1
  have hmajor : Tendsto (fun n : ℕ => volume.real E * ((n : ℝ) * rho ^ n + rho ^ n))
      atTop (nhds 0) := by
    simpa only [zero_add, mul_zero] using (hnrho.add hrhopow).const_mul (volume.real E)
  have hfar : Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      ∫ t : ℝ in E, fundamentalBody mu q a s d n t ∂(volume : Measure ℝ))
      atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [hnorm] with n hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (n : ℝ)]⟩
    calc
      ‖((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
          ∫ t : ℝ in E, fundamentalBody mu q a s d n t ∂(volume : Measure ℝ)‖ =
          Real.sqrt (n : ℝ) *
            ‖∫ t : ℝ in E, fundamentalBody mu q a s d n t ∂(volume : Measure ℝ)‖ := by
        rw [← Complex.real_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (n : ℝ) * (volume.real E * rho ^ n) :=
        mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
      _ ≤ ((n : ℝ) + 1) * (volume.real E * rho ^ n) :=
        mul_le_mul_of_nonneg_right hroot (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hrho.le n))
      _ = volume.real E * ((n : ℝ) * rho ^ n + rho ^ n) := by ring
  have hsum := (hcentral s d hd).add hfar
  have heq : (fun n : ℕ =>
      (∫ v : ℝ, centralFourierIntegrand mu q a delta s d n v ∂(volume : Measure ℝ)) +
        ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
          ∫ t : ℝ in E, fundamentalBody mu q a s d n t ∂(volume : Measure ℝ)) =ᶠ[atTop]
      (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        ∫ t : ℝ in B, fundamentalBody mu q a s d n t ∂(volume : Measure ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [centralFourierIntegral_eq_scaled mu q a delta s hdelta d n hn]
    change _ + ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      ∫ t : ℝ in B \ Set.Icc (-delta) delta, fundamentalBody mu q a s d n t = _
    rw [setIntegral_sdiff measurableSet_Icc (hfull n) hsub]
    ring
  have hlim := hsum.congr' heq
  simpa only [add_zero, fundamentalBody, B, H, neg_div] using hlim

theorem stage_normalLayerCharacteristic_scaled_tendsto (mu : Measure ℝ)
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
    Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      normalLayerCharacteristic mu q a (d n) s n)
      atTop (nhds ((((dyadicMesh J / (2 * Real.pi)) *
        (Real.sqrt (2 * Real.pi / normalVariance mu) *
          Real.exp (-(transverseVariance mu * s ^ 2) / 2))) : ℝ) : ℂ)) := by
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hgrid : ∀ᵐ x ∂mu, ∃ k : ℤ, normalValue x = dyadicMesh J * (k : ℝ) := by
    filter_upwards [hrange] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact stageAtom_normalValue_lattice J i
  have hconv := (stage_fundamentalFourierIntegral_tendsto mu J q a hb hq ha hS hD
    hrange hpos s d hd).const_mul (((dyadicMesh J / (2 * Real.pi) : ℝ) : ℂ))
  have heq : (fun n : ℕ => (((dyadicMesh J / (2 * Real.pi) : ℝ) : ℂ)) *
      (((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          Complex.exp (((-(t * d n) : ℝ) : ℂ) * Complex.I) *
            centeredNormalTangentCharacteristic mu q a t
              ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n ∂(volume : Measure ℝ)))) =ᶠ[atTop]
      (fun n : ℕ => ((Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        normalLayerCharacteristic mu q a (d n) s n) := by
    filter_upwards [hlayer] with n hn
    rw [normal_layer_Fourier_identity mu q a (dyadicMesh J) (d n) s hmesh hgrid n hn]
    ring
  simpa only [Complex.ofReal_mul] using hconv.congr' heq

end
end Shao.OQ3
