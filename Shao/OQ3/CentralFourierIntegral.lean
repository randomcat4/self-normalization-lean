import Shao.OQ3.NormalTangentPowerLimit
import Shao.OQ3.NormalTangentDomination
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual truncated central Fourier integral

Source: current/oq3/proofs/r1/report.md, lines 309-345, especially 335-343.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U12f scope: 4059b088d8038323e630d4dc8c694b0138fa22cf4caf338e26b0e7bdebaf97b2.
-/

namespace Shao.OQ3

open MeasureTheory Filter

noncomputable section

def centralFourierIntegrand (mu : Measure ℝ) (q a delta s : ℝ)
    (d : ℕ → ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  (Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ))).indicator
    (fun w : ℝ =>
      Complex.exp (((-(w * d n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
        (centeredNormalTangentCharacteristic mu q a
          ((Real.sqrt (n : ℝ))⁻¹ * w) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n) v

theorem centralFourierIntegrand_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a delta s : ℝ) (d : ℕ → ℝ) (n : ℕ) :
    Integrable (centralFourierIntegrand mu q a delta s d n) (volume : Measure ℝ) := by
  have hchar : Continuous (fun w : ℝ => centeredNormalTangentCharacteristic mu q a
      ((Real.sqrt (n : ℝ))⁻¹ * w) ((Real.sqrt (n : ℝ))⁻¹ * s)) :=
    (centeredNormalTangentCharacteristic_continuous mu q a).comp
      (show Continuous (fun w : ℝ =>
        ((Real.sqrt (n : ℝ))⁻¹ * w, (Real.sqrt (n : ℝ))⁻¹ * s)) by fun_prop)
  have hbody : Continuous (fun w : ℝ =>
      Complex.exp (((-(w * d n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
        (centeredNormalTangentCharacteristic mu q a
          ((Real.sqrt (n : ℝ))⁻¹ * w) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n) := by
    apply Continuous.mul
    · fun_prop
    · exact hchar.pow n
  have hi : IntegrableOn (fun w : ℝ =>
      Complex.exp (((-(w * d n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
        (centeredNormalTangentCharacteristic mu q a
          ((Real.sqrt (n : ℝ))⁻¹ * w) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n)
      (Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ)))
      (volume : Measure ℝ) := hbody.integrableOn_Icc
  exact hi.integrable_indicator measurableSet_Icc

theorem centralFourierIntegrand_tendsto (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (delta : ℝ) (hdelta : 0 < delta)
    (s : ℝ) (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) (v : ℝ) :
    Tendsto (fun n : ℕ => centralFourierIntegrand mu q a delta s d n v)
      atTop (nhds (Complex.exp ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ))) := by
  obtain ⟨M, hM⟩ := hd
  have ht : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ht
  have hmajor : ∀ n : ℕ, ‖v * d n / Real.sqrt (n : ℝ)‖ ≤
      (|v| * M) * (Real.sqrt (n : ℝ))⁻¹ := by
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM n) (abs_nonneg v))
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hmajorlim : Tendsto (fun n : ℕ => (|v| * M) * (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) := by simpa only [mul_zero] using hinv.const_mul (|v| * M)
  have hratio : Tendsto (fun n : ℕ => v * d n / Real.sqrt (n : ℝ)) atTop (nhds 0) :=
    squeeze_zero_norm hmajor hmajorlim
  have hpcont : Continuous (fun x : ℝ => Complex.exp (((-x : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have hphase : Tendsto (fun n : ℕ =>
      Complex.exp (((-(v * d n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) * Complex.I))
      atTop (nhds 1) := by
    simpa only [Function.comp_def, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using
      (hpcont.tendsto 0).comp hratio
  have hpower := centeredNormalTangentCharacteristic_power_tendsto mu hb q a hq ha v s
  have hbody : Tendsto (fun n : ℕ =>
      Complex.exp (((-(v * d n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
        (centeredNormalTangentCharacteristic mu q a
          ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n)
      atTop (nhds (Complex.exp ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ))) := by
    simpa only [one_mul] using hphase.mul hpower
  have hlarge : ∀ᶠ n : ℕ in atTop, |v| / delta ≤ Real.sqrt (n : ℝ) :=
    ht.eventually (eventually_ge_atTop _)
  have hwin : ∀ᶠ n : ℕ in atTop,
      v ∈ Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ)) := by
    filter_upwards [hlarge] with n hn
    have hh : |v| ≤ delta * Real.sqrt (n : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hdelta).mp hn
    simpa only [Set.mem_Icc, neg_mul] using abs_le.mp hh
  apply hbody.congr'
  filter_upwards [hwin] with n hn
  simp only [centralFourierIntegrand, Set.indicator_of_mem hn]

theorem exists_centralFourierIntegral_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : ℝ) (d : ℕ → ℝ),
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
        Tendsto (fun n : ℕ =>
          ∫ v : ℝ, centralFourierIntegrand mu q a delta s d n v ∂(volume : Measure ℝ))
          atTop (nhds (((Real.sqrt (2 * Real.pi / normalVariance mu) *
            Real.exp (-(transverseVariance mu * s ^ 2) / 2)) : ℝ) : ℂ)) := by
  obtain ⟨delta, c, hdelta, hc, hlocal⟩ :=
    exists_centeredNormalTangentCharacteristic_scaled_domination mu hb q a hq ha hS hD
  refine ⟨delta, hdelta, ?_⟩
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
        apply abs_le.mpr
        simpa only [Set.mem_Icc, neg_mul] using hv
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

end
end Shao.OQ3
