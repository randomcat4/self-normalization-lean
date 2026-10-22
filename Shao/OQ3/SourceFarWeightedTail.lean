import Shao.OQ3.FarEnergyExponentialCover
import Shao.OQ3.CenteredSampleTilt
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

private theorem sample_projection_linear (q a v s : ℝ) (n : ℕ) (z : Shao.Path n) :
    centeredSampleProjection q a v s n z =
      v * normalDeviation q z + s * ((∑ i, z i) - (n : ℝ) * a) := by
  simp only [centeredSampleProjection, centeredNormalProjection,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    normalDeviation]

private theorem sample_energy_mgf (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q t : ℝ) (n : ℕ) :
    Integrable (fun z : Shao.Path n => Real.exp (t * (Shao.energy z - (n : ℝ) * q)))
      (Measure.pi (fun _ : Fin n => mu)) ∧
      (∫ z : Shao.Path n, Real.exp (t * (Shao.energy z - (n : ℝ) * q))
        ∂Measure.pi (fun _ : Fin n => mu)) =
        (∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu) ^ n := by
  have hsingle : (fun x : ℝ => Real.exp (centeredNormalProjection q (q / 4) (-t) (8 * t) x)) =
      (fun x : ℝ => Real.exp (t * (x ^ 2 - q))) := by
    funext x
    congr 1
    unfold centeredNormalProjection normalValue
    ring
  have hsample : (fun z : Shao.Path n =>
      Real.exp (centeredSampleProjection q (q / 4) (-t) (8 * t) n z)) =
      (fun z : Shao.Path n => Real.exp (t * (Shao.energy z - (n : ℝ) * q))) := by
    funext z
    rw [sample_projection_linear, normalDeviation_eq_sum_energy]
    congr 1
    ring
  have h := iid_centeredSample_tilt mu hb q (q / 4) (-t) (8 * t) n
  exact ⟨by simpa only [hsample] using h.1,
    by simpa only [hsample, hsingle] using h.2.1⟩

theorem exists_source_far_weighted_tail_bound (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q H ell delta : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51)
    (hell : 0 ≤ ell) (hgap : ell * q < 7 / 200) (hdelta : 0 < delta)
    (henergy : ∀ᵐ x ∂mu, 1 ≤ x ^ 2 ∧ x ^ 2 ≤ 1 + H)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂mu) = q) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 0 < n →
      Integrable (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z))
        (Measure.pi (fun _ : Fin n => mu)) ∧
      (∫ z : Shao.Path n in {z | z ∈ sourceTail q n ∧
          normalDeviation q z ≤ -delta * (n : ℝ)},
        Real.exp (-ell * normalDeviation q z)
        ∂Measure.pi (fun _ : Fin n => mu)) ≤ C * Real.exp (-c * (n : ℝ)) := by
  classical
  have hq : 0 < q := lt_trans zero_lt_one hq0
  have hH : 0 < H := by linarith
  obtain ⟨c, hc, T, hT, hcover⟩ := exists_source_far_energy_exponential_cover
    mu hb q H ell delta hq0 hq1 hH0 hH1 hell hgap hdelta henergy hsecond
  refine ⟨(T.card : ℝ) + 1, c, by positivity, hc, ?_⟩
  intro n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnq : 0 < (n : ℝ) * q := mul_pos hnR hq
  let nu : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
  let Z : ℝ → ℝ := fun t => ∫ x : ℝ, Real.exp (t * (x ^ 2 - q)) ∂mu
  let rho : ℝ → Shao.Path n → ℝ := fun t z =>
    Real.exp (t * (Shao.energy z - (n : ℝ) * q)) / Z t ^ n
  let S : Shao.Path n → ℝ := fun z => ∑ t ∈ T, rho t z
  let E : Set (Shao.Path n) :=
    {z | z ∈ sourceTail q n ∧ normalDeviation q z ≤ -delta * (n : ℝ)}
  have hweightEq : (fun z : Shao.Path n =>
      Real.exp (centeredSampleProjection q (q / 4) (-ell) 0 n z)) =
      (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z)) := by
    funext z
    rw [sample_projection_linear]
    simp only [zero_mul, add_zero]
  have hw : Integrable (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z)) nu := by
    simpa only [hweightEq] using (iid_centeredSample_tilt mu hb q (q / 4) (-ell) 0 n).1
  have hrho (t : ℝ) (ht : t ∈ T) : Integrable (rho t) nu ∧ (∫ z, rho t z ∂nu) = 1 := by
    have hZ : 0 < Z t := (hT t ht).2
    obtain ⟨hf, hint⟩ := sample_energy_mgf mu hb q t n
    refine ⟨hf.div_const _, ?_⟩
    dsimp [rho]
    rw [integral_div, hint]
    exact div_self (pow_ne_zero n hZ.ne')
  have hrho0 (t : ℝ) (ht : t ∈ T) (z : Shao.Path n) : 0 ≤ rho t z :=
    div_nonneg (Real.exp_nonneg _) (pow_nonneg (hT t ht).2.le n)
  have hS : Integrable S nu := integrable_finsetSum T (fun t ht => (hrho t ht).1)
  have hS0 (z : Shao.Path n) : 0 ≤ S z :=
    Finset.sum_nonneg (fun t ht => hrho0 t ht z)
  have hSint : (∫ z, S z ∂nu) = (T.card : ℝ) := by
    dsimp [S]
    rw [integral_finsetSum T (fun t ht => (hrho t ht).1)]
    calc
      _ = ∑ _t ∈ T, (1 : ℝ) := Finset.sum_congr rfl (fun t ht => (hrho t ht).2)
      _ = (T.card : ℝ) := by simp
  have hcoords : ∀ᵐ z ∂nu, ∀ i : Fin n, 1 ≤ (z i) ^ 2 ∧ (z i) ^ 2 ≤ 1 + H := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => mu) (i := i)).eventually henergy
  have hM : Continuous (fun z : Shao.Path n => normalDeviation q z) := by
    unfold normalDeviation normalValue
    fun_prop
  have hE : MeasurableSet E :=
    (sourceTail_measurable q n).inter (measurableSet_le hM.measurable measurable_const)
  have hlarge : Integrable (fun z : Shao.Path n => Real.exp (-c * (n : ℝ)) * S z) nu :=
    hS.const_mul _
  have hbound : (fun z : Shao.Path n => Real.exp (-ell * normalDeviation q z)) ≤ᵐ[nu.restrict E]
      (fun z : Shao.Path n => Real.exp (-c * (n : ℝ)) * S z) := by
    filter_upwards [ae_restrict_of_ae hcoords, ae_restrict_mem hE] with z hz hzE
    have hfar := sourceTail_far_energy_mem q H delta hq hH hdelta n hn z hz hzE.1 hzE.2
    obtain ⟨t, ht, htest⟩ := hcover (sourceEnergyRatio q n z) hfar.1
    have hgeom := sourceTail_normalDeviation_energy_lower q hq n hn z hzE.1
    have hR2 : (n : ℝ) * q * sourceEnergyRatio q n z ^ 2 = Shao.energy z := by
      dsimp [sourceEnergyRatio]
      rw [Real.sq_sqrt (div_nonneg (Shao.energy_nonneg z) hnq.le)]
      field_simp
    have henergyArg : (n : ℝ) * (t * (q * sourceEnergyRatio q n z ^ 2 - q)) =
        t * (Shao.energy z - (n : ℝ) * q) := by
      rw [← hR2]
      ring
    have htestN := mul_lt_mul_of_pos_left htest hnR
    have hweighted := mul_le_mul_of_nonneg_left hgeom hell
    have harg : -ell * normalDeviation q z ≤ -c * (n : ℝ) +
        (t * (Shao.energy z - (n : ℝ) * q) - (n : ℝ) * Real.log (Z t)) := by
      change (n : ℝ) * (ell * q * (sourceEnergyRatio q n z - 1) ^ 2 + c) <
        (n : ℝ) * (t * (q * sourceEnergyRatio q n z ^ 2 - q) - Real.log (Z t)) at htestN
      rw [mul_sub, henergyArg] at htestN
      nlinarith only [htestN, hweighted]
    have hZ : 0 < Z t := (hT t ht).2
    have hpow : Real.exp ((n : ℝ) * Real.log (Z t)) = Z t ^ n := by
      rw [Real.exp_nat_mul, Real.exp_log hZ]
    have hrhoExp : Real.exp (t * (Shao.energy z - (n : ℝ) * q) -
        (n : ℝ) * Real.log (Z t)) = rho t z := by
      rw [Real.exp_sub, hpow]
    have hsingle : Real.exp (-ell * normalDeviation q z) ≤
        Real.exp (-c * (n : ℝ)) * rho t z := by
      have h := Real.exp_le_exp.mpr harg
      rwa [Real.exp_add, hrhoExp] at h
    have hsum : rho t z ≤ S z := Finset.single_le_sum (fun u hu => hrho0 u hu z) ht
    exact hsingle.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
  refine ⟨hw, ?_⟩
  change (∫ z in E, Real.exp (-ell * normalDeviation q z) ∂nu) ≤ _
  calc
    (∫ z in E, Real.exp (-ell * normalDeviation q z) ∂nu) ≤
        ∫ z in E, Real.exp (-c * (n : ℝ)) * S z ∂nu :=
      integral_mono_ae hw.integrableOn hlarge.integrableOn hbound
    _ ≤ ∫ z, Real.exp (-c * (n : ℝ)) * S z ∂nu :=
      setIntegral_le_integral hlarge (Filter.Eventually.of_forall fun z =>
        mul_nonneg (Real.exp_nonneg _) (hS0 z))
    _ = Real.exp (-c * (n : ℝ)) * (T.card : ℝ) := by
      rw [integral_const_mul, hSint]
    _ ≤ ((T.card : ℝ) + 1) * Real.exp (-c * (n : ℝ)) := by
      have h := Real.exp_nonneg (-c * (n : ℝ))
      nlinarith

end
end Shao.OQ3
