import Shao.OQ3.CharacteristicMeasureDomination
import Shao.OQ3.NormalLayerMassBound

namespace Shao.OQ3
open MeasureTheory Filter
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

private theorem centered_norm_eq_joint (mu : Measure ℝ) (q a t s : ℝ) :
    ‖centeredNormalTangentCharacteristic mu q a t s‖ =
      ‖jointCharacteristic mu (8 * t + s) (-t)‖ := by
  rw [centeredNormalTangentCharacteristic_factor, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

private theorem exp_gap_lower (x A : ℝ) (hx : 0 ≤ x) (hxA : x ≤ A) :
    x * Real.exp (-A) ≤ 1 - Real.exp (-x) := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  have heq : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [heq] at hh
  have hm : x * Real.exp (-A) ≤ x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hx
  nlinarith only [hh, hm]

private theorem gaussian_scaled_power (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a delta c : ℝ) (_hdelta : 0 < delta) (hc : 0 < c)
    (hlocal : ∀ t : ℝ, |t| ≤ delta →
      ‖centeredNormalTangentCharacteristic mu q a t 0‖ ≤ Real.exp (-c * t ^ 2))
    (n : ℕ) (hn : 1 ≤ n) : ∀ v : ℝ,
      |v| ≤ delta * Real.sqrt (n : ℝ) →
        ‖centeredNormalTangentCharacteristic mu q a ((Real.sqrt (n : ℝ))⁻¹ * v) 0 ^ n‖ ≤
          Real.exp (-c * v ^ 2) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hr2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  intro v hv
  have hv' : |(Real.sqrt (n : ℝ))⁻¹ * v| ≤ delta := by
    simpa [abs_mul, abs_inv, abs_of_pos hr, div_eq_mul_inv, mul_comm] using
      (div_le_iff₀ hr).mpr hv
  rw [norm_pow]
  calc
    _ ≤ Real.exp (-c * (((Real.sqrt (n : ℝ))⁻¹ * v) ^ 2)) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) (hlocal _ hv') n
    _ = Real.exp (-c * v ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp [hr.ne']
      rw [hr2]

private theorem compact_power_norm_integral_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ p ∈ K,
      Real.sqrt (n : ℝ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          ‖centeredNormalTangentCharacteristic (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) q a t 0 ^ n‖ ∂(volume : Measure ℝ)) ≤ C := by
  let nu (p : ℝ × ℝ) := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  have hnu (p : ℝ × ℝ) : IsProbabilityMeasure (nu p) := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu (4 + Real.sqrt 10) (by positivity) hb p.1 p.2)
  let (p : ℝ × ℝ) : IsProbabilityMeasure (nu p) := hnu p
  obtain ⟨m, hm, hm1, hcompare0⟩ :=
    exists_compact_tilted_characteristic_bound mu (4 + Real.sqrt 10) (by positivity) hb K hK 0 0
  have hzero_tilt : mu.tilted (fun x : ℝ => (0 : ℝ) * x + 0 * x ^ 2) = mu := by
    simpa only [zero_mul, zero_add] using tilted_const mu 0
  have hcompare : ∀ p ∈ K, ∀ t : ℝ,
      ‖centeredNormalTangentCharacteristic (nu p) q a t 0‖ ≤
        1 - m * (1 - ‖centeredNormalTangentCharacteristic mu q a t 0‖) := by
    intro p hp t
    simpa only [centered_norm_eq_joint, hzero_tilt, nu] using hcompare0 p hp (8 * t + 0) (-t)
  obtain ⟨delta0, c0, hdelta0, hc0, hgauss⟩ :=
    exists_centeredNormalTangentCharacteristic_gaussian_bound mu hb q a hq ha hS hD
  let H := Real.pi / dyadicMesh J
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hH : 0 < H := div_pos Real.pi_pos hmesh
  let delta := min delta0 (H / 2)
  have hdelta : 0 < delta := lt_min hdelta0 (by positivity)
  have hdeltaH : delta < H := (min_le_right delta0 (H / 2)).trans_lt (by linarith)
  have hdelta0le : delta ≤ delta0 := min_le_left _ _
  let c : ℝ := m * c0 * Real.exp (-c0 * delta ^ 2)
  have hc : 0 < c := mul_pos (mul_pos hm hc0) (Real.exp_pos _)
  have hlocal : ∀ p ∈ K, ∀ t : ℝ, |t| ≤ delta →
      ‖centeredNormalTangentCharacteristic (nu p) q a t 0‖ ≤ Real.exp (-c * t ^ 2) := by
    intro p hp t ht
    have hx : 0 ≤ c0 * t ^ 2 := mul_nonneg hc0.le (sq_nonneg _)
    have hxA : c0 * t ^ 2 ≤ c0 * delta ^ 2 :=
      mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2) hc0.le
    have hgap := exp_gap_lower (c0 * t ^ 2) (c0 * delta ^ 2) hx hxA
    simp only [← neg_mul] at hgap
    have hbase : ‖centeredNormalTangentCharacteristic mu q a t 0‖ ≤
        Real.exp (-c0 * t ^ 2) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
        hgauss t 0 (ht.trans hdelta0le) (by simpa using hdelta0.le)
    calc
      _ ≤ 1 - m * (1 - ‖centeredNormalTangentCharacteristic mu q a t 0‖) := hcompare p hp t
      _ ≤ 1 - m * (1 - Real.exp (-c0 * t ^ 2)) := by nlinarith only [mul_le_mul_of_nonneg_left hbase hm.le]
      _ ≤ 1 - c * t ^ 2 := by dsimp only [c]; nlinarith only [mul_le_mul_of_nonneg_left hgap hm.le]
      _ ≤ Real.exp (-c * t ^ 2) := by simpa only [neg_mul] using Real.one_sub_le_exp_neg (c * t ^ 2)
  let B := Set.Icc (-H) H
  let A := Set.Icc (-delta) delta
  let E := B \ A
  let Kfreq := Set.Icc (-H) (-delta) ∪ Set.Icc delta H
  let G : ℝ := ∫ v : ℝ, Real.exp (-c * v ^ 2) ∂(volume : Measure ℝ)
  have hG : 0 ≤ G := integral_nonneg fun _ => (Real.exp_pos _).le
  have hKfreq : IsCompact Kfreq := isCompact_Icc.union isCompact_Icc
  have hzero : (0 : ℝ) ∉ Kfreq := by
    rintro (hz | hz)
    · have := hz.2; linarith
    · have := hz.1; linarith
  have hband : ∀ t ∈ Kfreq, |t| ≤ Real.pi / dyadicMesh J := by
    intro t ht
    apply abs_le.mpr
    rcases ht with ht | ht
    · exact ⟨ht.1, by dsimp [H] at hdeltaH; linarith [ht.2]⟩
    · exact ⟨by dsimp [H] at hdeltaH; linarith [ht.1], ht.2⟩
  have hEK : E ⊆ Kfreq := by
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
    stage_far_arc_uniform mu J q a hrange hpos Kfreq hKfreq hzero hband
  let rho1 : ℝ := 1 - m * (1 - rho)
  have hrho1pos : 0 < rho1 := by
    have hh := mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hrho1.le)
    dsimp only [rho1]
    nlinarith only [hh, hrho]
  have hrho1lt : rho1 < 1 := by
    dsimp only [rho1]
    nlinarith only [mul_pos hm (sub_pos.mpr hrho1)]
  have hcontract_family (p : ℝ × ℝ) (hp : p ∈ K) (t : ℝ) (ht : t ∈ Kfreq) :
      ‖centeredNormalTangentCharacteristic (nu p) q a t 0‖ ≤ rho1 := by
    have hh := (hcontract t ht 0 (by simpa using heta)).le
    have hcmp := hcompare p hp t
    dsimp only [rho1]
    nlinarith only [hcmp, mul_le_mul_of_nonneg_left hh hm.le]
  have hfull (p : ℝ × ℝ) (n : ℕ) : IntegrableOn
      (fun t : ℝ => ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖) B
      (volume : Measure ℝ) := (normal_power_norm_continuous (nu p) q a n).integrableOn_Icc
  have hfar_integrable (p : ℝ × ℝ) (n : ℕ) : IntegrableOn
      (fun t : ℝ => ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖) E
      (volume : Measure ℝ) := (hfull p n).mono_set Set.sdiff_subset
  have hfar (p : ℝ × ℝ) (hp : p ∈ K) (n : ℕ) : (∫ t : ℝ in E,
      ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖ ∂(volume : Measure ℝ)) ≤
      volume.real E * rho1 ^ n := by
    have hh := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
      hEfinite (f := fun t : ℝ => ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖)
      (C := rho1 ^ n) (fun t ht => by
        rw [norm_norm, norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hcontract_family p hp t (hEK ht)) n)
    have hnonneg : 0 ≤ ∫ t : ℝ in E,
        ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖ ∂(volume : Measure ℝ) :=
      integral_nonneg fun _ => norm_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, mul_comm] using hh
  have hnrho := tendsto_self_mul_const_pow_of_lt_one hrho1pos.le hrho1lt
  have hrhopow := tendsto_pow_atTop_nhds_zero_of_lt_one hrho1pos.le hrho1lt
  have hmajor : Tendsto (fun n : ℕ => volume.real E * ((n : ℝ) * rho1 ^ n + rho1 ^ n))
      atTop (nhds 0) := by
    simpa only [zero_add, mul_zero] using (hnrho.add hrhopow).const_mul (volume.real E)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      volume.real E * ((n : ℝ) * rho1 ^ n + rho1 ^ n) < 1 :=
    hmajor.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨G + 1, by linarith, ?_⟩
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hsn hn1
  intro p hp
  have hscaled := gaussian_scaled_power (nu p) q a delta c hdelta hc (hlocal p hp) n hn1
  have hcentral : Real.sqrt (n : ℝ) *
      (∫ t : ℝ in A, ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖
        ∂(volume : Measure ℝ)) ≤ G := by
    rw [← central_norm_integral_eq_scaled (nu p) q a delta hdelta n hn1]
    apply integral_mono (centralFourierIntegrand_integrable (nu p) q a delta 0 (fun _ => 0) n).norm
      (integrable_exp_neg_mul_sq hc)
    intro v
    by_cases hv : v ∈ Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ))
    · simp only [centralFourierIntegrand, Set.indicator_of_mem hv, norm_mul,
        Complex.norm_exp_ofReal_mul_I, one_mul, mul_zero]
      apply hscaled v
      have habs : |v| ≤ delta * Real.sqrt (n : ℝ) := by
        apply abs_le.mpr
        simpa only [Set.mem_Icc, neg_mul] using hv
      exact habs
    · simp only [centralFourierIntegrand, Set.indicator_of_notMem hv, norm_zero]
      exact (Real.exp_pos _).le
  have hfar_scaled : Real.sqrt (n : ℝ) *
      (∫ t : ℝ in E, ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖
        ∂(volume : Measure ℝ)) ≤ 1 := by
    have hroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (n : ℝ)]⟩
    calc
      _ ≤ Real.sqrt (n : ℝ) * (volume.real E * rho1 ^ n) :=
        mul_le_mul_of_nonneg_left (hfar p hp n) (Real.sqrt_nonneg _)
      _ ≤ ((n : ℝ) + 1) * (volume.real E * rho1 ^ n) :=
        mul_le_mul_of_nonneg_right hroot (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hrho1pos.le n))
      _ = volume.real E * ((n : ℝ) * rho1 ^ n + rho1 ^ n) := by ring
      _ ≤ 1 := hsn.le
  have hdecomp : (∫ t : ℝ in B,
      ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖ ∂(volume : Measure ℝ)) =
      (∫ t : ℝ in A, ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖
        ∂(volume : Measure ℝ)) +
      ∫ t : ℝ in E, ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖
        ∂(volume : Measure ℝ) := by
    change _ = _ + ∫ t : ℝ in B \ A,
      ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖ ∂(volume : Measure ℝ)
    rw [setIntegral_sdiff measurableSet_Icc (hfull p n) hsub]
    ring
  have htotal : Real.sqrt (n : ℝ) * (∫ t : ℝ in B,
      ‖centeredNormalTangentCharacteristic (nu p) q a t 0 ^ n‖ ∂(volume : Measure ℝ)) ≤ G + 1 := by
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

theorem exists_compact_tilted_normal_layer_mass_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q a : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ p ∈ K, ∀ d : ℝ,
      Real.sqrt (n : ℝ) *
        (Measure.pi (fun _ : Fin n =>
          mu.tilted (fun x : ℝ => p.1 * x + p.2 * x ^ 2))).real
          {z : Shao.Path n | normalDeviation q z = d} ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    compact_power_norm_integral_bound mu J q a hb hq ha hS hD hrange hpos K hK
  let k : ℝ := dyadicMesh J / (2 * Real.pi)
  have hmesh : 0 < dyadicMesh J := by unfold dyadicMesh; positivity
  have hk : 0 < k := div_pos hmesh (mul_pos (by norm_num) Real.pi_pos)
  refine ⟨k * C, mul_pos hk hC, ?_⟩
  filter_upwards [hbound] with n hn
  intro p hp d
  let nu := mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let : IsProbabilityMeasure nu := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu (4 + Real.sqrt 10) (by positivity) hb p.1 p.2)
  have hnu_range : ∀ᵐ x ∂nu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i) :=
    (tilted_absolutelyContinuous mu (fun x => p.1 * x + p.2 * x ^ 2)).ae_le hrange
  have hgrid : ∀ᵐ x ∂nu, ∃ m : ℤ, normalValue x = dyadicMesh J * (m : ℝ) := by
    filter_upwards [hnu_range] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact stageAtom_normalValue_lattice J i
  have hnp := hn p hp
  change Real.sqrt (n : ℝ) * (Measure.pi (fun _ : Fin n => nu)).real
    {z : Shao.Path n | normalDeviation q z = d} ≤ k * C
  by_cases hlayer : ∃ m : ℤ, d + (n : ℝ) * q = dyadicMesh J * (m : ℝ)
  · have hFourier := normal_layer_Fourier_identity nu q a (dyadicMesh J) d 0 hmesh hgrid n hlayer
    have hmass : 0 ≤ (Measure.pi (fun _ : Fin n => nu)).real
        {z : Shao.Path n | normalDeviation q z = d} := ENNReal.toReal_nonneg
    have hbody : Continuous (fun t : ℝ =>
        Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
          centeredNormalTangentCharacteristic nu q a t 0 ^ n) := by
      apply Continuous.mul
      · fun_prop
      · exact ((centeredNormalTangentCharacteristic_continuous nu q a).comp
          (continuous_id.prodMk continuous_const)).pow n
    have _hbody_integrable : IntegrableOn (fun t : ℝ =>
        Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
          centeredNormalTangentCharacteristic nu q a t 0 ^ n)
        (Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J))
        (volume : Measure ℝ) := hbody.integrableOn_Icc
    have hmass_bound : (Measure.pi (fun _ : Fin n => nu)).real
        {z : Shao.Path n | normalDeviation q z = d} ≤ k *
        ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          ‖centeredNormalTangentCharacteristic nu q a t 0 ^ n‖ ∂(volume : Measure ℝ) := by
      calc
        _ = ‖normalLayerCharacteristic nu q a d 0 n‖ := by
          rw [normalLayerCharacteristic_zero_eq_mass, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hmass]
        _ = k * ‖∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
              centeredNormalTangentCharacteristic nu q a t 0 ^ n ∂(volume : Measure ℝ)‖ := by
          rw [hFourier, norm_mul]
          simp only [mul_zero, Complex.norm_real, Real.norm_eq_abs]
          change |k| * _ = k * _
          rw [abs_of_pos hk]
        _ ≤ k * ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            ‖Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
              centeredNormalTangentCharacteristic nu q a t 0 ^ n‖ ∂(volume : Measure ℝ) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
        _ = _ := by simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    calc
      _ ≤ Real.sqrt (n : ℝ) * (k *
          ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            ‖centeredNormalTangentCharacteristic nu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) :=
        mul_le_mul_of_nonneg_left hmass_bound (Real.sqrt_nonneg _)
      _ = k * (Real.sqrt (n : ℝ) *
          ∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
            ‖centeredNormalTangentCharacteristic nu q a t 0 ^ n‖ ∂(volume : Measure ℝ)) := by ring
      _ ≤ k * C := mul_le_mul_of_nonneg_left hnp hk.le
  · have hz := normal_layer_mass_zero_off_grid nu J q d n hnu_range hlayer
    simp only [measureReal_def, hz, ENNReal.toReal_zero, mul_zero]
    exact (mul_pos hk hC).le


end
end Shao.OQ3
