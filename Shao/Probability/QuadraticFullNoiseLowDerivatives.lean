import Shao.Probability.QuadraticCharacteristicOddPower
import Shao.Probability.QuadraticFullNoiseGlobalOddEven
import Shao.Probability.QuadraticFullNoiseConeDerivatives

/-! Actual low-frequency second derivatives of the source D and W=uE.
The exact complete public statement is frozen before implementation. -/
set_option autoImplicit false
namespace Shao.Probability
open MeasureTheory ProbabilityTheory

private lemma signed_power_diffs (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (m : ℕ) (σ u v : ℝ) :
    let f : ℝ → ℂ := fun r => quadraticChar ν (σ * r) v ^ m
    DifferentiableAt ℝ f u ∧ DifferentiableAt ℝ (fun r => deriv f r) u := by
  let P : Measure (Shao.Path m) := Measure.pi (fun _ : Fin m => ν)
  have hlaw (i : Fin m) : IdentDistrib (fun a : Shao.Path m => a i) (id : ℝ → ℝ) P ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using (measurePreserving_eval (fun _ : Fin m => ν) i).map_eq
  have hp (r : ℝ) : HasDerivAt (fun t => quadraticChar ν t v ^ m)
      (deriv (fun t => quadraticChar ν t v ^ m) r) r :=
    (iid_quadraticChar_power_hasDerivAt (fun i => measurable_pi_apply i)
      (iIndepFun_pi (fun _ : Fin m => measurable_id.aemeasurable)) hlaw h2 r v).differentiableAt.hasDerivAt
  have hpp (r : ℝ) : HasDerivAt (fun t => deriv (fun s => quadraticChar ν s v ^ m) t)
      (deriv (fun t => deriv (fun s => quadraticChar ν s v ^ m) t) r) r :=
    (iid_quadraticChar_power_deriv_hasDerivAt (fun i => measurable_pi_apply i)
      (iIndepFun_pi (fun _ : Fin m => measurable_id.aemeasurable)) hlaw h2 r v).differentiableAt.hasDerivAt
  have hfirst (r : ℝ) := (hp (σ * r)).scomp r
    (by simpa using (hasDerivAt_id r).const_mul σ)
  have hsecond := ((hpp (σ * u)).scomp u
    (by simpa using (hasDerivAt_id u).const_mul σ)).const_smul σ
  exact ⟨(hfirst u).differentiableAt,
    (hsecond.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => (hfirst r).deriv)).differentiableAt⟩


private lemma half_add_bound (z w : ℂ) (c : ℝ) (hz : ‖z‖ ≤ c) (hw : ‖w‖ ≤ c) :
    ‖(z + w) / 2‖ ≤ c := by
  calc
    _ = ‖z + w‖ / 2 := by simp
    _ ≤ (‖z‖ + ‖w‖) / 2 := div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ _ := by linarith

private lemma half_sub_bound (z w : ℂ) (c : ℝ) (hz : ‖z‖ ≤ c) (hw : ‖w‖ ≤ c) :
    ‖(z - w) / 2‖ ≤ c := by
  simpa only [sub_eq_add_neg] using half_add_bound z (-w) c hz (by simpa using hw)

private lemma odd_even_calculus (p q : ℝ → ℂ)
    (hp : ∀ r, HasDerivAt p (deriv p r) r)
    (hq : ∀ r, HasDerivAt q (deriv q r) r) (u c1 c2 : ℝ)
    (hpp : DifferentiableAt ℝ (fun r => deriv p r) u)
    (hqq : DifferentiableAt ℝ (fun r => deriv q r) u)
    (hp1 : ‖deriv p u‖ ≤ c1) (hq1 : ‖deriv q u‖ ≤ c1)
    (hp2 : ‖deriv (fun r => deriv p r) u‖ ≤ c2)
    (hq2 : ‖deriv (fun r => deriv q r) u‖ ≤ c2) :
    let D := fun r => (p r - q r) / 2
    let E := fun r => (p r + q r) / 2
    let W := fun r : ℝ => (r : ℂ) * E r
    DifferentiableAt ℝ D u ∧ DifferentiableAt ℝ (fun r => deriv D r) u ∧
      DifferentiableAt ℝ W u ∧ DifferentiableAt ℝ (fun r => deriv W r) u ∧
      ‖deriv (fun r => deriv D r) u‖ ≤ c2 ∧
      ‖deriv (fun r => deriv W r) u‖ ≤ 2 * c1 + |u| * c2 := by
  dsimp only
  let D := fun r => (p r - q r) / 2
  let E := fun r => (p r + q r) / 2
  let W := fun r : ℝ => (r : ℂ) * E r
  have hD (r : ℝ) : HasDerivAt D ((deriv p r - deriv q r) / 2) r :=
    ((hp r).sub (hq r)).div_const 2
  have hE (r : ℝ) : HasDerivAt E ((deriv p r + deriv q r) / 2) r :=
    ((hp r).add (hq r)).div_const 2
  have hDD : HasDerivAt (fun r => deriv D r)
      ((deriv (fun r => deriv p r) u - deriv (fun r => deriv q r) u) / 2) u :=
    (hpp.hasDerivAt.sub hqq.hasDerivAt |>.div_const 2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hD r).deriv)
  have hEE : HasDerivAt (fun r => deriv E r)
      ((deriv (fun r => deriv p r) u + deriv (fun r => deriv q r) u) / 2) u :=
    (hpp.hasDerivAt.add hqq.hasDerivAt |>.div_const 2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (hE r).deriv)
  have hEglobal (r : ℝ) : HasDerivAt E (deriv E r) r := (hE r).differentiableAt.hasDerivAt
  have hW (r : ℝ) : HasDerivAt W (E r + (r : ℂ) * deriv E r) r := by
    convert ((hasDerivAt_id r).ofReal_comp.mul (hEglobal r)) using 1 <;> simp [W]
    funext t
    rfl
  have hWW := ((hEglobal u).add ((hasDerivAt_id u).ofReal_comp.mul
    hEE.differentiableAt.hasDerivAt)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => (hW r).deriv)
  refine ⟨(hD u).differentiableAt, hDD.differentiableAt, (hW u).differentiableAt,
    hWW.differentiableAt, ?_, ?_⟩
  · change ‖deriv (fun r => deriv D r) u‖ ≤ c2
    rw [hDD.deriv]
    exact half_sub_bound _ _ c2 hp2 hq2
  · have hE1 : ‖deriv E u‖ ≤ c1 := by
      rw [(hE u).deriv]
      exact half_add_bound _ _ c1 hp1 hq1
    have hE2 : ‖deriv (fun r => deriv E r) u‖ ≤ c2 := by
      rw [hEE.deriv]
      exact half_add_bound _ _ c2 hp2 hq2
    change ‖deriv (fun r => deriv W r) u‖ ≤ _
    rw [hWW.deriv]
    calc
      _ = ‖2 * deriv E u + (u : ℂ) * deriv (fun r => deriv E r) u‖ := by
        congr 1
        simp only [Complex.ofReal_one, id_eq]
        ring
      _ ≤ 2 * ‖deriv E u‖ + |u| * ‖deriv (fun r => deriv E r) u‖ := by
        simpa only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs] using
          norm_add_le (2 * deriv E u) ((u : ℂ) * deriv (fun r => deriv E r) u)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hE1 (by norm_num))
        (mul_le_mul_of_nonneg_left hE2 (abs_nonneg u))


private lemma residual_exponential (ℓ j : ℕ) (hℓ : 6 ≤ ℓ) (hj : j ≤ 3)
    (V m2 u : ℝ) (hV : 0 ≤ V) (hcomp : m2 ≤ 4 * V) :
    Real.exp (-V * u ^ 2 / 32) ^ (ℓ - j) ≤
      Real.exp (-((ℓ : ℝ) * m2) * u ^ 2 / 256) := by
  have hnat : ℓ ≤ 2 * (ℓ - j) := by omega
  have hcast : (ℓ : ℝ) ≤ 2 * ((ℓ - j : ℕ) : ℝ) := by exact_mod_cast hnat
  have hc : (ℓ : ℝ) * m2 ≤ 8 * ((ℓ - j : ℕ) : ℝ) * V := by
    calc
      _ ≤ (ℓ : ℝ) * (4 * V) := mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcast hV]
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg u)]

private lemma normalized_drift_payment (n ℓ : ℕ) (hℓ : ℓ ≤ n)
    (μ m2 : ℝ) (hm2 : 0 ≤ m2)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * m2)
    (hbias : (n : ℝ) * |μ| ≤ 1) :
    (ℓ : ℝ) * |μ| ≤ 2 * Real.sqrt ((ℓ : ℝ) * m2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hln : (ℓ : ℝ) ≤ n := Nat.cast_le.mpr hℓ
  have hnb : 0 ≤ (n : ℝ) * |μ| := mul_nonneg hn (abs_nonneg μ)
  have hsq : ((n : ℝ) * |μ|) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbias) (by linarith : 0 ≤ 1 + (n : ℝ) * |μ|)]
  rw [mul_pow, sq_abs] at hsq
  have hc : (n : ℝ) * μ ^ 2 ≤ (4 / 3 : ℝ) * m2 := by
    have hp := mul_le_mul_of_nonneg_right hscale (mul_nonneg hn (sq_nonneg μ))
    have hq := mul_le_mul_of_nonneg_left hsq hm2
    nlinarith [hp, hq]
  have hlsq : ((ℓ : ℝ) * |μ|) ^ 2 ≤ (4 / 3 : ℝ) * ((ℓ : ℝ) * m2) := by
    calc
      _ = (ℓ : ℝ) * ((ℓ : ℝ) * μ ^ 2) := by rw [mul_pow, sq_abs]; ring
      _ ≤ (ℓ : ℝ) * ((n : ℝ) * μ ^ 2) := by gcongr
      _ ≤ (ℓ : ℝ) * ((4 / 3 : ℝ) * m2) := mul_le_mul_of_nonneg_left hc hl
      _ = _ := by ring
  have hT := mul_nonneg hl hm2
  have hs := Real.sq_sqrt hT
  nlinarith [Real.sqrt_nonneg ((ℓ : ℝ) * m2)]


private lemma polynomialPowerBounds (f : ℝ → ℂ)
    (hf : ∀ r, HasDerivAt f (deriv f r) r) (u : ℝ)
    (hff : DifferentiableAt ℝ (fun r => deriv f r) u)
    (m : ℕ) (hm : 2 ≤ m) (q L s : ℝ) (hq : 0 ≤ q) (_hL : 0 ≤ L) (hs : 0 ≤ s)
    (hf0 : ‖f u‖ ≤ q) (hf1 : ‖deriv f u‖ ≤ L)
    (hf2 : ‖deriv (fun r => deriv f r) u‖ ≤ s) :
    let p : ℝ → ℂ := fun r => f r ^ m
    ‖p u‖ ≤ q ^ m ∧
      ‖deriv p u‖ ≤ (m : ℝ) * L * q ^ (m - 1) ∧
      ‖deriv (fun r => deriv p r) u‖ ≤
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) * L ^ 2 * q ^ (m - 2) +
          (m : ℝ) * s * q ^ (m - 1) := by
  dsimp only
  have hfirst (r : ℝ) : deriv (fun t => f t ^ m) r =
      (m : ℂ) * f r ^ (m - 1) * deriv f r := (hf r).pow m |>.deriv
  have hsecond := ((((hf u).pow (m - 1)).const_mul (m : ℂ)).mul hff.hasDerivAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hfirst)
  refine ⟨by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hf0 m, ?_, ?_⟩
  · rw [hfirst]
    simp only [norm_mul, Complex.norm_natCast, norm_pow]
    calc
      _ ≤ (m : ℝ) * q ^ (m - 1) * L := by gcongr
      _ = _ := by ring
  · rw [hsecond.deriv]
    simp only [Pi.pow_apply]
    have heq : (m : ℂ) * (((m - 1 : ℕ) : ℂ) * f u ^ (m - 1 - 1) * deriv f u) * deriv f u +
        (m : ℂ) * f u ^ (m - 1) * deriv (fun r => deriv f r) u =
        (m : ℂ) * ((m - 1 : ℕ) : ℂ) * (deriv f u) ^ 2 * f u ^ (m - 2) +
          (m : ℂ) * deriv (fun r => deriv f r) u * f u ^ (m - 1) := by
      rw [show m - 1 - 1 = m - 2 by omega]
      ring
    rw [heq]
    calc
      _ ≤ ‖(m : ℂ) * ((m - 1 : ℕ) : ℂ) * deriv f u ^ 2 * f u ^ (m - 2)‖ +
          ‖(m : ℂ) * deriv (fun r => deriv f r) u * f u ^ (m - 1)‖ := norm_add_le _ _
      _ = (m : ℝ) * ((m - 1 : ℕ) : ℝ) * ‖deriv f u‖ ^ 2 * ‖f u‖ ^ (m - 2) +
          (m : ℝ) * ‖deriv (fun r => deriv f r) u‖ * ‖f u‖ ^ (m - 1) := by
        simp only [norm_mul, Complex.norm_natCast, norm_pow]
      _ ≤ _ := by gcongr

private lemma productNorms (p q : ℝ → ℂ)
    (hp : ∀ r, HasDerivAt p (deriv p r) r)
    (hq : ∀ r, HasDerivAt q (deriv q r) r) (u P0 P1 P2 Q1 Q2 : ℝ)
    (hP0 : 0 ≤ P0) (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (_hQ1 : 0 ≤ Q1) (_hQ2 : 0 ≤ Q2)
    (hpp : DifferentiableAt ℝ (fun r => deriv p r) u)
    (hqq : DifferentiableAt ℝ (fun r => deriv q r) u)
    (hp0 : ‖p u‖ ≤ P0) (hp1 : ‖deriv p u‖ ≤ P1)
    (hp2 : ‖deriv (fun r => deriv p r) u‖ ≤ P2)
    (hq0 : ‖q u‖ ≤ 1) (hq1 : ‖deriv q u‖ ≤ Q1)
    (hq2 : ‖deriv (fun r => deriv q r) u‖ ≤ Q2) :
    DifferentiableAt ℝ (fun r => p r * q r) u ∧
      DifferentiableAt ℝ (fun r => deriv (fun s => p s * q s) r) u ∧
      ‖deriv (fun r => p r * q r) u‖ ≤ P1 + P0 * Q1 ∧
      ‖deriv (fun r => deriv (fun s => p s * q s) r) u‖ ≤ P2 + 2 * P1 * Q1 + P0 * Q2 := by
  have hfirst (r : ℝ) : deriv (fun s => p s * q s) r = deriv p r * q r + p r * deriv q r :=
    ((hp r).mul (hq r)).deriv
  have hsecond := ((hpp.hasDerivAt.mul (hq u)).add ((hp u).mul hqq.hasDerivAt)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hfirst)
  refine ⟨((hp u).mul (hq u)).differentiableAt, hsecond.differentiableAt, ?_, ?_⟩
  · rw [hfirst]
    calc
      _ ≤ ‖deriv p u‖ * ‖q u‖ + ‖p u‖ * ‖deriv q u‖ := by
        simpa only [norm_mul] using norm_add_le (deriv p u * q u) (p u * deriv q u)
      _ ≤ P1 * 1 + P0 * Q1 := by gcongr
      _ = _ := by ring
  · rw [hsecond.deriv]
    calc
      _ ≤ ‖deriv (fun r => deriv p r) u‖ * ‖q u‖ + ‖deriv p u‖ * ‖deriv q u‖ +
          (‖deriv p u‖ * ‖deriv q u‖ + ‖p u‖ * ‖deriv (fun r => deriv q r) u‖) := by
        exact (norm_add_le _ _).trans (add_le_add
          (by simpa only [norm_mul] using (norm_add_le
            (deriv (fun r => deriv p r) u * q u) (deriv p u * deriv q u)))
          (by simpa only [norm_mul] using (norm_add_le
            (deriv p u * deriv q u) (p u * deriv (fun r => deriv q r) u))))
      _ ≤ P2 * 1 + P1 * Q1 + (P1 * Q1 + P0 * Q2) := by gcongr
      _ = _ := by ring

private lemma secondHalf_le (F : ℝ → ℂ) (u : ℝ) :
    ‖deriv (fun r => deriv (fun t => F t / 2) r) u‖ ≤ ‖deriv (fun r => deriv F r) u‖ := by
  simp only [deriv_div_const, norm_div, Complex.norm_ofNat]
  exact div_le_self (norm_nonneg _) (by norm_num)

private lemma signedSingleBounds (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (sigma u v : ℝ) (hsigma : |sigma| = 1) :
    ‖deriv (fun r => quadraticChar ν (sigma * r) v) u‖ ≤
        |∫ a : ℝ, a ∂ν| + (∫ a : ℝ, a ^ 2 ∂ν) * |u| + (∫ a : ℝ, |a| ^ 3 ∂ν) * |v| ∧
      ‖deriv (fun r => deriv (fun t => quadraticChar ν (sigma * t) v) r) u‖ ≤
        ∫ a : ℝ, a ^ 2 ∂ν := by
  let f : ℝ → ℂ := fun r => quadraticChar ν r v
  have hf (r : ℝ) : HasDerivAt f (deriv f r) r := by
    simpa only [one_mul, pow_one] using (signed_power_diffs ν h2 1 1 r v).1.hasDerivAt
  have hff (r : ℝ) : HasDerivAt (fun t => deriv f t) (deriv (fun t => deriv f t) r) r := by
    simpa only [one_mul, pow_one] using (signed_power_diffs ν h2 1 1 r v).2.hasDerivAt
  have hfirst (r : ℝ) : deriv (fun t => f (sigma * t)) r = sigma • deriv f (sigma * r) :=
    ((hf (sigma * r)).scomp r (by simpa using (hasDerivAt_id r).const_mul sigma)).deriv
  have hsecond := (((hff (sigma * u)).scomp u
    (by simpa using (hasDerivAt_id u).const_mul sigma)).const_smul sigma).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hfirst)
  have hb := quadraticChar_single_derivative_bounds ν h3 (sigma * u) v
  refine ⟨?_, ?_⟩
  · change ‖deriv (fun r => f (sigma * r)) u‖ ≤ _
    rw [hfirst, norm_smul, Real.norm_eq_abs, hsigma, one_mul]
    calc
      _ ≤ ‖deriv f (sigma * u) - Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ)‖ +
          ‖Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ)‖ := norm_le_norm_sub_add _ _
      _ ≤ (∫ a : ℝ, a ^ 2 ∂ν) * |sigma * u| + (∫ a : ℝ, |a| ^ 3 ∂ν) * |v| +
          ‖Complex.I * ((∫ a : ℝ, a ∂ν : ℝ) : ℂ)‖ := add_le_add hb.1 le_rfl
      _ = _ := by simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, hsigma, one_mul]; ring
  · change ‖deriv (fun r => deriv (fun t => f (sigma * t)) r) u‖ ≤ _
    rw [hsecond.deriv, norm_smul, norm_smul, Real.norm_eq_abs, hsigma, one_mul, one_mul]
    exact hb.2

private lemma odd_third_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    0 < ∫ a : ℝ, |a| ^ 3 ∂ν := by
  have hn : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν :=
    integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
  by_contra h
  have hz : (∫ a : ℝ, |a| ^ 3 ∂ν) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun a => pow_nonneg (abs_nonneg a) 3) h3).mp hz
  have hid : (id : ℝ → ℝ) =ᵐ[ν] (fun _ => (0 : ℝ)) := by
    filter_upwards [hae] with a ha
    exact abs_eq_zero.mp (eq_zero_of_pow_eq_zero ha)
  have hv := variance_congr hid
  have hv0 : variance (fun _ : ℝ => (0 : ℝ)) ν = 0 := by
    rw [variance_eq_sub (memLp_const (0 : ℝ))]
    simp
  linarith


private lemma actualGaussianPowers (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν)
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (n m : ℕ) (hmn : m ≤ n) (hm6 : 6 ≤ m)
    (hscale : (3 / 4 : ℝ) ≤ (n : ℝ) * ∫ a : ℝ, a ^ 2 ∂ν)
    (hbias : (n : ℝ) * |∫ a : ℝ, a ∂ν| ≤ 1)
    (hcomp : (∫ a : ℝ, a ^ 2 ∂ν) ≤ 4 * variance (id : ℝ → ℝ) ν)
    (u v : ℝ)
    (hu : |u| ≤ (1 / 128 : ℝ) / ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν))
    (hv : |v| ≤ (1 / 128 : ℝ) * |u| / ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν)) :
    let T : ℝ := (m : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν)
    let Q : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
    let G : ℝ := Real.exp (-T * u ^ 2 / 256)
    ∀ sigma : ℝ, |sigma| = 1 →
      let p : ℝ → ℂ := fun r => quadraticChar ν (sigma * r) v ^ m
      ‖p u‖ ≤ G ∧ ‖deriv p u‖ ≤ 2 * Q * G ∧
        ‖deriv (fun r => deriv p r) u‖ ≤ 9 * T * (1 + T * u ^ 2) * G := by
  let mu : ℝ := ∫ a : ℝ, a ∂ν
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
  let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
  let V : ℝ := variance (id : ℝ → ℝ) ν
  let gamma : ℝ := m3 / V
  let T : ℝ := (m : ℝ) * m2
  let Q : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
  let G : ℝ := Real.exp (-T * u ^ 2 / 256)
  let q : ℝ := Real.exp (-V * u ^ 2 / 32)
  let L : ℝ := |mu| + m2 * |u| + m3 * |v|
  have hm2 : 0 ≤ m2 := integral_nonneg fun a => sq_nonneg a
  have hm3 : 0 ≤ m3 := integral_nonneg fun a => pow_nonneg (abs_nonneg a) 3
  have hVle : V ≤ m2 := by
    have heq : V = m2 - mu ^ 2 := by
      simpa only [Pi.pow_apply, id_eq] using variance_eq_sub
        ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2)
    nlinarith only [heq, sq_nonneg mu]
  have hgammap : 0 < gamma := by
    have hpos := odd_third_pos ν h3 hV
    exact div_pos hpos hV
  have hvstrip : |v| * gamma ≤ (1 / 128 : ℝ) * |u| := (le_div_iff₀ hgammap).mp hv
  have hgammaV : gamma * V = m3 := div_mul_cancel₀ _ hV.ne'
  have hvpaid : m3 * |v| ≤ m2 * |u| / 128 := by
    have hp := mul_le_mul_of_nonneg_right hvstrip hV.le
    rw [mul_assoc, hgammaV] at hp
    have hm := mul_le_mul_of_nonneg_right hVle (abs_nonneg u)
    nlinarith only [hp, hm]
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) hm2
  have hL : L ≤ |mu| + 2 * m2 * |u| := by dsimp [L]; nlinarith only [hvpaid, mul_nonneg hm2 (abs_nonneg u)]
  have hmu : (m : ℝ) * |mu| ≤ 2 * Real.sqrt T := normalized_drift_payment n m hmn mu m2 hm2 hscale hbias
  have hmL : (m : ℝ) * L ≤ 2 * Q := by
    calc
      _ ≤ (m : ℝ) * (|mu| + 2 * m2 * |u|) := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ = (m : ℝ) * |mu| + 2 * T * |u| := by dsimp [T]; ring
      _ ≤ 2 * Real.sqrt T + 2 * T * |u| := add_le_add hmu le_rfl
      _ = _ := by dsimp [Q]; ring_nf; rw [Real.sq_sqrt hT]
  have hQ2 : Q ^ 2 ≤ 2 * T * (1 + T * u ^ 2) := by
    have hx : (Real.sqrt T * |u|) ^ 2 = T * u ^ 2 := by rw [mul_pow, Real.sq_sqrt hT, sq_abs]
    have hh : (1 + Real.sqrt T * |u|) ^ 2 ≤ 2 * (1 + T * u ^ 2) := by
      nlinarith only [hx, sq_nonneg (1 - Real.sqrt T * |u|)]
    calc
      _ = T * (1 + Real.sqrt T * |u|) ^ 2 := by dsimp [Q]; rw [mul_pow, Real.sq_sqrt hT]
      _ ≤ T * (2 * (1 + T * u ^ 2)) := mul_le_mul_of_nonneg_left hh hT
      _ = _ := by ring
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hG0 : 0 ≤ G := (Real.exp_pos _).le
  have hqj (j : ℕ) (hj : j ≤ 3) : q ^ (m - j) ≤ G := residual_exponential m j hm6 hj V m2 u hV.le hcomp
  dsimp only
  intro sigma hsigma
  let f : ℝ → ℂ := fun r => quadraticChar ν (sigma * r) v
  have hf (r : ℝ) : HasDerivAt f (deriv f r) r := by
    simpa only [pow_one] using (signed_power_diffs ν h2 1 sigma r v).1.hasDerivAt
  have hff : DifferentiableAt ℝ (fun r => deriv f r) u := by
    simpa only [pow_one] using (signed_power_diffs ν h2 1 sigma u v).2
  have hf0 : ‖f u‖ ≤ q := by
    have hcases : sigma = 1 ∨ sigma = -1 := abs_eq_abs.mp (by simpa only [abs_one] using hsigma)
    rcases hcases with rfl | rfl
    · simpa only [f, one_mul] using (quadraticChar_lowFrequency_damping ν h3 hV u v hu hv).1
    · simpa only [f, neg_one_mul] using (quadraticChar_lowFrequency_damping ν h3 hV u v hu hv).2
  have hfb := signedSingleBounds ν h2 h3 sigma u v hsigma
  obtain ⟨hp0, hp1, hp2⟩ := polynomialPowerBounds f hf u hff m (by omega) q L m2 hq0 hL0 hm2 hf0 hfb.1 hfb.2
  have hN : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hN1 : (((m - 1 : ℕ) : ℝ)) ≤ m := Nat.cast_le.mpr (Nat.sub_le _ _)
  refine ⟨hp0.trans (by simpa only [Nat.sub_zero] using hqj 0 (by omega)), hp1.trans ?_, hp2.trans ?_⟩
  · calc
      _ ≤ (2 * Q) * G := mul_le_mul hmL (hqj 1 (by omega)) (pow_nonneg hq0 _) (by dsimp [Q]; positivity)
      _ = _ := by ring
  · have hmain : (m : ℝ) * ((m - 1 : ℕ) : ℝ) * L ^ 2 ≤ 4 * Q ^ 2 := by
      calc
        _ ≤ (m : ℝ) * (m : ℝ) * L ^ 2 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hN1 hN) (sq_nonneg _)
        _ = ((m : ℝ) * L) ^ 2 := by ring
        _ ≤ (2 * Q) ^ 2 := pow_le_pow_left₀ (mul_nonneg hN hL0) hmL 2
        _ = _ := by ring
    calc
      _ ≤ (4 * Q ^ 2) * G + T * G := add_le_add
        (mul_le_mul hmain (hqj 2 (by omega)) (pow_nonneg hq0 _) (by positivity))
        (mul_le_mul_of_nonneg_left (hqj 1 (by omega)) hT)
      _ ≤ 9 * T * (1 + T * u ^ 2) * G := by
        have hp := mul_le_mul_of_nonneg_right hQ2 hG0
        nlinarith only [hp, mul_nonneg (mul_nonneg hT hT) (mul_nonneg (sq_nonneg u) hG0)]

private lemma oddProductBound (p X : ℝ → ℂ)
    (hp : ∀ r, HasDerivAt p (deriv p r) r) (hX : ∀ r, HasDerivAt X (deriv X r) r)
    (u A B M Q H G s t K : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (hG : 0 ≤ G) (hs : 0 ≤ s) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (hpp : DifferentiableAt ℝ (fun r => deriv p r) u)
    (hXX : DifferentiableAt ℝ (fun r => deriv X r) u)
    (hp0 : ‖p u‖ ≤ 2 * G * A) (hp1 : ‖deriv p u‖ ≤ 4 * G * (B + Q * A))
    (hp2 : ‖deriv (fun r => deriv p r) u‖ ≤ 18 * G * (M + Q * B + H * A))
    (hX0 : ‖X u‖ ≤ 1) (hX1 : ‖deriv X u‖ ≤ K * s)
    (hX2 : ‖deriv (fun r => deriv X r) u‖ ≤ K * t) :
    ‖deriv (fun r => deriv (fun z => p z / 2 * X z) r) u‖ ≤
      100 * K * G * (M + (Q + s) * B + (H + s * Q + t) * A) := by
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨_, _, _, hbound⟩ := productNorms p X hp hX u
    (2 * G * A) (4 * G * (B + Q * A)) (18 * G * (M + Q * B + H * A))
    (K * s) (K * t) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hpp hXX hp0 hp1 hp2 hX0 hX1 hX2
  have heq : (fun z => p z / 2 * X z) = (fun z => (p z * X z) / 2) := by funext z; ring
  rw [heq]
  refine (secondHalf_le (fun z => p z * X z) u).trans (hbound.trans ?_)
  calc
    _ = G * (18 * M + 18 * (Q * B) + 18 * (H * A) +
        8 * K * (s * B) + 8 * K * (s * Q * A) + 2 * K * (t * A)) := by ring
    _ ≤ G * (100 * K * M + 100 * K * (Q * B) + 100 * K * (H * A) +
        100 * K * (s * B) + 100 * K * (s * Q * A) + 100 * K * (t * A)) := by
      gcongr <;> nlinarith only [hK]
    _ = _ := by ring

theorem sourceTruncation_odd_even_fullNoise_lowFrequency_derivatives :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ν0 : Measure ℝ), IsProbabilityMeasure ν0 →
        ∀ n : ℕ, Integrable (fun z : ℝ => z ^ 2) ν0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν0) = 1 →
          (∫ z : ℝ, z ∂ν0) = 0 →
          ∀ x epsilon : ℝ, 0 ≤ x → 0 < epsilon → epsilon ≤ 1 / 2 →
            Shao.truncationBudget ν0 n x ≤ epsilon ^ 3 / 8 →
            ∀ i : ℕ, i ≤ n → ∀ h kappa L2 : ℝ,
              epsilon / (1 + x) ≤ h → 0 < kappa → kappa ≤ (1 / 128 : ℝ) →
                20 ≤ L2 → 1 ≤ kappa * Real.sqrt L2 →
                let ρ : Measure ℝ :=
                  ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
                let m : ℕ := n - i
                let mu : ℝ := ∫ z : ℝ, z ∂ρ
                let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
                let T : ℝ := (m : ℝ) * (∫ z : ℝ, z ^ 2 ∂ρ)
                let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
                L2 * gamma ^ 2 ≤ T →
                ∀ u v : ℝ, |u| ≤ kappa / gamma → |v| ≤ kappa * |u| / gamma →
                  let A : ℝ := (m : ℝ) * |mu| * |u| +
                    (m : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)
                  let B : ℝ := (m : ℝ) * |mu| + (m : ℝ) * m3 * (u ^ 2 + |v|)
                  let Q : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
                  let G : ℝ := Real.exp (-T * u ^ 2 / 256)
                  let D : ℝ → ℂ := fun r =>
                    (quadraticChar ρ r v ^ m - quadraticChar ρ (-r) v ^ m) / 2 *
                      quadraticFullNoiseChar ρ r v
                  let W : ℝ → ℂ := fun r => (r : ℂ) *
                    ((quadraticChar ρ r v ^ m + quadraticChar ρ (-r) v ^ m) / 2 *
                      quadraticFullNoiseChar ρ r v)
                  ‖deriv (fun r : ℝ => deriv D r) u‖ ≤ C * G *
                    ((m : ℝ) * m3 * |u| + (Q + gamma) * B +
                      (T * (1 + T * u ^ 2) + gamma * Q + h * gamma) * A) ∧
                  (u ≠ 0 → |v| ≤ |u| / (4 * h) →
                    ‖deriv (fun r : ℝ => deriv D r) u‖ ≤ C * G *
                      ((m : ℝ) * m3 * |u| + (Q + 1 / |u|) * B +
                        (T * (1 + T * u ^ 2) + Q / |u| + 1 / u ^ 2) * A) ∧
                    ‖deriv (fun r : ℝ => deriv W r) u‖ ≤ C * G *
                      (T * |u| * (1 + T * u ^ 2) + Q + 1 / |u|)) := by
  obtain ⟨C1, C2, hC1, hC2, hcone⟩ := quadraticFullNoiseChar_cone_derivative_bounds
  let K : ℝ := 100 + C1 + C2
  have hK : 100 ≤ K := by dsimp [K]; linarith
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  refine ⟨100 * K, by positivity, ?_⟩
  intro ν0 hp0 n h2 hnorm hmean x epsilon hx he hehalf hbudget i hi h kappa L2 hh hk hk128 hL2 hkL2
  dsimp only
  intro hTL u v hu hv
  let := hp0
  let ρ : Measure ℝ := ProbabilityTheory.cond ν0 {z | |z| ≤ epsilon / (1 + x)}
  let m : ℕ := n - i
  let mu : ℝ := ∫ z : ℝ, z ∂ρ
  let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂ρ
  let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂ρ
  let T : ℝ := (m : ℝ) * m2
  let gamma : ℝ := m3 / variance (id : ℝ → ℝ) ρ
  let A : ℝ := (m : ℝ) * |mu| * |u| + (m : ℝ) * m3 * (|u| ^ 3 + |u| * |v|)
  let B : ℝ := (m : ℝ) * |mu| + (m : ℝ) * m3 * (u ^ 2 + |v|)
  let Q : ℝ := Real.sqrt T * (1 + Real.sqrt T * |u|)
  let G : ℝ := Real.exp (-T * u ^ 2 / 256)
  let H : ℝ := T * (1 + T * u ^ 2)
  let M : ℝ := (m : ℝ) * m3 * |u|
  let p : ℝ → ℂ := fun r => quadraticChar ρ r v ^ m
  let q : ℝ → ℂ := fun r => quadraticChar ρ (-r) v ^ m
  let d : ℝ → ℂ := fun r => p r - q r
  let X : ℝ → ℂ := fun r => quadraticFullNoiseChar ρ r v
  obtain ⟨_, _, hp, hs, _, h2r, h3r, _⟩ := Shao.sourceTruncation_law_data ν0 n h2 hnorm x epsilon hx he hehalf hbudget
  have : IsProbabilityMeasure ρ := hp
  obtain ⟨hscalelo, hscalehi, _, _, _, hV, hVlo, _⟩ :=
    Shao.sourceTruncation_variance_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  obtain ⟨hm3p, hgammap, _, hm2gamma, hgamcut, _, _, _, _⟩ :=
    Shao.sourceTruncation_gamma_bounds ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget
  have hm2 : 0 ≤ m2 := integral_nonneg fun z => sq_nonneg z
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg m) hm2
  have hhpos : 0 < h := (div_pos he (by linarith : 0 < 1 + x)).trans_le hh
  have hsupport : ∀ᵐ z : ℝ ∂ρ, |z| ≤ h := hs.mono fun _ hz => hz.trans hh
  have hgam : gamma ≤ 2 * h := hgamcut.trans (by linarith)
  have hn : 0 < (n : ℝ) := by
    by_contra hn
    have hn0 : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    rw [hn0, zero_mul] at hscalelo
    norm_num at hscalelo
  have hcomp : m2 ≤ 4 * variance (id : ℝ → ℝ) ρ := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith only [hscalehi, hVlo]
  have hpaid := (Shao.sourceTruncation_paid_moments ν0 n h2 hnorm hmean x epsilon hx he hehalf hbudget).1
  have hbias : (n : ℝ) * |mu| ≤ 1 := by
    apply hpaid.trans
    apply (div_le_iff₀ (mul_pos (pow_pos he 2) (by linarith : 0 < 1 + x))).2
    have hp := mul_le_mul_of_nonneg_left (show 2 * epsilon ≤ 1 + x by linarith) (sq_nonneg epsilon)
    nlinarith only [hbudget, hp, pow_pos he 3]
  have hm6 : 6 ≤ m := by
    have hmupper : T ≤ (m : ℝ) * gamma ^ 2 := mul_le_mul_of_nonneg_left hm2gamma (Nat.cast_nonneg _)
    have hmlower : L2 ≤ (m : ℝ) := by
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hgammap)).mp
      exact hTL.trans hmupper
    have hreal : (6 : ℝ) ≤ m := by linarith
    exact_mod_cast hreal
  have hu128 : |u| ≤ (1 / 128 : ℝ) / gamma := hu.trans (div_le_div_of_nonneg_right hk128 hgammap.le)
  have hv128 : |v| ≤ (1 / 128 : ℝ) * |u| / gamma := hv.trans (by gcongr)
  have hodd := quadraticChar_odd_power_lowFrequency_normalized ρ h3r hV n m (by omega) hm6
    hscalelo hbias hcomp u v hu128 hv128
  change ‖d u‖ ≤ 2 * G * A ∧ ‖deriv d u‖ ≤ 4 * G * (B + Q * A) ∧
    ‖deriv (fun r => deriv d r) u‖ ≤ 18 * G * (M + Q * B + H * A) at hodd
  have hpglob (r : ℝ) : HasDerivAt p (deriv p r) r := by
    simpa only [one_mul] using (signed_power_diffs ρ h2r m 1 r v).1.hasDerivAt
  have hqglob (r : ℝ) : HasDerivAt q (deriv q r) r := by
    simpa only [neg_one_mul] using (signed_power_diffs ρ h2r m (-1) r v).1.hasDerivAt
  have hpp : DifferentiableAt ℝ (fun r => deriv p r) u := by
    simpa only [one_mul] using (signed_power_diffs ρ h2r m 1 u v).2
  have hqq : DifferentiableAt ℝ (fun r => deriv q r) u := by
    simpa only [neg_one_mul] using (signed_power_diffs ρ h2r m (-1) u v).2
  have hdglob (r : ℝ) : HasDerivAt d (deriv d r) r :=
    ((hpglob r).sub (hqglob r)).differentiableAt.hasDerivAt
  have hdprime (r : ℝ) : deriv d r = deriv p r - deriv q r := ((hpglob r).sub (hqglob r)).deriv
  have hdd : DifferentiableAt ℝ (fun r => deriv d r) u :=
    ((hpp.hasDerivAt.sub hqq.hasDerivAt).congr_of_eventuallyEq (Filter.Eventually.of_forall hdprime)).differentiableAt
  have hXglob (r : ℝ) : HasDerivAt X (deriv X r) r :=
    (quadraticFullNoiseChar_derivatives ρ h3r hV h hhpos hsupport hgam r v).1.differentiableAt.hasDerivAt
  have hXX : DifferentiableAt ℝ (fun r => deriv X r) u :=
    (quadraticFullNoiseChar_derivatives ρ h3r hV h hhpos hsupport hgam u v).2.1.differentiableAt
  have hX0 : ‖X u‖ ≤ 1 := (quadraticFullNoiseChar_product ρ h3r hV h hhpos hsupport u v).2.2.2
  obtain ⟨hX1, hX2⟩ := quadraticFullNoiseChar_derivative_bounds ρ h3r hV h hhpos hsupport hgam u v
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hglobalodd := oddProductBound d X hdglob hXglob u A B M Q H G gamma (h * gamma) K
    hA hB hM hQ hH hG hgammap.le (by positivity) hK1 hdd hXX hodd.1 hodd.2.1 hodd.2.2 hX0
    (hX1.trans (by change (67 / 3 : ℝ) * gamma ≤ K * gamma; gcongr; linarith))
    (hX2.trans (by change (70 / 3 : ℝ) * h * gamma ≤ K * (h * gamma); nlinarith only [mul_nonneg hhpos.le hgammap.le, hK]))
  refine ⟨hglobalodd, ?_⟩
  intro hun hvc
  have hau : 0 < |u| := abs_pos.mpr hun
  obtain ⟨hcX1, hcX2⟩ := hcone ρ hp h3r hV h hhpos hsupport u v hun hvc
  have hXc1 : ‖deriv X u‖ ≤ K * (1 / |u|) := hcX1.trans (by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by dsimp [K]; linarith) hau.le)
  have hXc2 : ‖deriv (fun r => deriv X r) u‖ ≤ K * (1 / u ^ 2) := hcX2.trans (by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by dsimp [K]; linarith) (sq_nonneg _))
  have hconeodd := oddProductBound d X hdglob hXglob u A B M Q H G (1 / |u|) (1 / u ^ 2) K
    hA hB hM hQ hH hG (by positivity) (by positivity) hK1 hdd hXX hodd.1 hodd.2.1 hodd.2.2 hX0 hXc1 hXc2
  refine ⟨?_, ?_⟩
  · convert hconeodd using 1 <;> dsimp [H] <;> congr 2 <;> ring
  · have hgauss := actualGaussianPowers ρ h2r h3r hV n m (by omega) hm6 hscalelo hbias hcomp u v hu128 hv128
    have hpgauss := hgauss 1 (by norm_num)
    have hqgauss := hgauss (-1) (by norm_num)
    simp only [one_mul, neg_one_mul] at hpgauss hqgauss
    obtain ⟨_, hFF, hF1, hF2⟩ := productNorms p X hpglob hXglob u G (2 * Q * G) (9 * H * G)
      (K * (1 / |u|)) (K * (1 / u ^ 2)) hG (by positivity) (by positivity) (by positivity) (by positivity)
      hpp hXX hpgauss.1 hpgauss.2.1 (hpgauss.2.2.trans_eq (by dsimp [H, T, m2, G]; ring)) hX0 hXc1 hXc2
    obtain ⟨_, hGG, hG1, hG2⟩ := productNorms q X hqglob hXglob u G (2 * Q * G) (9 * H * G)
      (K * (1 / |u|)) (K * (1 / u ^ 2)) hG (by positivity) (by positivity) (by positivity) (by positivity)
      hqq hXX hqgauss.1 hqgauss.2.1 (hqgauss.2.2.trans_eq (by dsimp [H, T, m2, G]; ring)) hX0 hXc1 hXc2
    have hFglob (r : ℝ) : HasDerivAt (fun z => p z * X z) (deriv (fun z => p z * X z) r) r :=
      ((hpglob r).mul (hXglob r)).differentiableAt.hasDerivAt
    have hGglob (r : ℝ) : HasDerivAt (fun z => q z * X z) (deriv (fun z => q z * X z) r) r :=
      ((hqglob r).mul (hXglob r)).differentiableAt.hasDerivAt
    obtain ⟨_, _, _, _, _, hW2⟩ := odd_even_calculus _ _ hFglob hGglob u _ _ hFF hGG hF1 hG1 hF2 hG2
    have hWeq : (fun r : ℝ => (r : ℂ) * ((p r * X r + q r * X r) / 2)) =
        (fun r : ℝ => (r : ℂ) * ((p r + q r) / 2 * X r)) := by funext r; ring
    rw [hWeq] at hW2
    refine hW2.trans ?_
    calc
      _ = G * (9 * (T * |u| * (1 + T * u ^ 2)) + (4 + 4 * K) * Q + 3 * K * (1 / |u|)) := by
        dsimp [H]
        rw [← sq_abs u]
        field_simp
        ring
      _ ≤ G * (100 * K * (T * |u| * (1 + T * u ^ 2)) + 100 * K * Q + 100 * K * (1 / |u|)) := by
        gcongr <;> nlinarith only [hK1]
      _ = _ := by ring

end Shao.Probability
