import Shao.Probability.QuadraticCharacteristic
import Mathlib.Probability.Moments.Variance

/-!
The actual centered quadratic characteristic integral and the two sharp
derivative bounds used in supplement 3358–3367. Centering affects the linear
frequency only; the quadratic phase remains the square of the original variable.
-/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

noncomputable def centeredQuadraticChar (ν : Measure ℝ) (u v : ℝ) : ℂ :=
  Complex.exp (-(((u * ∫ a : ℝ, a ∂ν : ℝ) : ℂ) * Complex.I)) *
    quadraticChar ν u v

private noncomputable def phase (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * Complex.I)

private lemma phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private lemma phase_continuous : Continuous phase := by
  unfold phase
  fun_prop

private lemma phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp [phase, add_mul, Complex.exp_add]

private lemma exp_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {S Q : ℝ → ℝ} (hS : Measurable S) (hQ : Measurable Q) (u v : ℝ) :
    Integrable (fun a => phase (u * S a + v * Q a)) ν := by
  exact (integrable_const (1 : ℝ)).mono'
    (phase_continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => (phase_norm _).le)

private lemma weighted_integrable {ν : Measure ℝ} {S Q g : ℝ → ℝ}
    (hS : Measurable S) (hQ : Measurable Q) (hg : Integrable g ν) (u v : ℝ) :
    Integrable (fun a => (g a : ℂ) * phase (u * S a + v * Q a)) ν := by
  refine hg.norm.mono' ((hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
    (phase_continuous.measurable.comp (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => ?_)
  simp only [norm_mul, phase_norm, mul_one, Complex.norm_real]
  exact le_rfl

private lemma exp_hasDerivAt (S Q r v : ℝ) :
    HasDerivAt (fun s : ℝ => phase (s * S + v * Q))
      (Complex.I * (S : ℂ) * phase (r * S + v * Q)) r := by
  unfold phase
  convert (((((hasDerivAt_id r).mul_const S).add_const (v * Q)).ofReal_comp).mul_const
    Complex.I).cexp using 1
  all_goals try funext x
  all_goals try dsimp
  all_goals push_cast
  all_goals ring

private lemma exp_integral_hasDerivAt {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {S Q : ℝ → ℝ} (hS : Measurable S) (hQ : Measurable Q)
    (hS2 : MemLp S 2 ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ a, phase (r * S a + v * Q a) ∂ν)
      (Complex.I * ∫ a, (S a : ℂ) * phase (u * S a + v * Q a) ∂ν) u := by
  have h1 : Integrable S ν := hS2.integrable (by norm_num)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun r a => Complex.I * ((S a : ℂ) * phase (r * S a + v * Q a)))
    (bound := fun a => |S a|) (by simp)
    (Filter.Eventually.of_forall fun r => (exp_integrable hS hQ r v).aestronglyMeasurable)
    (exp_integrable hS hQ u v)
    ((weighted_integrable hS hQ h1 u v).const_mul Complex.I).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a r _ => by
      simp only [norm_mul, Complex.norm_I, one_mul, phase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      exact le_rfl) h1.abs
    (Filter.Eventually.of_forall fun a r _ => by
      simpa only [mul_assoc] using exp_hasDerivAt (S a) (Q a) r v)).2
  simpa only [integral_const_mul] using hd

private lemma weighted_integral_hasDerivAt {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {S Q : ℝ → ℝ} (hS : Measurable S) (hQ : Measurable Q)
    (hS2 : MemLp S 2 ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ a, (S a : ℂ) * phase (r * S a + v * Q a) ∂ν)
      (Complex.I * ∫ a, ((S a ^ 2 : ℝ) : ℂ) * phase (u * S a + v * Q a) ∂ν) u := by
  have h1 : Integrable S ν := hS2.integrable (by norm_num)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ)
    (F' := fun r a => Complex.I * (((S a ^ 2 : ℝ) : ℂ) * phase (r * S a + v * Q a)))
    (bound := fun a => S a ^ 2) (by simp)
    (Filter.Eventually.of_forall fun r => (weighted_integrable hS hQ h1 r v).aestronglyMeasurable)
    (weighted_integrable hS hQ h1 u v)
    ((weighted_integrable hS hQ hS2.integrable_sq u v).const_mul Complex.I).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a r _ => by
      simp only [norm_mul, Complex.norm_I, one_mul, phase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S a))]
      exact le_rfl) hS2.integrable_sq
    (Filter.Eventually.of_forall fun a r _ => by
      convert (exp_hasDerivAt (S a) (Q a) r v).const_mul (S a : ℂ) using 1
      push_cast
      ring)).2
  simpa only [integral_const_mul] using hd

private noncomputable def center (ν : Measure ℝ) (a : ℝ) : ℝ :=
  a - ∫ b : ℝ, b ∂ν

private lemma center_measurable (ν : Measure ℝ) : Measurable (center ν) := by
  unfold center
  fun_prop

private lemma center_memLp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) : MemLp (center ν) 2 ν := by
  exact ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2).sub
    (memLp_const _)

theorem centeredQuadraticChar_eq_integral (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    centeredQuadraticChar ν u v =
      ∫ a : ℝ, Complex.exp
        (((u * (a - ∫ b : ℝ, b ∂ν) + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν := by
  have hp : Complex.exp (-(((u * ∫ a : ℝ, a ∂ν : ℝ) : ℂ) * Complex.I)) =
      phase (-(u * ∫ a : ℝ, a ∂ν)) := by simp [phase]
  unfold centeredQuadraticChar quadraticChar
  rw [hp]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    change phase (-(u * ∫ a : ℝ, a ∂ν)) * phase (u * a + v * a ^ 2) =
      phase (u * (a - ∫ b : ℝ, b ∂ν) + v * a ^ 2)
    rw [← phase_add]
    congr 1
    ring

theorem norm_centeredQuadraticChar (ν : Measure ℝ) (u v : ℝ) :
    ‖centeredQuadraticChar ν u v‖ = ‖quadraticChar ν u v‖ := by
  simp [centeredQuadraticChar, Complex.norm_exp, Complex.mul_re]

theorem centeredQuadraticChar_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt (fun r : ℝ => centeredQuadraticChar ν r v)
      (Complex.I * ∫ a : ℝ, ((a - ∫ b : ℝ, b ∂ν : ℝ) : ℂ) *
        Complex.exp
          (((u * (a - ∫ b : ℝ, b ∂ν) + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν) u := by
  exact (exp_integral_hasDerivAt (Q := fun a : ℝ => a ^ 2) (center_measurable ν) (by fun_prop)
    (center_memLp ν h2) u v).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => centeredQuadraticChar_eq_integral ν r v)

theorem centeredQuadraticChar_deriv_hasDerivAt (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    HasDerivAt
      (fun r : ℝ => deriv (fun s : ℝ => centeredQuadraticChar ν s v) r)
      (-(∫ a : ℝ, (((a - ∫ b : ℝ, b ∂ν) ^ 2 : ℝ) : ℂ) *
        Complex.exp
          (((u * (a - ∫ b : ℝ, b ∂ν) + v * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν)) u := by
  have hd := (weighted_integral_hasDerivAt (Q := fun a : ℝ => a ^ 2)
    (center_measurable ν) (by fun_prop)
    (center_memLp ν h2) u v).const_mul Complex.I
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul] at hd
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => (centeredQuadraticChar_hasDerivAt ν h2 r v).deriv)

theorem quadraticChar_centered_second_moment (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) :
    (∫ a : ℝ, (a - ∫ b : ℝ, b ∂ν) ^ 2 ∂ν) = variance (id : ℝ → ℝ) ν := by
  exact (variance_eq_integral
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2).aemeasurable).symm

private lemma unit_phase_variance {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {E : ℝ → ℂ} (hE : Integrable E ν) (hn : ∀ a, ‖E a‖ = 1) :
    (∫ a, ‖E a - ∫ b, E b ∂ν‖ ^ 2 ∂ν) = 1 - ‖∫ b, E b ∂ν‖ ^ 2 := by
  let c : ℂ := ∫ b, E b ∂ν
  change (∫ a, ‖E a - c‖ ^ 2 ∂ν) = 1 - ‖c‖ ^ 2
  have hi : Integrable (fun a => (E a * (starRingEnd ℂ) c).re) ν :=
    (hE.mul_const _).re
  have hp (a : ℝ) : ‖E a - c‖ ^ 2 =
      1 - 2 * (E a * (starRingEnd ℂ) c).re + ‖c‖ ^ 2 := by
    have hnorm : ‖E a‖ ^ 2 = 1 := by rw [hn]; norm_num
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im] at *
    nlinarith [hnorm]
  simp_rw [hp]
  have htwo : Integrable (fun a => 2 * (E a * (starRingEnd ℂ) c).re) ν := hi.const_mul 2
  have hsub : Integrable (fun a => 1 - 2 * (E a * (starRingEnd ℂ) c).re) ν :=
    (integrable_const (1 : ℝ)).sub htwo
  have hr : (∫ a, (E a * (starRingEnd ℂ) c).re ∂ν) =
      (c * (starRingEnd ℂ) c).re := by
    have h := integral_re (hE.mul_const ((starRingEnd ℂ) c))
    change (∫ a, (E a * (starRingEnd ℂ) c).re ∂ν) =
      (∫ a, E a * (starRingEnd ℂ) c ∂ν).re at h
    rw [integral_mul_const] at h
    exact h
  rw [integral_add hsub (integrable_const (‖c‖ ^ 2)),
    integral_sub (integrable_const (1 : ℝ)) htwo,
    integral_const_mul, hr]
  have hprob : ν.real Set.univ = 1 := by simp
  simp only [integral_const, hprob, one_smul]
  change 1 - 2 * (c * (starRingEnd ℂ) c).re + ‖c‖ ^ 2 = 1 - ‖c‖ ^ 2
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  ring

theorem quadraticChar_phase_variance (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (u v : ℝ) :
    (∫ a : ℝ, ‖Complex.exp
      (((u * a + v * a ^ 2 : ℝ) : ℂ) * Complex.I) - quadraticChar ν u v‖ ^ 2 ∂ν) =
      1 - ‖quadraticChar ν u v‖ ^ 2 := by
  exact unit_phase_variance (exp_integrable measurable_id (by fun_prop) u v)
    (fun a => phase_norm _)

private lemma covariance_bound {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {C : ℝ → ℝ} {E : ℝ → ℂ} (hC : MemLp C 2 ν)
    (hC0 : (∫ a, C a ∂ν) = 0) (hE : MemLp E 2 ν)
    (hCE : Integrable (fun a => (C a : ℂ) * E a) ν) :
    ‖∫ a, (C a : ℂ) * E a ∂ν‖ ≤
      Real.sqrt (∫ a, C a ^ 2 ∂ν) *
        Real.sqrt (∫ a, ‖E a - ∫ b, E b ∂ν‖ ^ 2 ∂ν) := by
  let c : ℂ := ∫ b, E b ∂ν
  have h1 := hC.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hcint : (∫ a, (C a : ℂ) * c ∂ν) = 0 := by
    rw [integral_mul_const, integral_complex_ofReal, hC0]
    simp
  have heq : (∫ a, (C a : ℂ) * E a ∂ν) =
      ∫ a, (C a : ℂ) * (E a - c) ∂ν := by
    calc
      _ = (∫ a, (C a : ℂ) * E a ∂ν) - ∫ a, (C a : ℂ) * c ∂ν := by
        rw [hcint, sub_zero]
      _ = ∫ a, (C a : ℂ) * E a - (C a : ℂ) * c ∂ν :=
        (integral_sub hCE ((h1.ofReal (𝕜 := ℂ)).mul_const c)).symm
      _ = _ := by congr 1; funext a; ring
  have hG : MemLp (fun a => E a - c) 2 ν := hE.sub (memLp_const c)
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      (2 : ℝ).HolderConjugate 2)
    (by simpa using hC) (by simpa using hG.norm)
  rw [heq]
  refine (norm_integral_le_integral_norm _).trans ?_
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_norm, abs_norm,
    Real.rpow_two, ← Real.sqrt_eq_rpow, sq_abs] using hh

theorem centeredQuadraticChar_derivative_bounds (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν) (u v : ℝ) :
    ‖deriv (fun r : ℝ => centeredQuadraticChar ν r v) u‖ ≤
        Real.sqrt (variance (id : ℝ → ℝ) ν) *
          Real.sqrt (1 - ‖quadraticChar ν u v‖ ^ 2) ∧
      ‖deriv (fun r : ℝ => deriv (fun s : ℝ => centeredQuadraticChar ν s v) r) u‖ ≤
        variance (id : ℝ → ℝ) ν := by
  let E : ℝ → ℂ := fun a => phase (u * center ν a + v * a ^ 2)
  have hC := center_memLp ν h2
  have hEint : Integrable E ν := exp_integrable (center_measurable ν) (by fun_prop) u v
  have hCE := weighted_integrable (Q := fun a : ℝ => a ^ 2) (center_measurable ν) (by fun_prop)
    (hC.integrable (by norm_num)) u v
  have hC0 : (∫ a, center ν a ∂ν) = 0 := by
    have h1 : Integrable (fun a : ℝ => a) ν :=
      ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr h2).integrable
        (by norm_num)
    change (∫ a : ℝ, a - ∫ b : ℝ, b ∂ν ∂ν) = 0
    rw [integral_sub h1 (integrable_const _)]
    simp
  have hEsq : MemLp E 2 ν := MemLp.of_bound hEint.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun a => (phase_norm _).le)
  have hcv := covariance_bound hC hC0 hEsq hCE
  have hV : (∫ a, center ν a ^ 2 ∂ν) = variance (id : ℝ → ℝ) ν :=
    quadraticChar_centered_second_moment ν h2
  have hEv := unit_phase_variance hEint (fun a => phase_norm _)
  have hEi : (∫ a, E a ∂ν) = centeredQuadraticChar ν u v :=
    (centeredQuadraticChar_eq_integral ν u v).symm
  rw [hV, hEv, hEi, norm_centeredQuadraticChar] at hcv
  constructor
  · rw [(centeredQuadraticChar_hasDerivAt ν h2 u v).deriv,
      norm_mul, Complex.norm_I, one_mul]
    exact hcv
  · rw [(centeredQuadraticChar_deriv_hasDerivAt ν h2 u v).deriv, norm_neg, ← hV]
    exact norm_integral_le_of_norm_le hC.integrable_sq
      (Filter.Eventually.of_forall fun a => by
        change ‖((center ν a ^ 2 : ℝ) : ℂ) *
          phase (u * center ν a + v * a ^ 2)‖ ≤ center ν a ^ 2
        simp only [norm_mul, phase_norm, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (center ν a))]
        exact le_rfl)

end Shao.Probability
