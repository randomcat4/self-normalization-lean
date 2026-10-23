import Shao.Probability.SourceFutureNoiseInversion

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped Topology

private def reflect (ξ : ℝ × ℝ) : ℝ × ℝ := (-ξ.1, ξ.2)

private lemma reflect_preserving :
    MeasurePreserving reflect (volume : Measure (ℝ × ℝ)) volume := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure ℝ))

private lemma reflect_integral (F : (ℝ × ℝ) → ℂ) :
    (∫ ξ : ℝ × ℝ, F (reflect ξ)) = ∫ ξ : ℝ × ℝ, F ξ := by
  exact reflect_preserving.integral_comp
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding F

private noncomputable def phase (w q : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  Complex.exp (((ξ.1 * w + ξ.2 * q : ℝ) : ℂ) * Complex.I)

private noncomputable def cosPhase (w q : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) * (Real.cos (ξ.1 * w) : ℂ)

private lemma phase_norm (w q : ℝ) (ξ : ℝ × ℝ) : ‖phase w q ξ‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private lemma cosPhase_norm_le (w q : ℝ) (ξ : ℝ × ℝ) : ‖cosPhase w q ξ‖ ≤ 1 := by
  simp only [cosPhase, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero,
    Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

private lemma phase_sum (w q : ℝ) (ξ : ℝ × ℝ) :
    phase w q ξ + phase (-w) q ξ = 2 * cosPhase w q ξ := by
  have he (r : ℝ) : phase r q ξ =
      Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((ξ.1 * r : ℝ) : ℂ) * Complex.I) := by
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he w, he (-w)]
  have hn : (((ξ.1 * -w : ℝ) : ℂ) * Complex.I) =
      -(((ξ.1 * w : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  rw [hn, ← mul_add, ← Complex.two_cos, ← Complex.ofReal_cos]
  dsimp [cosPhase]
  ring

private lemma cosPhase_reflect (w q : ℝ) (ξ : ℝ × ℝ) :
    cosPhase w q (reflect ξ) = cosPhase w q ξ := by
  simp [cosPhase, reflect, neg_mul, Real.cos_neg]

private lemma bounded_mul_integrable (F : (ℝ × ℝ) → ℂ) (hF : Integrable F)
    (A : (ℝ × ℝ) → ℂ) (hA : Continuous A) (hAb : ∀ ξ, ‖A ξ‖ ≤ 1) :
    Integrable (fun ξ => A ξ * F ξ) := by
  refine hF.norm.mono' (hA.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  simpa only [norm_mul, one_mul] using mul_le_mul_of_nonneg_right (hAb ξ) (norm_nonneg (F ξ))

private lemma phase_moment_integrable (F : (ℝ × ℝ) → ℂ) (k : ℕ)
    (hF : Integrable (fun ξ : ℝ × ℝ => (ξ.1 : ℂ) ^ k * F ξ)) (w q : ℝ) :
    Integrable (fun ξ : ℝ × ℝ => (Complex.I * (ξ.1 : ℂ)) ^ k * phase w q ξ * F ξ) := by
  have hi := (bounded_mul_integrable _ hF (phase w q) (by unfold phase; fun_prop)
    (fun ξ => (phase_norm w q ξ).le)).const_mul (Complex.I ^ k)
  convert hi using 1
  funext ξ
  rw [mul_pow]
  ring

private noncomputable def markedMoment (F : (ℝ × ℝ) → ℂ) (k : ℕ)
    (w q : ℝ) (ξ : ℝ × ℝ) : ℂ := (ξ.1 : ℂ) ^ k * cosPhase w q ξ * F ξ

private lemma markedMoment_integrable (F : (ℝ × ℝ) → ℂ) (k : ℕ)
    (hF : Integrable (fun ξ : ℝ × ℝ => (ξ.1 : ℂ) ^ k * F ξ)) (w q : ℝ) :
    Integrable (markedMoment F k w q) := by
  have hi := bounded_mul_integrable _ hF (cosPhase w q) (by unfold cosPhase; fun_prop)
    (cosPhase_norm_le w q)
  convert hi using 1
  funext ξ
  dsimp [markedMoment]
  ring

private lemma reflected_moment_integrable (F : (ℝ × ℝ) → ℂ) (k : ℕ)
    (hF : Integrable (fun ξ : ℝ × ℝ => (ξ.1 : ℂ) ^ k * F ξ)) :
    Integrable (fun ξ : ℝ × ℝ => (ξ.1 : ℂ) ^ k * F (reflect ξ)) := by
  have hi := reflect_preserving.integrable_comp_of_integrable hF
  have hj := hi.const_mul ((-1 : ℂ) ^ k)
  convert hj using 1
  funext ξ
  change (ξ.1 : ℂ) ^ k * F (reflect ξ) =
    (-1 : ℂ) ^ k * (((-ξ.1 : ℝ) : ℂ) ^ k * F (reflect ξ))
  have hn : ((-ξ.1 : ℝ) : ℂ) = (-1 : ℂ) * (ξ.1 : ℂ) := by push_cast; ring
  rw [hn, mul_pow]
  have he : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((ξ.1 : ℂ) ^ k * F (reflect ξ)) := by
      rw [he]; ring
    _ = _ := by ring

private lemma markedMoment_reflect_integral (F : (ℝ × ℝ) → ℂ) (k : ℕ) (w q : ℝ) :
    (∫ ξ : ℝ × ℝ, markedMoment (fun ζ => F (reflect ζ)) k w q ξ) =
      (-1 : ℂ) ^ k * ∫ ξ : ℝ × ℝ, markedMoment F k w q ξ := by
  rw [← reflect_integral (markedMoment F k w q), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only [markedMoment]
    rw [cosPhase_reflect]
    change (ξ.1 : ℂ) ^ k * cosPhase w q ξ * F (reflect ξ) =
      (-1 : ℂ) ^ k * (((-ξ.1 : ℝ) : ℂ) ^ k * cosPhase w q ξ * F (reflect ξ))
    rw [Complex.ofReal_neg, neg_eq_neg_one_mul, mul_pow]
    have he : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
          ((ξ.1 : ℂ) ^ k * cosPhase w q ξ * F (reflect ξ)) := by rw [he]; ring
      _ = _ := by ring

private lemma phase_moment_sum (F : (ℝ × ℝ) → ℂ) (k : ℕ)
    (hF : Integrable (fun ξ : ℝ × ℝ => (ξ.1 : ℂ) ^ k * F ξ)) (w q : ℝ) :
    (∫ ξ : ℝ × ℝ, (Complex.I * (ξ.1 : ℂ)) ^ k * phase w q ξ * F ξ) +
      (∫ ξ : ℝ × ℝ, (Complex.I * (ξ.1 : ℂ)) ^ k * phase (-w) q ξ * F ξ) =
      2 * Complex.I ^ k * ∫ ξ : ℝ × ℝ, markedMoment F k w q ξ := by
  rw [← integral_add (phase_moment_integrable F k hF w q)
    (phase_moment_integrable F k hF (-w) q), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp [markedMoment]
    rw [show (Complex.I * (ξ.1 : ℂ)) ^ k = Complex.I ^ k * (ξ.1 : ℂ) ^ k by rw [mul_pow]]
    calc
      _ = Complex.I ^ k * (ξ.1 : ℂ) ^ k * (phase w q ξ + phase (-w) q ξ) * F ξ := by ring
      _ = _ := by rw [phase_sum]; ring

private lemma testTransform_even (y : ℝ) (hy : 0 ≤ y) (u v : ℝ) :
    sourceFourierTestTransform y (-u) v = sourceFourierTestTransform y u v := by
  rw [sourceFourierTestTransform_eq y hy, sourceFourierTestTransform_eq y hy]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    by_cases hu : u = 0
    · simp [hu]
    · simp [hu, neg_ne_zero.mpr hu, neg_mul, Real.sin_neg]

private lemma testTransform_mark (y : ℝ) (hy : 0 ≤ y) (u v : ℝ) :
    (u : ℂ) * sourceFourierTestTransform y u v =
      2 * sourceMarkSine sourceKernelCutoff y u 0 v := by
  rw [sourceFourierTestTransform_eq y hy, sourceMarkSine, ← integral_const_mul,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    by_cases hu : u = 0
    · simp [hu]
    · have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
      simp only [ite_eq_right hu, add_zero]
      push_cast
      field_simp [huC]

private lemma odd_mark_identity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (w q : ℝ) (ξ : ℝ × ℝ) :
    cosPhase w q ξ * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 *
      (((quadraticChar ν ξ.1 ξ.2) ^ m - (quadraticChar ν (-ξ.1) ξ.2) ^ m) / 2 *
        quadraticFullNoiseChar ν ξ.1 ξ.2) =
    (1 / 4 : ℂ) *
      (markedMoment (fun ζ => sourceFutureNoiseKernelTransform ν m y ζ.1 ζ.2) 1 w q ξ -
        markedMoment (fun ζ => sourceFutureNoiseKernelTransform ν m y (reflect ζ).1
          (reflect ζ).2) 1 w q ξ) := by
  dsimp [markedMoment, reflect]
  rw [sourceFutureNoiseKernelTransform_factor ν h3 hV h hh hs m y hy,
    sourceFutureNoiseKernelTransform_factor ν h3 hV h hh hs m y hy,
    testTransform_even y hy,
    (quadraticFullNoiseChar_product ν h3 hV h hh hs ξ.1 ξ.2).2.1]
  have hb := testTransform_mark y hy ξ.1 ξ.2
  simp only [pow_one]
  linear_combination
    (-cosPhase w q ξ *
      ((quadraticChar ν ξ.1 ξ.2) ^ m - (quadraticChar ν (-ξ.1) ξ.2) ^ m) *
        quadraticFullNoiseChar ν ξ.1 ξ.2 / 4) * hb

private lemma even_mark_identity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (w q : ℝ) (ξ : ℝ × ℝ) :
    cosPhase w q ξ * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * (ξ.1 : ℂ) *
      (((quadraticChar ν ξ.1 ξ.2) ^ m + (quadraticChar ν (-ξ.1) ξ.2) ^ m) / 2 *
        quadraticFullNoiseChar ν ξ.1 ξ.2) =
    (1 / 4 : ℂ) *
      (markedMoment (fun ζ => sourceFutureNoiseKernelTransform ν m y ζ.1 ζ.2) 2 w q ξ +
        markedMoment (fun ζ => sourceFutureNoiseKernelTransform ν m y (reflect ζ).1
          (reflect ζ).2) 2 w q ξ) := by
  dsimp [markedMoment, reflect]
  rw [sourceFutureNoiseKernelTransform_factor ν h3 hV h hh hs m y hy,
    sourceFutureNoiseKernelTransform_factor ν h3 hV h hh hs m y hy,
    testTransform_even y hy,
    (quadraticFullNoiseChar_product ν h3 hV h hh hs ξ.1 ξ.2).2.1]
  have hb := testTransform_mark y hy ξ.1 ξ.2
  linear_combination
    (-cosPhase w q ξ * (ξ.1 : ℂ) *
      ((quadraticChar ν ξ.1 ξ.2) ^ m + (quadraticChar ν (-ξ.1) ξ.2) ^ m) *
        quadraticFullNoiseChar ν ξ.1 ξ.2 / 4) * hb

private lemma odd_hasDerivAt (f : ℝ → ℝ) (hf : ∀ r, DifferentiableAt ℝ f r) (w : ℝ) :
    HasDerivAt (fun r => (f r - f (-r)) / 2)
      ((deriv f w + deriv f (-w)) / 2) w := by
  have hd : HasDerivAt (fun r => (f r - f (-r)) / 2)
      ((deriv f w - deriv f (-w) * (-1)) / 2) w :=
    ((hf w).hasDerivAt.sub
      ((hf (-w)).hasDerivAt.comp w (hasDerivAt_id w).neg)).div_const 2
  convert hd using 1
  ring

private lemma even_hasDerivAt (f : ℝ → ℝ) (hf : ∀ r, DifferentiableAt ℝ f r) (w : ℝ) :
    HasDerivAt (fun r => (f r + f (-r)) / 2)
      ((deriv f w - deriv f (-w)) / 2) w := by
  have hd : HasDerivAt (fun r => (f r + f (-r)) / 2)
      ((deriv f w + deriv f (-w) * (-1)) / 2) w :=
    ((hf w).hasDerivAt.add
      ((hf (-w)).hasDerivAt.comp w (hasDerivAt_id w).neg)).div_const 2
  convert hd using 1
  ring

private lemma even_second_hasDerivAt (f : ℝ → ℝ)
    (hf : ∀ r, DifferentiableAt ℝ f r) (hff : ∀ r, DifferentiableAt ℝ (deriv f) r)
    (w : ℝ) :
    HasDerivAt (fun r => deriv (fun s => (f s + f (-s)) / 2) r)
      ((deriv (deriv f) w + deriv (deriv f) (-w)) / 2) w := by
  have he : (fun r => deriv (fun s => (f s + f (-s)) / 2) r) =
      fun r => (deriv f r - deriv f (-r)) / 2 :=
    funext fun r => (even_hasDerivAt f hf r).deriv
  rw [he]
  exact odd_hasDerivAt (deriv f) hff w

theorem sourceFutureNoiseKernel_odd_derivative_inverse
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (w q : ℝ) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let o : ℝ → ℝ := fun r => (f r - f (-r)) / 2
    let D : ℝ × ℝ → ℂ := fun ξ =>
      ((quadraticChar ν ξ.1 ξ.2) ^ m - (quadraticChar ν (-ξ.1) ξ.2) ^ m) / 2 *
        quadraticFullNoiseChar ν ξ.1 ξ.2
    let G : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        (Real.cos (ξ.1 * w) : ℂ) * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * D ξ
    DifferentiableAt ℝ o w ∧ Integrable G (volume : Measure (ℝ × ℝ)) ∧
      ((deriv o w : ℝ) : ℂ) =
        (2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) * ∫ ξ : ℝ × ℝ, G ξ := by
  let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
  let F : (ℝ × ℝ) → ℂ := fun ξ => sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2
  let G : (ℝ × ℝ) → ℂ := fun ξ =>
    cosPhase w q ξ * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 *
      (((quadraticChar ν ξ.1 ξ.2) ^ m - (quadraticChar ν (-ξ.1) ξ.2) ^ m) / 2 *
        quadraticFullNoiseChar ν ξ.1 ξ.2)
  change DifferentiableAt ℝ (fun r => (f r - f (-r)) / 2) w ∧
    Integrable G ∧ _
  have hf (r : ℝ) := sourceFutureNoiseKernel_spatial_derivatives ν h3 hV h hh hs m y hy r q
  have hod := odd_hasDerivAt f (fun r => (hf r).1) w
  have hM := sourceFutureNoiseKernelTransform_moment_integrable ν h3 hV h hh hs m y hy 1
  have hL := markedMoment_integrable F 1 hM w q
  have hR := markedMoment_integrable (fun ξ => F (reflect ξ)) 1
    (reflected_moment_integrable F 1 hM) w q
  have hGe : G = fun ξ => (1 / 4 : ℂ) *
      (markedMoment F 1 w q ξ - markedMoment (fun ζ => F (reflect ζ)) 1 w q ξ) := by
    funext ξ
    exact odd_mark_identity ν h3 hV h hh hs m y hy w q ξ
  have hGi : Integrable G := by
    rw [hGe]
    exact (hL.sub hR).const_mul _
  have hGint : (∫ ξ : ℝ × ℝ, G ξ) = (1 / 2 : ℂ) *
      ∫ ξ : ℝ × ℝ, markedMoment F 1 w q ξ := by
    rw [hGe, integral_const_mul, integral_sub hL hR, markedMoment_reflect_integral]
    norm_num
    ring
  have hder : ((deriv (fun r => (f r - f (-r)) / 2) w : ℝ) : ℂ) =
      ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) * Complex.I *
        ∫ ξ : ℝ × ℝ, markedMoment F 1 w q ξ := by
    rw [hod.deriv]
    push_cast
    rw [(hf w).2.2.1, (hf (-w)).2.2.1]
    change (_ * (∫ ξ, (Complex.I * (ξ.1 : ℂ)) ^ 1 * phase w q ξ * F ξ) +
      _ * (∫ ξ, (Complex.I * (ξ.1 : ℂ)) ^ 1 * phase (-w) q ξ * F ξ)) / 2 = _
    rw [← mul_add, phase_moment_sum F 1 hM w q]
    norm_num
    ring
  refine ⟨hod.differentiableAt, hGi, ?_⟩
  change ((deriv (fun r => (f r - f (-r)) / 2) w : ℝ) : ℂ) =
    (2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) * ∫ ξ : ℝ × ℝ, G ξ
  rw [hder, hGint]
  ring

theorem sourceFutureNoiseKernel_even_second_inverse
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (w q : ℝ) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let e : ℝ → ℝ := fun r => (f r + f (-r)) / 2
    let E : ℝ × ℝ → ℂ := fun ξ =>
      ((quadraticChar ν ξ.1 ξ.2) ^ m + (quadraticChar ν (-ξ.1) ξ.2) ^ m) / 2 *
        quadraticFullNoiseChar ν ξ.1 ξ.2
    let G : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        (Real.cos (ξ.1 * w) : ℂ) * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 *
          (ξ.1 : ℂ) * E ξ
    DifferentiableAt ℝ e w ∧ DifferentiableAt ℝ (fun r : ℝ => deriv e r) w ∧
      Integrable G (volume : Measure (ℝ × ℝ)) ∧
      ((deriv (fun r : ℝ => deriv e r) w : ℝ) : ℂ) =
        (-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) * ∫ ξ : ℝ × ℝ, G ξ := by
  let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
  let F : (ℝ × ℝ) → ℂ := fun ξ => sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2
  let G : (ℝ × ℝ) → ℂ := fun ξ =>
    cosPhase w q ξ * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * (ξ.1 : ℂ) *
      (((quadraticChar ν ξ.1 ξ.2) ^ m + (quadraticChar ν (-ξ.1) ξ.2) ^ m) / 2 *
        quadraticFullNoiseChar ν ξ.1 ξ.2)
  change DifferentiableAt ℝ (fun r => (f r + f (-r)) / 2) w ∧
    DifferentiableAt ℝ (fun r => deriv (fun s => (f s + f (-s)) / 2) r) w ∧
    Integrable G ∧ _
  have hf (r : ℝ) := sourceFutureNoiseKernel_spatial_derivatives ν h3 hV h hh hs m y hy r q
  have hed := even_hasDerivAt f (fun r => (hf r).1) w
  have hedd := even_second_hasDerivAt f (fun r => (hf r).1) (fun r => (hf r).2.1) w
  have hM := sourceFutureNoiseKernelTransform_moment_integrable ν h3 hV h hh hs m y hy 2
  have hL := markedMoment_integrable F 2 hM w q
  have hR := markedMoment_integrable (fun ξ => F (reflect ξ)) 2
    (reflected_moment_integrable F 2 hM) w q
  have hGe : G = fun ξ => (1 / 4 : ℂ) *
      (markedMoment F 2 w q ξ + markedMoment (fun ζ => F (reflect ζ)) 2 w q ξ) := by
    funext ξ
    exact even_mark_identity ν h3 hV h hh hs m y hy w q ξ
  have hGi : Integrable G := by
    rw [hGe]
    exact (hL.add hR).const_mul _
  have hGint : (∫ ξ : ℝ × ℝ, G ξ) = (1 / 2 : ℂ) *
      ∫ ξ : ℝ × ℝ, markedMoment F 2 w q ξ := by
    rw [hGe, integral_const_mul, integral_add hL hR, markedMoment_reflect_integral]
    norm_num
    ring
  have hder : ((deriv (fun r => deriv (fun s => (f s + f (-s)) / 2) r) w : ℝ) : ℂ) =
      -((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
        ∫ ξ : ℝ × ℝ, markedMoment F 2 w q ξ := by
    rw [hedd.deriv]
    push_cast
    rw [(hf w).2.2.2, (hf (-w)).2.2.2]
    change (_ * (∫ ξ, (Complex.I * (ξ.1 : ℂ)) ^ 2 * phase w q ξ * F ξ) +
      _ * (∫ ξ, (Complex.I * (ξ.1 : ℂ)) ^ 2 * phase (-w) q ξ * F ξ)) / 2 = _
    rw [← mul_add, phase_moment_sum F 2 hM w q]
    norm_num [Complex.I_sq]
    ring
  refine ⟨hed.differentiableAt, hedd.differentiableAt, hGi, ?_⟩
  change ((deriv (fun r => deriv (fun s => (f s + f (-s)) / 2) r) w : ℝ) : ℂ) =
    (-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) * ∫ ξ : ℝ × ℝ, G ξ
  rw [hder, hGint]
  ring

end Shao.Probability
