import Shao.Probability.SourceFourierTestKernel
import Shao.Probability.QuadraticFullNoise
import Shao.Probability.QuadraticCharacteristic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual positive-shift future/noise kernel and its source-normalized transform. -/

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

noncomputable def sourceFutureNoiseKernel (ν : Measure ℝ) (m : ℕ)
    (y : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ a : Shao.Path m, ∫ z : ℝ × ℝ,
    sourceFourierTest y
      (p.1 + Shao.prefixSum a m + z.1, p.2 + Shao.energy a + z.2)
      ∂quadraticFullNoiseLaw ν
    ∂Measure.pi (fun _ : Fin m => ν)

noncomputable def sourceFutureNoiseKernelTransform (ν : Measure ℝ) (m : ℕ)
    (y u v : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, (sourceFutureNoiseKernel ν m y p : ℂ) *
    Complex.exp (-(((u * p.1 + v * p.2 : ℝ) : ℂ) * Complex.I))

private lemma test_measurable (y : ℝ) : Measurable (sourceFourierTest y) := by
  let A : Set (ℝ × ℝ) := {p | |p.1| < y * Real.sqrt p.2}
  have hA : MeasurableSet A := (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hc : Measurable (fun p : ℝ × ℝ => sourceKernelCutoff p.2) :=
    sourceKernelCutoff_data.1.continuous.measurable.comp measurable_snd
  have he : sourceFourierTest y = A.indicator (fun p => sourceKernelCutoff p.2) := by
    funext p
    by_cases h : p ∈ A <;> simp [sourceFourierTest, Set.indicator, A] at h ⊢
  rw [he]
  exact hc.indicator hA

private lemma test_norm_le_one (y : ℝ) (p : ℝ × ℝ) : ‖sourceFourierTest y p‖ ≤ 1 := by
  unfold sourceFourierTest
  split_ifs
  · simpa only [mul_one, Real.norm_eq_abs,
      abs_of_nonneg (sourceKernelCutoff_data.2.2.1 p.2).1] using
      (sourceKernelCutoff_data.2.2.1 p.2).2
  · simp

private lemma pair_volume_rightInvariant :
    (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

private lemma shifted_joint_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : Ω → ℝ × ℝ} (hb : Measurable b) (y : ℝ) (hy : 0 ≤ y) :
    Integrable (fun q : Ω × (ℝ × ℝ) => sourceFourierTest y (q.2 + b q.1))
      (μ.prod volume) := by
  letI : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := pair_volume_rightInvariant
  have hm : AEStronglyMeasurable
      (fun q : Ω × (ℝ × ℝ) => sourceFourierTest y (q.2 + b q.1)) (μ.prod volume) :=
    ((test_measurable y).comp (measurable_snd.add (hb.comp measurable_fst))).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall fun ω =>
      (sourceFourierTest_integrable y hy).comp_add_right (b ω)
  · have he : (fun ω => ∫ p : ℝ × ℝ, ‖sourceFourierTest y (p + b ω)‖) =
        (fun _ : Ω => ∫ p : ℝ × ℝ, ‖sourceFourierTest y p‖) := by
      funext ω
      exact integral_add_right_eq_self
        (μ := (volume : Measure (ℝ × ℝ))) (fun p => ‖sourceFourierTest y p‖) (b ω)
    rw [he]
    exact integrable_const _

private noncomputable def futureShift (m : ℕ) (q : Shao.Path m × (ℝ × ℝ)) : ℝ × ℝ :=
  (Shao.prefixSum q.1 m + q.2.1, Shao.energy q.1 + q.2.2)

private lemma futureShift_measurable (m : ℕ) : Measurable (futureShift m) := by
  unfold futureShift Shao.prefixSum Shao.energy
  fun_prop

private lemma kernel_eq_joint (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] (m : ℕ) (y : ℝ) (p : ℝ × ℝ) :
    sourceFutureNoiseKernel ν m y p =
      ∫ q : Shao.Path m × (ℝ × ℝ), sourceFourierTest y (p + futureShift m q)
        ∂(Measure.pi (fun _ : Fin m => ν)).prod (quadraticFullNoiseLaw ν) := by
  have hi : Integrable (fun q : Shao.Path m × (ℝ × ℝ) =>
      sourceFourierTest y (p + futureShift m q))
      ((Measure.pi (fun _ : Fin m => ν)).prod (quadraticFullNoiseLaw ν)) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((test_measurable y).comp (measurable_const.add (futureShift_measurable m))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => test_norm_le_one y _)
  rw [integral_prod _ hi]
  unfold sourceFutureNoiseKernel
  congr 1
  funext a
  congr 1
  funext z
  congr 1
  ext
  · change p.1 + Shao.prefixSum a m + z.1 = p.1 + (Shao.prefixSum a m + z.1)
    ring
  · change p.2 + Shao.energy a + z.2 = p.2 + (Shao.energy a + z.2)
    ring

theorem sourceFutureNoiseKernel_integrable (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    Integrable (sourceFutureNoiseKernel ν m y) (volume : Measure (ℝ × ℝ)) := by
  have hp := (quadraticFullNoise_law_data ν h3 hV h hh hs).2.2.1
  haveI : IsProbabilityMeasure (quadraticFullNoiseLaw ν) := hp
  have hi := shifted_joint_integrable
    (μ := (Measure.pi (fun _ : Fin m => ν)).prod (quadraticFullNoiseLaw ν))
    (futureShift_measurable m) y hy
  exact hi.integral_prod_right.congr
    (Filter.Eventually.of_forall fun p => (kernel_eq_joint ν m y p).symm)

private def frequency (u v : ℝ) (p : ℝ × ℝ) : ℝ := u * p.1 + v * p.2

private noncomputable def negativePhase (t : ℝ) : ℂ :=
  Complex.exp (-((t : ℂ) * Complex.I))

private lemma negativePhase_norm (t : ℝ) : ‖negativePhase t‖ = 1 := by
  simp [negativePhase, Complex.norm_exp, Complex.mul_re]

private lemma negativePhase_continuous : Continuous negativePhase := by
  unfold negativePhase
  fun_prop

private lemma positive_shift_transform (y u v : ℝ) (b : ℝ × ℝ) :
    (∫ p : ℝ × ℝ, (sourceFourierTest y (p + b) : ℂ) *
      negativePhase (frequency u v p)) =
      Complex.exp (((frequency u v b : ℝ) : ℂ) * Complex.I) *
        sourceFourierTestTransform y u v := by
  letI : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := pair_volume_rightInvariant
  let f : (ℝ × ℝ) → ℂ := fun p => (sourceFourierTest y p : ℂ) *
    negativePhase (frequency u v p)
  have he : (fun p : ℝ × ℝ => (sourceFourierTest y (p + b) : ℂ) *
      negativePhase (frequency u v p)) =
      (fun p => Complex.exp (((frequency u v b : ℝ) : ℂ) * Complex.I) * f (p + b)) := by
    funext p
    dsimp [f]
    unfold negativePhase
    calc
      _ = (sourceFourierTest y (p + b) : ℂ) *
          Complex.exp (((frequency u v b : ℝ) : ℂ) * Complex.I +
            -(((frequency u v (p + b) : ℝ) : ℂ) * Complex.I)) := by
        congr 1
        congr 1
        dsimp [frequency]
        push_cast
        ring
      _ = _ := by rw [Complex.exp_add]; ring
  rw [he, integral_const_mul,
    integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ))) f b]
  rfl

private lemma averaged_transform
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : Ω → ℝ × ℝ} (hb : Measurable b) (y : ℝ) (hy : 0 ≤ y) (u v : ℝ) :
    (∫ p : ℝ × ℝ, ((∫ ω, sourceFourierTest y (p + b ω) ∂μ : ℝ) : ℂ) *
      negativePhase (frequency u v p)) =
      sourceFourierTestTransform y u v *
        ∫ ω, Complex.exp (((frequency u v (b ω) : ℝ) : ℂ) * Complex.I) ∂μ := by
  let J : Ω × (ℝ × ℝ) → ℂ := fun q =>
    (sourceFourierTest y (q.2 + b q.1) : ℂ) * negativePhase (frequency u v q.2)
  have hi := shifted_joint_integrable (μ := μ) hb y hy
  have hm : Measurable (fun q : Ω × (ℝ × ℝ) => negativePhase (frequency u v q.2)) := by
    apply negativePhase_continuous.measurable.comp
    unfold frequency
    fun_prop
  have hJ : Integrable J (μ.prod volume) := by
    refine hi.norm.mono' ((hi.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable) (Filter.Eventually.of_forall fun q => ?_)
    simp only [J, norm_mul, negativePhase_norm, mul_one, Complex.norm_real]
    exact le_rfl
  have he : (fun p : ℝ × ℝ =>
      ((∫ ω, sourceFourierTest y (p + b ω) ∂μ : ℝ) : ℂ) * negativePhase (frequency u v p)) =
      (fun p => ∫ ω, J (ω, p) ∂μ) := by
    funext p
    dsimp [J]
    rw [integral_mul_const, integral_complex_ofReal]
  rw [he, ← integral_prod_symm J hJ, integral_prod J hJ]
  dsimp only [J]
  simp_rw [positive_shift_transform]
  rw [integral_mul_const]
  ring

private lemma canonical_future_characteristic (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℕ) (u v : ℝ) :
    (∫ a : Shao.Path m, Complex.exp
      (((u * Shao.prefixSum a m + v * Shao.energy a : ℝ) : ℂ) * Complex.I)
      ∂Measure.pi (fun _ : Fin m => ν)) = (quadraticChar ν u v) ^ m := by
  have hLaw (i : Fin m) :
      IdentDistrib (fun a : Shao.Path m => a i) (id : ℝ → ℝ)
        (Measure.pi (fun _ : Fin m => ν)) ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (fun _ : Fin m => ν) i).map_eq
  have hIndep : iIndepFun (fun (i : Fin m) (a : Shao.Path m) => a i)
      (Measure.pi (fun _ : Fin m => ν)) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hf := iid_quadraticChar_factor
    (fun i => measurable_pi_apply i) hIndep hLaw u v
  convert hf using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by rfl

private lemma joint_characteristic (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)]
    (m : ℕ) (u v : ℝ) :
    (∫ q : Shao.Path m × (ℝ × ℝ),
      Complex.exp (((frequency u v (futureShift m q) : ℝ) : ℂ) * Complex.I)
      ∂(Measure.pi (fun _ : Fin m => ν)).prod (quadraticFullNoiseLaw ν)) =
      quadraticFullNoiseChar ν u v * (quadraticChar ν u v) ^ m := by
  have he : (fun q : Shao.Path m × (ℝ × ℝ) =>
      Complex.exp (((frequency u v (futureShift m q) : ℝ) : ℂ) * Complex.I)) =
      (fun q =>
        Complex.exp (((u * Shao.prefixSum q.1 m + v * Shao.energy q.1 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((u * q.2.1 + v * q.2.2 : ℝ) : ℂ) * Complex.I)) := by
    funext q
    rw [← Complex.exp_add]
    congr 1
    dsimp [frequency, futureShift]
    push_cast
    ring
  rw [he, integral_prod_mul
    (fun a : Shao.Path m => Complex.exp
      (((u * Shao.prefixSum a m + v * Shao.energy a : ℝ) : ℂ) * Complex.I))
    (fun z : ℝ × ℝ => Complex.exp (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I)),
    canonical_future_characteristic]
  change (quadraticChar ν u v) ^ m * quadraticFullNoiseChar ν u v = _
  ring

theorem sourceFutureNoiseKernelTransform_factor (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (u v : ℝ) :
    sourceFutureNoiseKernelTransform ν m y u v =
      sourceFourierTestTransform y u v * quadraticFullNoiseChar ν u v *
        (quadraticChar ν u v) ^ m := by
  have hp := (quadraticFullNoise_law_data ν h3 hV h hh hs).2.2.1
  haveI : IsProbabilityMeasure (quadraticFullNoiseLaw ν) := hp
  unfold sourceFutureNoiseKernelTransform
  simp_rw [kernel_eq_joint ν m y]
  change (∫ p : ℝ × ℝ,
    ((∫ q : Shao.Path m × (ℝ × ℝ), sourceFourierTest y (p + futureShift m q)
      ∂(Measure.pi (fun _ : Fin m => ν)).prod (quadraticFullNoiseLaw ν) : ℝ) : ℂ) *
        negativePhase (frequency u v p)) = _
  rw [averaged_transform (futureShift_measurable m) y hy u v,
    joint_characteristic ν m u v]
  ring

end Shao.Probability
