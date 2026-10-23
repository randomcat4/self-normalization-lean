import Shao.Probability.SourceFutureNoiseFourier
import Shao.Probability.SourceMarkFourierNorms
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory MeasureTheory.Measure WithLp
open scoped Topology ContDiff FourierTransform BigOperators

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

private lemma test_continuousAt (y : ℝ) (p : ℝ × ℝ)
    (hp : |p.1| ≠ y * Real.sqrt p.2) : ContinuousAt (sourceFourierTest y) p := by
  by_cases hlt : |p.1| < y * Real.sqrt p.2
  · have hh : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |q.1| < y * Real.sqrt q.2 :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hlt
    have he : sourceFourierTest y =ᶠ[𝓝 p] (fun q : ℝ × ℝ => sourceKernelCutoff q.2) := by
      filter_upwards [hh] with q hq
      simp [sourceFourierTest, hq]
    exact (sourceKernelCutoff_data.1.continuous.comp continuous_snd).continuousAt.congr_of_eventuallyEq he
  · have hgt : y * Real.sqrt p.2 < |p.1| := lt_of_le_of_ne (le_of_not_gt hlt) hp.symm
    have hh : ∀ᶠ q : ℝ × ℝ in 𝓝 p, y * Real.sqrt q.2 < |q.1| :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds hgt
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => (0 : ℝ)) p).congr_of_eventuallyEq
    filter_upwards [hh] with q hq
    simp [sourceFourierTest, not_lt.mpr hq.le]

private lemma third_moment_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν) :
    0 < ∫ a : ℝ, |a| ^ 3 ∂ν := by
  have hn : 0 ≤ ∫ a : ℝ, |a| ^ 3 ∂ν := integral_nonneg (fun a => pow_nonneg (abs_nonneg a) 3)
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

private noncomputable def scalarSmooth (gamma y : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t : ℝ, sourceFourierTest y (p.1 + gamma * t, p.2) ∂sourceScalarLaw

private lemma scalarSmooth_bound (gamma y : ℝ) (p : ℝ × ℝ) :
    ‖scalarSmooth gamma y p‖ ≤ 1 := by
  haveI : IsProbabilityMeasure sourceScalarLaw := sourceScalarLaw_data.1
  simpa [scalarSmooth] using
    norm_integral_le_of_norm_le (f := fun t : ℝ => sourceFourierTest y (p.1 + gamma * t, p.2))
      (integrable_const (μ := sourceScalarLaw) (1 : ℝ))
      (Filter.Eventually.of_forall fun t => test_norm_le_one y _)

private lemma scalarSmooth_continuous (gamma y : ℝ) (hgamma : gamma ≠ 0) :
    Continuous (scalarSmooth gamma y) := by
  haveI : IsProbabilityMeasure sourceScalarLaw := sourceScalarLaw_data.1
  haveI : NullSingletonClass sourceScalarLaw := by unfold sourceScalarLaw; infer_instance
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (F := fun (q : ℝ × ℝ) (t : ℝ) =>
      sourceFourierTest y (q.1 + gamma * t, q.2))
    (bound := fun _ : ℝ => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun q =>
      ((test_measurable y).comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun q =>
      Filter.Eventually.of_forall fun t => test_norm_le_one y _
  · exact integrable_const _
  · have hplus : ∀ᵐ t : ℝ ∂sourceScalarLaw, t ≠ (y * Real.sqrt p.2 - p.1) / gamma := by
      simp only [ae_iff]
      simp
    have hminus : ∀ᵐ t : ℝ ∂sourceScalarLaw, t ≠ (-y * Real.sqrt p.2 - p.1) / gamma := by
      simp only [ae_iff]
      simp
    filter_upwards [hplus, hminus] with t htp htm
    have hn : |p.1 + gamma * t| ≠ y * Real.sqrt p.2 := by
      intro he
      rcases le_total 0 (p.1 + gamma * t) with hp | hp
      · rw [abs_of_nonneg hp] at he
        apply htp
        apply (eq_div_iff hgamma).mpr
        nlinarith
      · rw [abs_of_nonpos hp] at he
        apply htm
        apply (eq_div_iff hgamma).mpr
        nlinarith
    exact ContinuousAt.comp (f := fun q : ℝ × ℝ => (q.1 + gamma * t, q.2))
      (test_continuousAt y (p.1 + gamma * t, p.2) hn) (by fun_prop)

private noncomputable def fullBase
    (c : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) : ℝ × ℝ :=
  ((∑ j : Fin 8, (c.1 j).1) - (∑ j : Fin 8, (c.2 j).1),
    (∑ j : Fin 8, (c.1 j).2) + (∑ j : Fin 8, (c.2 j).2))

private noncomputable def fullSmooth (ν : Measure ℝ) (y : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, sourceFourierTest y (p + z) ∂quadraticFullNoiseLaw ν

set_option maxHeartbeats 800000 in
private lemma fullSmooth_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (quadraticChordFamilyLaw ν)]
    (y : ℝ) (p : ℝ × ℝ) :
    fullSmooth ν y p =
      ∫ c : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ),
        scalarSmooth ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν) y
          (p + fullBase c)
        ∂(quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν) := by
  haveI : IsProbabilityMeasure sourceScalarLaw := sourceScalarLaw_data.1
  haveI : IsProbabilityMeasure (quadraticNoiseInputLaw ν) := by
    unfold quadraticNoiseInputLaw
    infer_instance
  let F := fun z : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ =>
    sourceFourierTest y (p + quadraticFullNoiseMap ν z)
  have hi : Integrable F (quadraticNoiseInputLaw ν) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((test_measurable y).comp (by unfold quadraticFullNoiseMap; fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => test_norm_le_one y _)
  unfold fullSmooth quadraticFullNoiseLaw
  rw [integral_map (μ := quadraticNoiseInputLaw ν) (φ := quadraticFullNoiseMap ν)
    (f := fun z : ℝ × ℝ => sourceFourierTest y (p + z))
    (by unfold quadraticFullNoiseMap; fun_prop)
    ((test_measurable y).comp (show Measurable (fun z : ℝ × ℝ => p + z) by fun_prop)).aestronglyMeasurable]
  change (∫ z, F z ∂quadraticNoiseInputLaw ν) = _
  rw [show quadraticNoiseInputLaw ν =
    ((quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν)).prod sourceScalarLaw from rfl,
    integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with c
  unfold scalarSmooth
  apply integral_congr_ae
  filter_upwards [] with t
  change sourceFourierTest y (p + quadraticFullNoiseMap ν (c, t)) = _
  have he : p + quadraticFullNoiseMap ν (c, t) =
      ((p + fullBase c).1 + ((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν) * t,
        (p + fullBase c).2) := by
    ext <;> dsimp [quadraticFullNoiseMap, fullBase] <;> ring
  rw [he]

private lemma fullSmooth_continuous (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (y : ℝ) :
    Continuous (fullSmooth ν y) := by
  haveI : IsProbabilityMeasure (quadraticChordFamilyLaw ν) :=
    (quadraticFullNoise_law_data ν h3 hV h hh hs).1
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  have hgamma : 0 < gamma := div_pos (third_moment_pos ν h3 hV) hV
  have he : fullSmooth ν y = fun p : ℝ × ℝ =>
      ∫ c : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ),
        scalarSmooth gamma y (p + fullBase c)
        ∂(quadraticChordFamilyLaw ν).prod (quadraticChordFamilyLaw ν) := by
    funext p
    exact fullSmooth_eq ν y p
  rw [he]
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro p
    exact ((scalarSmooth_continuous gamma y (ne_of_gt hgamma)).measurable.comp
      (by unfold fullBase; fun_prop)).aestronglyMeasurable
  · exact fun p => Filter.Eventually.of_forall fun c => scalarSmooth_bound gamma y _
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun c =>
      (scalarSmooth_continuous gamma y (ne_of_gt hgamma)).comp (continuous_id.add continuous_const)

private lemma fullSmooth_bound (ν : Measure ℝ)
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] (y : ℝ) (p : ℝ × ℝ) :
    ‖fullSmooth ν y p‖ ≤ 1 := by
  simpa [fullSmooth] using
    norm_integral_le_of_norm_le (f := fun z : ℝ × ℝ => sourceFourierTest y (p + z))
      (integrable_const (μ := quadraticFullNoiseLaw ν) (1 : ℝ))
      (Filter.Eventually.of_forall fun z => test_norm_le_one y _)

theorem sourceFutureNoiseKernel_continuous (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    Continuous (sourceFutureNoiseKernel ν m y) := by
  haveI : IsProbabilityMeasure (quadraticFullNoiseLaw ν) :=
    (quadraticFullNoise_law_data ν h3 hV h hh hs).2.2.1
  have hf := fullSmooth_continuous ν h3 hV h hh hs y
  have he : sourceFutureNoiseKernel ν m y = fun p : ℝ × ℝ =>
      ∫ a : Shao.Path m, fullSmooth ν y (p + (Shao.prefixSum a m, Shao.energy a))
        ∂Measure.pi (fun _ : Fin m => ν) := by
    funext p
    unfold sourceFutureNoiseKernel fullSmooth
    apply integral_congr_ae
    filter_upwards [] with a
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
  rw [he]
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro p
    exact (hf.measurable.comp (by unfold Shao.prefixSum Shao.energy; fun_prop)).aestronglyMeasurable
  · exact fun p => Filter.Eventually.of_forall fun a => fullSmooth_bound ν y _
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun a => hf.comp (continuous_id.add continuous_const)

private noncomputable def scalarDensitySchwartz : SchwartzMap ℝ ℂ :=
  (sourceScalarDensity_data.2.1.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp sourceScalarDensity_data.1)

private lemma scalarChar_fourier (t : ℝ) :
    sourceScalarChar t = 𝓕 scalarDensitySchwartz (-t / (2 * Real.pi)) := by
  unfold sourceScalarChar sourceScalarLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    sourceScalarDensity_data.1.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with r
  have he : -2 * Real.pi * r * (-t / (2 * Real.pi)) = t * r := by field_simp
  simp only [ENNReal.toReal_ofReal (sourceScalarDensity_data.2.2.1 r), Complex.real_smul,
    smul_eq_mul, he]
  change (sourceScalarDensity r : ℂ) * Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) = _
  rw [mul_comm (sourceScalarDensity r : ℂ)]
  congr 1

private lemma scalarChar_moment_integrable (gamma : ℝ) (hgamma : gamma ≠ 0) (k : ℕ) :
    Integrable (fun u : ℝ => |u| ^ k * ‖sourceScalarChar (gamma * u)‖) := by
  let b := 𝓕 scalarDensitySchwartz
  let c := -gamma / (2 * Real.pi)
  have hcn : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hgamma) (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hi := (b.integrable_pow_mul volume k).comp_mul_left' hcn
  have he (u : ℝ) : |u| ^ k * ‖sourceScalarChar (gamma * u)‖ =
      (|c| ^ k)⁻¹ * (‖c * u‖ ^ k * ‖b (c * u)‖) := by
    rw [scalarChar_fourier]
    have hc : -(gamma * u) / (2 * Real.pi) = c * u := by dsimp [c]; ring
    rw [hc, Real.norm_eq_abs, abs_mul, mul_pow]
    dsimp only [b]
    field_simp
  exact (hi.const_mul (|c| ^ k)⁻¹).congr (Filter.Eventually.of_forall fun u => (he u).symm)

private lemma cutoff_C2_bound : ∃ M : ℝ, 0 ≤ M ∧
    ∀ r : ℝ, |sourceKernelCutoff r| ≤ M ∧ |deriv sourceKernelCutoff r| ≤ M ∧
      |deriv (deriv sourceKernelCutoff) r| ≤ M := by
  have hd := (contDiff_infty_iff_deriv.mp sourceKernelCutoff_data.1).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨r0, h0⟩ := sourceKernelCutoff_data.1.continuous.abs.exists_forall_ge_of_hasCompactSupport
    sourceKernelCutoff_data.2.1.abs
  obtain ⟨r1, h1⟩ := hd.continuous.abs.exists_forall_ge_of_hasCompactSupport
    sourceKernelCutoff_data.2.1.deriv.abs
  obtain ⟨r2, h2⟩ := hdd.continuous.abs.exists_forall_ge_of_hasCompactSupport
    sourceKernelCutoff_data.2.1.deriv.deriv.abs
  refine ⟨|sourceKernelCutoff r0| + |deriv sourceKernelCutoff r1| +
    |deriv (deriv sourceKernelCutoff) r2|, by positivity, ?_⟩
  intro r
  specialize h0 r
  specialize h1 r
  specialize h2 r
  exact ⟨by linarith [abs_nonneg (deriv sourceKernelCutoff r1),
    abs_nonneg (deriv (deriv sourceKernelCutoff) r2)],
    by linarith [abs_nonneg (sourceKernelCutoff r0), abs_nonneg (deriv (deriv sourceKernelCutoff) r2)],
    by linarith [abs_nonneg (sourceKernelCutoff r0), abs_nonneg (deriv sourceKernelCutoff r1)]⟩

private lemma testTransform_mark (y : ℝ) (hy : 0 ≤ y) (u v : ℝ) (hu : u ≠ 0) :
    sourceFourierTestTransform y u v =
      ((2 / u : ℝ) : ℂ) * sourceMarkSine sourceKernelCutoff y u 0 v := by
  rw [sourceFourierTestTransform_eq y hy u v]
  unfold sourceMarkSine
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  simp only [ite_eq_right hu, add_zero, mul_add, mul_zero]
  push_cast
  ring

private lemma testTransform_v_L1 (y : ℝ) (hy : 0 ≤ y) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, u ≠ 0 →
      Integrable (fun v : ℝ => sourceFourierTestTransform y u v) ∧
      (∫ v : ℝ, ‖sourceFourierTestTransform y u v‖) ≤ A := by
  obtain ⟨M, hM, hMB⟩ := cutoff_C2_bound
  obtain ⟨C, hC, hbound⟩ := sourceMarkSine_norms (1 / 16) 4 (by norm_num) (by norm_num)
  have hsup : tsupport sourceKernelCutoff ⊆ Set.Icc (1 / 16 : ℝ) 4 := by
    intro r hr
    exact ⟨(sourceKernelCutoff_data.2.2.2.2 hr).1.le,
      (sourceKernelCutoff_data.2.2.2.2 hr).2.le⟩
  refine ⟨2 * C * M * y, by positivity, ?_⟩
  intro u hu
  obtain ⟨hi, _, hn, _⟩ := hbound M hM sourceKernelCutoff sourceKernelCutoff_data.1
    hsup hMB y u 0 hy (by simpa only [abs_zero] using (div_nonneg hy (by norm_num : (0 : ℝ) ≤ 16)))
  have hchar : Integrable (sourceMarkSine sourceKernelCutoff y u 0) :=
    integrable_norm_iff ((show Continuous (sourceMarkSine sourceKernelCutoff y u 0) from by
      unfold sourceMarkSine
      apply continuous_of_dominated (bound := fun r : ℝ => |sourceKernelCutoff r|)
      · intro v
        have hb : Continuous (fun r : ℝ => sourceKernelCutoff r * Real.sin (u * (y * Real.sqrt r + 0))) :=
          sourceKernelCutoff_data.1.continuous.mul (by fun_prop)
        exact ((Complex.ofRealCLM.continuous.comp hb).aestronglyMeasurable.mul
          (by fun_prop))
      · intro v
        filter_upwards [] with r
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
          Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, neg_zero, Real.exp_zero,
          mul_one]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
      · exact sourceKernelCutoff_data.1.continuous.integrable_of_hasCompactSupport
          sourceKernelCutoff_data.2.1 |>.abs
      · exact Filter.Eventually.of_forall fun r => by fun_prop).aestronglyMeasurable) |>.mp hi
  have hiT : Integrable (sourceFourierTestTransform y u) := by
    exact (hchar.const_mul ((2 / u : ℝ) : ℂ)).congr
      (Filter.Eventually.of_forall fun v => (testTransform_mark y hy u v hu).symm)
  refine ⟨hiT, ?_⟩
  have he : (∫ v : ℝ, ‖sourceFourierTestTransform y u v‖) =
      (2 / |u|) * ∫ v : ℝ, ‖sourceMarkSine sourceKernelCutoff y u 0 v‖ := by
    simp_rw [testTransform_mark y hy u _ hu, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [integral_const_mul]
  rw [he]
  calc
    _ ≤ (2 / |u|) * (C * M * min (y * |u|) (1 + Real.sqrt (y * |u|))) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ (2 / |u|) * (C * M * (y * |u|)) := by gcongr; exact min_le_left _ _
    _ = _ := by field_simp

private noncomputable def pairPhase (ξ p : ℝ × ℝ) : ℂ :=
  Complex.exp (-(((ξ.1 * p.1 + ξ.2 * p.2 : ℝ) : ℂ) * Complex.I))

private lemma pairPhase_norm (ξ p : ℝ × ℝ) : ‖pairPhase ξ p‖ = 1 := by
  simp [pairPhase, Complex.norm_exp, Complex.mul_re]

private lemma pairTransform_continuous (f : (ℝ × ℝ) → ℝ) (hf : Integrable f) :
    Continuous (fun ξ : ℝ × ℝ => ∫ p : ℝ × ℝ, (f p : ℂ) * pairPhase ξ p) := by
  apply continuous_of_dominated (bound := fun p => ‖f p‖)
  · intro ξ
    exact (hf.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul (by unfold pairPhase; fun_prop)
  · intro ξ
    exact Filter.Eventually.of_forall fun p => by
      simp only [norm_mul, pairPhase_norm, mul_one, Complex.norm_real]
      exact le_rfl
  · exact hf.norm
  · exact Filter.Eventually.of_forall fun p => by unfold pairPhase; fun_prop

private lemma futureTransform_continuous (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    Continuous (fun ξ : ℝ × ℝ => sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2) :=
  pairTransform_continuous _ (sourceFutureNoiseKernel_integrable ν h3 hV h hh hs m y hy)

private lemma fullNoise_norm_scalar (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h) (u v : ℝ) :
    ‖quadraticFullNoiseChar ν u v‖ ≤
      ‖sourceScalarChar (((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν) * u)‖ := by
  haveI : IsProbabilityMeasure (quadraticChordLaw ν) :=
    (quadraticChord_law_data ν h3 hV h hh hs).2.1
  have hnorm (r : ℝ) : ‖quadraticChordChar ν r v‖ ≤ 1 := by
    unfold quadraticChordChar
    simpa using norm_integral_le_of_norm_le (integrable_const (μ := quadraticChordLaw ν) (1 : ℝ))
      (Filter.Eventually.of_forall fun z => by
        simp [Complex.norm_exp, Complex.mul_re])
  rw [(quadraticFullNoiseChar_product ν h3 hV h hh hs u v).1]
  simp only [norm_mul, norm_pow]
  have ha := pow_le_pow_left₀ (norm_nonneg _) (hnorm u) 8
  have hb := pow_le_pow_left₀ (norm_nonneg _) (hnorm (-u)) 8
  simp only [one_pow] at ha hb
  calc
    _ ≤ (1 * 1) * ‖sourceScalarChar (((∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν) * u)‖ := by
      gcongr
    _ = _ := by simp

theorem sourceFutureNoiseKernelTransform_moment_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    Integrable (fun ξ : ℝ × ℝ => ((ξ.1 : ℂ) ^ k) *
      sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2)
      (volume : Measure (ℝ × ℝ)) := by
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
  have hg : 0 < gamma := div_pos (third_moment_pos ν h3 hV) hV
  let F : ℝ × ℝ → ℂ := fun ξ => ((ξ.1 : ℂ) ^ k) *
    sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2
  have hFc : Continuous F :=
    (Complex.ofRealCLM.continuous.comp continuous_fst).pow k |>.mul
      (futureTransform_continuous ν h3 hV h hh hs m y hy)
  have hFm : AEStronglyMeasurable F ((volume : Measure ℝ).prod volume) := hFc.aestronglyMeasurable
  obtain ⟨A, hA, hAv⟩ := testTransform_v_L1 y hy
  let B : ℝ → ℝ := fun u => |u| ^ k * ‖sourceScalarChar (gamma * u)‖
  have hB : Integrable B := scalarChar_moment_integrable gamma (ne_of_gt hg) k
  have hBn (u : ℝ) : 0 ≤ B u := by dsimp [B]; positivity
  have hpoint (u v : ℝ) : ‖F (u, v)‖ ≤ B u * ‖sourceFourierTestTransform y u v‖ := by
    dsimp [F, B]
    rw [sourceFutureNoiseKernelTransform_factor ν h3 hV h hh hs m y hy u v]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hp := pow_le_pow_left₀ (norm_nonneg _) (norm_quadraticChar_le_one ν u v) m
    simp only [one_pow] at hp
    have hXi := fullNoise_norm_scalar ν h3 hV h hh hs u v
    change ‖quadraticFullNoiseChar ν u v‖ ≤ ‖sourceScalarChar (gamma * u)‖ at hXi
    calc
      _ ≤ |u| ^ k * ((‖sourceFourierTestTransform y u v‖ *
          ‖sourceScalarChar (gamma * u)‖) * 1) := by gcongr
      _ = _ := by ring
  have hslice (u : ℝ) (hu : u ≠ 0) : Integrable (fun v : ℝ => F (u, v)) := by
    exact (((hAv u hu).1.norm).const_mul (B u)).mono'
      (hFc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => hpoint u v)
  have hint (u : ℝ) (hu : u ≠ 0) : (∫ v : ℝ, ‖F (u, v)‖) ≤ A * B u := by
    calc
      _ ≤ ∫ v : ℝ, B u * ‖sourceFourierTestTransform y u v‖ :=
        integral_mono (hslice u hu).norm (((hAv u hu).1.norm).const_mul (B u)) (hpoint u)
      _ = B u * ∫ v : ℝ, ‖sourceFourierTestTransform y u v‖ := integral_const_mul _ _
      _ ≤ B u * A := mul_le_mul_of_nonneg_left (hAv u hu).2 (hBn u)
      _ = _ := mul_comm _ _
  have hne : ∀ᵐ u : ℝ, u ≠ 0 := by simp only [ae_iff]; simp
  change Integrable F _
  rw [Measure.volume_eq_prod ℝ ℝ]
  apply (integrable_prod_iff hFm).mpr
  refine ⟨hne.mono hslice, ?_⟩
  refine (hB.const_mul A).mono' hFm.norm.integral_prod_right' ?_
  filter_upwards [hne] with u hu
  have hz : 0 ≤ ∫ v : ℝ, ‖F (u, v)‖ := integral_nonneg fun v => norm_nonneg (F (u, v))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hint u hu

private noncomputable def pairTransform (f : (ℝ × ℝ) → ℝ) (ξ : ℝ × ℝ) : ℂ :=
  ∫ p : ℝ × ℝ, (f p : ℂ) * pairPhase ξ p

private lemma pairVolume_haar : IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  infer_instance

private lemma euclidean_fourier_eq (f : (ℝ × ℝ) → ℝ)
    (x : WithLp 2 (ℝ × ℝ)) :
    𝓕 (fun z : WithLp 2 (ℝ × ℝ) => (f (ofLp z) : ℂ)) x =
      pairTransform f ((2 * Real.pi) • ofLp x) := by
  rw [Real.fourier_eq',
    ← (WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
      (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding]
  unfold pairTransform
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [smul_eq_mul]
  rw [mul_comm _ (f p : ℂ)]
  congr 1
  unfold pairPhase
  congr 1
  simp only [WithLp.prod_inner_apply, ofLp_toLp, RCLike.inner_apply, conj_trivial,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast
  ring

private lemma pair_inversion (f : (ℝ × ℝ) → ℝ) (hf : Integrable f)
    (hc : Continuous f) (hFT : Integrable (pairTransform f)) (p : ℝ × ℝ) :
    (f p : ℂ) = ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
      ∫ ξ : ℝ × ℝ,
        Complex.exp ((((ξ.1 * p.1 + ξ.2 * p.2 : ℝ) : ℂ)) * Complex.I) * pairTransform f ξ := by
  haveI : IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := pairVolume_haar
  let c : ℝ := 2 * Real.pi
  have hcp : 0 < c := by dsimp [c]; positivity
  have hcn : c ≠ 0 := ne_of_gt hcp
  let fe : WithLp 2 (ℝ × ℝ) → ℂ := fun x => (f (ofLp x) : ℂ)
  have hfe : Integrable fe :=
    (WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_of_integrable (hf.ofReal (𝕜 := ℂ))
  have hcfe : Continuous fe :=
    Complex.ofRealCLM.continuous.comp (hc.comp (WithLp.prod_continuous_ofLp 2 ℝ ℝ))
  have hFTscaled : Integrable (fun ξ : ℝ × ℝ => pairTransform f (c • ξ)) := hFT.comp_smul hcn
  have hfte : Integrable (𝓕 fe) := by
    have he : 𝓕 fe = fun x : WithLp 2 (ℝ × ℝ) => pairTransform f (c • ofLp x) := by
      funext x
      exact euclidean_fourier_eq f x
    rw [he]
    exact (WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_of_integrable hFTscaled
  have hinv := hfe.fourierInv_fourier_eq hfte (hcfe.continuousAt (x := toLp 2 p))
  change 𝓕⁻ (𝓕 fe) (toLp 2 p) = (f p : ℂ) at hinv
  rw [← hinv, Real.fourierInv_eq',
    ← (WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
      (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding]
  let G : ℝ × ℝ → ℂ := fun ξ =>
    Complex.exp ((((ξ.1 * p.1 + ξ.2 * p.2 : ℝ) : ℂ)) * Complex.I) * pairTransform f ξ
  have he : (fun ξ : ℝ × ℝ =>
      Complex.exp (((2 * Real.pi * inner ℝ (toLp 2 ξ : WithLp 2 (ℝ × ℝ)) (toLp 2 p) : ℝ) : ℂ) *
        Complex.I) • 𝓕 fe (toLp 2 ξ)) = fun ξ : ℝ × ℝ => G (c • ξ) := by
    funext ξ
    rw [show 𝓕 fe (toLp 2 ξ) = pairTransform f (c • ξ) from euclidean_fourier_eq f (toLp 2 ξ)]
    dsimp [G]
    congr 2
    simp only [WithLp.prod_inner_apply, ofLp_toLp, RCLike.inner_apply, conj_trivial,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    dsimp [c]
    push_cast
    ring
  change (∫ ξ : ℝ × ℝ,
    Complex.exp (((2 * Real.pi * inner ℝ (toLp 2 ξ : WithLp 2 (ℝ × ℝ)) (toLp 2 p) : ℝ) : ℂ) *
      Complex.I) • 𝓕 fe (toLp 2 ξ)) = _
  rw [he, Measure.integral_comp_smul (volume : Measure (ℝ × ℝ)) G c]
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hdim, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg c)), Complex.real_smul]
  change (((c ^ 2)⁻¹ : ℝ) : ℂ) * (∫ ξ : ℝ × ℝ, G ξ) = _
  simp only [Complex.ofReal_inv]
  rfl

theorem sourceFutureNoiseKernel_inversion (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (p : ℝ × ℝ) :
    (sourceFutureNoiseKernel ν m y p : ℂ) =
      ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
        ∫ ξ : ℝ × ℝ,
          Complex.exp ((((ξ.1 * p.1 + ξ.2 * p.2 : ℝ) : ℂ)) * Complex.I) *
            sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2 := by
  have hFT : Integrable (pairTransform (sourceFutureNoiseKernel ν m y)) := by
    have hi := sourceFutureNoiseKernelTransform_moment_integrable ν h3 hV h hh hs m y hy 0
    simp only [pow_zero, one_mul] at hi
    convert hi using 1
    rfl
  exact pair_inversion (sourceFutureNoiseKernel ν m y)
    (sourceFutureNoiseKernel_integrable ν h3 hV h hh hs m y hy)
    (sourceFutureNoiseKernel_continuous ν h3 hV h hh hs m y hy) hFT p

private noncomputable def inversePhase (w q : ℝ) (ξ : ℝ × ℝ) : ℂ :=
  Complex.exp ((((ξ.1 * w + ξ.2 * q : ℝ) : ℂ)) * Complex.I)

private lemma inversePhase_norm (w q : ℝ) (ξ : ℝ × ℝ) : ‖inversePhase w q ξ‖ = 1 := by
  simp [inversePhase, Complex.norm_exp, Complex.mul_re]

private noncomputable def inverseMoment (F : (ℝ × ℝ) → ℂ) (k : ℕ) (q w : ℝ) : ℂ :=
  ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) * ∫ ξ : ℝ × ℝ,
    (Complex.I * (ξ.1 : ℂ)) ^ k * inversePhase w q ξ * F ξ

private lemma inverse_integrand_hasDerivAt (F : (ℝ × ℝ) → ℂ)
    (k : ℕ) (q w : ℝ) (ξ : ℝ × ℝ) :
    HasDerivAt (fun r : ℝ => (Complex.I * (ξ.1 : ℂ)) ^ k * inversePhase r q ξ * F ξ)
      ((Complex.I * (ξ.1 : ℂ)) ^ (k + 1) * inversePhase w q ξ * F ξ) w := by
  have he : HasDerivAt (fun r : ℝ => inversePhase r q ξ)
      (inversePhase w q ξ * ((ξ.1 : ℂ) * Complex.I)) w := by
    simpa only [inversePhase, id_eq, mul_one] using
      (((((hasDerivAt_id w).const_mul ξ.1).add_const (ξ.2 * q)).ofReal_comp).mul_const
        Complex.I).cexp
  convert (he.const_mul ((Complex.I * (ξ.1 : ℂ)) ^ k)).mul_const (F ξ) using 1
  rw [pow_succ]
  ring

private lemma inverseMoment_hasDerivAt (F : (ℝ × ℝ) → ℂ) (hF : Continuous F)
    (hMom : ∀ k : ℕ, Integrable (fun ξ : ℝ × ℝ => (ξ.1 : ℂ) ^ k * F ξ))
    (k : ℕ) (q w : ℝ) :
    HasDerivAt (inverseMoment F k q) (inverseMoment F (k + 1) q w) w := by
  let J : ℕ → ℝ → (ℝ × ℝ) → ℂ := fun j r ξ =>
    (Complex.I * (ξ.1 : ℂ)) ^ j * inversePhase r q ξ * F ξ
  have hnorm (j : ℕ) (r : ℝ) (ξ : ℝ × ℝ) : ‖J j r ξ‖ = ‖(ξ.1 : ℂ) ^ j * F ξ‖ := by
    simp only [J, norm_mul, norm_pow, Complex.norm_I, one_mul, inversePhase_norm, mul_one]
  have hm (j : ℕ) (r : ℝ) : AEStronglyMeasurable (J j r) := by
    exact ((Complex.continuous_ofReal.comp continuous_fst).const_mul Complex.I |>.pow j |>.mul
      (by unfold inversePhase; fun_prop) |>.mul hF).aestronglyMeasurable
  have hi (j : ℕ) (r : ℝ) : Integrable (J j r) := by
    exact (hMom j).norm.mono' (hm j r)
      (Filter.Eventually.of_forall fun ξ => (hnorm j r ξ).le)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (F := J k) (F' := J (k + 1))
    (bound := fun ξ : ℝ × ℝ => ‖(ξ.1 : ℂ) ^ (k + 1) * F ξ‖) (by simp)
    (Filter.Eventually.of_forall fun r => hm k r) (hi k w) (hm (k + 1) w)
    (Filter.Eventually.of_forall fun ξ r _ => (hnorm (k + 1) r ξ).le)
    (hMom (k + 1)).norm
    (Filter.Eventually.of_forall fun ξ r _ => inverse_integrand_hasDerivAt F k q r ξ)).2
  exact hd.const_mul ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹)

theorem sourceFutureNoiseKernel_spatial_derivatives
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (w q : ℝ) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let J : ℕ → ℂ := fun k =>
      ((((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹) *
        ∫ ξ : ℝ × ℝ,
          (Complex.I * (ξ.1 : ℂ)) ^ k *
            Complex.exp ((((ξ.1 * w + ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
              sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2
    DifferentiableAt ℝ f w ∧
      DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
      ((deriv f w : ℝ) : ℂ) = J 1 ∧
      ((deriv (fun r : ℝ => deriv f r) w : ℝ) : ℂ) = J 2 := by
  let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
  let F : (ℝ × ℝ) → ℂ := fun ξ => sourceFutureNoiseKernelTransform ν m y ξ.1 ξ.2
  have hF : Continuous F := futureTransform_continuous ν h3 hV h hh hs m y hy
  have hMom : ∀ k : ℕ, Integrable (fun ξ : ℝ × ℝ => (ξ.1 : ℂ) ^ k * F ξ) :=
    sourceFutureNoiseKernelTransform_moment_integrable ν h3 hV h hh hs m y hy
  have h0 (r : ℝ) : (f r : ℂ) = inverseMoment F 0 q r := by
    simpa only [inverseMoment, pow_zero, one_mul, inversePhase, F, f] using
      sourceFutureNoiseKernel_inversion ν h3 hV h hh hs m y hy (r, q)
  have hdC (r : ℝ) : HasDerivAt (fun x : ℝ => (f x : ℂ)) (inverseMoment F 1 q r) r := by
    exact (inverseMoment_hasDerivAt F hF hMom 0 q r).congr_of_eventuallyEq
      (Filter.Eventually.of_forall h0)
  have hdR (r : ℝ) : HasDerivAt f (inverseMoment F 1 q r).re r := by
    simpa only [Complex.reCLM_apply, Function.comp_def, Complex.ofReal_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hdC r)
  have he1 (r : ℝ) : ((deriv f r : ℝ) : ℂ) = inverseMoment F 1 q r := by
    rw [(hdR r).deriv]
    exact ((hdR r).ofReal_comp).unique (hdC r)
  have hddC : HasDerivAt (fun r : ℝ => ((deriv f r : ℝ) : ℂ)) (inverseMoment F 2 q w) w := by
    exact (inverseMoment_hasDerivAt F hF hMom 1 q w).congr_of_eventuallyEq
      (Filter.Eventually.of_forall he1)
  have hddR : HasDerivAt (deriv f) (inverseMoment F 2 q w).re w := by
    simpa only [Complex.reCLM_apply, Function.comp_def, Complex.ofReal_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt w hddC
  have he2 : ((deriv (fun r : ℝ => deriv f r) w : ℝ) : ℂ) = inverseMoment F 2 q w := by
    rw [hddR.deriv]
    exact hddR.ofReal_comp.unique hddC
  exact ⟨(hdR w).differentiableAt, hddR.differentiableAt, he1 w, he2⟩

end Shao.Probability
