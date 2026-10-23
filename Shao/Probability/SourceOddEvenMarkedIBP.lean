import Shao.Probability.SourceOddEvenWholeLineIBP
import Shao.Probability.SourceKernelAmplitudeFamily
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped Topology ContDiff

private lemma derivative_family_measurable (F : ℝ → ℝ → ℂ)
    (hF : Measurable (Function.uncurry F)) (hd : ∀ v : ℝ, Differentiable ℝ (F v)) :
    Measurable (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs : Filter.Tendsto s Filter.atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall fun n => ?_⟩
    have hp : 0 < s n := by dsimp [s]; positivity
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp.ne'
  have hm (n : ℕ) : Measurable (fun p : ℝ × ℝ =>
      (s n)⁻¹ • (F p.1 (p.2 + s n) - F p.1 p.2)) := by
    convert ((hF.comp (measurable_fst.prodMk
      (measurable_snd.add_const (s n)))).sub hF).const_smul ((s n)⁻¹) using 1
    funext p
    rfl
  refine measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr fun p => ?_)
  exact ((hd p.1 p.2).hasDerivAt.tendsto_slope_zero).comp hs

private lemma raw_joint_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measurable (fun p : ℝ × ℝ => quadraticChar ν p.2 p.1) := by
  change Measurable (fun p : ℝ × ℝ => ∫ a : ℝ, Complex.exp
    (((p.2 * a + p.1 * a ^ 2 : ℝ) : ℂ) * Complex.I) ∂ν)
  exact (show StronglyMeasurable (fun z : (ℝ × ℝ) × ℝ => Complex.exp
    (((z.1.2 * z.2 + z.1.1 * z.2 ^ 2 : ℝ) : ℂ) * Complex.I)) from
      (by fun_prop : Measurable _).stronglyMeasurable).integral_prod_right'.measurable

private lemma full_joint_measurable (ν : Measure ℝ)
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] :
    Measurable (fun p : ℝ × ℝ => quadraticFullNoiseChar ν p.2 p.1) := by
  change Measurable (fun p : ℝ × ℝ => ∫ z : ℝ × ℝ, Complex.exp
    (((p.2 * z.1 + p.1 * z.2 : ℝ) : ℂ) * Complex.I) ∂quadraticFullNoiseLaw ν)
  exact (show StronglyMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Complex.exp
    (((z.1.2 * z.2.1 + z.1.1 * z.2.2 : ℝ) : ℂ) * Complex.I)) from
      (by fun_prop : Measurable _).stronglyMeasurable).integral_prod_right'.measurable

private lemma mark_joint_measurable (a : ℝ → ℝ) (ha : Measurable a) (y w : ℝ) :
    Measurable (fun p : ℝ × ℝ => sourceMarkSine a y p.1 w p.2) := by
  unfold sourceMarkSine
  exact (show StronglyMeasurable (fun z : (ℝ × ℝ) × ℝ =>
    ((a z.2 * Real.sin (z.1.1 * (y * Real.sqrt z.2 + w)) : ℝ) : ℂ) *
      Complex.exp (-(((z.1.2 * z.2 : ℝ) : ℂ) * Complex.I))) from
      (by fun_prop : Measurable _).stronglyMeasurable).integral_prod_right'.measurable

private lemma phase_norm (q v : ℝ) :
    ‖Complex.exp (((v * q : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

private lemma marked_pair_integrable
    (F : ℝ → ℝ → ℂ) (hF : Measurable (Function.uncurry F))
    (B : ℝ → ℝ) (hB : ∀ u : ℝ, 0 ≤ B u)
    (hB1 : Integrable (fun u : ℝ => |u| * B u))
    (hFB : ∀ u v : ℝ, ‖F v u‖ ≤ B u)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (hs : tsupport a ⊆ Set.Icc (1 / 16 : ℝ) 4)
    (M : ℝ) (hM : 0 ≤ M)
    (hMB : ∀ r : ℝ, |a r| ≤ M ∧ |deriv a r| ≤ M ∧ |deriv (deriv a) r| ≤ M)
    (y w q : ℝ) (hy : 0 ≤ y) (hw : |w| ≤ y / 16) :
    Integrable (fun ξ : ℝ × ℝ =>
      Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
        sourceMarkSine a y ξ.1 w ξ.2 * F ξ.2 ξ.1) (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨C, hC, hmark⟩ := sourceMarkSine_norms (1 / 16) 4 (by norm_num) (by norm_num)
  let G : (ℝ × ℝ) → ℂ := fun ξ =>
    Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
      sourceMarkSine a y ξ.1 w ξ.2 * F ξ.2 ξ.1
  have hm : Measurable G :=
    ((by fun_prop : Measurable (fun ξ : ℝ × ℝ =>
      Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I))).mul
      (mark_joint_measurable a ha.continuous.measurable y w)).mul (hF.comp measurable_swap)
  have hn (u v : ℝ) : ‖G (u, v)‖ ≤ B u * ‖sourceMarkSine a y u w v‖ := by
    dsimp [G]
    rw [norm_mul, norm_mul, phase_norm, one_mul]
    exact (mul_le_mul_of_nonneg_left (hFB u v) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hi (u : ℝ) : Integrable (fun v => G (u, v)) :=
    ((hmark M hM a ha hs hMB y u w hy hw).1.const_mul (B u)).mono'
      ((hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun v => hn u v)
  have hI (u : ℝ) : (∫ v : ℝ, ‖G (u, v)‖) ≤ C * M * y * (|u| * B u) := by
    calc
      _ ≤ ∫ v : ℝ, B u * ‖sourceMarkSine a y u w v‖ :=
        integral_mono (hi u).norm ((hmark M hM a ha hs hMB y u w hy hw).1.const_mul (B u))
          (fun v => hn u v)
      _ = B u * ∫ v : ℝ, ‖sourceMarkSine a y u w v‖ := integral_const_mul _ _
      _ ≤ B u * (C * M * min (y * |u|) (1 + Real.sqrt (y * |u|))) :=
        mul_le_mul_of_nonneg_left (hmark M hM a ha hs hMB y u w hy hw).2.2.1 (hB u)
      _ ≤ B u * (C * M * (y * |u|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (min_le_left (y * |u|) (1 + Real.sqrt (y * |u|))) (mul_nonneg hC.le hM)) (hB u)
      _ = _ := by ring
  rw [Measure.volume_eq_prod ℝ ℝ]
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall hi, ?_⟩
  exact (hB1.const_mul (C * M * y)).mono'
    hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      have hp : 0 ≤ ∫ v : ℝ, ‖G (u, v)‖ := integral_nonneg fun v : ℝ => norm_nonneg (G (u, v))
      simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hI u)

private lemma mark_integrand_integrable (a : ℝ → ℝ) (ha : Integrable a)
    (y u w v : ℝ) :
    Integrable (fun r : ℝ =>
      ((a r * Real.sin (u * (y * Real.sqrt r + w)) : ℝ) : ℂ) *
        Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I))) := by
  refine ha.abs.mono' ?_ (Filter.Eventually.of_forall fun r => ?_)
  · have hs : AEStronglyMeasurable (fun r : ℝ => Real.sin (u * (y * Real.sqrt r + w))) := by
      fun_prop
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (ha.aestronglyMeasurable.mul hs)).mul (by fun_prop)
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, neg_zero,
      Real.exp_zero, mul_one]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

private lemma mark_norm_le (a : ℝ → ℝ) (ha : Integrable a) (y u w v : ℝ) :
    ‖sourceMarkSine a y u w v‖ ≤ ∫ r : ℝ, |a r| := by
  unfold sourceMarkSine
  apply norm_integral_le_of_norm_le ha.abs
  exact Filter.Eventually.of_forall fun r => by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, neg_zero,
      Real.exp_zero, mul_one]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

private lemma mark_times_integrable (a : ℝ → ℝ) (ha : Integrable a)
    (haM : Measurable a) (F : ℝ → ℂ) (hF : Integrable F) (y w v : ℝ) :
    Integrable (fun u : ℝ => sourceMarkSine a y u w v * F u) := by
  exact hF.bdd_mul
    (((mark_joint_measurable a haM y w).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => mark_norm_le a ha y u w v)

private lemma fixed_v_mark_swap (a : ℝ → ℝ) (ha : Integrable a) (haM : Measurable a)
    (F : ℝ → ℂ) (hF : Integrable F) (hFM : Measurable F) (y w v : ℝ) :
    (∫ u : ℝ, sourceMarkSine a y u w v * F u) =
      ∫ r : ℝ, (a r : ℂ) * Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I)) *
        ∫ u : ℝ, (Real.sin ((y * Real.sqrt r + w) * u) : ℂ) * F u := by
  let J : (ℝ × ℝ) → ℂ := fun p =>
    ((a p.2 * Real.sin (p.1 * (y * Real.sqrt p.2 + w)) : ℝ) : ℂ) *
      Complex.exp (-(((v * p.2 : ℝ) : ℂ) * Complex.I)) * F p.1
  have hJ : Integrable J ((volume : Measure ℝ).prod volume) := by
    refine (hF.norm.mul_prod ha.abs).mono' (by unfold J; fun_prop) ?_
    exact Filter.Eventually.of_forall fun p => by
      dsimp [J]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, neg_zero,
        Real.exp_zero, mul_one]
      calc
        _ ≤ (|a p.2| * 1) * ‖F p.1‖ := by
          gcongr
          exact Real.abs_sin_le_one _
        _ = _ := by ring
  have he : (fun u : ℝ => sourceMarkSine a y u w v * F u) =
      fun u => ∫ r : ℝ, J (u, r) := by
    funext u
    unfold sourceMarkSine
    rw [← integral_mul_const]
  rw [he, ← integral_prod _ hJ, integral_prod_symm _ hJ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    change (∫ u : ℝ, J (u, r)) = (a r : ℂ) *
      Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I)) *
        ∫ u : ℝ, (Real.sin ((y * Real.sqrt r + w) * u) : ℂ) * F u
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp [J]
      rw [mul_comm (y * Real.sqrt r + w) u]
      push_cast
      ring

private lemma mark_cos_split (a : ℝ → ℝ) (ha : Integrable a) (y u w v : ℝ) :
    (Real.cos (u * w) : ℂ) * sourceMarkSine a y u 0 v =
      (1 / 2 : ℂ) * (sourceMarkSine a y u w v + sourceMarkSine a y u (-w) v) := by
  unfold sourceMarkSine
  rw [← integral_const_mul,
    ← integral_add (mark_integrand_integrable a ha y u w v)
      (mark_integrand_integrable a ha y u (-w) v), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    simp only [add_zero, mul_add, mul_neg, Real.sin_add, Real.sin_neg, Real.cos_neg,
      Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_neg]
    ring

private lemma cutoff_integrable : Integrable sourceKernelCutoff :=
  sourceKernelCutoff_data.1.continuous.integrable_of_hasCompactSupport sourceKernelCutoff_data.2.1

private lemma amplitude_data (theta : ℝ) (ht : |theta| ≤ (1 / 16 : ℝ)) :
    let a : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + theta) ^ 2
    ContDiff ℝ ∞ a ∧ tsupport a ⊆ Set.Icc (1 / 16 : ℝ) 4 ∧ Integrable a ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ,
        |a r| ≤ M ∧ |deriv a r| ≤ M ∧ |deriv (deriv a) r| ≤ M := by
  obtain ⟨M, hM, hfamily⟩ := sourceKernel_marked_amplitude_family
  have ha := hfamily 2 (Or.inr rfl) theta ht
  have hcompact : HasCompactSupport (fun r => sourceKernelCutoff r / (Real.sqrt r + theta) ^ 2) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) ha.2.1
  refine ⟨ha.1, ha.2.1, ha.1.continuous.integrable_of_hasCompactSupport hcompact,
    M, hM.le, fun r => ⟨?_, ?_, ?_⟩⟩
  · simpa only [iteratedDeriv_zero] using ha.2.2 0 (by norm_num) r
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using ha.2.2 1 (by norm_num) r
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using ha.2.2 2 (by norm_num) r

private lemma theta_bound (y w : ℝ) (hy : 0 < y) (hw : |w| ≤ y / 16) :
    |w / y| ≤ (1 / 16 : ℝ) := by
  rw [abs_div, abs_of_pos hy]
  apply (div_le_iff₀ hy).mpr
  linarith

private lemma source_phase_pos (y w r : ℝ) (hy : 0 < y) (hw : |w| ≤ y / 16)
    (hr : r ∈ tsupport sourceKernelCutoff) : 0 < y * Real.sqrt r + w := by
  have hc := sourceKernelCutoff_data.2.2.2.2 hr
  have hs : (1 / 4 : ℝ) < Real.sqrt r := by
    have hsq := Real.sq_sqrt (show 0 ≤ r by linarith [hc.1])
    have hn := Real.sqrt_nonneg r
    nlinarith [hc.1]
  have hwlo := (abs_le.mp hw).1
  nlinarith

private lemma fixed_v_shifted_mark_IBP (F : ℝ → ℂ)
    (hF : Integrable F) (hFM : Measurable F)
    (hF2 : Integrable (deriv (deriv F))) (hF2M : Measurable (deriv (deriv F)))
    (hIBP : ∀ a : ℝ, a ≠ 0 →
      (∫ u : ℝ, (Real.sin (a * u) : ℂ) * F u) =
        -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
          ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (deriv F) u)
    (y w v : ℝ) (hy : 0 < y) (hw : |w| ≤ y / 16) :
    (∫ u : ℝ, sourceMarkSine sourceKernelCutoff y u w v * F u) =
      -(((y ^ 2 : ℝ) : ℂ)⁻¹) *
        ∫ u : ℝ, sourceMarkSine
          (fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2) y u w v *
            deriv (deriv F) u := by
  let A : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
  have hA := amplitude_data (w / y) (theta_bound y w hy hw)
  rw [fixed_v_mark_swap sourceKernelCutoff cutoff_integrable
    sourceKernelCutoff_data.1.continuous.measurable F hF hFM,
    fixed_v_mark_swap A hA.2.2.1 hA.1.continuous.measurable (deriv (deriv F)) hF2 hF2M,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r => by
    change (sourceKernelCutoff r : ℂ) * Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I)) *
      (∫ u : ℝ, (Real.sin ((y * Real.sqrt r + w) * u) : ℂ) * F u) =
        -(((y ^ 2 : ℝ) : ℂ)⁻¹) * ((A r : ℂ) *
          Complex.exp (-(((v * r : ℝ) : ℂ) * Complex.I)) *
            ∫ u : ℝ, (Real.sin ((y * Real.sqrt r + w) * u) : ℂ) * deriv (deriv F) u)
    by_cases hr : sourceKernelCutoff r = 0
    · simp [A, hr]
    · have hp := source_phase_pos y w r hy hw (subset_tsupport _ hr)
      rw [hIBP (y * Real.sqrt r + w) hp.ne']
      have hd : 0 < Real.sqrt r + w / y := by
        have hrel : Real.sqrt r + w / y = (y * Real.sqrt r + w) / y := by
          field_simp
        rw [hrel]
        exact div_pos hp hy
      have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
      have hdC : ((Real.sqrt r + w / y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have hpC : ((y * Real.sqrt r + w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      dsimp [A]
      push_cast at hdC hpC ⊢
      field_simp [hyC, hdC, hpC]

private lemma fixed_v_cos_mark_IBP (F : ℝ → ℂ)
    (hF : Integrable F) (hFM : Measurable F)
    (hF2 : Integrable (deriv (deriv F))) (hF2M : Measurable (deriv (deriv F)))
    (hIBP : ∀ a : ℝ, a ≠ 0 →
      (∫ u : ℝ, (Real.sin (a * u) : ℂ) * F u) =
        -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
          ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (deriv F) u)
    (y w v : ℝ) (hy : 0 < y) (hw : |w| ≤ y / 16) :
    (∫ u : ℝ, (Real.cos (u * w) : ℂ) * sourceMarkSine sourceKernelCutoff y u 0 v * F u) =
      ((-1 / 2 : ℂ) * (((y ^ 2 : ℝ) : ℂ)⁻¹)) *
        ((∫ u : ℝ, sourceMarkSine
          (fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2) y u w v * deriv (deriv F) u) +
        ∫ u : ℝ, sourceMarkSine
          (fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2) y u (-w) v * deriv (deriv F) u) := by
  have hplus := mark_times_integrable sourceKernelCutoff cutoff_integrable
    sourceKernelCutoff_data.1.continuous.measurable F hF y w v
  have hminus := mark_times_integrable sourceKernelCutoff cutoff_integrable
    sourceKernelCutoff_data.1.continuous.measurable F hF y (-w) v
  have he : (fun u : ℝ =>
      (Real.cos (u * w) : ℂ) * sourceMarkSine sourceKernelCutoff y u 0 v * F u) =
      fun u => (1 / 2 : ℂ) *
        (sourceMarkSine sourceKernelCutoff y u w v * F u +
          sourceMarkSine sourceKernelCutoff y u (-w) v * F u) := by
    funext u
    rw [mark_cos_split sourceKernelCutoff cutoff_integrable]
    ring
  rw [he, integral_const_mul, integral_add hplus hminus,
    fixed_v_shifted_mark_IBP F hF hFM hF2 hF2M hIBP y w v hy hw,
    fixed_v_shifted_mark_IBP F hF hFM hF2 hF2M hIBP y (-w) v hy (by simpa using hw)]
  simp only [neg_div, ← sub_eq_add_neg]
  ring

private lemma marked_pair_IBP
    (F : ℝ → ℝ → ℂ) (hFM : Measurable (Function.uncurry F))
    (hd : ∀ v : ℝ, Differentiable ℝ (F v))
    (hdd : ∀ v : ℝ, Differentiable ℝ (deriv (F v)))
    (hi : ∀ v : ℝ, Integrable (F v))
    (hi2 : ∀ v : ℝ, Integrable (deriv (deriv (F v))))
    (hIBP : ∀ v a : ℝ, a ≠ 0 →
      (∫ u : ℝ, (Real.sin (a * u) : ℂ) * F v u) =
        -(((a ^ 2 : ℝ) : ℂ)⁻¹) *
          ∫ u : ℝ, (Real.sin (a * u) : ℂ) * deriv (deriv (F v)) u)
    (B : ℝ → ℝ) (hB : ∀ u : ℝ, 0 ≤ B u)
    (hB1 : Integrable (fun u : ℝ => |u| * B u))
    (hFB : ∀ u v : ℝ, ‖deriv (deriv (F v)) u‖ ≤ B u)
    (y w q : ℝ) (hy : 0 < y) (hw : |w| ≤ y / 16)
    (hG0 : Integrable (fun ξ : ℝ × ℝ =>
      Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) * (Real.cos (ξ.1 * w) : ℂ) *
        sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * F ξ.2 ξ.1)) :
    let Gplus : (ℝ × ℝ) → ℂ := fun ξ =>
      Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
        sourceMarkSine (fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2)
          y ξ.1 w ξ.2 * deriv (deriv (F ξ.2)) ξ.1
    let Gminus : (ℝ × ℝ) → ℂ := fun ξ =>
      Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
        sourceMarkSine (fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2)
          y ξ.1 (-w) ξ.2 * deriv (deriv (F ξ.2)) ξ.1
    Integrable Gplus ∧ Integrable Gminus ∧
      (∫ ξ : ℝ × ℝ,
        Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) * (Real.cos (ξ.1 * w) : ℂ) *
          sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * F ξ.2 ξ.1) =
        ((-1 / 2 : ℂ) * (((y ^ 2 : ℝ) : ℂ)⁻¹)) *
          ((∫ ξ : ℝ × ℝ, Gplus ξ) + ∫ ξ : ℝ × ℝ, Gminus ξ) := by
  let G0 : (ℝ × ℝ) → ℂ := fun ξ =>
    Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) * (Real.cos (ξ.1 * w) : ℂ) *
      sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * F ξ.2 ξ.1
  let Aplus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
  let Aminus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2
  let Gplus : (ℝ × ℝ) → ℂ := fun ξ =>
    Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) * sourceMarkSine Aplus y ξ.1 w ξ.2 *
      deriv (deriv (F ξ.2)) ξ.1
  let Gminus : (ℝ × ℝ) → ℂ := fun ξ =>
    Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) * sourceMarkSine Aminus y ξ.1 (-w) ξ.2 *
      deriv (deriv (F ξ.2)) ξ.1
  have hF1M := derivative_family_measurable F hFM hd
  have hF2M := derivative_family_measurable (fun v : ℝ => deriv (F v)) hF1M hdd
  have hAp := amplitude_data (w / y) (theta_bound y w hy hw)
  have hAm : ContDiff ℝ ∞ Aminus ∧ tsupport Aminus ⊆ Set.Icc (1 / 16 : ℝ) 4 ∧
      Integrable Aminus ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ,
        |Aminus r| ≤ M ∧ |deriv Aminus r| ≤ M ∧ |deriv (deriv Aminus) r| ≤ M := by
    simpa only [Aminus, neg_div, ← sub_eq_add_neg] using
      amplitude_data ((-w) / y) (theta_bound y (-w) hy (by simpa using hw))
  obtain ⟨Mp, hMp, hMpB⟩ := hAp.2.2.2
  obtain ⟨Mm, hMm, hMmB⟩ := hAm.2.2.2
  have hGp : Integrable Gplus := marked_pair_integrable (fun v : ℝ => deriv (deriv (F v))) hF2M B hB hB1 hFB
    Aplus hAp.1 hAp.2.1 Mp hMp hMpB y w q hy.le hw
  have hGm : Integrable Gminus := marked_pair_integrable (fun v : ℝ => deriv (deriv (F v))) hF2M B hB hB1 hFB
    Aminus hAm.1 hAm.2.1 Mm hMm hMmB y (-w) q hy.le (by simpa using hw)
  refine ⟨hGp, hGm, ?_⟩
  change (∫ ξ : ℝ × ℝ, G0 ξ) = _
  have hpoint (v : ℝ) : (∫ u : ℝ, G0 (u, v)) =
      ((-1 / 2 : ℂ) * (((y ^ 2 : ℝ) : ℂ)⁻¹)) *
        ((∫ u : ℝ, Gplus (u, v)) + ∫ u : ℝ, Gminus (u, v)) := by
    have hc := fixed_v_cos_mark_IBP (F v) (hi v)
      (hFM.comp (measurable_const.prodMk measurable_id)) (hi2 v)
      (hF2M.comp (measurable_const.prodMk measurable_id)) (hIBP v) y w v hy hw
    simp_rw [mul_assoc] at hc
    dsimp only [G0, Gplus, Gminus]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, hc]
    ring
  rw [Measure.volume_eq_prod ℝ ℝ] at hG0 hGp hGm ⊢
  rw [integral_prod_symm _ hG0, integral_prod_symm _ hGp, integral_prod_symm _ hGm]
  change (∫ v : ℝ, ∫ u : ℝ, G0 (u, v)) =
    ((-1 / 2 : ℂ) * (((y ^ 2 : ℝ) : ℂ)⁻¹)) *
      ((∫ v : ℝ, ∫ u : ℝ, Gplus (u, v)) + ∫ v : ℝ, ∫ u : ℝ, Gminus (u, v))
  simp_rw [hpoint]
  rw [integral_const_mul, integral_add hGp.integral_prod_right hGm.integral_prod_right]

private lemma signed_joint_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure (quadraticFullNoiseLaw ν)] (m : ℕ) (σ : ℂ) :
    Measurable (fun p : ℝ × ℝ =>
      ((quadraticChar ν p.2 p.1) ^ m + σ * (quadraticChar ν (-p.2) p.1) ^ m) / 2 *
        quadraticFullNoiseChar ν p.2 p.1) := by
  have hr := raw_joint_measurable ν
  have hn : Measurable (fun p : ℝ × ℝ => quadraticChar ν (-p.2) p.1) :=
    hr.comp (measurable_fst.prodMk measurable_snd.neg)
  exact (((hr.pow_const m).add ((hn.pow_const m).const_mul σ)).div_const 2).mul (full_joint_measurable ν)

theorem sourceFutureNoiseKernel_odd_derivative_markedIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 < y) (w q : ℝ) (hw : |w| ≤ y / 16) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let o : ℝ → ℝ := fun r => (f r - f (-r)) / 2
    let D : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let Aplus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
    let Aminus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2
    let Gplus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aplus y ξ.1 w ξ.2 *
          deriv (fun t : ℝ => deriv (D ξ.2) t) ξ.1
    let Gminus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aminus y ξ.1 (-w) ξ.2 *
          deriv (fun t : ℝ => deriv (D ξ.2) t) ξ.1
    DifferentiableAt ℝ o w ∧
      Integrable Gplus (volume : Measure (ℝ × ℝ)) ∧
      Integrable Gminus (volume : Measure (ℝ × ℝ)) ∧
      ((deriv o w : ℝ) : ℂ) =
        (-Complex.I / (((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)) *
          ((∫ ξ : ℝ × ℝ, Gplus ξ) + ∫ ξ : ℝ × ℝ, Gminus ξ) := by
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ν) :=
    (quadraticFullNoise_law_data ν h3 hV h hh hs).2.2.1
  let D : ℝ → ℝ → ℂ := fun v u =>
    ((quadraticChar ν u v) ^ m - (quadraticChar ν (-u) v) ^ m) / 2 * quadraticFullNoiseChar ν u v
  have hDM : Measurable (Function.uncurry D) := by
    convert signed_joint_measurable ν m (-1) using 1
    funext p
    dsimp [D, Function.uncurry]
    ring
  have hdata (v : ℝ) := quadraticFullNoise_odd_wholeLine_twiceIBP ν h3 hV h hh hs m v
  have hInv := sourceFutureNoiseKernel_odd_derivative_inverse ν h3 hV h hh hs m y hy.le w q
  obtain ⟨B, hB, hBI, hBB⟩ := quadraticFullNoise_odd_even_derivative_envelope ν h3 hV h hh hs m
  have hB1 : Integrable (fun u : ℝ => |u| * B u) := by simpa only [pow_one] using hBI 1
  have hpair := marked_pair_IBP D hDM (fun v => (hdata v).1) (fun v => (hdata v).2.1)
    (fun v => (hdata v).2.2.1) (fun v => (hdata v).2.2.2.2.1)
    (fun v a ha => ((hdata v).2.2.2.2.2 a ha).2.2)
    B hB hB1 (fun u v => (hBB u v).2.2.1) y w q hy hw hInv.2.1
  refine ⟨hInv.1, hpair.1, hpair.2.1, ?_⟩
  have hc : (2 * Complex.I / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) *
      ((-1 / 2 : ℂ) * (((y ^ 2 : ℝ) : ℂ)⁻¹)) =
      -Complex.I / (((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ) := by
    simp only [div_eq_mul_inv, Complex.ofReal_mul, mul_inv_rev]
    ring
  rw [hInv.2.2, hpair.2.2, ← mul_assoc, hc]

theorem sourceFutureNoiseKernel_even_second_markedIBP
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (m : ℕ) (y : ℝ) (hy : 0 < y) (w q : ℝ) (hw : |w| ≤ y / 16) :
    let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel ν m y (r, q)
    let e : ℝ → ℝ := fun r => (f r + f (-r)) / 2
    let E : ℝ → ℝ → ℂ := fun v u =>
      ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 *
        quadraticFullNoiseChar ν u v
    let W : ℝ → ℝ → ℂ := fun v u => (u : ℂ) * E v u
    let Aplus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r + w / y) ^ 2
    let Aminus : ℝ → ℝ := fun r => sourceKernelCutoff r / (Real.sqrt r - w / y) ^ 2
    let Gplus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aplus y ξ.1 w ξ.2 *
          deriv (fun t : ℝ => deriv (W ξ.2) t) ξ.1
    let Gminus : ℝ × ℝ → ℂ := fun ξ =>
      Complex.exp ((((ξ.2 * q : ℝ) : ℂ)) * Complex.I) *
        sourceMarkSine Aminus y ξ.1 (-w) ξ.2 *
          deriv (fun t : ℝ => deriv (W ξ.2) t) ξ.1
    DifferentiableAt ℝ e w ∧ DifferentiableAt ℝ (fun r : ℝ => deriv e r) w ∧
      Integrable Gplus (volume : Measure (ℝ × ℝ)) ∧
      Integrable Gminus (volume : Measure (ℝ × ℝ)) ∧
      ((deriv (fun r : ℝ => deriv e r) w : ℝ) : ℂ) =
        ((((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)⁻¹) *
          ((∫ ξ : ℝ × ℝ, Gplus ξ) + ∫ ξ : ℝ × ℝ, Gminus ξ) := by
  have : IsProbabilityMeasure (quadraticFullNoiseLaw ν) :=
    (quadraticFullNoise_law_data ν h3 hV h hh hs).2.2.1
  let E : ℝ → ℝ → ℂ := fun v u =>
    ((quadraticChar ν u v) ^ m + (quadraticChar ν (-u) v) ^ m) / 2 * quadraticFullNoiseChar ν u v
  let W : ℝ → ℝ → ℂ := fun v u => (u : ℂ) * E v u
  have hEM : Measurable (Function.uncurry E) := by
    convert signed_joint_measurable ν m 1 using 1
    funext p
    dsimp [E, Function.uncurry]
    ring
  have hWM : Measurable (Function.uncurry W) :=
    (Complex.measurable_ofReal.comp measurable_snd).mul hEM
  have hdata (v : ℝ) := quadraticFullNoise_even_wholeLine_twiceIBP ν h3 hV h hh hs m v
  have hInv := sourceFutureNoiseKernel_even_second_inverse ν h3 hV h hh hs m y hy.le w q
  obtain ⟨B, hB, hBI, hBB⟩ := quadraticFullNoise_odd_even_derivative_envelope ν h3 hV h hh hs m
  have hB1 : Integrable (fun u : ℝ => |u| * B u) := by simpa only [pow_one] using hBI 1
  have hG0 : Integrable (fun ξ : ℝ × ℝ =>
      Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) * (Real.cos (ξ.1 * w) : ℂ) *
        sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * W ξ.2 ξ.1) := by
    refine hInv.2.2.1.congr (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp [W, E]
    ring
  have hpair := marked_pair_IBP W hWM (fun v => (hdata v).1) (fun v => (hdata v).2.1)
    (fun v => (hdata v).2.2.1) (fun v => (hdata v).2.2.2.2.1)
    (fun v a ha => ((hdata v).2.2.2.2.2 a ha).2.2)
    B hB hB1 (fun u v => (hBB u v).2.2.2.2.2) y w q hy hw hG0
  have hIntegral :
      (∫ ξ : ℝ × ℝ, Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
        (Real.cos (ξ.1 * w) : ℂ) * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 *
          (ξ.1 : ℂ) * E ξ.2 ξ.1) =
      ∫ ξ : ℝ × ℝ, Complex.exp (((ξ.2 * q : ℝ) : ℂ) * Complex.I) *
        (Real.cos (ξ.1 * w) : ℂ) * sourceMarkSine sourceKernelCutoff y ξ.1 0 ξ.2 * W ξ.2 ξ.1 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by dsimp [W]; ring
  refine ⟨hInv.1, hInv.2.1, hpair.1, hpair.2.1, ?_⟩
  have hc : (-2 / (((2 * Real.pi) ^ 2 : ℝ) : ℂ)) *
      ((-1 / 2 : ℂ) * (((y ^ 2 : ℝ) : ℂ)⁻¹)) =
      ((((2 * Real.pi) ^ 2 * y ^ 2 : ℝ) : ℂ)⁻¹) := by
    simp only [div_eq_mul_inv, Complex.ofReal_mul, mul_inv_rev]
    ring
  rw [hInv.2.2.2, hIntegral, hpair.2.2, ← mul_assoc, hc]

end Shao.Probability
