import Shao.Probability.QuadraticFullNoise
import Shao.Probability.BoundedQuadraticTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

noncomputable def quadraticChordCharComplex (nu : Measure ℝ) (z w : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ,
    Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)
    ∂quadraticChordLaw nu

noncomputable def quadraticFullNoiseCharComplex (nu : Measure ℝ) (z w : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ,
    Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)
    ∂quadraticFullNoiseLaw nu



open scoped BigOperators

private lemma qcc_exp_remainder (b : ℝ) :
    |Real.exp b - (1 + b)| ≤ b ^ 2 * Real.exp |b| := by
  have hp := Complex.norm_exp_sub_sum_le_norm_mul_exp (b : ℂ) 2
  norm_num [Finset.sum_range_succ] at hp
  have he : Complex.exp (b : ℂ) - (1 + (b : ℂ)) =
      ((Real.exp b - (1 + b) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he] at hp
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hp

private lemma qcc_cosh_remainder (b : ℝ) :
    Real.cosh b - 1 ≤ b ^ 2 * Real.exp |b| := by
  have hp := qcc_exp_remainder b
  have hn := qcc_exp_remainder (-b)
  rw [abs_neg, neg_sq] at hn
  rw [Real.cosh_eq]
  linarith [le_abs_self (Real.exp b - (1 + b)),
    le_abs_self (Real.exp (-b) - (1 + -b))]

private lemma qcc_norm_one_sub_cos (a b : ℝ) :
    ‖1 - Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)‖ =
      Real.cosh b - Real.cos a := by
  have he : ‖1 - Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)‖ ^ 2 =
      (Real.cosh b - Real.cos a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.cos_add_mul_I]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linear_combination (Real.cos a ^ 2 - 1) * Real.cosh_sq_sub_sinh_sq b +
      Real.sinh b ^ 2 * Real.sin_sq_add_cos_sq a
  have hn : 0 ≤ Real.cosh b - Real.cos a := by
    have hc : 1 ≤ Real.cosh b := by
      rw [Real.cosh_eq]
      linarith [Real.add_one_le_exp b, Real.add_one_le_exp (-b)]
    linarith [hc, Real.cos_le_one a]
  nlinarith [norm_nonneg (1 - Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I))]

theorem complex_cosine_chord_bound (a b : ℝ) :
    ‖1 - Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
      2 * Real.exp |b| * (1 - Real.cos a + b ^ 2) := by
  rw [qcc_norm_one_sub_cos]
  have hg : 0 ≤ 1 - Real.cos a := sub_nonneg.mpr (Real.cos_le_one a)
  have he : 1 ≤ Real.exp |b| := Real.one_le_exp (abs_nonneg b)
  have hm := mul_le_mul_of_nonneg_right he hg
  have hb := qcc_cosh_remainder b
  nlinarith [mul_nonneg (sq_nonneg b) (Real.exp_pos |b|).le]

private lemma qcc_triangle_weight_nonneg (r : ℝ) :
    0 ≤ (if |r| ≤ 1 then 1 - |r| else 0 : ℝ) := by
  split_ifs with h
  · linarith
  · exact le_rfl

private lemma qcc_triangle_weight_measurable :
    Measurable (fun r : ℝ => if |r| ≤ 1 then 1 - |r| else (0 : ℝ)) := by
  exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
    (measurable_const.sub continuous_abs.measurable) measurable_const

private lemma qcc_triangle_weight_indicator (r : ℝ) :
    (if |r| ≤ 1 then 1 - |r| else (0 : ℝ)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun r => 1 - |r|) r := by
  by_cases h : |r| ≤ 1
  · have hr : r ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp h
    simp [h, hr]
  · have hr : r ∉ Set.Icc (-1 : ℝ) 1 := fun hr => h (abs_le.mpr hr)
    simp [h, hr]

private lemma qcc_triangle_weight_integrable :
    Integrable (fun r : ℝ => if |r| ≤ 1 then 1 - |r| else (0 : ℝ)) := by
  have hc : Continuous (fun r : ℝ => 1 - |r|) := by fun_prop
  have hi : Integrable ((Set.Icc (-1 : ℝ) 1).indicator (fun r => 1 - |r|)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hc.integrableOn_Icc
  exact hi.congr (Filter.Eventually.of_forall fun r => (qcc_triangle_weight_indicator r).symm)

private lemma qcc_triangle_weighted_integral (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ r : ℝ, ((if |r| ≤ 1 then 1 - |r| else 0 : ℝ) : ℂ) * g r) =
      (∫ r : ℝ in (-1)..0, ((1 + r : ℝ) : ℂ) * g r) +
      (∫ r : ℝ in 0..1, ((1 - r : ℝ) : ℂ) * g r) := by
  have he : (fun r : ℝ => ((if |r| ≤ 1 then 1 - |r| else 0 : ℝ) : ℂ) * g r) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun r => ((1 - |r| : ℝ) : ℂ) * g r) := by
    funext r
    by_cases h : r ∈ Set.Icc (-1 : ℝ) 1
    · simp [h, abs_le.mpr h]
    · have ha : ¬ |r| ≤ 1 := fun ha => h (abs_le.mp ha)
      simp [h, ha]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hc : Continuous (fun r : ℝ => ((1 - |r| : ℝ) : ℂ) * g r) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-1) 0)
    (hc.intervalIntegrable 0 1)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : r ≤ 0 := by simpa using hr.2
    dsimp only
    rw [abs_of_nonpos hr0]
    congr 2
    ring
  · apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := by simpa using hr.1
    dsimp only
    rw [abs_of_nonneg hr0]

private lemma qcc_real_density_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) (g : α → ℂ) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, (w x : ℂ) * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), Complex.real_smul]

private lemma qcc_affine_phase_integral (a b c k : ℝ) (t : ℂ) (ht : t ≠ 0) :
    let z : ℂ := t * Complex.I
    let E : ℝ → ℂ := fun r => Complex.exp (t * (r : ℂ) * Complex.I)
    (∫ r : ℝ in a..b, ((c + k * r : ℝ) : ℂ) * E r) =
      (((c + k * b : ℝ) : ℂ) * E b / z - (k : ℂ) * E b / z ^ 2) -
      (((c + k * a : ℝ) : ℂ) * E a / z - (k : ℂ) * E a / z ^ 2) := by
  dsimp only
  let z : ℂ := t * Complex.I
  let E : ℝ → ℂ := fun r => Complex.exp (t * (r : ℂ) * Complex.I)
  have hz : z ≠ 0 := mul_ne_zero ht Complex.I_ne_zero
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r _
    have he : HasDerivAt E (z * E r) r := by
      convert ((((hasDerivAt_id r).ofReal_comp).const_mul t).mul_const Complex.I).cexp using 1
      all_goals dsimp [z, E]
      all_goals ring
    have ha : HasDerivAt (fun s : ℝ => ((c + k * s : ℝ) : ℂ)) (k : ℂ) r := by
      simpa only [mul_one, id_eq] using
        (((hasDerivAt_id r).const_mul k).const_add c).ofReal_comp
    convert ((ha.mul he).div_const z).sub ((he.const_mul (k : ℂ)).div_const (z ^ 2)) using 1
    dsimp [E]
    field_simp
    ring
  · exact (show Continuous (fun r : ℝ =>
      ((c + k * r : ℝ) : ℂ) * E r) by dsimp [E]; fun_prop).intervalIntegrable a b

private lemma qcc_triangle_char (t : ℂ) :
    (∫ r : ℝ, Complex.exp (t * (r : ℂ) * Complex.I) ∂quadraticTriangleLaw) =
      if t = 0 then 1 else 2 * (1 - Complex.cos t) / t ^ 2 := by
  let := quadraticTriangle_probability_char.1
  by_cases ht : t = 0
  · simp [ht]
  · unfold quadraticTriangleLaw
    rw [qcc_real_density_integral volume _ qcc_triangle_weight_measurable
      qcc_triangle_weight_nonneg]
    rw [qcc_triangle_weighted_integral _ (by fun_prop), if_neg ht]
    have hleft := qcc_affine_phase_integral (-1) 0 1 1 t ht
    have hright := qcc_affine_phase_integral 0 1 1 (-1) t ht
    dsimp only at hleft hright
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hleft hright
    rw [hleft, hright]
    have hexp : Complex.exp (t * Complex.I) +
        Complex.exp (-t * Complex.I) = 2 * Complex.cos t := by
      simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    rw [neg_mul] at hexp
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      add_zero, Complex.ofReal_one, mul_one, one_mul, Complex.ofReal_neg,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_ofNat, sub_self, mul_neg_one]
    rw [show (t * Complex.I) ^ 2 = -t ^ 2 by rw [mul_pow, Complex.I_sq]; ring]
    field_simp
    linear_combination -Complex.I * hexp


private lemma qcc_phase_bound (z w : ℂ) (x y M1 M2 : ℝ)
    (hx : |x| ≤ M1) (hy : |y| ≤ M2) :
    ‖Complex.exp ((z * (x : ℂ) + w * (y : ℂ)) * Complex.I)‖ ≤
      Real.exp (M1 * |z.im| + M2 * |w.im|) := by
  rw [Complex.norm_exp_mul_I]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_add]
  calc
    -(z.im * x + w.im * y) ≤ |z.im * x| + |w.im * y| := by
      linarith [neg_le_abs (z.im * x), neg_le_abs (w.im * y)]
    _ = |z.im| * |x| + |w.im| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ |z.im| * M1 + |w.im| * M2 := by gcongr
    _ = _ := by ring

private lemma qcc_measure_L1 (mu : Measure (ℝ × ℝ)) [IsProbabilityMeasure mu]
    (M1 M2 : ℝ) (hsupport : ∀ᵐ p : ℝ × ℝ ∂mu, |p.1| ≤ M1 ∧ |p.2| ≤ M2)
    (z w : ℂ) :
    Integrable (fun p : ℝ × ℝ =>
      Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)) mu ∧
      ‖∫ p : ℝ × ℝ,
        Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I) ∂mu‖ ≤
        Real.exp (M1 * |z.im| + M2 * |w.im|) := by
  have hb : ∀ᵐ p : ℝ × ℝ ∂mu,
      ‖Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)‖ ≤
        Real.exp (M1 * |z.im| + M2 * |w.im|) :=
    hsupport.mono fun p hp => qcc_phase_bound z w p.1 p.2 M1 M2 hp.1 hp.2
  exact ⟨(integrable_const _).mono' (by fun_prop) hb,
    by simpa using norm_integral_le_of_norm_le (integrable_const _) hb⟩


private lemma qcc_measure_entire (mu : Measure (ℝ × ℝ)) [IsProbabilityMeasure mu]
    (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hsupport : ∀ᵐ p : ℝ × ℝ ∂mu, |p.1| ≤ M1 ∧ |p.2| ≤ M2) :
    Differentiable ℂ (fun p : ℂ × ℂ =>
      ∫ x : ℝ × ℝ,
        Complex.exp ((p.1 * (x.1 : ℂ) + p.2 * (x.2 : ℂ)) * Complex.I) ∂mu) := by
  let A : (ℝ × ℝ) → (ℂ × ℂ →L[ℂ] ℂ) := fun x =>
    ((x.1 : ℂ) * Complex.I) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      ((x.2 : ℂ) * Complex.I) • ContinuousLinearMap.snd ℂ ℂ ℂ
  let F : (ℂ × ℂ) → (ℝ × ℝ) → ℂ := fun p x => Complex.exp (A x p)
  let F' : (ℂ × ℂ) → (ℝ × ℝ) → (ℂ × ℂ →L[ℂ] ℂ) :=
    fun p x => Complex.exp (A x p) • A x
  have hval (p : ℂ × ℂ) (x : ℝ × ℝ) :
      F p x = Complex.exp ((p.1 * (x.1 : ℂ) + p.2 * (x.2 : ℂ)) * Complex.I) := by
    change Complex.exp ((x.1 : ℂ) * Complex.I * p.1 +
      (x.2 : ℂ) * Complex.I * p.2) = _
    congr 1
    ring
  have hF : Differentiable ℂ (fun p : ℂ × ℂ => ∫ x, F p x ∂mu) := by
    intro p0
    let U : Set (ℂ × ℂ) := {p | |p.1.im| < |p0.1.im| + 1 ∧
      |p.2.im| < |p0.2.im| + 1}
    let C : ℝ := Real.exp (M1 * (|p0.1.im| + 1) + M2 * (|p0.2.im| + 1))
    have hU : U ∈ nhds p0 := by
      have h1 : IsOpen {p : ℂ × ℂ | |p.1.im| < |p0.1.im| + 1} :=
        isOpen_lt (by fun_prop) continuous_const
      have h2 : IsOpen {p : ℂ × ℂ | |p.2.im| < |p0.2.im| + 1} :=
        isOpen_lt (by fun_prop) continuous_const
      have hp0 : p0 ∈ {p : ℂ × ℂ | |p.1.im| < |p0.1.im| + 1} ∩
          {p : ℂ × ℂ | |p.2.im| < |p0.2.im| + 1} := by
        exact ⟨show |p0.1.im| < |p0.1.im| + 1 by linarith,
          show |p0.2.im| < |p0.2.im| + 1 by linarith⟩
      exact (h1.inter h2).mem_nhds hp0
    have hi : Integrable (F p0) mu := by
      change Integrable (fun x => F p0 x) mu
      simp_rw [hval]
      exact (qcc_measure_L1 mu M1 M2 hsupport p0.1 p0.2).1
    have hderiv (p : ℂ × ℂ) (x : ℝ × ℝ) :
        HasFDerivAt (fun p => F p x) (F' p x) p := (A x).hasFDerivAt.cexp
    have hb : ∀ᵐ x : ℝ × ℝ ∂mu, ∀ p ∈ U, ‖F' p x‖ ≤ (M1 + M2) * C := by
      filter_upwards [hsupport] with x hx
      intro p hp
      have hA : ‖A x‖ ≤ M1 + M2 := by
        apply (A x).opNorm_le_bound (add_nonneg hM1 hM2)
        intro q
        change ‖(x.1 : ℂ) * Complex.I * q.1 + (x.2 : ℂ) * Complex.I * q.2‖ ≤ _
        have hq1 : ‖q.1‖ ≤ ‖q‖ := le_max_left _ _
        have hq2 : ‖q.2‖ ≤ ‖q‖ := le_max_right _ _
        calc
          _ ≤ ‖(x.1 : ℂ) * Complex.I * q.1‖ +
              ‖(x.2 : ℂ) * Complex.I * q.2‖ := norm_add_le _ _
          _ = |x.1| * ‖q.1‖ + |x.2| * ‖q.2‖ := by
            simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ M1 * ‖q‖ + M2 * ‖q‖ :=
            add_le_add (mul_le_mul hx.1 hq1 (norm_nonneg _) hM1)
              (mul_le_mul hx.2 hq2 (norm_nonneg _) hM2)
          _ = _ := by ring
      have hFval : ‖F p x‖ ≤ C := by
        rw [hval]
        refine (qcc_phase_bound p.1 p.2 x.1 x.2 M1 M2 hx.1 hx.2).trans ?_
        apply Real.exp_le_exp.mpr
        exact add_le_add (mul_le_mul_of_nonneg_left hp.1.le hM1)
          (mul_le_mul_of_nonneg_left hp.2.le hM2)
      calc
        _ = ‖F p x‖ * ‖A x‖ := norm_smul _ _
        _ ≤ C * (M1 + M2) := mul_le_mul hFval hA (norm_nonneg _) (Real.exp_pos _).le
        _ = _ := mul_comm _ _
    exact (hasFDerivAt_integral_of_dominated_of_fderiv_le (F := F) (F' := F') hU
      (Filter.Eventually.of_forall fun p => (show Continuous (F p) by
        change Continuous (fun x => F p x)
        simp_rw [hval]
        fun_prop).aestronglyMeasurable)
      hi (show Continuous (F' p0) by dsimp [F', A]; fun_prop).aestronglyMeasurable hb
      (integrable_const _) (Filter.Eventually.of_forall fun x p _ => hderiv p x)).differentiableAt
  convert hF using 1
  funext p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (hval p x).symm


private lemma qcc_chord_support (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    ∀ᵐ p : ℝ × ℝ ∂quadraticChordLaw nu, |p.1| ≤ 2 * h ∧ |p.2| ≤ 4 * h ^ 2 := by
  filter_upwards [(quadraticChord_law_data nu h3 hV h hh hs).2.2.1] with p hp
  exact ⟨hp.1, hp.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hp.1 (by positivity : 0 ≤ 2 * h)])⟩

private lemma qcc_full_support (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
    ∀ᵐ p : ℝ × ℝ ∂quadraticFullNoiseLaw nu,
      |p.1| ≤ 32 * h + |gamma| ∧ |p.2| ≤ 64 * h ^ 2 := by
  dsimp only
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
  obtain ⟨hf, hi, _, _⟩ := quadraticFullNoise_law_data nu h3 hV h hh hs
  let := hf
  let := hi
  let := (quadraticChord_law_data nu h3 hV h hh hs).2.1
  let := sourceScalarLaw_data.1
  have hfamily : ∀ᵐ p : Fin 8 → ℝ × ℝ ∂quadraticChordFamilyLaw nu,
      ∀ j, |(p j).1| ≤ 2 * h ∧ |(p j).2| ≤ 4 * h ^ 2 := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval (fun _ : Fin 8 => quadraticChordLaw nu) j).quasiMeasurePreserving.ae
      (qcc_chord_support nu h3 hV h hh hs)
  have hp : ∀ᵐ p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)
      ∂(quadraticChordFamilyLaw nu).prod (quadraticChordFamilyLaw nu),
      (∀ j, |(p.1 j).1| ≤ 2 * h ∧ |(p.1 j).2| ≤ 4 * h ^ 2) ∧
      (∀ j, |(p.2 j).1| ≤ 2 * h ∧ |(p.2 j).2| ≤ 4 * h ^ 2) :=
    (measurePreserving_fst.quasiMeasurePreserving.ae hfamily).and
      (measurePreserving_snd.quasiMeasurePreserving.ae hfamily)
  have hin : ∀ᵐ p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ ∂quadraticNoiseInputLaw nu,
      ((∀ j, |(p.1.1 j).1| ≤ 2 * h ∧ |(p.1.1 j).2| ≤ 4 * h ^ 2) ∧
       (∀ j, |(p.1.2 j).1| ≤ 2 * h ∧ |(p.1.2 j).2| ≤ 4 * h ^ 2)) ∧ |p.2| ≤ 1 :=
    (measurePreserving_fst.quasiMeasurePreserving.ae hp).and
      (measurePreserving_snd.quasiMeasurePreserving.ae sourceScalarLaw_data.2.2.1)
  unfold quadraticFullNoiseLaw
  apply (ae_map_iff (by unfold quadraticFullNoiseMap; fun_prop) (by measurability)).mpr
  filter_upwards [hin] with p hp
  have hsum (f : Fin 8 → ℝ) (C : ℝ) (hf : ∀ j, |f j| ≤ C) :
      |∑ j, f j| ≤ 8 * C := by
    calc
      _ ≤ ∑ j : Fin 8, |f j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 8, C := Finset.sum_le_sum fun j _ => hf j
      _ = _ := by simp
  have hz1 := hsum (fun j => (p.1.1 j).1) (2 * h) (fun j => (hp.1.1 j).1)
  have hz2 := hsum (fun j => (p.1.2 j).1) (2 * h) (fun j => (hp.1.2 j).1)
  have hy1 := hsum (fun j => (p.1.1 j).2) (4 * h ^ 2) (fun j => (hp.1.1 j).2)
  have hy2 := hsum (fun j => (p.1.2 j).2) (4 * h ^ 2) (fun j => (hp.1.2 j).2)
  change |(∑ j, (p.1.1 j).1) - (∑ j, (p.1.2 j).1) + gamma * p.2| ≤ _ ∧
    |(∑ j, (p.1.1 j).2) + (∑ j, (p.1.2 j).2)| ≤ _
  constructor
  · have ht : |gamma * p.2| ≤ |gamma| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hp.2 (abs_nonneg gamma)).trans_eq (mul_one _)
    linarith [abs_add_le ((∑ j, (p.1.1 j).1) - (∑ j, (p.1.2 j).1)) (gamma * p.2),
      abs_sub (∑ j, (p.1.1 j).1) (∑ j, (p.1.2 j).1)]
  · linarith [abs_add_le (∑ j, (p.1.1 j).2) (∑ j, (p.1.2 j).2)]


private lemma qcc_full_product (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (z w : ℂ) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
    quadraticFullNoiseCharComplex nu z w =
      quadraticChordCharComplex nu z w ^ 8 *
      quadraticChordCharComplex nu (-z) w ^ 8 *
      (∫ t : ℝ, Complex.exp ((gamma : ℂ) * z * (t : ℂ) * Complex.I) ∂sourceScalarLaw) := by
  dsimp only
  let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
  let F : ℂ → ℂ → (Fin 8 → ℝ × ℝ) → ℂ := fun z w p =>
    Complex.exp ((z * ((∑ j : Fin 8, (p j).1 : ℝ) : ℂ) +
      w * ((∑ j : Fin 8, (p j).2 : ℝ) : ℂ)) * Complex.I)
  let := (quadraticChord_law_data nu h3 hV h hh hs).2.1
  let := sourceScalarLaw_data.1
  let := (quadraticFullNoise_law_data nu h3 hV h hh hs).1
  have hF (z w : ℂ) (p : Fin 8 → ℝ × ℝ) : F z w p =
      ∏ j : Fin 8, Complex.exp ((z * ((p j).1 : ℂ) +
        w * ((p j).2 : ℂ)) * Complex.I) := by
    dsimp [F]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have hI (z w : ℂ) : (∫ p, F z w p ∂quadraticChordFamilyLaw nu) =
      quadraticChordCharComplex nu z w ^ 8 := by
    simp_rw [hF]
    unfold quadraticChordFamilyLaw quadraticChordCharComplex
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin 8) (μ := quadraticChordLaw nu)
        (fun p : ℝ × ℝ => Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)))
  have he (p : ((Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ)) × ℝ) :
      Complex.exp ((z * ((quadraticFullNoiseMap nu p).1 : ℂ) +
        w * ((quadraticFullNoiseMap nu p).2 : ℂ)) * Complex.I) =
      (F z w p.1.1 * F (-z) w p.1.2) *
        Complex.exp ((gamma : ℂ) * z * (p.2 : ℂ) * Complex.I) := by
    dsimp [F, quadraticFullNoiseMap, gamma]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold quadraticFullNoiseCharComplex quadraticFullNoiseLaw
  rw [integral_map (by unfold quadraticFullNoiseMap; fun_prop) (by fun_prop)]
  simp_rw [he]
  unfold quadraticNoiseInputLaw
  rw [integral_prod_mul (fun p : (Fin 8 → ℝ × ℝ) × (Fin 8 → ℝ × ℝ) =>
      F z w p.1 * F (-z) w p.2)
    (fun t : ℝ => Complex.exp ((gamma : ℂ) * z * (t : ℂ) * Complex.I)),
    integral_prod_mul (F z w) (F (-z) w), hI, hI]


private lemma qcc_triangle_support : ∀ᵐ r : ℝ ∂quadraticTriangleLaw, |r| ≤ 1 := by
  rw [ae_iff]
  change volume.withDensity _ {r : ℝ | ¬ |r| ≤ 1} = 0
  have hs : MeasurableSet {r : ℝ | ¬ |r| ≤ 1} :=
    (measurableSet_le continuous_abs.measurable measurable_const).compl
  rw [withDensity_apply _ hs]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hs] with r hr
  simp [hr]

private lemma qcc_scalar_L1 (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hs : ∀ᵐ r : ℝ ∂mu, |r| ≤ M) (t : ℂ) :
    Integrable (fun r : ℝ => Complex.exp (t * (r : ℂ) * Complex.I)) mu ∧
      ‖∫ r : ℝ, Complex.exp (t * (r : ℂ) * Complex.I) ∂mu‖ ≤
        Real.exp (M * |t.im|) := by
  have hb : ∀ᵐ r : ℝ ∂mu, ‖Complex.exp (t * (r : ℂ) * Complex.I)‖ ≤
      Real.exp (M * |t.im|) := by
    filter_upwards [hs] with r hr
    simpa using qcc_phase_bound t 0 r 0 M 0 hr (by simp)
  exact ⟨(integrable_const _).mono' (by fun_prop) hb,
    by simpa using norm_integral_le_of_norm_le (integrable_const _) hb⟩

private lemma qcc_pair_support (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    ∀ᵐ p : ℝ × ℝ ∂nu.prod nu, |p.1| ≤ h ∧ |p.2| ≤ h :=
  (measurePreserving_fst.quasiMeasurePreserving.ae hs).and
    (measurePreserving_snd.quasiMeasurePreserving.ae hs)

private lemma qcc_quotient_relation (d : ℝ) (theta : ℂ) :
    (((d ^ 2 / 2 : ℝ) : ℂ) *
      (if (d : ℂ) * theta = 0 then 1 else
        2 * (1 - Complex.cos ((d : ℂ) * theta)) / ((d : ℂ) * theta) ^ 2)) =
    if theta = 0 then ((d ^ 2 / 2 : ℝ) : ℂ) else
      (1 - Complex.cos ((d : ℂ) * theta)) / theta ^ 2 := by
  by_cases ht : theta = 0
  · simp [ht]
  · by_cases hd : d = 0
    · simp [hd, ht]
    · simp only [ht, mul_ne_zero (Complex.ofReal_ne_zero.mpr hd) ht, ite_false]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hd, ht]

private lemma qcc_quotient_integrable (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) (z w : ℂ) :
    Integrable (fun p : ℝ × ℝ =>
      if z + w * ((p.1 + p.2 : ℝ) : ℂ) = 0 then
        (((p.1 - p.2) ^ 2 / 2 : ℝ) : ℂ)
      else (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
        (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) /
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)) ^ 2) (nu.prod nu) := by
  let := quadraticTriangle_probability_char.1
  let C : ℝ := Real.exp (2 * h * (‖z‖ + 2 * h * ‖w‖))
  refine (integrable_const (2 * h ^ 2 * C)).mono' ?_ ?_
  · exact (Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
      (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · filter_upwards [qcc_pair_support nu h hs] with p hp
    let d : ℝ := p.1 - p.2
    let theta : ℂ := z + w * ((p.1 + p.2 : ℝ) : ℂ)
    have hd : |d| ≤ 2 * h := (abs_sub _ _).trans (by linarith [hp.1, hp.2])
    have ha : |p.1 + p.2| ≤ 2 * h := (abs_add_le _ _).trans (by linarith [hp.1, hp.2])
    have htheta : ‖theta‖ ≤ ‖z‖ + 2 * h * ‖w‖ := by
      calc
        _ ≤ ‖z‖ + ‖w * ((p.1 + p.2 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖z‖ + ‖w‖ * |p.1 + p.2| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ha (norm_nonneg w)]
    have him : |((d : ℂ) * theta).im| ≤ 2 * h * (‖z‖ + 2 * h * ‖w‖) := by
      refine (Complex.abs_im_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hd htheta (norm_nonneg _) (by positivity)
    have htri := (qcc_scalar_L1 quadraticTriangleLaw 1 qcc_triangle_support
      ((d : ℂ) * theta)).2
    rw [one_mul] at htri
    have htriC : ‖∫ r : ℝ, Complex.exp ((d : ℂ) * theta * (r : ℂ) * Complex.I)
        ∂quadraticTriangleLaw‖ ≤ C := htri.trans (Real.exp_le_exp.mpr him)
    change ‖if theta = 0 then ((d ^ 2 / 2 : ℝ) : ℂ) else
      (1 - Complex.cos ((d : ℂ) * theta)) / theta ^ 2‖ ≤ _
    rw [← qcc_quotient_relation, ← qcc_triangle_char, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ d ^ 2 / 2)]
    have hd2 : d ^ 2 / 2 ≤ 2 * h ^ 2 := by
      nlinarith [sq_abs d, mul_nonneg (sub_nonneg.mpr hd) (by positivity : 0 ≤ 2 * h + |d|)]
    exact mul_le_mul hd2 htriC (norm_nonneg _) (by positivity)

private lemma qcc_chord_exact (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hs : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) (z w : ℂ) :
    quadraticChordCharComplex nu z w =
      (∫ p : ℝ × ℝ,
        if z + w * ((p.1 + p.2 : ℝ) : ℂ) = 0 then
          (((p.1 - p.2) ^ 2 / 2 : ℝ) : ℂ)
        else (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) /
            (z + w * ((p.1 + p.2 : ℝ) : ℂ)) ^ 2 ∂nu.prod nu) /
        (variance (id : ℝ → ℝ) nu : ℂ) := by
  let := (quadraticChord_law_data nu h3 hV h hh hs).1
  let := (quadraticChord_law_data nu h3 hV h hh hs).2.1
  let := quadraticTriangle_probability_char.1
  let P : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p =>
    (p.2 * (p.1.1 - p.1.2), p.2 * (p.1.1 ^ 2 - p.1.2 ^ 2))
  let f : ℝ × ℝ → ℂ := fun p =>
    Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I)
  have hiL := (qcc_measure_L1 (quadraticChordLaw nu) (2 * h) (4 * h ^ 2)
    (qcc_chord_support nu h3 hV h hh hs) z w).1
  have hiP : Integrable (f ∘ P) ((quadraticBiasedPairLaw nu).prod quadraticTriangleLaw) :=
    hiL.comp_aemeasurable (f := P) (by fun_prop)
  have he : f ∘ P = fun p : (ℝ × ℝ) × ℝ =>
      Complex.exp ((((p.1.1 - p.1.2 : ℝ) : ℂ) *
        (z + w * ((p.1.1 + p.1.2 : ℝ) : ℂ))) * (p.2 : ℂ) * Complex.I) := by
    funext p
    dsimp [f, P]
    congr 1
    push_cast
    ring
  have hk : quadraticChordCharComplex nu z w =
      ∫ p : ℝ × ℝ, (if ((p.1 - p.2 : ℝ) : ℂ) *
        (z + w * ((p.1 + p.2 : ℝ) : ℂ)) = 0 then 1 else
        2 * (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) /
          (((p.1 - p.2 : ℝ) : ℂ) * (z + w * ((p.1 + p.2 : ℝ) : ℂ))) ^ 2)
        ∂quadraticBiasedPairLaw nu := by
    change (∫ p, f p ∂Measure.map P
      ((quadraticBiasedPairLaw nu).prod quadraticTriangleLaw)) = _
    rw [integral_map (by fun_prop) (by dsimp [f]; fun_prop)]
    change (∫ p, (f ∘ P) p ∂_) = _
    rw [he, integral_prod _ (he ▸ hiP)]
    simp_rw [qcc_triangle_char]
  rw [hk]
  unfold quadraticBiasedPairLaw
  rw [qcc_real_density_integral _ _ (by fun_prop)
    (fun p => div_nonneg (sq_nonneg _) (by positivity))]
  have heq (p : ℝ × ℝ) :
      (((p.1 - p.2) ^ 2 / (2 * variance (id : ℝ → ℝ) nu) : ℝ) : ℂ) *
        (if ((p.1 - p.2 : ℝ) : ℂ) * (z + w * ((p.1 + p.2 : ℝ) : ℂ)) = 0
          then 1 else 2 * (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
            (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) /
            (((p.1 - p.2 : ℝ) : ℂ) * (z + w * ((p.1 + p.2 : ℝ) : ℂ))) ^ 2) =
      (if z + w * ((p.1 + p.2 : ℝ) : ℂ) = 0 then
        (((p.1 - p.2) ^ 2 / 2 : ℝ) : ℂ)
      else (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
        (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) /
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)) ^ 2) /
        (variance (id : ℝ → ℝ) nu : ℂ) := by
    rw [← qcc_quotient_relation]
    push_cast
    ring
  simp_rw [heq]
  rw [integral_div]


private lemma qcc_tilt_compare (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h lam b s : ℝ) (hh : 0 < h) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam) (hs : 0 ≤ s) (hslope : s * h ≤ lam)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    IsProbabilityMeasure rho ∧
      ∀ g : ℝ → ℝ, Integrable g nu → (∀ a, 0 ≤ g a) →
        (∫ a : ℝ, g a ∂nu) ≤ Real.exp (4 * lam * h) * ∫ a : ℝ, g a ∂rho := by
  dsimp only
  let S : ℝ := |b| * h + s * h ^ 2
  let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
  have habs : |b| = lam := by rcases hb with rfl | rfl <;> simp [abs_of_nonneg hlam]
  have hS : S ≤ 2 * lam * h := by
    dsimp [S]
    rw [habs]
    nlinarith [mul_le_mul_of_nonneg_right hslope hh.le]
  rcases boundedQuadraticTilt_density_moments nu h b s hh hs hsupport with
    ⟨_, _, _, _, _, _, hrho, _, _, _, _, _, _, hc, _⟩
  let := hrho
  refine ⟨hrho, ?_⟩
  intro g hi hg
  have hg0 : 0 ≤ ∫ a, g a ∂rho := integral_nonneg hg
  have hlow := (hc g hi (Filter.Eventually.of_forall hg)).1
  have he : Real.exp (2 * S) * Real.exp (-(2 * S)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ = Real.exp (2 * S) * (Real.exp (-(2 * S)) * ∫ a, g a ∂nu) := by rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (2 * S) * ∫ a, g a ∂rho :=
      mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hg0

private lemma qcc_gap_integrable (mu rho : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure rho] (u v : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))) (mu.prod rho) := by
  refine (integrable_const (2 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall ?_)
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  linarith [Real.neg_one_le_cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))]

private lemma qcc_pair_gap_compare (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h lam b s : ℝ) (hh : 0 < h) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam) (hs : 0 ≤ s) (hslope : s * h ≤ lam)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) (u v : ℝ) :
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    (∫ p : ℝ × ℝ, 1 - Real.cos
      ((p.1 - p.2) * (u + v * (p.1 + p.2))) ∂nu.prod nu) ≤
      Real.exp (8 * lam * h) * (1 - ‖quadraticChar rho u v‖ ^ 2) := by
  dsimp only
  let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
  obtain ⟨hprob, hc⟩ := qcc_tilt_compare nu h lam b s hh hlam hb hs hslope hsupport
  let := hprob
  let G : ℝ × ℝ → ℝ := fun p =>
    1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))
  have hG (p : ℝ × ℝ) : 0 ≤ G p := sub_nonneg.mpr (Real.cos_le_one _)
  have hinner (a : ℝ) :
      (∫ a' : ℝ, G (a, a') ∂nu) ≤ Real.exp (4 * lam * h) * ∫ a' : ℝ, G (a, a') ∂rho := by
    apply hc
    · refine (integrable_const (2 : ℝ)).mono' (by dsimp [G]; fun_prop) (Filter.Eventually.of_forall ?_)
      intro a'
      rw [Real.norm_eq_abs, abs_of_nonneg (hG _)]
      dsimp [G]
      linarith [Real.neg_one_le_cos ((a - a') * (u + v * (a + a')))]
    · intro a'
      exact hG _
  have hFnu : Integrable (fun a => ∫ a', G (a, a') ∂rho) nu :=
    (qcc_gap_integrable nu rho u v).integral_prod_left
  have hFnonneg (a : ℝ) : 0 ≤ ∫ a', G (a, a') ∂rho := integral_nonneg fun a' => hG _
  have hout := hc (fun a => ∫ a', G (a, a') ∂rho) hFnu hFnonneg
  rw [quadraticChar_gap_identity rho u v]
  change (∫ p, G p ∂nu.prod nu) ≤ Real.exp (8 * lam * h) * ∫ p, G p ∂rho.prod rho
  rw [integral_prod _ (qcc_gap_integrable nu nu u v),
    integral_prod _ (qcc_gap_integrable rho rho u v)]
  calc
    _ ≤ ∫ a, Real.exp (4 * lam * h) * (∫ a', G (a, a') ∂rho) ∂nu :=
      integral_mono ((qcc_gap_integrable nu nu u v).integral_prod_left)
        (hFnu.const_mul _) hinner
    _ = Real.exp (4 * lam * h) * ∫ a, (∫ a', G (a, a') ∂rho) ∂nu := integral_const_mul _ _
    _ ≤ Real.exp (4 * lam * h) *
        (Real.exp (4 * lam * h) * ∫ a, (∫ a', G (a, a') ∂rho) ∂rho) :=
      mul_le_mul_of_nonneg_left hout (Real.exp_pos _).le
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]; congr 2 <;> ring


private lemma qcc_cone_geometry (a a' h u v lam b s : ℝ)
    (hh : 0 < h) (ha : |a| ≤ h) (ha' : |a'| ≤ h)
    (hv : |v| ≤ |u| / (4 * h)) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam) (hs : 0 ≤ s) (hslope : s * h ≤ lam) :
    let t := u + v * (a + a')
    let B := -b + s * (a + a')
    |u| / 2 ≤ |t| ∧ |B| ≤ 3 * lam ∧ |(a - a') * B| ≤ 6 * lam * h := by
  dsimp only
  have hsum : |a + a'| ≤ 2 * h := (abs_add_le a a').trans (by linarith)
  have hdiff : |a - a'| ≤ 2 * h := (abs_sub a a').trans (by linarith)
  have hprod : |v * (a + a')| ≤ |u| / 2 := by
    rw [abs_mul]
    calc
      _ ≤ (|u| / (4 * h)) * (2 * h) := mul_le_mul hv hsum (abs_nonneg _) (by positivity)
      _ = _ := by field_simp; ring
  have hreal : |u| / 2 ≤ |u + v * (a + a')| := by
    have ht := abs_sub (u + v * (a + a')) (v * (a + a'))
    rw [add_sub_cancel_right] at ht
    linarith
  have habs : |b| = lam := by rcases hb with rfl | rfl <;> simp [abs_of_nonneg hlam]
  have hB : |-b + s * (a + a')| ≤ 3 * lam := by
    calc
      _ ≤ |-b| + |s * (a + a')| := abs_add_le _ _
      _ = lam + s * |a + a'| := by rw [abs_neg, habs, abs_mul, abs_of_nonneg hs]
      _ ≤ lam + s * (2 * h) := by gcongr
      _ ≤ _ := by linarith
  refine ⟨hreal, hB, ?_⟩
  rw [abs_mul]
  calc
    _ ≤ (2 * h) * (3 * lam) := mul_le_mul hdiff hB (abs_nonneg _) (by positivity)
    _ = _ := by ring

private lemma qcc_cone_point (a a' h u v lam b s : ℝ)
    (hh : 0 < h) (ha : |a| ≤ h) (ha' : |a'| ≤ h)
    (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) (hlam : 0 ≤ lam)
    (hb : b = lam ∨ b = -lam) (hs : 0 ≤ s) (hslope : s * h ≤ lam) :
    let theta : ℂ := (u : ℂ) - (b : ℂ) * Complex.I +
      ((v : ℂ) + (s : ℂ) * Complex.I) * ((a + a' : ℝ) : ℂ)
    |u| / 2 ≤ ‖theta‖ ∧ theta ≠ 0 ∧
      ‖if theta = 0 then (((a - a') ^ 2 / 2 : ℝ) : ℂ) else
        (1 - Complex.cos (((a - a' : ℝ) : ℂ) * theta)) / theta ^ 2‖ ≤
        8 * Real.exp (6 * lam * h) / u ^ 2 *
          (1 - Real.cos ((a - a') * (u + v * (a + a'))) +
            9 * lam ^ 2 * (a - a') ^ 2) := by
  dsimp only
  let d : ℝ := a - a'
  let t : ℝ := u + v * (a + a')
  let B : ℝ := -b + s * (a + a')
  let theta : ℂ := (u : ℂ) - (b : ℂ) * Complex.I +
    ((v : ℂ) + (s : ℂ) * Complex.I) * ((a + a' : ℝ) : ℂ)
  obtain ⟨ht, hB, hdB⟩ := qcc_cone_geometry a a' h u v lam b s hh ha ha' hv hlam hb hs hslope
  have htheta : theta = (t : ℂ) + (B : ℂ) * Complex.I := by
    dsimp [theta, t, B]
    push_cast
    ring
  have hnorm : |u| / 2 ≤ ‖theta‖ := by
    have hre : theta.re = t := by rw [htheta]; simp
    have hr := Complex.abs_re_le_norm theta
    rw [hre] at hr
    exact ht.trans hr
  have hne : theta ≠ 0 := by
    intro he
    have := abs_pos.mpr hu
    rw [he, norm_zero] at hnorm
    linarith
  refine ⟨hnorm, hne, ?_⟩
  have hphase : (d : ℂ) * theta = ((d * t : ℝ) : ℂ) +
      ((d * B : ℝ) : ℂ) * Complex.I := by
    rw [htheta]
    push_cast
    ring
  have hnum := complex_cosine_chord_bound (d * t) (d * B)
  rw [← hphase] at hnum
  have hB2 : B ^ 2 ≤ 9 * lam ^ 2 := by
    nlinarith [sq_abs B, mul_nonneg (sub_nonneg.mpr hB)
      (by positivity : 0 ≤ 3 * lam + |B|)]
  have hdB2 : (d * B) ^ 2 ≤ 9 * lam ^ 2 * d ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hB2 (sq_nonneg d)]
  have hg : 0 ≤ 1 - Real.cos (d * t) := sub_nonneg.mpr (Real.cos_le_one _)
  have hnum' : ‖1 - Complex.cos ((d : ℂ) * theta)‖ ≤
      2 * Real.exp (6 * lam * h) * (1 - Real.cos (d * t) + 9 * lam ^ 2 * d ^ 2) := by
    refine hnum.trans ?_
    gcongr
  have hsq : u ^ 2 / 4 ≤ ‖theta‖ ^ 2 := by
    nlinarith [sq_abs u, norm_nonneg theta,
      mul_nonneg (by linarith : 0 ≤ ‖theta‖ - |u| / 2)
        (by positivity : 0 ≤ ‖theta‖ + |u| / 2)]
  change ‖if theta = 0 then ((d ^ 2 / 2 : ℝ) : ℂ) else
    (1 - Complex.cos ((d : ℂ) * theta)) / theta ^ 2‖ ≤ _
  rw [ite_eq_right hne, norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hne) 2)).mpr
  calc
    _ ≤ 2 * Real.exp (6 * lam * h) *
        (1 - Real.cos (d * t) + 9 * lam ^ 2 * d ^ 2) := hnum'
    _ = (8 * Real.exp (6 * lam * h) / u ^ 2 *
        (1 - Real.cos (d * t) + 9 * lam ^ 2 * d ^ 2)) * (u ^ 2 / 4) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)


private lemma qcc_cone_bound (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (lam b s : ℝ) (hlam : 0 ≤ lam) (hb : b = lam ∨ b = -lam)
    (hs : 0 ≤ s) (hslope : s * h ≤ lam)
    (u v : ℝ) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    ‖quadraticChordCharComplex nu ((u : ℂ) - (b : ℂ) * Complex.I)
      ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤
      144 * Real.exp (14 * lam * h) *
        ((1 - ‖quadraticChar rho u v‖ ^ 2) / variance (id : ℝ → ℝ) nu + lam ^ 2) / u ^ 2 := by
  dsimp only
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
  let z : ℂ := (u : ℂ) - (b : ℂ) * Complex.I
  let w : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
  let Q : ℝ × ℝ → ℂ := fun p =>
    if z + w * ((p.1 + p.2 : ℝ) : ℂ) = 0 then
      (((p.1 - p.2) ^ 2 / 2 : ℝ) : ℂ)
    else (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
      (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) / (z + w * ((p.1 + p.2 : ℝ) : ℂ)) ^ 2
  let G : ℝ × ℝ → ℝ := fun p =>
    1 - Real.cos ((p.1 - p.2) * (u + v * (p.1 + p.2)))
  let gap : ℝ := 1 - ‖quadraticChar rho u v‖ ^ 2
  let := (qcc_tilt_compare nu h lam b s hh hlam hb hs hslope hsupport).1
  have hgap : 0 ≤ gap := by
    have hc := norm_quadraticChar_le_one rho u v
    dsimp [gap]
    nlinarith [norm_nonneg (quadraticChar rho u v)]
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hQi : Integrable Q (nu.prod nu) := qcc_quotient_integrable nu h hh hsupport z w
  have hGi : Integrable G (nu.prod nu) := qcc_gap_integrable nu nu u v
  obtain ⟨hDi, hDm⟩ := quadratic_pair_square_moment nu h3
  have hmajor : Integrable (fun p : ℝ × ℝ => 8 * Real.exp (6 * lam * h) / u ^ 2 *
      (G p + 9 * lam ^ 2 * (p.1 - p.2) ^ 2)) (nu.prod nu) :=
    (hGi.add (hDi.const_mul _)).const_mul _
  have hpoint : ∀ᵐ p : ℝ × ℝ ∂nu.prod nu, ‖Q p‖ ≤
      8 * Real.exp (6 * lam * h) / u ^ 2 * (G p + 9 * lam ^ 2 * (p.1 - p.2) ^ 2) := by
    filter_upwards [qcc_pair_support nu h hsupport] with p hp
    exact (qcc_cone_point p.1 p.2 h u v lam b s hh hp.1 hp.2 hu hv hlam hb hs hslope).2.2
  have hK := qcc_chord_exact nu h3 hV h hh hsupport z w
  have hGc : (∫ p, G p ∂nu.prod nu) ≤ Real.exp (8 * lam * h) * gap :=
    qcc_pair_gap_compare nu h lam b s hh hlam hb hs hslope hsupport u v
  have he : Real.exp (6 * lam * h) * Real.exp (8 * lam * h) = Real.exp (14 * lam * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he6 : Real.exp (6 * lam * h) ≤ Real.exp (14 * lam * h) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hlam hh.le])
  calc
    _ = ‖∫ p, Q p ∂nu.prod nu‖ / V := by
      rw [hK, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV]
    _ ≤ (∫ p, ‖Q p‖ ∂nu.prod nu) / V :=
      div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) hV.le
    _ ≤ (∫ p, 8 * Real.exp (6 * lam * h) / u ^ 2 *
        (G p + 9 * lam ^ 2 * (p.1 - p.2) ^ 2) ∂nu.prod nu) / V :=
      div_le_div_of_nonneg_right (integral_mono_ae hQi.norm hmajor hpoint) hV.le
    _ = 8 * Real.exp (6 * lam * h) / (V * u ^ 2) *
        ((∫ p, G p ∂nu.prod nu) + 18 * lam ^ 2 * V) := by
      rw [integral_const_mul, integral_add hGi (hDi.const_mul _), integral_const_mul, hDm]
      dsimp [V]
      ring
    _ ≤ 8 * Real.exp (6 * lam * h) / (V * u ^ 2) *
        (Real.exp (8 * lam * h) * gap + 18 * lam ^ 2 * V) :=
      mul_le_mul_of_nonneg_left (add_le_add hGc le_rfl) (by positivity)
    _ = 8 * Real.exp (14 * lam * h) * gap / (V * u ^ 2) +
        144 * Real.exp (6 * lam * h) * lam ^ 2 / u ^ 2 := by
      calc
        _ = 8 * (Real.exp (6 * lam * h) * Real.exp (8 * lam * h)) * gap / (V * u ^ 2) +
            144 * Real.exp (6 * lam * h) * lam ^ 2 / u ^ 2 := by field_simp [show V ≠ 0 from hV.ne', hu]; ring
        _ = _ := by rw [he]
    _ ≤ 144 * Real.exp (14 * lam * h) * gap / (V * u ^ 2) +
        144 * Real.exp (14 * lam * h) * lam ^ 2 / u ^ 2 := by
      apply add_le_add
      · gcongr <;> norm_num
      · gcongr
    _ = _ := by
      change 144 * Real.exp (14 * lam * h) * gap / (V * u ^ 2) +
        144 * Real.exp (14 * lam * h) * lam ^ 2 / u ^ 2 =
        144 * Real.exp (14 * lam * h) * (gap / V + lam ^ 2) / u ^ 2
      field_simp [show V ≠ 0 from hV.ne', hu] <;> ring


theorem quadraticComplexChord_extension_and_cone
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h) :
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂nu) / V
    let Q : ℂ → ℂ → ℝ × ℝ → ℂ := fun z w p =>
      if z + w * ((p.1 + p.2 : ℝ) : ℂ) = 0 then
        (((p.1 - p.2) ^ 2 / 2 : ℝ) : ℂ)
      else
        (1 - Complex.cos (((p.1 - p.2 : ℝ) : ℂ) *
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)))) /
          (z + w * ((p.1 + p.2 : ℝ) : ℂ)) ^ 2
    let S : ℂ → ℂ := fun z =>
      ∫ t : ℝ, Complex.exp
        ((gamma : ℂ) * z * (t : ℂ) * Complex.I) ∂sourceScalarLaw
    IsProbabilityMeasure (quadraticChordLaw nu) ∧
      IsProbabilityMeasure (quadraticFullNoiseLaw nu) ∧
      Differentiable ℂ (fun p : ℂ × ℂ =>
        quadraticChordCharComplex nu p.1 p.2) ∧
      Differentiable ℂ (fun p : ℂ × ℂ =>
        quadraticFullNoiseCharComplex nu p.1 p.2) ∧
      (∀ z w : ℂ,
        Integrable (fun p : ℝ × ℝ =>
          Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I))
          (quadraticChordLaw nu) ∧
        Integrable (Q z w) (nu.prod nu) ∧
        quadraticChordCharComplex nu z w =
          (∫ p : ℝ × ℝ, Q z w p ∂nu.prod nu) / (V : ℂ) ∧
        ‖quadraticChordCharComplex nu z w‖ ≤
          Real.exp (2 * h * |z.im| + 4 * h ^ 2 * |w.im|) ∧
        Integrable (fun p : ℝ × ℝ =>
          Complex.exp ((z * (p.1 : ℂ) + w * (p.2 : ℂ)) * Complex.I))
          (quadraticFullNoiseLaw nu) ∧
        Integrable (fun t : ℝ => Complex.exp
          ((gamma : ℂ) * z * (t : ℂ) * Complex.I)) sourceScalarLaw ∧
        ‖S z‖ ≤ Real.exp (|gamma| * |z.im|) ∧
        quadraticFullNoiseCharComplex nu z w =
          quadraticChordCharComplex nu z w ^ 8 *
          quadraticChordCharComplex nu (-z) w ^ 8 * S z) ∧
      (∀ u v : ℝ,
        quadraticChordCharComplex nu (u : ℂ) (v : ℂ) =
          quadraticChordChar nu u v ∧
        quadraticFullNoiseCharComplex nu (u : ℂ) (v : ℂ) =
          quadraticFullNoiseChar nu u v) ∧
      ∀ lam b s : ℝ, 0 ≤ lam → (b = lam ∨ b = -lam) →
        0 ≤ s → s ≤ lam ^ 2 → s * h ≤ lam →
        let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
        IsProbabilityMeasure rho ∧
          ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
            let theta : ℝ × ℝ → ℂ := fun p =>
              (u : ℂ) - (b : ℂ) * Complex.I +
              ((v : ℂ) + (s : ℂ) * Complex.I) *
                ((p.1 + p.2 : ℝ) : ℂ)
            (∀ᵐ p : ℝ × ℝ ∂nu.prod nu,
              |u| / 2 ≤ ‖theta p‖ ∧ theta p ≠ 0) ∧
            ‖quadraticChordCharComplex nu
                ((u : ℂ) - (b : ℂ) * Complex.I)
                ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤
              144 * Real.exp (14 * lam * h) *
                ((1 - ‖quadraticChar rho u v‖ ^ 2) / V + lam ^ 2) /
                  u ^ 2 := by
  dsimp only
  obtain ⟨_, hchord, _, _⟩ := quadraticChord_law_data nu h3 hV h hh hsupport
  obtain ⟨_, _, hfull, _⟩ := quadraticFullNoise_law_data nu h3 hV h hh hsupport
  let := hchord
  let := hfull
  let := sourceScalarLaw_data.1
  have hcs := qcc_chord_support nu h3 hV h hh hsupport
  have hfs := qcc_full_support nu h3 hV h hh hsupport
  refine ⟨hchord, hfull, ?_, ?_, ?_, ?_, ?_⟩
  · exact qcc_measure_entire (quadraticChordLaw nu) (2 * h) (4 * h ^ 2)
      (by positivity) (by positivity) hcs
  · exact qcc_measure_entire (quadraticFullNoiseLaw nu)
      (32 * h + |(∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu|)
      (64 * h ^ 2) (by positivity) (by positivity) hfs
  · intro z w
    have hk := qcc_measure_L1 (quadraticChordLaw nu) (2 * h) (4 * h ^ 2) hcs z w
    have hf := qcc_measure_L1 (quadraticFullNoiseLaw nu)
      (32 * h + |(∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu|)
      (64 * h ^ 2) hfs z w
    have hs := qcc_scalar_L1 sourceScalarLaw 1 sourceScalarLaw_data.2.2.1
      (((((∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu : ℝ)) : ℂ) * z)
    refine ⟨hk.1, qcc_quotient_integrable nu h hh hsupport z w,
      qcc_chord_exact nu h3 hV h hh hsupport z w, hk.2, hf.1, hs.1, ?_,
      qcc_full_product nu h3 hV h hh hsupport z w⟩
    simpa only [one_mul, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      zero_mul, add_zero, abs_mul] using hs.2
  · intro u v
    simp only [quadraticChordCharComplex, quadraticChordChar,
      quadraticFullNoiseCharComplex, quadraticFullNoiseChar,
      Complex.ofReal_add, Complex.ofReal_mul, and_self]
  · intro lam b s hlam hb hs hsquare hslope
    refine ⟨(qcc_tilt_compare nu h lam b s hh hlam hb hs hslope hsupport).1, ?_⟩
    intro u v hu hv
    constructor
    · filter_upwards [qcc_pair_support nu h hsupport] with p hp
      have hc := qcc_cone_point p.1 p.2 h u v lam b s hh hp.1 hp.2 hu hv hlam hb hs hslope
      exact ⟨hc.1, hc.2.1⟩
    · exact qcc_cone_bound nu h3 hV h hh hsupport lam b s hlam hb hs hslope u v hu hv


private lemma qcc_monomial_exp_bound (k : ℕ) (hk : 0 < k) (x : ℝ) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-x) ≤ (k : ℝ) ^ k := by
  have hK : (0 : ℝ) < k := by exact_mod_cast hk
  have h := (Real.mul_exp_neg_le_exp_neg_one (x / (k : ℝ))).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have hb : x * Real.exp (-(x / (k : ℝ))) ≤ k := by
    calc
      _ = ((x / (k : ℝ)) * Real.exp (-(x / (k : ℝ)))) * k := by
        field_simp
      _ ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right h hK.le
      _ = _ := one_mul _
  have hp := pow_le_pow_left₀ (mul_nonneg hx (Real.exp_pos _).le) hb k
  have he : Real.exp (-(x / (k : ℝ))) ^ k = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  simpa only [mul_pow, he] using hp

private lemma qcc_gap_power (ell j : ℕ) (hell : 0 < ell)
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z ^ ell * (1 - z ^ 2) ^ j ≤ (2 * (j : ℝ) / (ell : ℝ)) ^ j := by
  by_cases hj : j = 0
  · subst j
    simpa using (show z ^ ell ≤ 1 from pow_le_one₀ hz0 hz1)
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj
  have hL : (0 : ℝ) < ell := by exact_mod_cast hell
  let g : ℝ := 1 - z ^ 2
  have hg : 0 ≤ g := by dsimp [g]; nlinarith
  have hze : z ^ 2 ≤ Real.exp (-g) := by
    have he := Real.add_one_le_exp (-g)
    dsimp [g] at he
    linarith
  have hp := pow_le_pow_left₀ (sq_nonneg z) hze ell
  have hs : (z ^ ell) ^ 2 ≤ (Real.exp (-(ell : ℝ) * g / 2)) ^ 2 := by
    calc
      _ = (z ^ 2) ^ ell := by rw [← pow_mul, ← pow_mul]; congr 1; omega
      _ ≤ Real.exp (-g) ^ ell := hp
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hzexp : z ^ ell ≤ Real.exp (-(ell : ℝ) * g / 2) := by
    nlinarith [pow_nonneg hz0 ell, Real.exp_pos (-(ell : ℝ) * g / 2)]
  have hm := qcc_monomial_exp_bound j hjpos ((ell : ℝ) * g / 2) (by positivity)
  change z ^ ell * g ^ j ≤ _
  calc
    _ ≤ Real.exp (-(ell : ℝ) * g / 2) * g ^ j :=
      mul_le_mul_of_nonneg_right hzexp (pow_nonneg hg j)
    _ ≤ _ := by
      rw [div_pow]
      apply (le_div_iff₀ (pow_pos hL j)).mpr
      calc
        _ = (2 : ℝ) ^ j * ((((ell : ℝ) * g / 2) ^ j) *
            Real.exp (-((ell : ℝ) * g / 2))) := by
          simp only [div_pow, mul_pow]
          rw [show -(ell : ℝ) * g / 2 = -((ell : ℝ) * g / 2) by ring]
          field_simp <;> ring
        _ ≤ (2 : ℝ) ^ j * (j : ℝ) ^ j := mul_le_mul_of_nonneg_left hm (by positivity)
        _ = _ := (mul_pow _ _ _).symm

private lemma qcc_power_cancel (ell J : ℕ) (hell : 0 < ell)
    (z V lam : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hV : 0 < V) :
    z ^ ell * ((1 - z ^ 2) / V + lam ^ 2) ^ J ≤
      (2 * (J : ℝ) / ((ell : ℝ) * V) + lam ^ 2) ^ J := by
  have hL : (0 : ℝ) < ell := by exact_mod_cast hell
  have hg : 0 ≤ 1 - z ^ 2 := by nlinarith
  rw [add_pow, Finset.mul_sum, add_pow]
  apply Finset.sum_le_sum
  intro j hj
  have hjJ : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjb : z ^ ell * ((1 - z ^ 2) / V) ^ j ≤
      (2 * (J : ℝ) / ((ell : ℝ) * V)) ^ j := by
    calc
      _ = (z ^ ell * (1 - z ^ 2) ^ j) / V ^ j := by rw [div_pow]; ring
      _ ≤ (2 * (j : ℝ) / (ell : ℝ)) ^ j / V ^ j :=
        div_le_div_of_nonneg_right (qcc_gap_power ell j hell z hz0 hz1) (by positivity)
      _ ≤ (2 * (J : ℝ) / (ell : ℝ)) ^ j / V ^ j := by
        gcongr
      _ = _ := by rw [← div_pow]; congr 1 <;> field_simp <;> ring
  calc
    _ = (z ^ ell * ((1 - z ^ 2) / V) ^ j) * (lam ^ 2) ^ (J - j) *
        (J.choose j : ℝ) := by ring
    _ ≤ _ := by gcongr


private lemma qcc_K_power (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤ 2 * variance (id : ℝ → ℝ) nu)
    (lam b s : ℝ) (hlam : 0 ≤ lam) (hb : b = lam ∨ b = -lam)
    (hs : 0 ≤ s) (hslope : s * h ≤ lam)
    (ell J : ℕ) (hell : 0 < ell)
    (u v : ℝ) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    let T : ℝ := (ell : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu)
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    ‖quadraticChar rho u v‖ ^ ell *
      ‖quadraticChordCharComplex nu ((u : ℂ) - (b : ℂ) * Complex.I)
        ((v : ℂ) + (s : ℂ) * Complex.I)‖ ^ J ≤
      (144 * (1 + 4 * (J : ℝ))) ^ J * Real.exp (14 * (J : ℝ) * lam * h) *
        (T⁻¹ + lam ^ 2) ^ J / |u| ^ (2 * J) := by
  dsimp only
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let T : ℝ := (ell : ℝ) * m2
  let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
  let z0 : ℝ := ‖quadraticChar rho u v‖
  let K : ℂ := quadraticChordCharComplex nu ((u : ℂ) - (b : ℂ) * Complex.I)
    ((v : ℂ) + (s : ℂ) * Complex.I)
  let := (qcc_tilt_compare nu h lam b s hh hlam hb hs hslope hsupport).1
  have hz0 : 0 ≤ z0 := norm_nonneg _
  have hz1 : z0 ≤ 1 := norm_quadraticChar_le_one rho u v
  have hL : (0 : ℝ) < ell := by exact_mod_cast hell
  have hVm2 : V ≤ m2 := by
    simpa only [Pi.pow_apply, id_eq] using
      (variance_le_expectation_sq (μ := nu) (X := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable)
  have hm2 : 0 < m2 := hV.trans_le hVm2
  have hT : 0 < T := mul_pos hL hm2
  have hLV : 0 < (ell : ℝ) * V := mul_pos hL hV
  have hrecip : 1 / ((ell : ℝ) * V) ≤ 2 / T := by
    apply (div_le_div_iff₀ hLV hT).mpr
    dsimp [T]
    nlinarith [mul_le_mul_of_nonneg_left hm2V hL.le]
  have hclock : 2 * (J : ℝ) / ((ell : ℝ) * V) + lam ^ 2 ≤
      (1 + 4 * (J : ℝ)) * (T⁻¹ + lam ^ 2) := by
    have hr := mul_le_mul_of_nonneg_left hrecip (show 0 ≤ 2 * (J : ℝ) by positivity)
    have htinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    rw [div_eq_mul_inv, div_eq_mul_inv] at hr
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg hJ (sq_nonneg lam)]
  have hK := qcc_cone_bound nu h3 hV h hh hsupport lam b s hlam hb hs hslope u v hu hv
  have hcancel := qcc_power_cancel ell J hell z0 V lam hz0 hz1 hV
  have heJ : Real.exp (14 * lam * h) ^ J = Real.exp (14 * (J : ℝ) * lam * h) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have huJ : (u ^ 2) ^ J = |u| ^ (2 * J) := by rw [← sq_abs u, pow_mul]
  calc
    _ ≤ z0 ^ ell * (144 * Real.exp (14 * lam * h) *
        ((1 - z0 ^ 2) / V + lam ^ 2) / u ^ 2) ^ J :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg K) hK J) (pow_nonneg hz0 ell)
    _ = (144 : ℝ) ^ J * Real.exp (14 * (J : ℝ) * lam * h) *
        (z0 ^ ell * ((1 - z0 ^ 2) / V + lam ^ 2) ^ J) / |u| ^ (2 * J) := by
      rw [div_pow, mul_pow, mul_pow, heJ, huJ]
      ring
    _ ≤ (144 : ℝ) ^ J * Real.exp (14 * (J : ℝ) * lam * h) *
        (2 * (J : ℝ) / ((ell : ℝ) * V) + lam ^ 2) ^ J / |u| ^ (2 * J) := by
      gcongr
    _ ≤ (144 : ℝ) ^ J * Real.exp (14 * (J : ℝ) * lam * h) *
        ((1 + 4 * (J : ℝ)) * (T⁻¹ + lam ^ 2)) ^ J / |u| ^ (2 * J) := by
      gcongr
    _ = _ := by rw [mul_pow, mul_pow]; ring

private lemma qcc_gamma_bound (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤ 2 * variance (id : ℝ → ℝ) nu) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
    0 ≤ gamma ∧ gamma ≤ 2 * h := by
  dsimp only
  have h2 : Integrable (fun a : ℝ => a ^ 2) nu := by
    refine (integrable_const (h ^ 2)).mono' (by fun_prop) ?_
    filter_upwards [hsupport] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a), sq_abs] using
      pow_le_pow_left₀ (abs_nonneg a) ha 2
  have hm3 : (∫ a : ℝ, |a| ^ 3 ∂nu) ≤ h * ∫ a : ℝ, a ^ 2 ∂nu := by
    rw [← integral_const_mul]
    apply integral_mono_ae h3 (h2.const_mul h)
    filter_upwards [hsupport] with a ha
    have he : |a| ^ 3 = |a| * a ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg a)
  refine ⟨div_nonneg (integral_nonneg fun a => by positivity) hV.le, ?_⟩
  apply (div_le_iff₀ hV).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm2V hh.le]

private lemma qcc_shift_K_bound (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h) (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (lam b s : ℝ) (hlam : 0 ≤ lam) (hb : b = lam ∨ b = -lam)
    (hs : 0 ≤ s) (hslope : s * h ≤ lam) (u v : ℝ) :
    ‖quadraticChordCharComplex nu ((u : ℂ) - (b : ℂ) * Complex.I)
      ((v : ℂ) + (s : ℂ) * Complex.I)‖ ≤ Real.exp (6 * lam * h) := by
  let := (quadraticChord_law_data nu h3 hV h hh hsupport).2.1
  have hK := (qcc_measure_L1 (quadraticChordLaw nu) (2 * h) (4 * h ^ 2)
    (qcc_chord_support nu h3 hV h hh hsupport)
    ((u : ℂ) - (b : ℂ) * Complex.I) ((v : ℂ) + (s : ℂ) * Complex.I)).2
  have habs : |b| = lam := by rcases hb with rfl | rfl <;> simp [abs_of_nonneg hlam]
  refine hK.trans (Real.exp_le_exp.mpr ?_)
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, zero_sub,
    Complex.add_im, abs_neg, habs, abs_of_nonneg hs]
  nlinarith [mul_le_mul_of_nonneg_left hslope hh.le]


theorem quadraticComplexChord_matching_power
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (h : ℝ) (hh : 0 < h)
    (hsupport : ∀ᵐ a : ℝ ∂nu, |a| ≤ h)
    (hm2V : (∫ a : ℝ, a ^ 2 ∂nu) ≤
      2 * variance (id : ℝ → ℝ) nu)
    (lam b s : ℝ) (hlam : 0 ≤ lam) (hb : b = lam ∨ b = -lam)
    (hs : 0 ≤ s) (hsquare : s ≤ lam ^ 2) (hslope : s * h ≤ lam)
    (ell J : ℕ) (hell : 0 < ell)
    (u v : ℝ) (hu : u ≠ 0) (hv : |v| ≤ |u| / (4 * h)) :
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
    let T : ℝ := (ell : ℝ) * m2
    let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
    let reflectedRho : Measure ℝ :=
      nu.tilted (fun a => -b * a - s * a ^ 2)
    let z : ℂ := (u : ℂ) - (b : ℂ) * Complex.I
    let w : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
    let CJ : ℝ := (144 * (1 + 4 * (J : ℝ))) ^ J
    0 < T ∧
      ‖quadraticChar rho u v‖ ^ ell *
          ‖quadraticChordCharComplex nu z w‖ ^ J ≤
        CJ * Real.exp (14 * (J : ℝ) * lam * h) *
          (T⁻¹ + lam ^ 2) ^ J / |u| ^ (2 * J) ∧
      ‖quadraticChar rho u v‖ ^ ell *
          ‖quadraticFullNoiseCharComplex nu z w‖ ≤
        (4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
          (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 ∧
      ‖quadraticChar reflectedRho (-u) v‖ ^ ell *
          ‖quadraticFullNoiseCharComplex nu z w‖ ≤
        (4752 : ℝ) ^ 8 * Real.exp (162 * lam * h) *
          (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 := by
  dsimp only
  let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
  let T : ℝ := (ell : ℝ) * m2
  let rho : Measure ℝ := nu.tilted (fun a => b * a - s * a ^ 2)
  let reflectedRho : Measure ℝ := nu.tilted (fun a => -b * a - s * a ^ 2)
  let z : ℂ := (u : ℂ) - (b : ℂ) * Complex.I
  let w : ℂ := (v : ℂ) + (s : ℂ) * Complex.I
  let gamma : ℝ := (∫ a : ℝ, |a| ^ 3 ∂nu) / variance (id : ℝ → ℝ) nu
  let S : ℂ := ∫ t : ℝ, Complex.exp
    ((gamma : ℂ) * z * (t : ℂ) * Complex.I) ∂sourceScalarLaw
  have hL : (0 : ℝ) < ell := by exact_mod_cast hell
  have hm2 : 0 < m2 := hV.trans_le (by
    simpa only [Pi.pow_apply, id_eq] using
      (variance_le_expectation_sq (μ := nu) (X := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable))
  have hT : 0 < T := mul_pos hL hm2
  have hbref : -b = lam ∨ -b = -lam := by
    rcases hb with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (neg_neg lam)
  have hzneg : -z = ((-u : ℝ) : ℂ) - ((-b : ℝ) : ℂ) * Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hK := qcc_shift_K_bound nu h3 hV h hh hsupport lam b s hlam hb hs hslope u v
  have hKm : ‖quadraticChordCharComplex nu (-z) w‖ ≤ Real.exp (6 * lam * h) := by
    rw [hzneg]
    exact qcc_shift_K_bound nu h3 hV h hh hsupport lam (-b) s hlam hbref hs hslope (-u) v
  have hK8 : ‖quadraticChar rho u v‖ ^ ell * ‖quadraticChordCharComplex nu z w‖ ^ 8 ≤
      (4752 : ℝ) ^ 8 * Real.exp (112 * lam * h) * (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 := by
    convert qcc_K_power nu h3 hV h hh hsupport hm2V lam b s hlam hb hs hslope ell 8 hell u v hu hv using 1 <;> norm_num [T, m2]
  have hR8 : ‖quadraticChar reflectedRho (-u) v‖ ^ ell *
      ‖quadraticChordCharComplex nu (-z) w‖ ^ 8 ≤
      (4752 : ℝ) ^ 8 * Real.exp (112 * lam * h) * (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 := by
    rw [hzneg]
    convert qcc_K_power nu h3 hV h hh hsupport hm2V lam (-b) s hlam hbref hs hslope ell 8 hell
      (-u) v (neg_ne_zero.mpr hu) (by simpa using hv) using 1 <;> norm_num [T, m2]
  obtain ⟨hg0, hg2⟩ := qcc_gamma_bound nu h3 hV h hh hsupport hm2V
  change 0 ≤ gamma at hg0
  change gamma ≤ 2 * h at hg2
  let := sourceScalarLaw_data.1
  have habs : |b| = lam := by rcases hb with rfl | rfl <;> simp [abs_of_nonneg hlam]
  have hzIm : |z.im| = lam := by
    dsimp [z]
    simp [Complex.mul_im, habs]
  have hS : ‖S‖ ≤ Real.exp (2 * lam * h) := by
    have hc := (qcc_scalar_L1 sourceScalarLaw 1 sourceScalarLaw_data.2.2.1 ((gamma : ℂ) * z)).2
    have he : |((gamma : ℂ) * z).im| = gamma * lam := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, abs_mul, abs_of_nonneg hg0, hzIm]
    rw [one_mul, he] at hc
    refine hc.trans (Real.exp_le_exp.mpr ?_)
    nlinarith [mul_le_mul_of_nonneg_right hg2 hlam]
  have hrest (k : ℝ) (hk0 : 0 ≤ k) (hk : k ≤ Real.exp (6 * lam * h)) :
      k ^ 8 * ‖S‖ ≤ Real.exp (50 * lam * h) := by
    calc
      _ ≤ Real.exp (6 * lam * h) ^ 8 * Real.exp (2 * lam * h) :=
        mul_le_mul (pow_le_pow_left₀ hk0 hk 8) hS (norm_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1 <;> norm_num <;> ring
  have hXi : ‖quadraticFullNoiseCharComplex nu z w‖ =
      ‖quadraticChordCharComplex nu z w‖ ^ 8 *
      ‖quadraticChordCharComplex nu (-z) w‖ ^ 8 * ‖S‖ := by
    rw [qcc_full_product nu h3 hV h hh hsupport z w, norm_mul, norm_mul, norm_pow, norm_pow]
  refine ⟨hT, qcc_K_power nu h3 hV h hh hsupport hm2V lam b s hlam hb hs hslope ell J hell u v hu hv, ?_, ?_⟩
  · rw [hXi]
    calc
      _ = (‖quadraticChar rho u v‖ ^ ell * ‖quadraticChordCharComplex nu z w‖ ^ 8) *
          (‖quadraticChordCharComplex nu (-z) w‖ ^ 8 * ‖S‖) := by ring
      _ ≤ ((4752 : ℝ) ^ 8 * Real.exp (112 * lam * h) *
          (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16) * Real.exp (50 * lam * h) :=
        mul_le_mul hK8 (hrest _ (norm_nonneg _) hKm) (by positivity) (by positivity)
      _ = _ := by
        calc
          _ = (4752 : ℝ) ^ 8 * (Real.exp (112 * lam * h) * Real.exp (50 * lam * h)) *
              (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
  · rw [hXi]
    calc
      _ = (‖quadraticChar reflectedRho (-u) v‖ ^ ell * ‖quadraticChordCharComplex nu (-z) w‖ ^ 8) *
          (‖quadraticChordCharComplex nu z w‖ ^ 8 * ‖S‖) := by ring
      _ ≤ ((4752 : ℝ) ^ 8 * Real.exp (112 * lam * h) *
          (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16) * Real.exp (50 * lam * h) :=
        mul_le_mul hR8 (hrest _ (norm_nonneg _) hK) (by positivity) (by positivity)
      _ = _ := by
        calc
          _ = (4752 : ℝ) ^ 8 * (Real.exp (112 * lam * h) * Real.exp (50 * lam * h)) *
              (T⁻¹ + lam ^ 2) ^ 8 / |u| ^ 16 := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring

end Shao.Probability
