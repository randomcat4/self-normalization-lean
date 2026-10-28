import Shao.OQ3.GaussianSmoothedPairDensity

namespace Shao.OQ3
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem pair_gaussian_pdf_normalization
    (b : ℝ) (hb : 0 < b) (u : ℝ × ℝ) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    (ProbabilityTheory.gaussianPDFReal 0 v u.1 * ProbabilityTheory.gaussianPDFReal 0 v u.2 =
      (1 / (4 * Real.pi * b)) * Real.exp (-(u.1 ^ 2 + u.2 ^ 2) / (4 * b))) ∧
      ProbabilityTheory.gaussianPDF 0 v u.1 * ProbabilityTheory.gaussianPDF 0 v u.2 =
        ENNReal.ofReal ((1 / (4 * Real.pi * b)) * Real.exp (-(u.1 ^ 2 + u.2 ^ 2) / (4 * b))) := by
  intro v
  have hv : (v : ℝ) = 2 * b := by
    dsimp only [v]
    rw [Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2 * b)]
    rfl
  have hs : Real.sqrt (4 * Real.pi * b) ^ 2 = 4 * Real.pi * b :=
    Real.sq_sqrt (by positivity)
  have hsq : Real.sqrt (4 * Real.pi * b) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hr :
      ProbabilityTheory.gaussianPDFReal 0 v u.1 * ProbabilityTheory.gaussianPDFReal 0 v u.2 =
        (1 / (4 * Real.pi * b)) * Real.exp (-(u.1 ^ 2 + u.2 ^ 2) / (4 * b)) := by
    simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, hv]
    have he : Real.exp (-u.1 ^ 2 / (2 * (2 * b))) *
        Real.exp (-u.2 ^ 2 / (2 * (2 * b))) =
        Real.exp (-(u.1 ^ 2 + u.2 ^ 2) / (4 * b)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hn : (Real.sqrt (2 * Real.pi * (2 * b)))⁻¹ *
        (Real.sqrt (2 * Real.pi * (2 * b)))⁻¹ = 1 / (4 * Real.pi * b) := by
      have harg : 2 * Real.pi * (2 * b) = 4 * Real.pi * b := by ring
      rw [harg]
      field_simp
      nlinarith [hs]
    calc
      _ = ((Real.sqrt (2 * Real.pi * (2 * b)))⁻¹ *
          (Real.sqrt (2 * Real.pi * (2 * b)))⁻¹) *
          (Real.exp (-u.1 ^ 2 / (2 * (2 * b))) * Real.exp (-u.2 ^ 2 / (2 * (2 * b)))) := by ring
      _ = _ := by rw [hn, he]
  refine ⟨hr, ?_⟩
  rw [ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDF,
    ← ENNReal.ofReal_mul (ProbabilityTheory.gaussianPDFReal_nonneg 0 v u.1), hr]

theorem gaussian_smoothed_pair_real_density
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (b : ℝ) (hb : 0 < b) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let k : (ℝ × ℝ) → ℝ := fun x => (1 / (4 * Real.pi * b)) *
      ∫ w : ℝ × ℝ, Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu
    IsProbabilityMeasure rho ∧ rho = volume.withDensity (fun x => ENNReal.ofReal (k x)) ∧
      Measurable k ∧ (∀ x : ℝ × ℝ, 0 ≤ k x ∧ k x ≤ 1 / (4 * Real.pi * b)) ∧
        Integrable k ∧ (∫ x : ℝ × ℝ, k x) = 1 := by
  intro v gamma rho k
  let c : ℝ := 1 / (4 * Real.pi * b)
  let f : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun x w =>
    Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b))
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hfpos (x w : ℝ × ℝ) : 0 ≤ f x w := (Real.exp_pos _).le
  have hfle (x w : ℝ × ℝ) : f x w ≤ 1 := by
    apply Real.exp_le_one_iff.2
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x.1 - w.1),
      sq_nonneg (x.2 - w.2)]) (by positivity)
  have hj : Continuous (Function.uncurry f) := by
    dsimp only [Function.uncurry, f]
    fun_prop
  have hi (x : ℝ × ℝ) : Integrable (f x) nu := by
    apply (integrable_const (1 : ℝ)).mono' (by
      have h : Continuous (f x) := by dsimp only [f]; fun_prop
      exact h.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfpos x w)]
      exact hfle x w)
  have hm : Measurable k := by
    change Measurable (fun x : ℝ × ℝ => c * (∫ w : ℝ × ℝ, f x w ∂nu))
    exact hj.stronglyMeasurable.integral_prod_right'.measurable.const_mul c
  have hbound (x : ℝ × ℝ) : 0 ≤ k x ∧ k x ≤ c := by
    have hle : (∫ w : ℝ × ℝ, f x w ∂nu) ≤ 1 := by
      simpa using integral_mono_ae (hi x) (integrable_const (1 : ℝ))
        (Filter.Eventually.of_forall (hfle x))
    refine ⟨mul_nonneg hc (integral_nonneg (hfpos x)), ?_⟩
    exact (mul_le_mul_of_nonneg_left hle hc).trans_eq (mul_one c)
  have hv : (v : ℝ) = 2 * b := by
    dsimp only [v]
    rw [Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2 * b)]
    rfl
  have hvne : v ≠ 0 := by
    have hp : 0 < (v : ℝ) := by rw [hv]; positivity
    exact_mod_cast hp.ne'
  obtain ⟨hrho, hd, _, _⟩ := gaussian_smoothed_pair_law_density nu v hvne
  have hkernel (x : ℝ × ℝ) :
      (∫⁻ w : ℝ × ℝ, ProbabilityTheory.gaussianPDF 0 v (x.1 - w.1) *
        ProbabilityTheory.gaussianPDF 0 v (x.2 - w.2) ∂nu) = ENNReal.ofReal (k x) := by
    calc
      _ = ∫⁻ w : ℝ × ℝ, ENNReal.ofReal (c * f x w) ∂nu :=
        lintegral_congr (fun w => (pair_gaussian_pdf_normalization b hb
          (x.1 - w.1, x.2 - w.2)).2)
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal ((hi x).const_mul c)
          (Filter.Eventually.of_forall (fun w => mul_nonneg hc (hfpos x w))),
          integral_const_mul]
  have heq : rho = volume.withDensity (fun x => ENNReal.ofReal (k x)) := by
    rw [hd]
    congr 1
    funext x
    exact hkernel x
  letI : IsProbabilityMeasure rho := hrho
  have hmass : (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (k x)) = 1 := by
    have h : rho Set.univ = 1 := measure_univ
    rw [heq, withDensity_apply _ MeasurableSet.univ] at h
    simpa only [Measure.restrict_univ] using h
  have hn : 0 ≤ᵐ[volume] k := Filter.Eventually.of_forall (fun x => (hbound x).1)
  have hint : Integrable k := ⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hn).2 (by rw [hmass]; norm_num)⟩
  have hval : (∫ x : ℝ × ℝ, k x) = 1 := by
    have h := ofReal_integral_eq_lintegral_ofReal hint hn
    rw [hmass] at h
    have ht := congrArg ENNReal.toReal h
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x => (hbound x).1)),
      ENNReal.toReal_one] using ht
  exact ⟨hrho, heq, hm, hbound, hint, hval⟩

theorem gaussian_smoothed_pair_normalized_inverse
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (b : ℝ) (hb : 0 < b) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    let k : (ℝ × ℝ) → ℝ := fun x => (1 / (4 * Real.pi * b)) *
      ∫ w : ℝ × ℝ, Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu
    ∀ x : ℝ × ℝ,
      Integrable (fun z : ℝ × ℝ =>
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)) ∧
        (((1 / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          ∫ z : ℝ × ℝ,
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
              (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)) =
          ((k x : ℝ) : ℂ) := by
  intro v gamma rho k x
  obtain ⟨hi, he⟩ := (gaussian_smoothed_pair_law_fourier_integral nu b hb).2.2 x
  refine ⟨hi, ?_⟩
  have hcomplex :
      (∫ w : ℝ × ℝ,
        Complex.exp (-((((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b) : ℝ) : ℂ)) ∂nu) =
        ((∫ w : ℝ × ℝ,
          Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, neg_div]
    exact integral_ofReal
  rw [he, hcomplex]
  dsimp only [k]
  push_cast
  field_simp [Real.pi_ne_zero, hb.ne']
  ring

end
end Shao.OQ3
