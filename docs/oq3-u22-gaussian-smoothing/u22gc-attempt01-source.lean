import Shao.OQ3.GaussianDampedCharacteristicIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem pair_gaussian_noise_characteristic
    (v : ℝ≥0) :
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    IsProbabilityMeasure gamma ∧ ∀ z : ℝ × ℝ,
      (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂gamma) =
        Complex.exp (-((v : ℝ) : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) := by
  intro gamma
  refine ⟨by dsimp only [gamma]; infer_instance, ?_⟩
  intro z
  have hreal (t : ℝ) :
      (∫ w : ℝ, Complex.exp (((t * w : ℝ) : ℂ) * Complex.I)
        ∂ProbabilityTheory.gaussianReal 0 v) =
        Complex.exp (-((v : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    simpa [charFun_apply_real] using
      (ProbabilityTheory.charFun_gaussianReal (μ := 0) (v := v) t)
  have hid (w : ℝ × ℝ) :
      Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((z.1 * w.1 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((z.2 * w.2 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp only [gamma]
  simp_rw [hid]
  rw [integral_prod_mul, hreal, hreal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pair_independent_sum_characteristic
    (nu eta : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] [IsProbabilityMeasure eta] :
    let rho : Measure (ℝ × ℝ) := (nu.prod eta).map (fun q => q.1 + q.2)
    IsProbabilityMeasure rho ∧ ∀ z : ℝ × ℝ,
      (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
        (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu) *
          ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂eta := by
  intro rho
  refine ⟨by dsimp only [rho]; infer_instance, ?_⟩
  intro z
  let f : (ℝ × ℝ) → ℂ := fun w =>
    Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I)
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hm : Measurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => q.1 + q.2) := by fun_prop
  have hj : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => f (q.1 + q.2)) := by
    fun_prop
  have hi : Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) => f (q.1 + q.2))
      (nu.prod eta) := by
    apply (integrable_const (1 : ℝ)).mono' hj.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      simp [f, Complex.norm_exp, Complex.mul_re])
  have hid (a d : ℝ × ℝ) : f (a + d) = f a * f d := by
    dsimp only [f]
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add]
    push_cast
    ring
  change (∫ w : ℝ × ℝ, f w ∂rho) = (∫ w : ℝ × ℝ, f w ∂nu) *
    ∫ w : ℝ × ℝ, f w ∂eta
  calc
    _ = ∫ q : (ℝ × ℝ) × (ℝ × ℝ), f (q.1 + q.2) ∂nu.prod eta :=
      integral_map_of_stronglyMeasurable hm hf.stronglyMeasurable
    _ = ∫ a : ℝ × ℝ, (∫ d : ℝ × ℝ, f (a + d) ∂eta) ∂nu := integral_prod _ hi
    _ = ∫ a : ℝ × ℝ, f a * (∫ d : ℝ × ℝ, f d ∂eta) ∂nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => by
        simp_rw [hid a]
        exact integral_const_mul _ _)
    _ = _ := integral_mul_const _ _

theorem gaussian_smoothed_pair_law_fourier_integral
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (b : ℝ) (hb : 0 < b) :
    let v : ℝ≥0 := Real.toNNReal (2 * b)
    let gamma : Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
    let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
    IsProbabilityMeasure rho ∧
      (∀ z : ℝ × ℝ,
        (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
          (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu) *
            Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))) ∧
      ∀ x : ℝ × ℝ,
        Integrable (fun z : ℝ × ℝ =>
          Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
            (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)) ∧
          (∫ z : ℝ × ℝ,
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
              (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)) =
            ((Real.pi / b : ℝ) : ℂ) *
              ∫ w : ℝ × ℝ,
                Complex.exp (-((((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b) : ℝ) : ℂ)) ∂nu := by
  intro v gamma rho
  obtain ⟨hgamma, hnoise⟩ := pair_gaussian_noise_characteristic v
  letI : IsProbabilityMeasure gamma := hgamma
  obtain ⟨hrho, hchar⟩ := pair_independent_sum_characteristic nu gamma
  have hv : (v : ℝ) = 2 * b := Real.toNNReal_of_nonneg (by positivity)
  have hactual (z : ℝ × ℝ) :
      (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
        (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu) *
          Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ)) := by
    rw [hchar z, hnoise z, hv]
    congr 1
    congr 1
    push_cast
    ring
  refine ⟨hrho, hactual, fun x => ?_⟩
  simpa only [hactual, mul_assoc] using
    (gaussian_damped_pair_characteristic_integral nu b hb x)

end
end Shao.OQ3
