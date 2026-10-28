import Shao.OQ3.GaussianOscillatoryIntegral

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem pair_characteristic_measurable_norm_le_one
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu] :
    let Phi : (ℝ × ℝ) → ℂ := fun z =>
      ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu
    StronglyMeasurable Phi ∧ ∀ z : ℝ × ℝ, ‖Phi z‖ ≤ 1 := by
  intro Phi
  have hc : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      Complex.exp (((p.1.1 * p.2.1 + p.1.2 * p.2.2 : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  refine ⟨hc.stronglyMeasurable.integral_prod_right', fun z => ?_⟩
  simpa using (norm_integral_le_of_norm_le_const (μ := nu) (C := (1 : ℝ))
    (Filter.Eventually.of_forall (fun w : ℝ × ℝ => by
      simp [Complex.norm_exp, Complex.mul_re])))

theorem gaussian_damped_pair_characteristic_integral
    (nu : Measure (ℝ × ℝ)) [IsProbabilityMeasure nu]
    (b : ℝ) (hb : 0 < b) (x : ℝ × ℝ) :
    let Phi : (ℝ × ℝ) → ℂ := fun z =>
      ∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu
    Integrable (fun z : ℝ × ℝ =>
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) * Phi z *
        Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))) ∧
      (∫ z : ℝ × ℝ,
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) * Phi z *
          Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))) =
        ((Real.pi / b : ℝ) : ℂ) *
          ∫ w : ℝ × ℝ,
            Complex.exp (-((((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b) : ℝ) : ℂ)) ∂nu := by
  intro Phi
  let g : (ℝ × ℝ) → ℂ := fun z =>
    Complex.exp (-(b : ℂ) * ((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ))
  let f : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun z w =>
    Complex.exp (-Complex.I * (((x.1 - w.1) * z.1 + (x.2 - w.2) * z.2 : ℝ) : ℂ)) * g z
  have hg : Integrable g := by
    simpa [g] using (pair_gaussian_oscillatory_integral b hb (0, 0)).1
  have hc : Continuous (Function.uncurry f) := by
    dsimp only [Function.uncurry, f, g]
    fun_prop
  have hdom : Integrable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ‖g p.1‖ * (1 : ℝ))
      (volume.prod nu) := hg.norm.mul_prod (integrable_const (1 : ℝ))
  have hfi : Integrable (Function.uncurry f) (volume.prod nu) := by
    apply hdom.mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => by
      simp [Function.uncurry, f, norm_mul, Complex.norm_exp, Complex.mul_re])
  have hid (z : ℝ × ℝ) :
      Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) * Phi z * g z =
        ∫ w : ℝ × ℝ, f z w ∂nu := by
    calc
      _ = ∫ w : ℝ × ℝ,
          (Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
            Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I)) * g z ∂nu := by
        rw [integral_mul_const, integral_const_mul]
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun w => by
          dsimp only [f]
          congr 1
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring)
  refine ⟨hfi.integral_prod_left.congr
    (Filter.Eventually.of_forall (fun z => (hid z).symm)), ?_⟩
  calc
    _ = ∫ z : ℝ × ℝ, ∫ w : ℝ × ℝ, f z w ∂nu :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    _ = ∫ w : ℝ × ℝ, ∫ z : ℝ × ℝ, f z w ∂nu := integral_integral_swap hfi
    _ = ∫ w : ℝ × ℝ, ((Real.pi / b : ℝ) : ℂ) *
        Complex.exp (-((((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b) : ℝ) : ℂ)) ∂nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun w =>
        (pair_gaussian_oscillatory_integral b hb (x.1 - w.1, x.2 - w.2)).2)
    _ = _ := integral_const_mul _ _

end
end Shao.OQ3
