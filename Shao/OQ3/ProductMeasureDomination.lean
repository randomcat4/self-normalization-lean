import Shao.OQ3.TiltedMeasureDomination
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

theorem prod_measure_domination (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0)
    (hdom : (m : ℝ≥0∞) • mu ≤ nu) :
    (m : ℝ≥0∞) ^ 2 • mu.prod mu ≤ nu.prod nu := by
  have h := Measure.prod_mono hdom hdom
  simpa only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, pow_two] using h

private theorem cosine_pair_integrable (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (u v : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2)))) (mu.prod mu) := by
  refine Integrable.of_bound (by fun_prop) 2 ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  linarith [Real.neg_one_le_cos ((z.1 - z.2) * (u + v * (z.1 + z.2)))]

theorem cosine_pair_integral_domination (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0)
    (hdom : (m : ℝ≥0∞) • mu ≤ nu) (u v : ℝ) :
    (m : ℝ) ^ 2 *
      (∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂mu.prod mu) ≤
      ∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂nu.prod nu := by
  have hI_mu := cosine_pair_integrable mu u v
  have _hI_scaled := hI_mu.smul_measure (show (m : ℝ≥0∞) ^ 2 ≠ ∞ by simp)
  have hI_nu := cosine_pair_integrable nu u v
  have hnonneg : ∀ᵐ z : ℝ × ℝ ∂nu.prod nu,
      0 ≤ 1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) :=
    Filter.Eventually.of_forall fun _ => sub_nonneg.mpr (Real.cos_le_one _)
  have h := integral_mono_measure (prod_measure_domination mu nu m hdom) hnonneg hI_nu
  simpa only [integral_smul_measure, ENNReal.toReal_pow, ENNReal.coe_toReal, smul_eq_mul] using h

theorem quadratic_tilted_cosine_pair_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ)
    (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L) (s t : ℝ) :
    Real.exp (-4 * (L * (M + M ^ 2))) *
      (∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
        ∂(mu.tilted (fun x => u0 * x + v0 * x ^ 2)).prod
          (mu.tilted (fun x => u0 * x + v0 * x ^ 2))) ≤
      ∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
        ∂(mu.tilted (fun x => u * x + v * x ^ 2)).prod
          (mu.tilted (fun x => u * x + v * x ^ 2)) := by
  let mu0 := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
  let mu1 := mu.tilted (fun x => u * x + v * x ^ 2)
  let : IsProbabilityMeasure mu0 := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb u0 v0)
  let : IsProbabilityMeasure mu1 := isProbabilityMeasure_tilted
    (quadratic_exp_integrable_of_ae_abs_le mu M hM hb u v)
  let B : ℝ := L * (M + M ^ 2)
  let m : ℝ≥0 := ⟨Real.exp (-2 * B), Real.exp_nonneg _⟩
  have hm : ENNReal.ofReal (Real.exp (-2 * B)) = (m : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal (Real.exp_nonneg _)
  have hdom : (m : ℝ≥0∞) • mu0 ≤ mu1 := by
    rw [← hm]
    exact quadratic_tilted_measure_domination mu M L hM hL hb u0 v0 u v hu hv
  have h := cosine_pair_integral_domination mu0 mu1 m hdom s t
  have hsquare : (m : ℝ) ^ 2 = Real.exp (-4 * B) := by
    change Real.exp (-2 * B) ^ 2 = Real.exp (-4 * B)
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hsquare] at h
  exact h

end
end Shao.OQ3
