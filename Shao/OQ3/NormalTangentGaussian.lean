import Shao.OQ3.RegularCovariance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Actual normal/tangent covariance and the central Gaussian integral

Source: current/oq3/proofs/r1/report.md, lines 238-258 and 309-345.
SHA256: 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662.
Frozen U12b scope: b5887ae7c85b81ef3d5acc2a82ecce83702d99f5dcc555cc08541193579756f4.
-/

namespace Shao.OQ3

open MeasureTheory

noncomputable section

def normalTangentQuadratic (mu : Measure ℝ) (v s : ℝ) : ℝ :=
  normalVariance mu * v ^ 2 +
    2 * ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu * v * s +
    ProbabilityTheory.variance (fun x : ℝ => x) mu * s ^ 2

theorem covariance_normal_id (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) :
    ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu =
      8 * parabolaCovariance mu 0 0 - parabolaCovariance mu 0 1 := by
  have h1 : MemLp (fun x : ℝ => x) 2 mu := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable (4 + Real.sqrt 10)
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, id_eq] using hx
  have h2 : MemLp (fun x : ℝ => x ^ 2) 2 mu := by
    have hm : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
    apply MemLp.of_bound hm.aestronglyMeasurable ((4 + Real.sqrt 10) ^ 2)
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  change ProbabilityTheory.covariance (fun x : ℝ => 8 * x - x ^ 2) (fun x : ℝ => x) mu =
    8 * ProbabilityTheory.variance (fun x : ℝ => x) mu -
      ProbabilityTheory.covariance (fun x : ℝ => x) (fun x : ℝ => x ^ 2) mu
  rw [ProbabilityTheory.covariance_fun_sub_left (h1.const_mul 8) h2 h1,
    ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_self (X := fun x : ℝ => x) (by fun_prop),
    ProbabilityTheory.covariance_comm (fun x : ℝ => x ^ 2) (fun x : ℝ => x)]

theorem normal_tangent_covariance_det (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) :
    normalVariance mu * ProbabilityTheory.variance (fun x : ℝ => x) mu -
      (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu) ^ 2 =
        (parabolaCovariance mu).det := by
  rw [normalVariance_eq_covariance mu hb, covariance_normal_id mu hb, Matrix.det_fin_two]
  change (64 * parabolaCovariance mu 0 0 - 16 * parabolaCovariance mu 0 1 +
      parabolaCovariance mu 1 1) * parabolaCovariance mu 0 0 -
        (8 * parabolaCovariance mu 0 0 - parabolaCovariance mu 0 1) ^ 2 =
      parabolaCovariance mu 0 0 * parabolaCovariance mu 1 1 -
        parabolaCovariance mu 0 1 * parabolaCovariance mu 0 1
  ring

private theorem quadratic_complete_square (S C V D v s : ℝ) (hS : S ≠ 0)
    (hdet : S * V - C ^ 2 = D) :
    S * v ^ 2 + 2 * C * v * s + V * s ^ 2 =
      S * (v + (C / S) * s) ^ 2 + (D / S) * s ^ 2 := by
  rw [← hdet]
  field_simp [hS]
  ring

theorem normalTangentQuadratic_complete_square (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hS : 0 < normalVariance mu) (v s : ℝ) :
    normalTangentQuadratic mu v s =
      normalVariance mu *
          (v + (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu /
            normalVariance mu) * s) ^ 2 +
        transverseVariance mu * s ^ 2 := by
  exact quadratic_complete_square _ _ _ _ v s hS.ne' (normal_tangent_covariance_det mu hb)

theorem normalTangentQuadratic_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) (v s : ℝ) (hne : v ≠ 0 ∨ s ≠ 0) :
    0 < normalTangentQuadratic mu v s := by
  rw [normalTangentQuadratic_complete_square mu hb hS v s]
  have ht : 0 < transverseVariance mu := div_pos hD hS
  by_cases hs : s = 0
  · have hv : v ≠ 0 := hne.elim id (fun h => False.elim (h hs))
    simpa [hs] using mul_pos hS (sq_pos_of_ne_zero hv)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hS.le (sq_nonneg _))
      (mul_pos ht (sq_pos_of_ne_zero hs))

private theorem normalTangentGaussian_eq (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (hS : 0 < normalVariance mu) (s : ℝ) :
    (fun v : ℝ => Real.exp (-(normalTangentQuadratic mu v s) / 2)) =
      (fun v : ℝ => Real.exp (-(normalVariance mu / 2) *
          (v + (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu /
            normalVariance mu) * s) ^ 2) *
        Real.exp (-(transverseVariance mu * s ^ 2) / 2)) := by
  funext v
  rw [normalTangentQuadratic_complete_square mu hb hS v s, ← Real.exp_add]
  congr 1
  ring

theorem normalTangentGaussian_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (hS : 0 < normalVariance mu) (s : ℝ) :
    Integrable (fun v : ℝ => Real.exp (-(normalTangentQuadratic mu v s) / 2)) := by
  have hg := integrable_exp_neg_mul_sq (half_pos hS)
  have hshift := ((measurePreserving_add_right (volume : Measure ℝ)
    ((ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu /
      normalVariance mu) * s)).integrable_comp hg.aestronglyMeasurable).mpr hg
  rw [normalTangentGaussian_eq mu hb hS s]
  exact hshift.mul_const _

theorem integral_normalTangentGaussian (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (hS : 0 < normalVariance mu) (s : ℝ) :
    (∫ v : ℝ, Real.exp (-(normalTangentQuadratic mu v s) / 2)) =
      Real.sqrt (2 * Real.pi / normalVariance mu) *
        Real.exp (-(transverseVariance mu * s ^ 2) / 2) := by
  rw [normalTangentGaussian_eq mu hb hS s, integral_mul_const,
    integral_add_right_eq_self (fun v : ℝ => Real.exp (-(normalVariance mu / 2) * v ^ 2)),
    integral_gaussian]
  have harg : Real.pi / (normalVariance mu / 2) = 2 * Real.pi / normalVariance mu := by
    field_simp [hS.ne']
  rw [harg]

end
end Shao.OQ3
