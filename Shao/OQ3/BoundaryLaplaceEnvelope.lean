import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_laplace_monomial_integrable
    (d : ℝ) (hd : 0 < d) (m n : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      |p.1| ^ m * p.2 ^ n * Real.exp (-d * (p.2 + p.1 ^ 2)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))
 := by
  have hm : (-1 : ℝ) < (m : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hn : (-1 : ℝ) < (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hUraw : Integrable (fun u : ℝ => u ^ m * Real.exp (-d * u ^ 2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq hd hm
  have hU : Integrable (fun u : ℝ => |u| ^ m * Real.exp (-d * u ^ 2)) := by
    convert hUraw.norm using 1
    funext u
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hV0 : IntegrableOn (fun v : ℝ => v ^ n * Real.exp (-d * v)) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) hn (by norm_num) hd
  have hV : IntegrableOn (fun v : ℝ => v ^ n * Real.exp (-d * v)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (f := fun v : ℝ => v ^ n * Real.exp (-d * v))
      (μ := volume) (b := 0) (by finiteness)).mpr hV0
  convert hU.mul_prod hV using 1
  funext p
  rw [show -d * (p.2 + p.1 ^ 2) = -d * p.1 ^ 2 + -d * p.2 by ring, Real.exp_add]
  ring

theorem boundary_laplace_error_envelope_integrable
    (d CA CF a0 rho : ℝ) (hd : 0 < d) :
    Integrable (fun p : ℝ × ℝ =>
      (CA * (|p.1| + p.2) + |a0| * CF * (|p.1| ^ 3 + |p.1| * p.2 + p.2 ^ 2) +
        |a0| / rho * (|p.1| + p.2)) * Real.exp (-d * (p.2 + p.1 ^ 2)))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))
 := by
  have h10 := boundary_laplace_monomial_integrable d hd 1 0
  have h01 := boundary_laplace_monomial_integrable d hd 0 1
  have h30 := boundary_laplace_monomial_integrable d hd 3 0
  have h11 := boundary_laplace_monomial_integrable d hd 1 1
  have h02 := boundary_laplace_monomial_integrable d hd 0 2
  have hh := (((h10.add h01).const_mul CA).add
    (((h30.add h11).add h02).const_mul (|a0| * CF))).add
      ((h10.add h01).const_mul (|a0| / rho))
  convert hh using 1
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_zero, pow_one, mul_one, one_mul]
  ring

end
end Shao.OQ3
