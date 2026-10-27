import Shao.OQ3.GaussianHermitePolynomialRecursor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv

namespace Shao.OQ3
noncomputable section

theorem gaussian_hermite_scaled_complex_iterated_derivative
    (c a : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ =>
      (c : ℂ) * Complex.exp (((-(a * y) ^ 2 / 2 : ℝ) : ℂ))) x =
        ((c * a ^ n *
          ((-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval (a * x) *
            Real.exp (-(a * x) ^ 2 / 2)) : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun y => Real.exp (-y ^ 2 / 2)
  let q : ℝ → ℝ := fun y => c * f (a * y)
  have hf : ContDiff ℝ ⊤ f := by dsimp [f]; fun_prop
  have hq : ContDiff ℝ ⊤ q := by dsimp [q, f]; fun_prop
  have hembed (m : ℕ) (t : ℝ) :
      iteratedDeriv m (fun y : ℝ => (q y : ℂ)) t =
        (iteratedDeriv m q t : ℂ) := by
    induction m generalizing t with
    | zero => rfl
    | succ m ih =>
      have hfun : iteratedDeriv m (fun y : ℝ => (q y : ℂ)) =
          (fun y : ℝ => (iteratedDeriv m q y : ℂ)) := funext ih
      rw [iteratedDeriv_succ, iteratedDeriv_succ, hfun]
      exact ((hq.differentiable_iteratedDeriv m (by simp) t).hasDerivAt.ofReal_comp).deriv
  have hfun : (fun y : ℝ =>
      (c : ℂ) * Complex.exp (((-(a * y) ^ 2 / 2 : ℝ) : ℂ))) =
        (fun y : ℝ => (q y : ℂ)) := by
    funext y
    simp only [q, f, Complex.ofReal_mul, Complex.ofReal_exp]
  have hreal : iteratedDeriv n q x =
      c * a ^ n *
        ((-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval (a * x) *
          Real.exp (-(a * x) ^ 2 / 2)) := by
    change iteratedDeriv n (fun y : ℝ => c * f (a * y)) x = _
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_const_mul (hf.of_le le_top) a]
    change c * (a ^ n * iteratedDeriv n (fun y : ℝ => Real.exp (-y ^ 2 / 2)) (a * x)) = _
    rw [gaussian_hermite_iterated_derivative]
    ring
  rw [hfun, hembed, hreal]

end
end Shao.OQ3
