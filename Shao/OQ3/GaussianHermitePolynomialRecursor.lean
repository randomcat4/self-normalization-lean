import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Shao.OQ3
noncomputable section

def gaussianHermitePolynomial (n : ℕ) : Polynomial ℝ :=
  Nat.rec (1 : Polynomial ℝ)
    (fun _ P => Polynomial.X * P - P.derivative) n

theorem gaussian_hermite_polynomial_recursion :
    gaussianHermitePolynomial 0 = 1 ∧
      ∀ n : ℕ, gaussianHermitePolynomial (n + 1) =
        Polynomial.X * gaussianHermitePolynomial n -
          (gaussianHermitePolynomial n).derivative := by
  constructor
  · rfl
  · intro n
    rfl

theorem gaussian_hermite_iterated_derivative (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => Real.exp (-y ^ 2 / 2)) x =
      (-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval x *
        Real.exp (-x ^ 2 / 2) := by
  induction n generalizing x with
  | zero => simp [gaussianHermitePolynomial]
  | succ n ih =>
    have hfun :
        iteratedDeriv n (fun y : ℝ => Real.exp (-y ^ 2 / 2)) =
          fun y : ℝ => (-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval y *
            Real.exp (-y ^ 2 / 2) := funext ih
    rw [iteratedDeriv_succ, hfun]
    have hquadratic : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have hh := (((hasDerivAt_id x).pow 2).neg.div_const 2)
      change HasDerivAt (fun y : ℝ => -y ^ 2 / 2)
        (-(2 * x ^ (2 - 1) * 1) / 2) x at hh
      convert hh using 1 <;> ring
    have hgaussian : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
        (-x * Real.exp (-x ^ 2 / 2)) x := by
      convert hquadratic.exp using 1 <;> ring
    have hd := (((gaussianHermitePolynomial n).hasDerivAt x).const_mul
      ((-1 : ℝ) ^ n)).mul hgaussian
    change deriv ((fun y : ℝ => (-1 : ℝ) ^ n * (gaussianHermitePolynomial n).eval y) *
      fun y : ℝ => Real.exp (-y ^ 2 / 2)) x = _
    rw [hd.deriv]
    simp only [gaussian_hermite_polynomial_recursion.2 n, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X, pow_succ]
    ring

theorem gaussian_hermite_polynomial_first_four :
    gaussianHermitePolynomial 0 = 1 ∧
      gaussianHermitePolynomial 1 = Polynomial.X ∧
      gaussianHermitePolynomial 2 = Polynomial.X ^ 2 - 1 ∧
      gaussianHermitePolynomial 3 = Polynomial.X ^ 3 - 3 * Polynomial.X := by
  have h0 : gaussianHermitePolynomial 0 = 1 := gaussian_hermite_polynomial_recursion.1
  have h1 : gaussianHermitePolynomial 1 = Polynomial.X := by
    rw [gaussian_hermite_polynomial_recursion.2 0, h0]
    simp
  have h2 : gaussianHermitePolynomial 2 = Polynomial.X ^ 2 - 1 := by
    rw [gaussian_hermite_polynomial_recursion.2 1, h1]
    simp [pow_two]
  have h3 : gaussianHermitePolynomial 3 = Polynomial.X ^ 3 - 3 * Polynomial.X := by
    rw [gaussian_hermite_polynomial_recursion.2 2, h2]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_pow,
      Polynomial.derivative_X, Polynomial.derivative_one]
    norm_num [map_ofNat]
    ring
  exact ⟨h0, h1, h2, h3⟩

end
end Shao.OQ3
