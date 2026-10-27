import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.CompMul

namespace Shao.OQ3
open MeasureTheory
noncomputable section

theorem actual_cgf_iterated_deriv_scaling
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : Ω → ℝ) (a : ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (ProbabilityTheory.cgf (fun w => a * X w) mu) t =
      a ^ k * iteratedDeriv k (ProbabilityTheory.cgf X mu) (a * t) := by
  have hscale (f : ℝ → ℝ) (n : ℕ) (s : ℝ) :
      iteratedDeriv n (fun x => f (a * x)) s = a ^ n * iteratedDeriv n f (a * s) := by
    induction n generalizing s with
    | zero => simp
    | succ n ih =>
      calc
        _ = deriv (iteratedDeriv n (fun x => f (a * x))) s := by
          rw [iteratedDeriv_succ]
        _ = deriv (fun x => a ^ n * iteratedDeriv n f (a * x)) s := by
          congr 1
          funext x
          exact ih x
        _ = a ^ n * (a * deriv (iteratedDeriv n f) (a * s)) := by
          rw [deriv_const_mul_field, deriv_comp_mul_left, smul_eq_mul]
        _ = _ := by rw [iteratedDeriv_succ, pow_succ]; ring
  have hid : ProbabilityTheory.cgf (fun w => a * X w) mu =
      fun s => ProbabilityTheory.cgf X mu (a * s) := by
    funext s
    simp only [ProbabilityTheory.cgf, ProbabilityTheory.mgf_const_mul]
  rw [hid]
  exact hscale (ProbabilityTheory.cgf X mu) k t

end
end Shao.OQ3
