/- Public exact interfaces for already accepted scalar suffix lemmas. -/
import Shao.Probability.SourceSuffixMomentBudgets
import Lean

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceSuffixScalarInterfaces
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Classical

theorem scaled_polynomial_exponentials
    (p : ℕ) (lambda s d : ℝ) (hl : 0 < lambda) (hs : 0 < s) :
    |d| ^ p ≤ ((p.factorial : ℝ) / lambda ^ p) * Real.rpow s (-(p : ℝ) / 2) *
      (Real.exp (lambda * Real.sqrt s * d) + Real.exp (-lambda * Real.sqrt s * d)) := by
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceSuffixMomentBudgets".toName)
      ("Shao.Probability.smb_scaled_polynomial_exponentials".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent ("p".toName)) $(Lean.mkIdent ("lambda".toName)) $(Lean.mkIdent ("s".toName)) $(Lean.mkIdent ("d".toName)) $(Lean.mkIdent ("hl".toName)) $(Lean.mkIdent ("hs".toName))))

theorem gamma_kernel (alpha rate : ℝ) (ha : 0 < alpha) (hr : 0 < rate) :
    IntegrableOn (fun s : ℝ => Real.rpow s (alpha - 1) * Real.exp (-rate * s)) (Set.Ioi 0) ∧
      (∫ s : ℝ in Set.Ioi 0, Real.rpow s (alpha - 1) * Real.exp (-rate * s)) =
        Real.rpow (1 / rate) alpha * Real.Gamma alpha := by
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceSuffixMomentBudgets".toName)
      ("Shao.Probability.smb_gamma_kernel".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent ("alpha".toName)) $(Lean.mkIdent ("rate".toName)) $(Lean.mkIdent ("ha".toName)) $(Lean.mkIdent ("hr".toName))))

theorem inverse_laplace (a T b : ℝ) (ha : 0 < a) (hb : 0 < b) (hT : b ≤ T) :
    Real.rpow T (-a) ≤ Real.exp 1 * a *
      (∫ s : ℝ in Set.Ioo 0 (1 / b), Real.rpow s (a - 1) * Real.exp (-s * T)) := by
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceSuffixMomentBudgets".toName)
      ("Shao.Probability.smb_inverse_laplace".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent ("a".toName)) $(Lean.mkIdent ("T".toName)) $(Lean.mkIdent ("b".toName)) $(Lean.mkIdent ("ha".toName)) $(Lean.mkIdent ("hb".toName)) $(Lean.mkIdent ("hT".toName))))

theorem one_add_pow_bound (u : ℝ) (hu : 0 ≤ u) (p : ℕ) :
    (1 + u) ^ p ≤ (2 : ℝ) ^ p * (1 + u ^ p) := by
  run_tac
    let n := Lean.mkPrivateNameCore ("Shao.Probability.SourceSuffixMomentBudgets".toName)
      ("Shao.Probability.smb_one_add_pow_bound".toName)
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent n) $(Lean.mkIdent ("u".toName)) $(Lean.mkIdent ("hu".toName)) $(Lean.mkIdent ("p".toName))))

end Shao.Probability.SourceSuffixScalarInterfaces
