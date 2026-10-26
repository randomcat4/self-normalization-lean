import Shao.OQ5.P51.ClippedStudentizer
import Shao.OQ5.P51.LiteralStudentizerBudgetDomination
set_option autoImplicit false
universe u
namespace Shao.OQ5.P51

theorem literal_clippedCentered_comparison_on_projectionGood (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (rho y : ℝ)
    (x : Fin n → Ω) (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hsym : ∀ a b : Ω, r a b = r b a) (hrho : 0 ≤ rho)
    (hwindow : (1 + rho) * y ≤ Real.sqrt (n : ℝ))
    (hGood : x ∈ projectionGood n g y)
    (hLower : -(1 / 2 : ℝ) ≤ centeredDelta n g r x) :
    clippedCenteredDelta n g r 512 rho y x = centeredDelta n g r x ∧
    0 < projectionV n g x *
      Real.sqrt (1 + clippedCenteredDelta n g r 512 rho y x) ∧
    0 < Real.sqrt (centeredSq n g r x) ∧
    projectionV n g x * Real.sqrt (1 + clippedCenteredDelta n g r 512 rho y x) =
      Real.sqrt (centeredSq n g r x) ∧
    clippedCenteredStatistic n g r 512 rho y x =
      (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
        (projectionW n g x + residualStatisticD n r x) /
          Real.sqrt (centeredSq n g r x)) := by
  have hsigma : (1 : ℝ) ≤ 1 + rho := by linarith only [hrho]
  have hDom : |centeredDelta n g r x| ≤ studentizerClipBudget n r 512 rho y x := by
    simpa only [studentizerClipBudget] using
      (literal_studentizer_budget_domination n g r x (1 + rho) y
        hsym hn hsigma hy hwindow hGood)
  exact clippedCentered_comparison_on_projectionGood n g r 512 rho y x
    hn hy hGood hDom hLower

theorem literal_clippedCentered_comparison_exception_subset (n : ℕ) {Ω : Type u}
    (g : Ω → ℝ) (r : Ω → Ω → ℝ) (rho y : ℝ)
    (hn : 4 ≤ n) (hy : (1 : ℝ) ≤ y)
    (hsym : ∀ a b : Ω, r a b = r b a) (hrho : 0 ≤ rho)
    (hwindow : (1 + rho) * y ≤ Real.sqrt (n : ℝ))
    :
    {x : Fin n → Ω |
      clippedCenteredStatistic n g r 512 rho y x ≠
        (if Real.sqrt (centeredSq n g r x) = 0 then 0 else
          (projectionW n g x + residualStatisticD n r x) /
            Real.sqrt (centeredSq n g r x))} ⊆
      (projectionGood n g y)ᶜ ∪ lowerStudentizerBad n g r y := by
  have hsigma : (1 : ℝ) ≤ 1 + rho := by linarith only [hrho]
  have hDom : ∀ x : Fin n → Ω, x ∈ projectionGood n g y →
      |centeredDelta n g r x| ≤ studentizerClipBudget n r 512 rho y x := by
    intro x hGood
    simpa only [studentizerClipBudget] using
      (literal_studentizer_budget_domination n g r x (1 + rho) y
        hsym hn hsigma hy hwindow hGood)
  exact clippedCentered_comparison_exception_subset n g r 512 rho y hn hy hDom

end Shao.OQ5.P51
