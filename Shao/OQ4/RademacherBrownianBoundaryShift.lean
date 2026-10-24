import Shao.Probability.BrownianFirstTerm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
universe uB

namespace Shao.OQ4.RademacherBrownianBoundaryShift

theorem actual_brownian_boundary_shift
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (x y : ℕ → ℝ)
    (hx : Tendsto x atTop (𝓝 (0 : ℝ)))
    (hy : Tendsto y atTop (𝓝 (0 : ℝ)))
    (hxpos : ∀ᶠ k : ℕ in atTop, 0 < x k)
    (hypos : ∀ᶠ k : ℕ in atTop, 0 < y k) :
    (∀ᶠ k : ℕ in atTop,
      0 < Shao.Probability.BrownianSup.probability B P hB (x k) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB (y k) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB (y k) /
        Shao.Probability.BrownianSup.probability B P hB (x k)) ∧
    Tendsto (fun k : ℕ =>
      Real.log (Shao.Probability.BrownianSup.probability B P hB (y k) /
        Shao.Probability.BrownianSup.probability B P hB (x k)) -
      (Real.pi ^ 2 / 8) * (1 / (x k) ^ 2 - 1 / (y k) ^ 2))
      atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (fun k : ℕ =>
      (Shao.Probability.BrownianSup.probability B P hB (y k) /
        Shao.Probability.BrownianSup.probability B P hB (x k)) /
      Real.exp ((Real.pi ^ 2 / 8) * (1 / (x k) ^ 2 - 1 / (y k) ^ 2)))
      atTop (𝓝 (1 : ℝ)) := by
  let b : ℝ → ℝ := Shao.Probability.BrownianSup.probability B P hB
  let f : ℝ → ℝ := Shao.Probability.BrownianSup.firstTerm
  have hfpos (s : ℝ) : 0 < f s := by
    exact mul_pos (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos)
      (Real.exp_pos _)
  have hflog (s : ℝ) :
      Real.log (f s) = Real.log (4 / Real.pi) - (Real.pi ^ 2 / 8) / s ^ 2 := by
    dsimp only [f, Shao.Probability.BrownianSup.firstTerm]
    rw [Real.log_mul
      (div_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos).ne'
      (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hrel (z : ℕ → ℝ) (hz : Tendsto z atTop (𝓝 (0 : ℝ)))
      (hzpos : ∀ᶠ k : ℕ in atTop, 0 < z k) :
      Tendsto (fun k : ℕ => b (z k) / f (z k)) atTop (𝓝 (1 : ℝ)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      Shao.Probability.BrownianSup.actual_brownian_firstTerm B P hB ε hε
    have hsmall : ∀ᶠ k : ℕ in atTop, z k < δ :=
      hz.eventually (eventually_lt_nhds hδ)
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hzpos.and hsmall)
    refine ⟨K, ?_⟩
    intro k hk
    simpa only [Real.dist_eq] using hbound (z k) (hK k hk).1 (hK k hk).2
  have hpositive : ∀ᶠ k : ℕ in atTop,
      0 < b (x k) ∧ 0 < b (y k) ∧ 0 < b (y k) / b (x k) := by
    obtain ⟨δ, hδ, hbound⟩ :=
      Shao.Probability.BrownianSup.actual_brownian_eventually_positive B P hB
    have hsmallx : ∀ᶠ k : ℕ in atTop, x k < δ :=
      hx.eventually (eventually_lt_nhds hδ)
    have hsmally : ∀ᶠ k : ℕ in atTop, y k < δ :=
      hy.eventually (eventually_lt_nhds hδ)
    filter_upwards [hxpos, hypos, hsmallx, hsmally] with k hxk hyk hxd hyd
    have hpx := (hbound (x k) hxk hxd).1
    have hpy := (hbound (y k) hyk hyd).1
    exact ⟨hpx, hpy, div_pos hpy hpx⟩
  have hlogx := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (hrel x hx hxpos)
  have hlogy := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    (hrel y hy hypos)
  have hlogs : Tendsto (fun k : ℕ =>
      Real.log (b (y k) / f (y k)) - Real.log (b (x k) / f (x k)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, Function.comp_def] using hlogy.sub hlogx
  have heq : (fun k : ℕ =>
      Real.log (b (y k) / b (x k)) -
        (Real.pi ^ 2 / 8) * (1 / (x k) ^ 2 - 1 / (y k) ^ 2)) =ᶠ[atTop]
      (fun k : ℕ =>
        Real.log (b (y k) / f (y k)) - Real.log (b (x k) / f (x k))) := by
    filter_upwards [hpositive] with k hk
    rw [Real.log_div hk.2.1.ne' hk.1.ne',
      Real.log_div hk.2.1.ne' (hfpos (y k)).ne',
      Real.log_div hk.1.ne' (hfpos (x k)).ne', hflog, hflog]
    ring
  have hlog : Tendsto (fun k : ℕ =>
      Real.log (b (y k) / b (x k)) -
        (Real.pi ^ 2 / 8) * (1 / (x k) ^ 2 - 1 / (y k) ^ 2))
      atTop (𝓝 (0 : ℝ)) :=
    hlogs.congr' heq.symm
  have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
  have heqexp : (fun k : ℕ =>
      Real.exp (Real.log (b (y k) / b (x k)) -
        (Real.pi ^ 2 / 8) * (1 / (x k) ^ 2 - 1 / (y k) ^ 2))) =ᶠ[atTop]
      (fun k : ℕ => (b (y k) / b (x k)) /
        Real.exp ((Real.pi ^ 2 / 8) * (1 / (x k) ^ 2 - 1 / (y k) ^ 2))) := by
    filter_upwards [hpositive] with k hk
    rw [Real.exp_sub, Real.exp_log hk.2.2]
  refine ⟨hpositive, hlog, ?_⟩
  simpa only [Real.exp_zero, Function.comp_def] using hexp.congr' heqexp

end Shao.OQ4.RademacherBrownianBoundaryShift
end
