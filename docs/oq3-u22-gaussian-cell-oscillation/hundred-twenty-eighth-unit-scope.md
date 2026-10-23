# OQ3 unit128 / U22au — genuine measurable oscillation supremum

Original target: B, repair01.md section2 equations(4)–(6), report cell oscillation. Direct consumer: integral of the actual indicator-cell oscillation under Phi2; finite-measure theorem supplies genuine integrability before integral monotonicity. This unit does not provide tube estimates, an actual Edgeworth theorem or original B/D closure.

Exact definition and declarations are frozen below before source implementation. All functions/sets use the existing product-real norm. Inserting zero makes the supremum nonempty even for h≤0; for h>0 the ball is nonempty and zero is already a genuine diagonal pair value. The global bound on f guarantees a finite real supremum. No measurable/continuous f premise is needed: strict superlevel sets of the moving open-ball supremum are open by fixed-pair witnesses. This does not replace the source supremum by an assumed majorant, and an eventual integral proof must derive bounds for the actual definition. No assumptions may be silently changed.

```lean
def openBallOscillation (f : (ℝ × ℝ) → ℝ) (h : ℝ) (z : ℝ × ℝ) : ℝ :=
  sSup (insert 0 {r : ℝ | ∃ u ∈ Metric.ball z h, ∃ v ∈ Metric.ball z h,
    r = |f u - f v|})

theorem open_ball_oscillation_properties
    (f : (ℝ × ℝ) → ℝ) (C h : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ C) :
    (∀ z, 0 ≤ openBallOscillation f h z ∧ openBallOscillation f h z ≤ 2 * C) ∧
    (∀ z, ∀ u ∈ Metric.ball z h, ∀ v ∈ Metric.ball z h,
      |f u - f v| ≤ openBallOscillation f h z) ∧
    (∀ t : ℝ, IsOpen {z : ℝ × ℝ | t < openBallOscillation f h z}) ∧
    Measurable (openBallOscillation f h)

theorem open_ball_oscillation_integrable
    (μ : MeasureTheory.Measure (ℝ × ℝ)) [MeasureTheory.IsFiniteMeasure μ]
    (f : (ℝ × ℝ) → ℝ) (C h : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, |f x| ≤ C) :
    MeasureTheory.Integrable (openBallOscillation f h) μ
```
