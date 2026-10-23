# U22z — exact leading integral and quantitative scaled cutoff integral

Complete declarations frozen before implementation. Module Shao.OQ3.BoundaryLaplaceIntegral, two public theorems, zero definitions. Source repair01.md equation14, lines183–210. First evaluate the genuine Gaussian/positive-normal product integral with its exact constant and prove integrability. Second combine X's all-halfplane pointwise quantitative bound with Y's proved integrable envelope to obtain a uniform absolute order-t bound for the scaled cutoff integral. Only almost-everywhere strong measurability of the actual cutoff kernel is an additional analytic input; neither its integrability nor the desired integral error is assumed. The original actual C3/amplitude germs will supply this measurability after a common window shrink. Original-coordinate Jacobian/scaling, common actual chart/window assembly, relative normalization and actual probability/Edgeworth/far-field errors remain separate tasks; B/D stay open.

```lean
import Shao.OQ3.BoundaryLaplaceCutoff
import Shao.OQ3.BoundaryLaplaceEnvelope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem boundary_laplace_leading_integral
    (lambda Lambda1 a0 : ℝ) (hlambda : 0 < lambda) (hLambda1 : 0 < Lambda1) :
    let mu : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let L : (ℝ × ℝ) → ℝ := fun p =>
      a0 * Real.exp (-(lambda * p.2 + Lambda1 / 2 * p.1 ^ 2))
    Integrable L mu ∧ (∫ p : ℝ × ℝ, L p ∂mu) =
      a0 * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)

theorem boundary_laplace_cutoff_integral_error
    (F A : (ℝ × ℝ) → ℝ) (lambda Lambda1 rho CF CA c d : ℝ)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hrho : 0 < rho) (hd : 0 < d)
    (hdc : d ≤ c) (hdl : d ≤ lambda) (hdq : d ≤ Lambda1 / 2)
    (hbound : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |F (r, z) - F (0, 0) - lambda * z - Lambda1 / 2 * r ^ 2| ≤
        CF * (|r| ^ 3 + |r| * z + z ^ 2))
    (hmargin : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (hamplitude : ∀ r z : ℝ, |r| ≤ rho → 0 ≤ z → z ≤ rho →
      |A (r, z) - A (0, 0)| ≤ CA * (|r| + z))
    (hmeas : ∀ t : ℝ, 0 < t → t ≤ 1 →
      AEStronglyMeasurable (fun p : ℝ × ℝ =>
        if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
          A (t * p.1, t ^ 2 * p.2) *
            Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0)
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0)))) :
    let mu : Measure (ℝ × ℝ) :=
      (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ici 0))
    let K : ℝ → (ℝ × ℝ) → ℝ := fun t p =>
      if |t * p.1| ≤ rho ∧ t ^ 2 * p.2 ≤ rho then
        A (t * p.1, t ^ 2 * p.2) *
          Real.exp (-((F (t * p.1, t ^ 2 * p.2) - F (0, 0)) / t ^ 2)) else 0
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      Integrable (K t) mu ∧
        |(∫ p : ℝ × ℝ, K t p ∂mu) -
          A (0, 0) * (Real.sqrt (2 * Real.pi / Lambda1) / lambda)| ≤ C * t

end
end Shao.OQ3
```
