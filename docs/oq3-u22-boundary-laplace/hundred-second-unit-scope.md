# U22u — actual covariance amplitude on the given mean chart

Complete declarations frozen before implementation. Module Shao.OQ3.OpenDomainCovarianceAmplitude. Two public theorems, zero definitions. Source binding: original repair01.md equations (8),(12), lines124–171. First prove actual tilted covariance determinant C-infinity on the true open MGF domain, from actual smooth mean derivatives. Second use a GIVEN actual mean partial-homeomorphism (so it can be exactly R/T's witness), recover smooth inverse by the proved inverse theorem, compose the exact source G and form the literal inverse square-root determinant amplitude. Produce one positive closed rectangle on which inverse parameters lie in the true domain, actual determinant stays positive and amplitude varies by at most C*(|r|+z).

The actual center determinant positivity is explicit, supplied in the original root by its retained actual covariance spectral positivity. It is not replaced by a bound on another law, and is not claimed to follow here merely from determinant nonzero. All original source spectral/WC/moment/global saddle/far probability scope remains. No desired amplitude bound is assumed. No Jacobian/tail equivalence/Laplace/probability/root closure claim. Source/header UTF8 LF; established exact hash kernel/full-owned AX and one fresh final review required.

```lean
import Shao.OQ3.OpenDomainMeanInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem open_domain_quadratic_covariance_det_contDiffOn
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ =>
        (parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det)
      (interior (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))

theorem open_domain_chart_covariance_amplitude
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (level a0 : ℝ) (hlevel : 0 < level) (ha0 : 0 < a0)
    (hmean : (∫ x : ℝ, x ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2),
      ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)) =
        (a0, a0 ^ 2 / level ^ 2))
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (he : (e : (ℝ × ℝ) → (ℝ × ℝ)) = fun p =>
      (∫ x : ℝ, x ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2),
        ∫ x : ℝ, x ^ 2 ∂mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)))
    (hsource : theta ∈ e.source)
    (hpositive : 0 < (parabolaCovariance
      (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det) :
    let Omega : Set (ℝ × ℝ) := interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    let G : (ℝ × ℝ) → (ℝ × ℝ) := fun w =>
      (a0 + w.1, (a0 + w.1) ^ 2 / level ^ 2 - w.2)
    let P : (ℝ × ℝ) → (ℝ × ℝ) := fun w => e.symm (G w)
    let detF : (ℝ × ℝ) → ℝ := fun w =>
      (parabolaCovariance
        (mu.tilted (fun x => (P w).1 * x + (P w).2 * x ^ 2))).det
    let A : (ℝ × ℝ) → ℝ := fun w => (Real.sqrt (detF w))⁻¹
    P (0, 0) = theta ∧ ContDiffAt ℝ ∞ P (0, 0) ∧
      ContDiffAt ℝ ∞ A (0, 0) ∧
      A (0, 0) = (Real.sqrt (parabolaCovariance
        (mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))).det)⁻¹ ∧
      ∃ rho C : ℝ, 0 < rho ∧ 0 < C ∧ ∀ r z : ℝ,
        |r| ≤ rho → 0 ≤ z → z ≤ rho →
        P (r, z) ∈ Omega ∧ 0 < detF (r, z) ∧
          |A (r, z) - A (0, 0)| ≤ C * (|r| + z)

end
end Shao.OQ3
```
