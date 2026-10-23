# Actual Xi cone product — candidate complete signatures

Status: `AWAITING_ROOT_FREEZE`. No production implementation. Intended module: `Shao/Probability/QuadraticFullNoiseConeDerivatives.lean`, consuming the actual K and scalar interfaces after their independent acceptance.

```lean
import Shao.Probability.QuadraticFullNoise
import Shao.Probability.QuadraticChordConeDerivatives
import Shao.Probability.SourceScalarFourierDerivatives

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory

theorem quadraticFullNoiseChar_cone_retained_derivatives :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
            let R : ℝ :=
              (quadraticChordChar ν u v).re ^ 6 *
                (quadraticChordChar ν (-u) v).re ^ 6
            DifferentiableAt ℝ (fun t : ℝ => quadraticFullNoiseChar ν t v) u ∧
            DifferentiableAt ℝ
              (fun t : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v) t) u ∧
            ‖quadraticFullNoiseChar ν u v‖ ≤ R ∧
            ‖deriv (fun t : ℝ => quadraticFullNoiseChar ν t v) u‖ ≤ C1 * R / |u| ∧
            ‖deriv
              (fun t : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v) t) u‖ ≤
                C2 * R / u ^ 2

theorem quadraticFullNoiseChar_cone_derivative_bounds :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun a : ℝ => |a| ^ 3) ν →
        0 < variance (id : ℝ → ℝ) ν →
        ∀ h : ℝ, 0 < h → (∀ᵐ a : ℝ ∂ν, |a| ≤ h) →
          ∀ u v : ℝ, u ≠ 0 → |v| ≤ |u| / (4 * h) →
            ‖deriv (fun t : ℝ => quadraticFullNoiseChar ν t v) u‖ ≤ C1 / |u| ∧
            ‖deriv
              (fun t : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v) t) u‖ ≤
                C2 / u ^ 2

end Shao.Probability
```
