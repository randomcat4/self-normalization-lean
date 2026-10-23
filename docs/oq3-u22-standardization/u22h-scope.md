# U22h — reusable genuine positive covariance whitening data

FROZEN before implementation, 2026-10-23, OQ3 lane. Source R2report53–59/83–92 and root-contract2/4. The next actual unbounded open-domain standardized family must produce its actual whitening matrix and entry/frequency bounds from retained uniform actual covariance spectra. U22g only transfers moments under an explicit entry bound; it does not produce the whitening construction. This finite-dimensional helper supplies that missing matrix interface, without claiming any root theorem by itself.

Module `Shao.OQ3.QuadraticWhiteningSpectralData`, zero public definitions and one public theorem. The accepted private `CovarianceWhitening.whitening_spectral_data` proof at library lines29–210 is the complete mathematical proof pattern; it is not publicly callable and must not be referenced through a private name. Reproduce its exact numeric argument in this owned module, with full source attribution and independent review, then derive actual entry bounds from its genuine frequency bounds. No prior review substitutes for reviewing the new exact source.

```lean
import Shao.OQ3.CovarianceWhitening

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix BigOperators
noncomputable section

theorem quadratic_whitening_spectral_data
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hsym : D 1 0 = D 0 1)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hspec : ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
      xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
        hi * (xi ^ 2 + eta ^ 2)) :
    let s : ℝ := Real.sqrt (D 0 0 * D 1 1 - (D 0 1) ^ 2)
    let t : ℝ := Real.sqrt (D 0 0 + D 1 1 + 2 * s)
    let A : Matrix (Fin 2) (Fin 2) ℝ :=
      ![![(D 1 1 + s) / (s * t), -(D 0 1) / (s * t)],
        ![-(D 0 1) / (s * t), (D 0 0 + s) / (s * t)]]
    0 < s ∧ 0 < t ∧ Aᵀ = A ∧ A * D * A = 1 ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
        0 < xi * (A *ᵥ ![xi, eta]) 0 + eta * (A *ᵥ ![xi, eta]) 1) ∧
      (∀ xi eta : ℝ,
        (1 / Real.sqrt hi) * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A 0 0 + eta * A 1 0) ^ 2 +
            (xi * A 0 1 + eta * A 1 1) ^ 2) ∧
        Real.sqrt ((xi * A 0 0 + eta * A 1 0) ^ 2 +
            (xi * A 0 1 + eta * A 1 1) ^ 2) ≤
          (1 / Real.sqrt lo) * Real.sqrt (xi ^ 2 + eta ^ 2)) ∧
      ∀ i j : Fin 2, |A i j| ≤ 1 / Real.sqrt lo
```

D and both spectral constants remain explicit numeric inputs. The later actual-law consumer must substitute its literal parabolaCovariance at each true tilt and retain/prove hspec from the source hypotheses. The output matrix is the literal positive symmetric construction; its denominators must be proved positive before any field operations. Frequency bounds apply to the actual transposed frequency map in both directions; entry bounds follow from testing rows and squaring nonnegative quantities. No support, moments, weak-Cramer or probability theorem is proved here. No positive matrix is silently replaced by a supplied arbitrary A, and no source-level spectrum or nondegeneracy assumption is weakened.

Next consumer, not frozen by this scope: combine the actual-law matrix data with U22g and the accepted general centered affine mean/covariance and affine weak-Cramer producers, giving actual standardized open-domain compact families under the retained actual uniform spectra/WC assumptions. B/D, compact inverse-image/global-rate/Edgeworth/cell/Laplace/far-probability obligations remain OPEN.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy, accepted shared-v34 packages and necessary Shao read-only source-view, no shared/cache/pins/root-import edits. Complete source-to-statement/proof review by fresh independent gpt-6.1-sol/xhigh and all actual-owner/private/generated transitive-axiom coverage required, only propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/proof-setting weakening. Retain failures and do not repeat unchanged passed checks. No new execution wrapper.
