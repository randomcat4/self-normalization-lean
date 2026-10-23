# U22i — actual unbounded open-domain covariance-whitened family

FROZEN before implementation, 2026-10-23, OQ3 lane. Source R2report38–61/83–92 and root-contract2/4. This consumer binds the actual tilt covariance to the actual positive symmetric whitening construction, uses genuine compact raw-moment and matrix-entry transfer, and retains the original family's explicit uniform spectra and weak-Cramer assumptions. No bounded-support premise or single-reference-law stability argument is introduced.

Module `Shao.OQ3.OpenDomainWhitenedFamily`, zero public definitions and one public theorem. Exact imports and TYPE:

```lean
import Shao.OQ3.OpenDomainAffineMoments
import Shao.OQ3.QuadraticWhiteningSpectralData

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem compact_open_domain_covariance_whitened_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (lo hi beta c R : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hspec : ∀ p ∈ Theta,
      let D : Matrix (Fin 2) (Fin 2) ℝ :=
        parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      ∀ xi eta : ℝ,
        lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2))
    (hWC : ∀ p ∈ Theta, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
      ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - means p)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
    let Phi : (ℝ × ℝ) → ℝ → ℝ → ℂ := fun p xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂laws p
    let L : ℝ := 1 / Real.sqrt hi
    let U : ℝ := 1 / Real.sqrt lo
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < L ∧ 0 < U ∧ 0 < cA ∧ 0 ≤ RA ∧
      (∀ p ∈ Theta,
        0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
          0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
        IsProbabilityMeasure (laws p) ∧
        (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (laws p) ∧
          (∫ y : Fin 2 → ℝ, y i ∂laws p) = 0) ∧
        (∀ i j : Fin 2, ProbabilityTheory.covariance
          (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
            if i = j then 1 else 0) ∧
        (∀ xi eta : ℝ,
          L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
            Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
              (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
          Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
              (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
            U * Real.sqrt (xi ^ 2 + eta ^ 2)) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤ 1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ∧
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ≤ C
```

The law, true exponential-integrability interior, covariance, centering, positive symmetric whitening, map law and characteristic function are all literal. The caller retains the original B uniform actual covariance spectra and uniform actual tilted weak-Cramer bound. No arbitrary replacement covariance, whitening or family-moment conclusion is input. The exponent beta is unchanged; only the explicit constants cA/RA are adjusted. This works for arbitrary unbounded mu under these actual-domain/family assumptions, not by extending the bounded C density lower-bound mechanism. Empty Theta is permitted. The helper's affine transfer works for all nonnegative beta; root B must still retain beta<2/5 and every other original root condition.

Natural-order uniform Euclidean moments are produced with the constant chosen before p. This scope does not yet state a real 8+delta power, a Lindeberg condition, a local inverse/compact inverse-image neighborhood, global rate geometry, Song's Edgeworth theorem, cell reconstruction/summation, boundary Laplace or far-probability bounds. None of B/D is closed by this family interface alone. The accepted bounded C scope remains unchanged.

Proof uses genuine all-domain tilted probability/L2 from U22a, actual whitening and entry/frequency data from U22h, U22g's genuine centered affine moment transfer, and the accepted general centered affine mean/covariance and affine weak-Cramer producers. Full exact interface identity and single actual matrix/law are required; no projection may substitute a partial or different family witness. No new external-result axiom.

Server-only CPU14–17/native8192/j4/autoImplicit=false/one heavy command; accepted package/source-view only, root alone shared/cache/pins/root-imports/integration. Full fresh independent complete proof/source semantic review and every actual owner/private/generated transitive axiom required, only propext/Classical.choice/Quot.sound. No sorry/admit/new axiom/unsafe/native_decide/implemented_by/weak settings. Preserve exact failed versions, never repeat unchanged successful checks; no new execution wrapper.
