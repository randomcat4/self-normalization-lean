# OQ3 unit170 CK — actual true-open-domain local exponential envelope
Exact ONE complete declaration and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.OpenDomainExponentialEnvelope. Import ONLY Shao.Probability.BivariateLegendre; namespace Shao.OQ3; open MeasureTheory; scoped Topology; noncomputable section. ONEpublic theorem ZEROdefinitions.

Source-bound missing compacttilt jointCFcontinuity step: from an ACTUAL interior point of the FULL exponential Integrable MGF domain derive positive r with both literal corners theta+(r,r),theta+(-r,r) still in the true domain. The ACTUAL explicit g is the sum of the two corner exponentials, not an assumed envelope. Prove g Integrable/nonnegative, and EVERY parameter in ordinaryProd/MAXnorm ball radiusr has exp(p1*x+p2*x²)<=g(x) and genuineIntegrable, for ALLrealx includingunbounded/support/atoms. Uses onlyx²>=0 and two signs ofx; no bounded-support/desiredcontinuity/gap assumption, no dropped exponentialnormalizer. This auxiliary doesnotitselfprovejointCFcontinuity or parameter-uniformgap. RootBivariateLegendre source d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58 definitionfullyconsumed and exactv60source-map/library/serverbound; standardrootqualifiedchecksreused. Rootv60receiptc495f3cd checkedc82108f6/tree1039e99c, main77df0204/noticeaccepted35b781a2 distinct. PR225305173d6/tree2480c5d5 exact59files frozenrootintake, currentcontinuationfeat/oq3-middle-frequency-and-inversion. CJ16944595698 qualifiedfull90linereport579eeb8e. No oldgatereplay/sharedwrite. ActualEdgeworth/weightederror/thetauniformmiddle-gap/integrals/exterior/newrhoLaplace/originalB-DOPEN; strictrootbeta/attribution/correctedA-boundedC/p54unchanged.

```lean
theorem open_domain_local_exponential_envelope
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    ∃ r : ℝ, 0 < r ∧
      (theta.1 + r, theta.2 + r) ∈
        Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) ∧
      (theta.1 - r, theta.2 + r) ∈
        Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) ∧
      let g : ℝ → ℝ := fun x =>
        Real.exp ((theta.1 + r) * x + (theta.2 + r) * x ^ 2) +
          Real.exp ((theta.1 - r) * x + (theta.2 + r) * x ^ 2)
      Integrable g mu ∧ (∀ x : ℝ, 0 ≤ g x) ∧
        ∀ p : ℝ × ℝ, ‖p - theta‖ < r →
          Integrable (fun x : ℝ => Real.exp (p.1 * x + p.2 * x ^ 2)) mu ∧
            ∀ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ≤ g x
```
