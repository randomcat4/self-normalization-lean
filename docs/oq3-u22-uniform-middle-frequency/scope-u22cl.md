# OQ3 unit171 CL — genuine actual tilt/frequency joint Fourier continuity on the TRUE MGF interior
Exact THREE complete declarations and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.OpenDomainTiltedFourierContinuity. Imports Shao.OQ3.OpenDomainExponentialEnvelope, Mathlib.MeasureTheory.Measure.Tilted, Mathlib.Analysis.Complex.Trigonometric; namespace Shao.OQ3; open MeasureTheory; scoped Topology; noncomputable section. THREEpublictheorems ZEROdefinitions.

Use CK's PROVEDactualtwo-cornerintegrableenvelope to prove JOINT ordinarypair-parameter/frequency continuity of the ACTUAL complexweighted numerator at ANYtheta inTRUEfullMGFinterior andANYrealpairfrequency; provegenuineIntegrable. ProveactualpartitionZ(theta)>0 andcontinuity atthatpoint. ApplyexactPRIMARYintegral_tilted identity and real-scalarconstantintegral factoring to PROVE jointcontinuity of ACTUALtilted-law Fourierintegral, retainingnormalizer and actualtiltlawprobability/genuinephaseIntegrable. No bounded-support/moment/WC/assumedcontinuity/uniformgap/proxymeasure input. Real-smul-in-Complex in numerator isliteral expθweight, no hiddenphasechange. Publicstatementletsnu/phase fullyexplicit. ContinuousAt onfullambientspace legitimate becausepointtrueinterior andlocaldomination, notproofonlyonanassumedcompactfamily. Thisdoesnotyetassertcanonicalwhiteningparametercontinuity oruniformmiddlefrequencygap/Edgeworth. CKsource9df6b51d firstkernel/allownerAXPASS freshfullreviewACTIVE atfreeze; mustqualifybeforeCLacceptance. Rootdefinition d8bd5dc7/v60receiptc495f3cd checkedc82108f6/tree1039e99c; main77df0204/noticeaccepted35b781a2 distinct; PR225305173d6 frozenrootintake/CJ44595698qualified. Nooldgatereplay/sharedwrite. Sourceactualtilt/uniformfamily context r2/report.md/repair01.md; originalB-D/weightederror/integration/exterior/newrhoLaplaceOPEN; strictrootbeta/attribution/correctedA-boundedC/p54unchanged.

```lean
theorem open_domain_weighted_fourier_continuousAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta xi : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    Integrable (fun x : ℝ =>
      Real.exp (theta.1 * x + theta.2 * x ^ 2) •
        Complex.exp (((xi.1 * x + xi.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)) mu ∧
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ∫ x : ℝ, Real.exp (z.1.1 * x + z.1.2 * x ^ 2) •
          Complex.exp (((z.2.1 * x + z.2.2 * x ^ 2 : ℝ) : ℂ) * Complex.I) ∂mu)
        (theta, xi)

theorem open_domain_partition_function_continuousAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    0 < (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu) ∧
      ContinuousAt (fun p : ℝ × ℝ =>
        ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu) theta

theorem open_domain_tilted_fourier_continuousAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta xi : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let phase : ℝ → ℂ := fun x =>
      Complex.exp (((xi.1 * x + xi.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
    IsProbabilityMeasure nu ∧ Integrable phase nu ∧
      ContinuousAt (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
        ∫ x : ℝ, Complex.exp
          (((z.2.1 * x + z.2.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
          ∂mu.tilted (fun x => z.1.1 * x + z.1.2 * x ^ 2)) (theta, xi)
```
