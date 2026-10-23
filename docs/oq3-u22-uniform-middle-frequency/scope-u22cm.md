# OQ3 unit172 CM — actual RAW compact tilted-law uniform frequency gap
Exact TWO complete declarations and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.CompactOpenDomainTiltedFrequencyGap. Imports Shao.OQ3.OpenDomainTiltedFourierContinuity, Shao.OQ3.WeakCramerPairNonlattice, Mathlib.Topology.Order.Compact. Namespace Shao.OQ3; open MeasureTheory; scoped Topology; noncomputable section. TWO publictheorems ZEROdefinitions.

First specialize CHgenuineWCnonlattice to the ACTUAL rawparabola law underactualtrue-interior tilt, via PROVED pushforwardcoordinate Fourierintegral identity and actualtilt/pushforwardprobability; noatoms/density/moment/desirednonlattice input. Then use CLPROVEDjointtheta/frequencycontinuity and maxoncompactTheta×K to choose ONEpositivegamma<1 BEFOREANYtheta/frequency. Theta compactinsideTRUEfullMGFinterior, genuineONEcommonrawtiltedWC premise andKcompactexcludingzero; Theta/Kmayempty. No assumptionofjointcontinuity/gap/mean/E/covariance. Thisis RAWtiltedcharacteristic, notyetcanonicalwhitened; laterBUuniformspectralfrequencybounds canmapwhitenedcompactannulus intoRAWcompactannulus withoutrequiringtheta-continuityofE. Rootstrict0<beta<2/5 unchanged; auxiliaryhbeta>=0 retained, nonewfarfrequencythresholdclaim. CLsource7f72f0c5 firstkernel/ownerAXPASS freshreviewACTIVEatfreeze; qualifybeforeCMacceptance. CHsource29d092b7 qualifiedjointreport398b579b; rootv60receiptc495f3cd checkedc82108f6/tree1039e99c, main77df0204/noticeaccepted35b781a2distinct; PR225305173d6 exact59files frozenrootintake. Nooldgatereplay/sharedwrite. OriginalSongEdgeworth/weightederror/lowfrequency/integration/exterior/newrhoLaplace/B-DOPEN, correctedA/boundedC/p54/strictrootbeta/attributionunchanged.

```lean
theorem open_domain_tilted_weak_cramer_nonlattice
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ x : ℝ,
        Complex.exp (((u * x + v * x ^ 2 : ℝ) : ℂ) * Complex.I)
          ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))‖ ≤
            1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta)) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    IsProbabilityMeasure nu ∧ ∀ u v : ℝ, u ≠ 0 ∨ v ≠ 0 →
      ‖(∫ x : ℝ,
        Complex.exp (((u * x + v * x ^ 2 : ℝ) : ℂ) * Complex.I) ∂nu)‖ < 1

theorem compact_open_domain_tilted_frequency_gap
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ theta ∈ Theta, ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ x : ℝ,
        Complex.exp (((u * x + v * x ^ 2 : ℝ) : ℂ) * Complex.I)
          ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))‖ ≤
            1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (K : Set (ℝ × ℝ)) (hKcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧
      ∀ theta ∈ Theta, ∀ a ∈ K,
        ‖(∫ x : ℝ,
          Complex.exp (((a.1 * x + a.2 * x ^ 2 : ℝ) : ℂ) * Complex.I)
            ∂mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2))‖ ≤ gamma
```
