# OQ3 unit173 CN — actual affine-family common annulus gap
Exact TWO complete declarations and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.CompactOpenDomainAffineFrequencyGap. Imports Shao.OQ3.CompactOpenDomainTiltedFrequencyGap, Shao.OQ3.AffineWeakCramer. Namespace Shao.OQ3; open MeasureTheory; scoped Topology; noncomputable section. TWO publictheorems ZEROdefinitions.

First prove compactness of literal Euclidean pair annulus for ANY real delta/H, using ordinary Prod/MAX norm only as enclosing closed ball, never replacing the Euclidean radial hypothesis. Then derive ONE gamma∈(0,1) before everytheta/frequency for actual affine-parabola pushforwards of actual TRUE-full-MGF-interior tilted measures. Theta compact; original RAWtilted common Euclidean WC retained. A/b arbitrary parameter families, no continuity assumed; explicit uniformEuclidean lowerL>0 andupperU>0 bounds map delta≤radius≤H into fixedRAWannulus Ldelta≤radius≤UH, then CM provedRAWcompactgap plus old exactaffinephase normidentity. Actual laws are PROVEDprobability. delta>0; H may ANYreal (emptyannuli covered); Theta mayempty. No assumedgap/nonlattice/continuity/moments/atoms/density. CanonicalBUactualmeans/A specialization follows, not yet claimed here. Rootstrict0<beta<2/5 unchanged (auxbeta>=0). OriginalSongEdgeworth/weightederror/lowfrequency/integrals/exterior/newrhoLaplace/B-D OPEN; correctedA/boundedC/p54/attributionunchanged.

CMsource ddd8da6a8728fa307860646e6f53d2d3607b9dc0c0702eaa4260a63fd38f3955 firstkernel/AXPASS freshfullreviewACTIVE atfreeze, qualificationrequired beforeCNacceptance. OldAffineWeakCramer exact29457076f283c08b093949d3c12cfb020ea0bb496e51573ad74554114e94031f qualifiedfullindependentreportf554f4331bedd26dc516ca724464c971934ed88f52d0cdc249aed08039161ce5; fullconsumed2publicinterfaces/ALLY/nu/xiA/etaA/phi/cA/RA letvalues read, reusequalification notwholeoldproof. Rootv60receiptc495f3cd actualcheckedc82108f6/tree1039e99c distinctnotice main77df0204/accepted35b781a2; PR225305173d6/tree2480c5d5 frozen. Exactoldsource/library/v60map/server/producerbinding beforefirstkernel. Nooldgatereplay/sharedwrite.

```lean
theorem isCompact_euclidean_pair_annulus (delta H : ℝ) :
    IsCompact {a : ℝ × ℝ |
      delta ≤ Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ∧
        Real.sqrt (a.1 ^ 2 + a.2 ^ 2) ≤ H}

theorem compact_open_domain_affine_frequency_gap
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
    (A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (b : (ℝ × ℝ) → (Fin 2 → ℝ))
    (L U : ℝ) (hL : 0 < L) (hU : 0 < U)
    (hfreq : ∀ theta ∈ Theta, ∀ xi eta : ℝ,
      L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
          Real.sqrt ((xi * A theta 0 0 + eta * A theta 1 0) ^ 2 +
            (xi * A theta 0 1 + eta * A theta 1 1) ^ 2) ∧
        Real.sqrt ((xi * A theta 0 0 + eta * A theta 1 0) ^ 2 +
          (xi * A theta 0 1 + eta * A theta 1 1) ^ 2) ≤
            U * Real.sqrt (xi ^ 2 + eta ^ 2))
    (delta H : ℝ) (hdelta : 0 < delta) :
    let nu : (ℝ × ℝ) → Measure ℝ := fun theta =>
      mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun theta x =>
      A theta *ᵥ (![x, x ^ 2] - b theta)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun theta =>
      (nu theta).map (Y theta)
    let Phi : (ℝ × ℝ) → ℝ → ℝ → ℂ := fun theta xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂laws theta
    (∀ theta ∈ Theta, IsProbabilityMeasure (laws theta)) ∧
      ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧
        ∀ theta ∈ Theta, ∀ xi eta : ℝ,
          delta ≤ Real.sqrt (xi ^ 2 + eta ^ 2) →
            Real.sqrt (xi ^ 2 + eta ^ 2) ≤ H → ‖Phi theta xi eta‖ ≤ gamma
```
