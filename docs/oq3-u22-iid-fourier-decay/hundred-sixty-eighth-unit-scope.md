# OQ3 unit168 CI — actual pair-law Fourier continuity and compact nonzero-frequency gap
Exact TWO full declarations and ALL values frozen BEFORE implementation. ZERO nameddefs ZEROstatementlets. Module Shao.OQ3.WeakCramerPairCompactGap. Imports Shao.OQ3.WeakCramerPairNonlattice and Mathlib.Topology.Order.Compact. Namespace Shao.OQ3; open MeasureTheory; scoped Topology; noncomputable section.

Prove actual Fourier integral continuous in literal pair coordinates using unit-norm kernel and dominated convergence under the actual probability law, then use CH genuineWC nonlattice and compact maximum to give positivegamma<1 on ANY compact frequency set excludingzero. NO desiredgap/norm<1/continuity premise; continuity isPROVED, only genuine oneobservationWC isinput. K mayempty, no unstatedannulusnonemptiness; positivegammainemptycase e.g.1/2. This is a fixed-law gap; common uniformity over a parameter family isNOTclaimed. Noatom/moment/density assumptions, no Hilbertpairnorm confusion. hbeta>=0 matchingWCauxiliaries retained; rootstrict0<beta<2/5 unchanged. CHsource29d092b7 firstkernel/ownerAXPASS, independentreview pending atfreeze; qualification requiredbeforeCIacceptance. CFqualifiedb1c009a8; CGreviewACTIVE separately. Rootv59 receipt30f1cbf1 checked29c9804c; PR221e730ce57 frozenrootintake. ActualEdgeworth/frequencyintegration/exterior/newrhoLaplace/originalB-DOPEN; no sharedwrite/checkreplay.

```lean
theorem continuous_pair_characteristic
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law] :
    Continuous (fun a : ℝ × ℝ =>
      ∫ w : ℝ × ℝ,
        Complex.exp (((a.1 * w.1 + a.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂law)

theorem weak_cramer_pair_compact_frequency_gap
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (K : Set (ℝ × ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧ ∀ a ∈ K,
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((a.1 * w.1 + a.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤ gamma
```
