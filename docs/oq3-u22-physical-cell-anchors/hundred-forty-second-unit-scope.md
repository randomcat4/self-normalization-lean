# OQ3 U22BI / unit142 — frozen true-rate lower semicontinuity and closure anchor

FROZEN before implementation. math-theorem/no math-ultra. OQ3 lead author; fresh independent full newsource/proof/everyactualownedtype/everyglobal-localvalue and actual-owner recursive standard3 axiom audit mandatory. Two public theorems, no global definitions. All checks designatedserver only CPU14–17 max1heavy/-M8192/-j4/-DautoImplicit=false, pinned Lean4.36.0-rc1/mathlib807d3836 and read-onlypackages.

Source-bound gap: repair01 section3 asks for a rate-minimizing anchor inside each truncated cell. The actual disjoint grid uses half-open Ioc cells, so interior-cell attainment is not available. The preserved anchor note proposes actual compact closures, retained inside the closed physical local window. This unit must PRODUCE a true global EReal Legendre-rate minimum on that closure, without assuming rate continuity/semicontinuity/attainment or sample atomlessness.

Exact imports planned: Shao.Probability.BivariateLegendre; Mathlib.Topology.Semicontinuity.Basic; Mathlib.Topology.Instances.EReal.Lemmas; Mathlib.Topology.Instances.Real.Lemmas. Root-owned BivariateLegendre source SHAd8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58 verified exact both localreadonlylibrary andserver; v53 receipt source_files_sha256 explicitly binds it (receipt6c4c3ff622f79210bcef2c86aadd90f9b2f9095afd5d45ba4da412629b5956d2/acceptedec5f51dbf8bfd4e3d4ca81db63c5b24dcaf37da1). Fully consumed true bivariateMGFDomain/bivariateLogMGF/bivariateLegendreRate definition values; oldqualifiedproofs/checks reused, no sharedimplementation edit. Primary semicontinuity/EReal/Real objects observedpresent in sharedreadonlyview; no cachehydration/rebuild.

Exact complete declarations and ALL statement local values:
```lean
theorem bivariate_legendre_rate_lower_semicontinuous
    {Ω : Type*} [MeasurableSpace Ω] (mu : MeasureTheory.Measure Ω) [NeZero mu]
    (W : Ω → ℝ × ℝ) :
    LowerSemicontinuous (Shao.Probability.bivariateLegendreRate mu W)

theorem actual_parabola_cell_closure_rate_anchor
    (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu]
    (aL aR qL qR level a0 rho : ℝ)
    (hA : (((Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}) :
          Set (ℝ × ℝ)).Nonempty) :
    let V : Set (ℝ × ℝ) := {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
    let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
    IsCompact (closure A) ∧
      ∃ y ∈ closure A, y ∈ Q ∩ V ∧
        ∀ w ∈ closure A,
          Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) y ≤
            Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w
```

First: arbitrary measurable Ω, arbitrary nonzero measure mu and arbitrary W, using EXACT true exponential-integrability domain and EReal supremum over all its tests. No probability assumption or W global measurability premise is added; fixed-domain tests are real affine continuous functions of z, and their EReal casts are continuous, so their supremum is lower semicontinuous. Empty test domain and infinite supremum values remain genuine EReal cases.

Second: actual scalar probability measure, ALL seven real geometry parameters, and actual nonempty original half-open-grid/closedwindow cell. No positive rho/level/order/gridwidth/spectral/finiteness hypothesis is hidden; nonempty hA rules out impossible geometry but must be the actual cell. Prove compact closure from its inclusion in the original closed grid rectangle Q, and closure inclusion in V from V closedness. Its anchor lies in the actual closure and Q∩V; it is not asserted inside A. The minimum is the TRUE global EReal rate over closure A, not a renamed real proxy or local assumed minimum.

Proof-local values allowed: g(w)=w.1²/level²-w.2; fixed-test T_theta(z)=theta.1*z.1+theta.2*z.2-bivariateLogMGF mu W theta; actual V/A/Q exactly above. Obtain nonempty closure from actual hA and apply lower-semicontinuous minimum attainment on the proved compact set. No desired anchor/rate inequality may enter as an assumption. Total division covers level0 puregeometry; original physical probability scope still retains positivelevel/domain conditions.

OPEN: anchor rate may be +infinity in this generic statement; actual physical patch identification with the qualified finite analytic rate is a subsequent source-bound producer, and the genuine tail positivity inside AL's V must be consumed when needed. No minimum inside a half-open A or atomic-boundary nullity is claimed. Exact disjointpartition/weightedreconstruction, uniformtruewhitening/cellfamily, actualsampleEdgeworth/summation/full exterior and originalB/D remain OPEN. Accepted correctedfixedlawA/boundedcompacttiltC scopes and allp54/WC/externalattribution constraints retained. This closes only explicit compact-closure attainment data after independent qualification.

