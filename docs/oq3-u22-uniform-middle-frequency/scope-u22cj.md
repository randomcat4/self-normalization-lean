# OQ3 unit169 CJ — actual normalized iid middle-frequency geometric and polynomial damping
Exact TWO complete declarations and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.NormalizedIIDPairMiddleFrequency. Imports Shao.OQ3.WeakCramerPairCompactGap, Shao.OQ3.NormalizedIIDPairCharacteristic, Shao.OQ3.NormalizedIIDPairSuperpolynomialDecay; namespace Shao.OQ3; open MeasureTheory Filter; scoped Topology BigOperators; noncomputable section. TWO public theorems ZERO definitions.

Apply PROVED compact-frequency gap to the ACTUAL normalizediid pi/map characteristic factor at exact scaledfrequency (xi/sqrt(n),eta/sqrt(n)) in compactKexcludingzero. gamma chosenbefore n/freq; then N chosenbefore n/freq for ANYrealpolynomialorder p and epsilon>0. No gap/continuity/normalizedCFerror asinput: onlygenuineoneobsWC, actualprobabilitylaw, compactfrequencysetexcludingzero. Geometric gamma^n dominated by exp(-(1-gamma)*n), then CFscalarstretchedexp with alpha1. Fixedlawonly, no uniformtiltfamily claim. n>=1 visible/derived. EmptyKallowed. Noatom/density/moments/mean/covariance/HilbertProdassumption; literalEuclideanWC andcoordinatephases, rootstrict0<beta<2/5 unchangedthoughnotrequired forthismiddlefrequencyauxiliary. CI source87853bd1 firstkernel/AXPASS jointfreshCHCIreviewACTIVE atfreeze; qualify beforeCJacceptance. CDsource22120e10 report9adffbf2 andCFsourceacf5eb8f reportb1c009a8 qualified. Rootv60 notice received PR217mergedviaPR223 exactfd718003; receiptc495f3cd checkedcodec82108f6/tree1039e99c, main77df0204/accepted35b781a2 distinct. No branchchange/oldgatereplay. PR221e730ce57stillfrozenrootintake; newCC-CIpacketpendingCHCIreview excludesCJ. ActualEdgeworth/weightederror/uniformparameter-middle-gap/integration/exterior/newrhoLaplace/originalB-DOPEN.

```lean
theorem normalized_iid_pair_compact_middle_frequency_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (K : Set (ℝ × ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ xi eta : ℝ,
        (xi / Real.sqrt (n : ℝ), eta / Real.sqrt (n : ℝ)) ∈ K →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          ‖(∫ w : ℝ × ℝ,
            Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
              gamma ^ n

theorem normalized_iid_pair_compact_middle_frequency_decay
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (K : Set (ℝ × ℝ)) (hcompact : IsCompact K)
    (hzero : ∀ a ∈ K, a.1 ≠ 0 ∨ a.2 ≠ 0)
    (p epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ xi eta : ℝ,
        (xi / Real.sqrt (n : ℝ), eta / Real.sqrt (n : ℝ)) ∈ K →
          let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
          let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
            (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
          let rho : Measure (ℝ × ℝ) := Q.map S
          Real.rpow (n : ℝ) p *
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ <
                epsilon
```
