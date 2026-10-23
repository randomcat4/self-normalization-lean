# OQ3 unit154 BU — actual compact-open pair whitened probability family
Complete exact declaration/all statementvalues frozen BEFORE implementation. Module Shao.OQ3.CompactOpenDomainPairProbability; imports Shao.OQ3.CompactOpenDomainCovarianceSpectrum, Shao.OQ3.ParabolaPairWhiteningFamily, Shao.OQ3.OpenDomainWhitenedFamily, Shao.OQ3.OpenDomainRealMoments. Namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Matrix Topology ContDiff; noncomputable section. One public theorem, zero definitions.

Sourcebound task: actual compactopen standardizedprobabilitylaw prerequisites of original repair01.md SonguniformEdgeworth. Remove retained uniformcovariancespectrum premise usingBR; choose canonicalPAIRcontinuouslinearequivalences viaBO whose actual centeredaction is EXACTtwo coordinates of the SAME Fin2 Y definingactualpushforwardlaws. Retain qualifiedI's entire actualcentering/unitcovariance/probability/positivecanonicalmatrix/frequency/weakCramer/naturalallmoments packet. Add genuineuniform8+delta REALradialmoment for EVERYdelta>0 viaqualifiedJ. Input uniformactualtilt weakCramer is explicitretained, notclaimedfrompointwiseWC/arbitrarylaw. No boundedsupport or desiredspectrum/moment/covariance/Edgeworth premise.

```lean
theorem compact_open_domain_pair_whitened_probability_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hdet : ∀ p ∈ Theta, 0 < (parabolaCovariance
      (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det)
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
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      (∀ p ∈ Theta, ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
        xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2)) ∧
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
      (∀ p : Theta,
        (∀ w : ℝ × ℝ, E p w =
          (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
        ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
        ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo) ∧
        ∀ x : ℝ, E p ((x, x ^ 2) - (means p 0, means p 1)) =
          (Y p x 0, Y p x 1)) ∧
      (∀ delta : ℝ, 0 < delta → ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ =>
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta)) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ∧
        (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ≤ C) ∧
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

All tilt/D/s/t/A/means/Y/laws/Phi and L/U/cA/RA values are EXACT I values. lo/hi>0 andactualspectralbounds CONCLUSIONS. ActualpairErow is samecanonicalA asGaussianfamily; fullcenteredEaction equals coordinatesY for EVERYx, no alternatecenter/law. Efamilychoicecontinuitynotasserted. Natural/realmoment constants dependonexponent but chosenBEFOREp; emptyThetavalid. WeakCramerbeta>=0 maintained, no sourceSongthreshold/Edgeworth assertion follows merelyfromthispacket.

Qualifieddependencies: BRc54c920a116lines2actual reportaf9b4b7e23778b3d63eeb9658d5c2e0dff43e6dd66224d080f6a349eb2569a61 all116source/fulltypes/values CORRECT, full119linesparentread; BO9c48fd8a9434a7c28cb9761358f93255fb0dcf0d836093fc2a0c10afd8d65fdc report7dc938dc06414bf96bf9f758d276b759c04b68bac0296cda56cf37158b17a48f all66source/fulltype/values CORRECT, full79lineparentread; I OpenDomainWhitenedFamily622601d0f8650bfc684f4dfde9a615700ad48c4911f5316734193278e115ee8e reportu22i-proof-review.md SHA7bb803f036a85be8e21c5462c2d50a7533946dba856f47c570b8c442429ccab4 CORRECT all120source1actual, consumedcompletepublicdeclaration/allvaluesnowread; J OpenDomainRealMoments4da837a392834289bb9b90b25953435b41a68b89038ef2e7f361648a30debbe7 reportu22j-proof-review.md SHA5a6203ea15d71a8bb33a7941f69f774ab551bf786a8051ee3698d21ef7fe1be7 CORRECT all138source3actual inclprivatehelper, consumedcomplete eight_add_delta theorem+allletvaluesnowread. ActualI/Jsourcebinding rootv57receipt map/serverhashverify BEFOREfirstkernel. No oldproof/checkreplay.

Only designatedserverCPU14–17/native-M8192-j4/autoImplicitfalse/oneheavy; solechildlease1 serialfreshNONAUTHOR completeALLNEWsource/fulltypes/ALLvalues/allactualownergen/recursiveAX whiteliststd3. CurrentBSBTreviewactive; BUfreshreviewafteritstops. No math-ultra/newsidebar/crossmessages/localLean/cache/package/rootsharedwrites. No sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings; preserveoriginalfailures/warnings/exactfirstPASS; no cosmeticPASSedits/passedcheckreplay. Activefeat/oq3-covariance-cell-family parent0b64fc exactmergedancestorPR210 atrootv57; no merge/rebase. Actualiid standardizedsamplelaw identity, externalSongtheoremformalproof, weightedprobabilityreconstruction/cellsum/exterior andoriginalB/D remainOPEN; fixedlawcorrectedA/boundedC,p54andexternalattributionunchanged.
