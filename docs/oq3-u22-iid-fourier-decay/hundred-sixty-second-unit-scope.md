# OQ3 unit162 CC — actual iid standardized-law bounded-test assembly
Exact complete declaration and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.ActualStandardizedIIDCellTest. Imports ONLY Shao.OQ3.ParabolaIIDStandardizedLaw, Shao.OQ3.StandardizedCellBoundedBorelTest, Shao.OQ3.StandardizedCellChangeOfMeasure. Namespace Shao.OQ3; open MeasureTheory; scoped Topology BigOperators; noncomputable section. One public theorem zero definitions.

Source-bound next actual probability assembly: combine the EXACT actual raw iid P, actual tilted iid Q, actual normalized iid pair-law pushforward rho, and EXACT globally bounded measurable actual test used in weighted reconstruction. Input theta is in TRUE full integrability domain (interior not needed at this generic interface). All probability instances are proved from actual integral tilt normalization, not supplied as proxy-law assumptions. No Edgeworth or desired distribution comparison premise or conclusion. Closed rectangle closureanchor and originalhalfopenA retained; explicit M0/R0/S0 are supplied later from actual canonicalfamily. y arbitrary here; no mean0/covI claim without separately binding actual source mean and E.

```lean
theorem iid_quadratic_standardized_rectangular_bounded_test
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))
    (n : ℕ) (hn : 1 ≤ n) (y : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (aL aR qL qR M0 R0 S0 : ℝ)
    (hM0 : 0 ≤ M0) (hR0 : 0 ≤ R0) (hS0 : 0 ≤ S0)
    (hboundTheta : ‖theta‖ ≤ M0)
    (hE : ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ R0)
    (hEinv : ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ S0)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ))
    (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hrect : A ⊆ Set.Ioc aL aR ×ˢ Set.Ioc qL qR) :
    let f : ℝ → ℝ := fun x => theta.1 * x + theta.2 * x ^ 2
    let K : ℝ := Real.log (∫ x : ℝ, Real.exp (f x) ∂mu)
    let nu : Measure ℝ := mu.tilted f
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let F : (ℝ × ℝ) → (ℝ × ℝ) := fun w => Real.sqrt (n : ℝ) • E (w - y)
    let T : Shao.Path n → (ℝ × ℝ) := fun z => F (M z)
    let rho : Measure (ℝ × ℝ) := Q.map T
    let B : Set (ℝ × ℝ) := {v | y + (Real.sqrt (n : ℝ))⁻¹ • E.symm v ∈ A}
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let C0 : ℝ := Real.exp ((2 * M0) * S0 * R0)
    let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
    let law : Measure (ℝ × ℝ) := nu.map Y
    let QY : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let SN : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun v =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, v i
    IsProbabilityMeasure nu ∧ IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧
      IsProbabilityMeasure law ∧ IsProbabilityMeasure rho ∧ rho = QY.map SN ∧
      0 < C0 ∧ MeasurableSet B ∧ B = F '' A ∧
      Measurable (B.indicator g) ∧
      (∀ v : ℝ × ℝ, |B.indicator g v| ≤ C0) ∧
      Integrable (B.indicator g) rho ∧
      P.real (M ⁻¹' A) =
        Real.exp (-(n : ℝ) * (theta.1 * y.1 + theta.2 * y.2 - K)) *
          ∫ v : ℝ × ℝ, B.indicator g v ∂rho
```

All 16 statement let values above match AO/BV/CB exactly: f/K/nu/P/Q/M/F/T/rho/B/g/C0/Y/law/QY/SN. Fin n realpair iid sum normalization is genuine inverse sqrt n. Output rho equality uses actual one-observation law under same true quadratic tilt. Exact changeofmeasure is expressed as the global actual indicator test integral, using measurable B and the genuine integrability, not a totalized nonintegrable expression.

Consumed old BV155 source3c44e20c9003e0b743829a5ad46ee56f12f72c9cc8fbaa6bea61c5cbb3c526b7 reportu22bubv-proof-review.md SHA0ede4b14deb562e06696b2ac0c56d63b430f41c48b21063626a4870e69090c56, complete238source/4actualincl1generated/allvalues CORRECT108lines parentread; BV full consumed iid_parabola_affine_standardized_law interface/allvalues read. BV qualifiedfrozenPR217 dependency not rootv59map member. AO sourcececdbf313e675681bf62060134fe562b29e2f297cd35680ecd6c06f3496d01e1 reportu22amanao-proof-review.md SHAcfc9387484993a86e29be3f9d5436c565b37eb59fdb23a5e1a3da35839ccc31a complete371source15actual/fullvalues CORRECT163lines parentread; complete AO actual f/K/P/Q/M/F/T/rho/B/g and all conclusions read, rootv59map/library/server exact binding beforekernel. CB source1c42bc43f9187acee18fd2600ce0798038f2418aea7da3ce349e54e2336104c9 receipt789cdb80ce04b08a4fcd6823fa1778928c8af234f66e7aa6418a7f3d377945e9 firstkernel/actual2std3PASS, fresh joint CA/CBfullreviewACTIVE at freeze; cannot qualify CC until dependency fullyqualified.

Primary pinned MeasureTheory/Measure/Tilted.lean126 isProbabilityMeasure_tilted [NeZero mu] with genuine Integrable exp f -> actualmu.tiltedf probability, read. Shared BivariateLegendre definition TRUE bivariateMGFDomain is exactly Integrableexp(theta1*x+theta2*x²), full definitionread source d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58. Oldproofs/checks reused not reread/replayed.

Rootv59 receipt30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc checkedcode29c9804c552f0cc494355e6556c112aa3c36c908, mainb6bdf733 distinct. Later registry explicitlyreportsacceptedheadd9956f24a088a74d7265c6266db1746685be9d35/treedaf0d75114c28a26de01399fbaafade1ebae97a1, keptseparate. PR217fd718003 frozenrootintake. BW-CB publication pendingfreshjointreview; CC source NOT part of that frozen milestone and must stayoutsideits stagedfilemanifest. ServeronlyCPU14–17/nativeM8192/j4/autoImplicitfalse/max1heavy. Solechildlease1; no localLean/cache/package/sharedwrite/math-ultra/newsidebar/crossmessages/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/semanticweakenings. Every actualownedconstantinclgenerated/fulltype/allvalues fresh NONAUTHOR fullreview+recursiveAXstd3 mandatory. PreservefirstPASS exact and allfailures/warnings; no cosmeticedit/replay.

Actual SongEdgeworth proof/quantitativeweightederror/exterior/originalB-D OPEN; this supplies actual probability/test identity, not root closure. A/boundedC/p54/strictthreshold/externalattribution preserved.
