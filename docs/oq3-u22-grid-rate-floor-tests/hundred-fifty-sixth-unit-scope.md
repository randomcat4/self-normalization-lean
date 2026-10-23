# OQ3 unit156 BW — exact actual finite-grid weighted reconstruction
Complete declaration/all statementletvalues frozen BEFOREimplementation. Module Shao.OQ3.PhysicalGridWeightedReconstruction; imports Shao.OQ3.ParabolaGridCardinality and Shao.OQ3.StandardizedCellChangeOfMeasure ONLY. Namespace Shao.OQ3; open MeasureTheory; scoped Matrix Topology BigOperators; noncomputable section. One public theorem zero definitions.

Sourceboundnextdependency: repair01.md exactcellreconstruction leadingtoward(7). Produce the ACTUAL finite activehalfopengridK and C*n²count fromBM, useBKexactdisjointcoverand measurability to sum actualP.real(MpreimageV), applyAOactualsamplechangeofmeasurecellwise with originalmu,n,M. Arbitrary functions theta,y,E are quantified AFTERsamefiniteK; onlyactualtheta membershipTRUE MGFdomain foractivecells isassumed. No desiredprobabilityidentity, assumedcellcount, boundaryzero, integrabilityconclusion orGaussian/Edgeworthcomparison premise. LateractualBQ/BTclosureanchors/e.symm/Ecanonical instantiate these functions; thisgenericexactidentity alone doesnotclaimmean0 forarbitraryy.

```lean
theorem iid_parabola_finite_grid_weighted_reconstruction
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) (hn : 1 ≤ n)
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
       Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    0 < C ∧ ∃ K : Finset (ℤ × ℤ),
      (∀ k : ℤ × ℤ, k ∈ K ↔ (cell k).Nonempty) ∧
      (K.card : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
      P.real (M ⁻¹' V) = ∑ k ∈ K, P.real (M ⁻¹' cell k) ∧
      ∀ theta : (ℤ × ℤ) → (ℝ × ℝ),
        (∀ k ∈ K, theta k ∈
          Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) →
      ∀ (y : (ℤ × ℤ) → (ℝ × ℝ))
        (E : (ℤ × ℤ) → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))),
      let logZ : (ℤ × ℤ) → ℝ := fun k => Real.log
        (∫ x : ℝ, Real.exp ((theta k).1 * x + (theta k).2 * x ^ 2) ∂mu)
      let Q : (ℤ × ℤ) → Measure (Shao.Path n) := fun k =>
        Measure.pi (fun _ : Fin n =>
          mu.tilted (fun x => (theta k).1 * x + (theta k).2 * x ^ 2))
      let F : (ℤ × ℤ) → (ℝ × ℝ) → (ℝ × ℝ) := fun k w =>
        Real.sqrt (n : ℝ) • E k (w - y k)
      let T : (ℤ × ℤ) → Shao.Path n → (ℝ × ℝ) := fun k z => F k (M z)
      let laws : (ℤ × ℤ) → Measure (ℝ × ℝ) := fun k => (Q k).map (T k)
      let B : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k => F k '' cell k
      let g : (ℤ × ℤ) → (ℝ × ℝ) → ℝ := fun k v =>
        Real.exp (-Real.sqrt (n : ℝ) *
          ((theta k).1 * ((E k).symm v).1 + (theta k).2 * ((E k).symm v).2))
      (∀ k ∈ K, MeasurableSet (B k) ∧ Integrable (g k) (laws k)) ∧
      P.real (M ⁻¹' V) =
        ∑ k ∈ K, Real.exp (-(n : ℝ) *
          ((theta k).1 * (y k).1 + (theta k).2 * (y k).2 - logZ k)) *
          ∫ v : ℝ × ℝ in B k, g k v ∂laws k
```

AllV/cell/C/P/M/logZ/Q/F/T/laws/B/gvalues literalactualobjects; B=Fimagecell, law=actualtiltedIIDproductpushforward, samegexactAO. Integrability/measurability are CONCLUSIONS. C>0 andKexactactive/card bound beforetheta/y/E, so indexset andboundindependentthosechoices. n>=1 explicit; rho>=0; level0allowedgeometrytotaldivision, physicalconsumersretainlevel>0. HalfopenIocindicesincludeallreal/gridline/negativepoints throughpriorBK/BJ, noatomdiscarded. Emptyactivefamilyorcellsgenericcovered.

Qualifiedimmutable: BM ParabolaGridCardinality e6e771e3a7f746cf36b94c623bd77f52887c2599c7820d2e480e71451dc13c42 report52cdbdc8bc14545bcdb2ce3306027b4b88b889c02d14041014f8b4c11b3ee7f7 all93source6actualincl4gen CORRECT full147lineparentread. BK ParabolaFiniteGridCover b9303194ada7248223e0b98947d71db21a66117c0ee07cba563e31c2d8b87178 report00ea72556d773f38448f49c169f2c8c20251a4c08d7b796ba91b8eaa99871a99 all112source3actual CORRECT full135parentread. Completeconsumedactualtypesforactivefinitecardinality/exactfinitecover/Vcompact plusallV/cell/K/Cvaluesread. AOsourcececdbf313e675681bf62060134fe562b29e2f297cd35680ecd6c06f3496d01e1 reportcfc9387484993a86e29be3f9d5436c565b37eb59fdb23a5e1a3da35839ccc31a all117source10actualincl9gen CORRECT; completepublictype+allf,K,P,Q,M,F,T,rho,B,gvaluesread. Rootv57sourcebindings andactualserverhashesverifybeforefirstcheck; oldproofs/checksreuse withoutwholeoldproofreread/replay.

PrimarypinnedAPI intake: MeasureTheory/Measure/Real.lean290 measureReal_biUnion_finset (restrictedPairwiseDisjoint,measurableeach,finiteeach defaultfromactualPprob) ->exactrealsum; Data/Set/Card.lean655 Set.ncard_eq_toFinset_card (s)(hfinite) ->exactactivecount; allfunctionsactualmeasurablefiniteM/square/sum. Subsets/union/preimage equalities provedexplicitly.

OnlydesignatedserverCPU14–17/native-M8192-j4/autoImplicitfalse/oneheavy, solechildlease1 freshNONAUTHOR allNEWsource/fulltypes/ALLvalues/allactualownergen/recursiveAXstd3. No math-ultra/newsidebar/crossmessages/localLean/cache/package/sharedwrite/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Preserveoriginalfailures/warnings/exactfirstPASS; no passedgate replay/cosmeticedit. Activefeat/oq3-weighted-grid-reconstruction HEADfd718003cddb5ac4458073966048c4a5bc7e25e1 PR217frozenrootintake, no lane merge/rebase.

A partial finiteidentity is NOT originalB/D theorem. ActualexternalSongEdgeworthformalproof, weightedquantitativecomparison/cellsumerror, commonratefloor onSAMEwindow, exterior andoriginalB/D remainOPEN. CorrectedfixedlawA/boundedC,p54andSong/Angst-Polyattribution/strictthreshold unchanged. Intake note u22-bw-reconstruction-intake.md records commonfloorobstacle andcandidateexplicitshrink route; notnewpremisesorprovenresult.
