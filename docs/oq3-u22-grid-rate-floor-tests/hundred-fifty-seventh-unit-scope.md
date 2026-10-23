# OQ3 unit157 BX — same inverse-chart rate anchors and exact weighted grid reconstruction
Exactcomplete declaration/allstatementletvalues frozen BEFOREimplementation. Module Shao.OQ3.PhysicalGridRateAnchorReconstruction; imports Shao.OQ3.PhysicalGridWeightedReconstruction and Shao.OQ3.PhysicalWindowCellRateAnchors ONLY. Namespace Shao.OQ3; open MeasureTheory; scoped Matrix Topology BigOperators; noncomputable section. One public theorem zero definitions.

Sourcebound adapter: BW156 genericexactfiniteweightedprobabilityidentity nowinstantiated by sourceclosure-minimizinganchors in SAMEliteralphysicalV and SAMEgiveninversechart e, plus SAMEgiven E family overTheta=e.symm imageV. Its inputsdomain/anchorbundle are reduced EXISTING BQ/BT conclusions, not desiredprobabilityreconstruction. No suppliedcellcount/reconstruction/desiredratefloor/Edgeworth/Gaussiancomparison premise. e is passed bycaller, not reselected; E canonicalwhenexistingBTsamefamily isused. Thisadapterdoesnotitselfassertarbitrarilygiven e equalsactualmeans or arbitraryE whitens; existingBQ/BTprovide those additionalfacts, retainedseparately.

```lean
theorem physical_grid_rate_anchor_weighted_reconstruction
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) (hn : 1 ≤ n)
    (level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) :
    let V : Set (ℝ × ℝ) := {w | |w.1 - a0| ≤ rho ∧
      0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let Theta : Set (ℝ × ℝ) := e.symm '' V
    let Klog : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
    let J : (ℝ × ℝ) → ℝ := fun w =>
      (e.symm w).1 * w.1 + (e.symm w).2 * w.2 - Klog (e.symm w)
    let I : (ℝ × ℝ) → EReal :=
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
    (∀ w ∈ V, e.symm w ∈
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) →
    (∀ aL aR qL qR : ℝ,
      let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩ V
      let Q : Set (ℝ × ℝ) := Set.Icc aL aR ×ˢ Set.Icc qL qR
      A.Nonempty → ∃ y ∈ closure A, y ∈ Q ∩ V ∧ I y = (J y : EReal) ∧
        ∀ w ∈ closure A, I y ≤ I w ∧ J y ≤ J w) →
    ∀ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
    let cell : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      (Set.Ioc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
       Set.Ioc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))) ∩ V
    let rect : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k =>
      Set.Icc ((k.1 : ℝ) / (n : ℝ)) (((k.1 : ℝ) + 1) / (n : ℝ)) ×ˢ
      Set.Icc ((k.2 : ℝ) / (n : ℝ)) (((k.2 : ℝ) + 1) / (n : ℝ))
    let C : ℝ := (2 * rho + 2) * ((|a0| + rho) ^ 2 / level ^ 2 + rho + 2)
    let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    0 < C ∧ ∃ K : Finset (ℤ × ℤ),
      (∀ k : ℤ × ℤ, k ∈ K ↔ (cell k).Nonempty) ∧
      (K.card : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
      ∃ y : (ℤ × ℤ) → (ℝ × ℝ),
        (∀ k ∈ K, y k ∈ closure (cell k) ∧ y k ∈ rect k ∩ V ∧
          I (y k) = (J (y k) : EReal) ∧
          ∀ w ∈ closure (cell k), I (y k) ≤ I w ∧ J (y k) ≤ J w) ∧
        let tau : (ℤ × ℤ) → (ℝ × ℝ) := fun k => e.symm (y k)
        ∃ Ec : (ℤ × ℤ) → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
          (∀ k ∈ K, tau k ∈ Theta ∧
            tau k ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) ∧
            ∀ htau : tau k ∈ Theta, Ec k = E ⟨tau k, htau⟩) ∧
          let Q : (ℤ × ℤ) → Measure (Shao.Path n) := fun k =>
            Measure.pi (fun _ : Fin n =>
              mu.tilted (fun x => (tau k).1 * x + (tau k).2 * x ^ 2))
          let F : (ℤ × ℤ) → (ℝ × ℝ) → (ℝ × ℝ) := fun k w =>
            Real.sqrt (n : ℝ) • Ec k (w - y k)
          let T : (ℤ × ℤ) → Shao.Path n → (ℝ × ℝ) := fun k z => F k (M z)
          let laws : (ℤ × ℤ) → Measure (ℝ × ℝ) := fun k => (Q k).map (T k)
          let B : (ℤ × ℤ) → Set (ℝ × ℝ) := fun k => F k '' cell k
          let g : (ℤ × ℤ) → (ℝ × ℝ) → ℝ := fun k v =>
            Real.exp (-Real.sqrt (n : ℝ) *
              ((tau k).1 * ((Ec k).symm v).1 + (tau k).2 * ((Ec k).symm v).2))
          (∀ k ∈ K, MeasurableSet (B k) ∧ Integrable (g k) (laws k)) ∧
          P.real (M ⁻¹' V) = ∑ k ∈ K, Real.exp (-(n : ℝ) * J (y k)) *
            ∫ v : ℝ × ℝ in B k, g k v ∂laws k
```

AllV/Theta/Klog/J/I/cell/rect/C/P/M/tau/Q/F/T/laws/B/g literalactualobjects. Produce finiteACTIVEsameK/card<=Cn² viaBW, choose y atclosurecell∩originalCLOSEDrectangle∩V withactualfiniteglobalERealI=J andBOTH minima overENTIREclosure. Settau=e.symm(y) exactly; actualTheta/domain membershipproved onactiveK. ExtendprovideddependentE toallintegerindices via identityoutsideactive/Theta; onactiveK Ec is EXACT E atactualtau forEVERYmembershipproof (proofirrelevance, no alternatewhitener). ApplyBWsameK/alltheta/y/Ecpayload and rewriteexactreal exponenttoJ(y). MeasurableB/truegIntegrableunderactualtiltedproductpushforward remainoutputs. Noassumedanchorinhalfopencell, no boundaryatomsdiscarded. Arbitrary inactivey/E values outsideK irrelevant.

DependencyBW sourcea151ebbf369d42b63402603413735335ef0afea30d83da8c9207e5bca38dff48 130lines1public4actualincl3generated firstkernel/AXPASS, independentfreshcompletefullreviewACTIVE; mustqualifybeforeBXacceptance. CompleteBWactualtype/allvaluesnowread. QualifiedBL source dcc7e3c5d2b881403791abfe37c952b08eee3eda071f1818382c33cd33051b09 report9817b85d0c069cbf595409b4c2be3abaf1a3523d1cf2888c5b97f880b44e3c7d full141source1actual/allvaluesCORRECT full114parentread; fullpublictype/allvalues previouslyconsumed, itsstrongerbundle exactlysuppliesrequiredreducedanchor/domainfields. BL importedforactualchart/rateinfrastructure; no oldproofinvocation/replay. StrongerBQ/BT samephysicalTheta/Ecanonicalfacts independentqualifiedPR217, no wholeoldproofreread/checkreplay.

OnlydesignatedserverCPU14–17/native-M8192-j4/autoImplicitfalse/oneheavy, solechildlease1. BWfreshreviewactive; BXreviewfreshNONAUTHORafterBWstopped. AllNEWsource/proofs/fullactualtypes/ALLvalues/allactualownergen/recursiveAXstd3 mandatory. No math-ultra/newsidebar/crossmessages/localLean/cache/package/sharedwrite/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Preservefirstfailures/warnings/exactfirstPASS, nopassedgate replay/cosmeticedits. Activefeat/oq3-weighted-grid-reconstruction parentPR217fd718003cddb5ac4458073966048c4a5bc7e25e1; frozenrootintake no lane merge/rebase.

Rootv58 maincae262e8330f9d96ce77cf67af821f454d451773 receipt253f5cce5c2503ded6a632585e4a93184b7284ea89fdc25d9a6ec65470e96025 checkedcode88ae3c04be8f09ce57ec6d5334fb33b2632d2f3d; acceptedheadnotprovided. Partialfiniteidentity NOTroot. ActualsampleEdgeworth/externalSongformalproof/quantitativeweightederror/commonrateflooronSAMEwindow/exterior/originalB-D OPEN. CorrectedA/boundedC,p54/strictthreshold/externalattributionunchanged.
