# OQ3 unit158 BY — actual true-global-rate floor on explicit shrunk physical window
Exactcomplete declarations/ALLstatementletvalues frozen BEFOREimplementation. Module Shao.OQ3.PhysicalWindowRateFloor; import Shao.OQ3.OpenDomainBoundaryLowerBound ONLY. Namespace Shao.OQ3; open MeasureTheory; scoped Matrix Topology; noncomputable section. Two publictheorems zero definitions.

Sourcecritical gap from u22-bw-reconstruction-intake.md: finitecount andcellwiseanchor minima alone doNOT implycommonexponentialratefloor. Bridge actualqualifiedboundaryphasegrowth andlocalTRUEglobalERealrateidentity to an EXPLICITLYSHRUNK physicalwindow. cap>0 is theoriginalwindowradius; outputeta>0<=cap and<=delta explicitly, never silentlyassertflooronunchangedoldwindow. First obtainsfiniteactualI=F at everynewphysicalpoint andI(center)<=I(w); second transfersittoexistingrealanalyticJ whenactualtrueI=J onoriginalcapwindow. Lateractualproducer must bind SAMEsourcephaseLambda viauniqueactualLrow and preserve/rebuildshrunkenTheta/anchors/Gaussian/Laplace facts; notclaimedhere.

```lean
theorem actual_parabola_rate_floor_of_boundary_lower_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (level a0 cap delta c : ℝ)
    (hcap : 0 < cap) (hdelta : 0 < delta) (hc : 0 < c)
    (F : (ℝ × ℝ) → ℝ)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
        (a0 + u.1, (a0 + u.1) ^ 2 / level ^ 2 - u.2) = (F u : EReal))
    (hgrowth : ∀ r z : ℝ, |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0)) :
    let I : (ℝ × ℝ) → EReal :=
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
    let V : ℝ → Set (ℝ × ℝ) := fun eta =>
      {w | |w.1 - a0| ≤ eta ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ eta}
    I (a0, a0 ^ 2 / level ^ 2) = (F (0, 0) : EReal) ∧
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ cap ∧ eta ≤ delta ∧ ∀ w ∈ V eta,
        I w = (F (w.1 - a0, w.1 ^ 2 / level ^ 2 - w.2) : EReal) ∧
        I (a0, a0 ^ 2 / level ^ 2) ≤ I w

theorem actual_parabola_analytic_rate_floor_of_boundary_lower_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (level a0 cap delta c : ℝ)
    (hcap : 0 < cap) (hdelta : 0 < delta) (hc : 0 < c)
    (F : (ℝ × ℝ) → ℝ)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2))
        (a0 + u.1, (a0 + u.1) ^ 2 / level ^ 2 - u.2) = (F u : EReal))
    (hgrowth : ∀ r z : ℝ, |r| ≤ delta → 0 ≤ z → z ≤ delta →
      c * (z + r ^ 2) ≤ F (r, z) - F (0, 0))
    (J : (ℝ × ℝ) → ℝ)
    (hJ : ∀ w : ℝ × ℝ,
      |w.1 - a0| ≤ cap ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ cap →
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w =
        (J w : EReal)) :
    let V : ℝ → Set (ℝ × ℝ) := fun eta =>
      {w | |w.1 - a0| ≤ eta ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ eta}
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ cap ∧ eta ≤ delta ∧
      ∀ w ∈ V eta, J (a0, a0 ^ 2 / level ^ 2) ≤ J w
```

F is passed with actualtrueLegendreidentityheq and genuinelyprovedpositivec normal/tangential lowerboundhgrowth, exactlyexistingT outputs underretainedLambda1>0. No desiredratefloor/probabilityasymptotic premise. V eta isliteralclosedphysicalwindow. ActualI definition isfixedglobalbivariateLegendreRate ofmu/parabola; noarbitraryproxyI. Proofchooseepsilonballfromheq, eta=mincap(mindelta(epsilon/2)), positive. Defaultpairmaxdistance bound on(r,z) fromliteral|r|<=eta,0<=z<=eta ensuresstrictballmembership; G(r,z)=w exactalgebra. Atcenterheq yieldsIcenter=F0. c(z+r²)>=0 givesF0<=Fcoords; finiteERealcoercionorder givesactualfloor. SecondsubsetVeta⊆Vcap, includesactualcenterinVcap; bothactualI=Jidentities transferfloorbyEReal.coe_le_coe_iff. No divisionbysmallunknown orcompactminshortcut. level0purealgebratotaldivisionallowed; physicalconsumersretainpositivelevel.

OldqualifiedT OpenDomainBoundaryLowerBound source426d3b0713595bea5fbb4205b550f2e20e6a7f9f4aea1c555bd847cdb060dcc4, reportu22st-proof-review.md SHA9dd3afba4c9d742aea2c2772c014a679c7caa022179e2df3c50ff27ec006b205 CORRECT all105source/publicproof/actualtypes/values. CompleteconsumedTpublicinterface/allOmega/nu/means/K/D/pr/row/B/J/G/F/v/Lambda1valuesread previously; its fullproofs/checksreused notreread/replayed. Thismodule doesNOTinvokeTproducerproof orselecta differentchart; accepts itsactualheq/hgrowthvalues asinputs to a reusablebridge. BL/BQsourcepointpatch can supplyhJ oncap; exactT/JchartrelationshipandconditionalactualLambda binding remain fornextproducer. Actualserver/rootv58sourcehashbindingbeforefirstkernelcheck pending.

Primarypinnedserverinterfacesread: Metric.eventually_nhds_iff (Topology/MetricSpace/Pseudo/Defs.lean781) givesepsilon>0 and∀implicitpoint dist<epsilon->predicate; EReal.coe_le_coe_iff (Data/EReal/Basic.lean55) iffrealorder. No oldmodulebuild/reviewreplay.

OnlyserverCPU14–17/native-M8192-j4/autoImplicitfalse/oneheavy; solechildlease1 currentlyBX157freshreviewactive, BYfreshNONAUTHORcompleteALLNEWsource/fulltypes/ALLvalues/allactualowngen/recursiveAXstd3 reviewafteritstops. No math-ultra/newsidebar/crossmessages/localLean/cache/package/sharedwrite/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Preservefailures/warnings/exactfirstPASS no cosmeticPASSedits/checkreplay. Activefeat/oq3-weighted-grid-reconstruction parentPR217fd718003 rootintake no merge/rebase. Rootv58maincae262e8 receipt253f5cce checkedcode88ae3c04, no acceptedheadinvented.

Partialratefloor/helper NOTroot. Fullsamephysicalproducerwithnewradius, weightedquantitativeerror, actualSongEdgeworthformalproof, exterior andoriginalB-DOPEN; correctedfixedlawA/boundedC,p54/strictthreshold/externalattribution unchanged.
