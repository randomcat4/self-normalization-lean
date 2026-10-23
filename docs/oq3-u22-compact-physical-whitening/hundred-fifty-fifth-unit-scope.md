# OQ3 unit155 BV — actual iid standardized sample pushforward identity
Exactcomplete declarations/allstatementletvalues frozen BEFORE implementation. Module Shao.OQ3.ParabolaIIDStandardizedLaw, import Shao.OQ3.StandardizedCellChangeOfMeasure ONLY. Namespace Shao.OQ3; open MeasureTheory; scoped Matrix Topology BigOperators; noncomputable section. Two public theorems zero definitions.

Sourcebound bridge: repair01.md actual Z_{n,theta} is a normalized iid sum of the actual one-observation covariance-whitened centered parabola law; preexisting cellchangeofmeasure uses the SAME pushforward of actualtiltedproductQ by sqrt(n)E(M-y). Prove equality as actualmeasures, not a formal moment identity or assumed desired Edgeworth estimate. First applies toanyrealprobnu andANY y/E,n>=1 (does not assertzero-mean forarbitraryy); consumers instantiate actualtilt and its actualmean fromBQ. Second exactpair/Fin2lawbridge binds BU's actualY coordinates to the SAMEpairE andcenter; hpoint is literalBO-produced identity, not a desiredprobabilityconclusion.

```lean
theorem iid_parabola_affine_standardized_law
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
    let law : Measure (ℝ × ℝ) := nu.map Y
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let QY : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let T : Shao.Path n → (ℝ × ℝ) := fun z =>
      Real.sqrt (n : ℝ) • E (M z - y)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun v =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, v i
    IsProbabilityMeasure law ∧ IsProbabilityMeasure (Q.map T) ∧
      (∀ z : Shao.Path n, T z = S (fun i => Y (z i))) ∧
      Q.map T = QY.map S

theorem parabola_affine_law_eq_coordinate_map
    (nu : Measure ℝ) (y : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (Y : ℝ → (Fin 2 → ℝ)) (hY : Measurable Y)
    (hpoint : ∀ x : ℝ, E ((x, x ^ 2) - y) = (Y x 0, Y x 1)) :
    nu.map (fun x => E ((x, x ^ 2) - y)) =
      (nu.map Y).map (fun v : Fin 2 → ℝ => (v 0, v 1))
```

Firstproof exactfinitealgebra: sqrt(n)*(M-y)=sqrt(n)^{-1} sum_i((zi,zi²)-y), usingn>=1 andsqrt(n)^2=n. Continuouslinearity movesactualE throughscaling/sum. MeasurableY and actualnu probability givegenuineprobabilitylaw and iidproduct; primaryMeasure.pi_map_pi transportscoordinatewiseY. Measurablefinite normalizedsum S plusMeasure.map_map yieldactualQ.mapT=QY.mapS. Nocentering/integrability/weakCramer neededforequality, no atomlessness ornormalization change. Secondproof primarymap_map andexactpointwisehpoint, measurablecoordinateevaluation; anymeasureNu permitted. ALL pointwisenoprobabilityclaim beyond true maps/probability.

ConsumedpreexistingStandardizedCellChangeOfMeasure SHAcecdbf313e675681bf62060134fe562b29e2f297cd35680ecd6c06f3496d01e1 completefullpublicdeclaration/allf,K,P,Q,M,F,T,rho,B,gvaluesread, qualifiedreportbindingtoverifybeforeacceptance. Its oldproof/checks notneededmathematically; importonlyprovidesactualShao.Path/energy/product/mapinfrastructure alreadycanonical. PrimaryfixedMathlibMeasure.pi_map_pi (allcoordinateAEMeasurable andSigmaFinitepushforwardlaws), Measure.map_map andmapprobabilityifffullinterfacesinspectbeforefirstcheck; no oldqualifiedwholeproofreread/gatereplay. Shao.Path/energyactualdefinitions consumedmustcheckexactvalues.

OnlydesignatedserverCPU14–17/native-M8192-j4/autoImplicitfalse/oneheavy sharedlane, solechildlease1. CurrentBSBTreviewactive; BU/BVfreshfullreviewsqueue. CompleteallNEWsource/proofs/fullactualtypes/ALLvalues/allactualownergen/recursiveAXstd3 whitelist independentNONAUTHOR required. No math-ultra/newsidebar/crossmessages/localLean/cache/package/sharedwrite/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. Preservefailure/warnings/exactfirstPASS, no passedcheckreplay. Activebranchfeat/oq3-covariance-cell-family parent0b64fc rootv57mergedPR210ancestor; no merge/rebase. Actual externalSongEdgeworthproof/weightedreconstruction/cellsum/exterior/originalB-D remainOPEN, fixedlawA/boundedC/p54/externalattribution retained.
