# OQ3 unit178 CS — uniform actual isotropic-law local Gaussian bound
Exact ONE COMPLETE declaration frozen BEFORE implementation. Module Shao.OQ3.UniformPairCharacteristicLocalGaussian. Import Shao.OQ3.PairCharacteristicQuadraticRemainder. Namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Topology BigOperators; noncomputable section. ONEpublictheorem ZEROdefinitions ZEROstatementletvalues.

ANYactualFin2probabilityfamily onANYindexsubsetK, coordinateGENUINEMemLp2/actualzero means/covI andonepositiveuniformGENUINEthirdradialmomentbound ->existsONEdelta>0 delta<=1 BEFOREALLp/freq withliteralEuclideanradius<=delta, ACTUALone-observationCFnorm<=exp(-(u²+v²)/4), frequency0included. No continuity/compactness/weakCramer/gap/desiredCFerror hypothesis; noexponentialmoment/atoms/density/boundedsupport. Uniformthirdmoment inputisactualcommonfiniteexpectationand genuineIntegrability, exactlysuppliedlaterbyBU/CPnatural3momentpacket; notnewrootassumption. DeriveactualCFquadraticerrorviaCR, chooseexplicitmin1(1/(4KC)), quadraticapproxnonnegative, normtriangle andCradius³<=radius²/4, then1-radius²/4<=exp(-radius²/4). No independentEchoices or innerproductonordinaryProd. No actualnormalizedsampleGaussian/canonicalfamilyconsumerclaimedhere.

CR177exact85628bd4208dc5753439183d21a8f10ed27c07398e0c7cadb1a902147f1febe9 all138source2actualfirstkernel03/ownerAXPASS freshfullreviewACTIVEatfreeze; qualifybeforeCSacceptance. FULLconsumedCR2interface allGENUINEL2/mean/covI/Integrablethirdmoment/ALLu,v/actualradialM3 read. Exactsource/originalproducerbindingbeforekernel. CQ176alreadyqualifiedfullreport070dafbf. PR2289c8680b4/treed0a6f95c63files7CJ–CPunits frozenrootintake, continuationlowfreq; rootv61receipt915bdc06 actualchecked78a8cfa7/treeea2f84f8 distinctnoticeaf94328d/fc7b79eb/tree10144eb4. No oldgate/sharedwrite. Actualcanonicalcompacttrue-domainproducer/normalizediidGaussian bound/Edgeworth/derivatives/Fourierintegrals/weightederror/exterior/newrhoLaplace/originalB-DOPEN; correctedA/boundedC/p54/strictrootbeta/attributionunchanged.

```lean
theorem uniform_isotropic_pair_characteristic_local_gaussian_bound
    {ι : Type*} (K : Set ι) (laws : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ p ∈ K, IsProbabilityMeasure (laws p))
    (hL2 : ∀ p ∈ K, ∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (laws p))
    (hmean : ∀ p ∈ K, ∀ i : Fin 2, (∫ y : Fin 2 → ℝ, y i ∂laws p) = 0)
    (hcov : ∀ p ∈ K, ∀ i j : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
        if i = j then 1 else 0)
    (hthird : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K,
      Integrable (fun y : Fin 2 → ℝ =>
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3) (laws p) ∧
      (∫ y : Fin 2 → ℝ,
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂laws p) ≤ C) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ p ∈ K, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
        ‖(∫ y : Fin 2 → ℝ,
          Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂laws p)‖ ≤
            Real.exp (-(u ^ 2 + v ^ 2) / 4)
```
