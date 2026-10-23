# OQ3 unit179 CT — SAME actual Fin2 affine law and raw iid characteristic power
Exact ONE COMPLETE declaration and ALL7statementletvalues frozen BEFORE implementation. Module Shao.OQ3.ParabolaFin2IIDCharacteristic. Imports Shao.OQ3.NormalizedIIDPairCharacteristic, Mathlib.Data.Matrix.Mul. Namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Matrix Topology BigOperators; noncomputable section. ONEpublictheorem ZEROdefinitions.

Anyactualscalarprobabilitynu, n>=1, literalA/b and paircontinuousLinearEquivE withexplicitpointwiseidentity onSAMEcenteredparabolastatistic ->actualFin2maplaw probability, actualrawscalar iidQmapT probability, EXACTactualsampleCF=actualFin2Phi(xi/sqrtn,eta/sqrtn)^n. DerivesgenuineFin2Ycontinuity/measurability/mapintegralidentity andusesCDactualiidpower/BVactualrawiidprobability. No assumeddesiredlaw/CFpoweridentity, moments/gap/CFerror orEuclidean/Prodnormsubstitution. hpoint is honestexactcoordinateactionalreadyPROVEDbycanonicalBU/CPproducer; thisauxiliaryhasarbitraryb anddoesNOTclaimmean0/covI. Intendedreusablebridge forSAMEcanonicalfamilylocalGaussian/middle/far consumers, preventingduplicatedmapcoherenceproofs and independentEchoicecomparisons.

CDsource22120e1075826e4a26411834c4aff8e645dbff2a59b4ed539d5067e0080ac6ca qualifiedfullreport9adffbf22ebf3fa1e2b6fe0dacfb1a2d9ff670716f6c16cd502d44452a503eeb123linesFULLpreviousparentread; FULLconsumediid_parabola_standardized_characteristic_factor includingALLactualY/Q/M/T/rho/Phi andallparameters read. BVsource3c44e20c9003e0b743829a5ad46ee56f12f72c9cc8fbaa6bea61c5cbb3c526b7 qualifiedjointreport0ede4b14deb562e06696b2ac0c56d63b430f41c48b21063626a4870e69090c56108linesFULLpreviousparentread; FULLconsumed iid_parabola_affine_standardized_law includingALLY/law/Q/QY/M/T/S read. Exactv61library/map/currentserver/originalproducerbindingbeforekernel, reusequalifiedoldproof/checks notentireoldproof/reports. PR2289c8680b4/treed0a6f95c exact63files frozenrootintake; newCQqualified/CRreviewACTIVE/CSauthorPASS separatecontinuation. Rootv61receipt915bdc06 actualchecked78a8cfa7/treeea2f84f8 distinctnoticeaf94328d/fc7b79eb/tree10144eb4. OriginalB-D/actualcanonicaluniformGaussian/rawiidGaussian/Edgeworth/derivatives/integrals/weightederror/exterior/newrhoLaplace OPEN; correctedA/boundedC/p54/strictrootbeta/attributionunchanged. Nooldgate/sharedwrite.

```lean
theorem iid_parabola_fin2_characteristic_factor
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hpoint : ∀ x : ℝ, E ((x, x ^ 2) - (b 0, b 1)) =
      ((A *ᵥ (![x, x ^ 2] - b)) 0, (A *ᵥ (![x, x ^ 2] - b)) 1))
    (xi eta : ℝ) :
    let Y : ℝ → (Fin 2 → ℝ) := fun x => A *ᵥ (![x, x ^ 2] - b)
    let law : Measure (Fin 2 → ℝ) := nu.map Y
    let Phi : ℝ → ℝ → ℂ := fun u v =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let T : Shao.Path n → (ℝ × ℝ) := fun z =>
      Real.sqrt (n : ℝ) • E (M z - (b 0, b 1))
    let rho : Measure (ℝ × ℝ) := Q.map T
    IsProbabilityMeasure law ∧ IsProbabilityMeasure rho ∧
      (∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
          (Phi (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ))) ^ n
```
