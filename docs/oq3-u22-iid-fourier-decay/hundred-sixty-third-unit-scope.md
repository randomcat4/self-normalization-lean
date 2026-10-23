# OQ3 unit163 CD — actual normalized iid pair Fourier factor and weak-Cramer exponential bound
Exact complete declarations and ALL statement let values frozen BEFORE implementation. Module Shao.OQ3.NormalizedIIDPairCharacteristic. Imports ONLY Shao.OQ3.ParabolaIIDStandardizedLaw, Shao.Probability.QuadraticCharacteristic, Mathlib.MeasureTheory.Integral.Pi, Mathlib.Analysis.SpecialFunctions.Pow.Real. Namespace Shao.OQ3; open MeasureTheory ProbabilityTheory; scoped Topology BigOperators; noncomputable section. THREE public theorems zero definitions.

Actual source next dependency: the finite iid Fourier engine before quantitative Edgeworth. No charFun API requiring an InnerProductSpace on ordinary MAXnorm realpair is silently used. Use literal realpair linear-frequency integral with unit complex exponential; positive n and exact inverse sqrt normalization. First actual ANYprobability pairlaw normalizedsum Fourierintegral equals its one-observation Fourierintegral at frequency/sqrt n, raised to n. Second binds qualified BV actual rawparabola iid standardizedpushforward with SAME arbitrary y/E and actual oneobservation Y. No mean0/covI assertion for arbitraryy/E. Third derives actual normalizedsum exponentialfar-frequency damping from the genuine oneobservation Euclidean-frequency weak-Cramer bound, not from a desired normalizedsum/probabilitycomparison premise. Exactscaled-frequency condition remains explicit; later rewriting into the asymptotic n^(1+beta/2)*|t|^-beta form is not silently assumed. Strict beta<2/5 is required later by the root truncation/smoothing estimate, not by this elementary auxiliary bound; rootcondition stays unchanged.

```lean
theorem normalized_iid_pair_characteristic_factor
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (xi eta : ℝ) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    let Phi : ℝ → ℝ → ℂ := fun u v =>
      ∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law
    (∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
        (Phi (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ))) ^ n

theorem iid_parabola_standardized_characteristic_factor
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 1 ≤ n)
    (y : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (xi eta : ℝ) :
    let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x ^ 2) - y)
    let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
    let M : Shao.Path n → (ℝ × ℝ) := fun z =>
      ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
    let T : Shao.Path n → (ℝ × ℝ) := fun z =>
      Real.sqrt (n : ℝ) • E (M z - y)
    let rho : Measure (ℝ × ℝ) := Q.map T
    let Phi : ℝ → ℝ → ℂ := fun u v =>
      ∫ x : ℝ, Complex.exp (((u * (Y x).1 + v * (Y x).2 : ℝ) : ℂ) * Complex.I) ∂nu
    (∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) =
        (Phi (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ))) ^ n

theorem normalized_iid_pair_weak_cramer_exponential_bound
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (n : ℕ) (hn : 1 ≤ n) (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (xi eta : ℝ)
    (hfreq : R < Real.sqrt
      ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) :
    let Q : Measure (Fin n → (ℝ × ℝ)) := Measure.pi (fun _ : Fin n => law)
    let S : (Fin n → (ℝ × ℝ)) → (ℝ × ℝ) := fun z =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, z i
    let rho : Measure (ℝ × ℝ) := Q.map S
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
        Real.exp (-(n : ℝ) * c * Real.rpow (Real.sqrt
          ((xi / Real.sqrt (n : ℝ)) ^ 2 + (eta / Real.sqrt (n : ℝ)) ^ 2)) (-beta))
```

ALL values Q/S/rho/Phi forfirst, Y/Q/M/T/rho/Phi forsecond, Q/S/rho forthird appear in full above. The generic pairlaw is actual samplinglaw (not necessarily possessing density), iid productQ and its genuine mapS. No moment, atomlessness or integrability premise is imposed for bounded unit-modulus Fourierkernels. The underlying complex integrals are genuinely integrable under probability/finite laws by norm1. The actualparabolaadapter uses BV's exact rho equality and probability of its actual oneobservationlaw; mapping its Fourierkernel back through Y identifies Phi exactly. No centerphase or transposed frequency is discarded.

Primary API exploration is currently ACTIVE in solefresh child oq3_u22cd_cf_api_intake, reportonly; no implementationwrittenyet. Its role is proofAPI resolution, not final review; eventual final reviewer must be a DIFFERENT fresh NONAUTHOR context. Candidate proof: integral_map under actual probability; exp of finite sum factors; exact product integration under pi; normpower and genuine hWC at exact scaled frequency; 1-a<=exp(-a) and nonnegative bases yield exp(-n*a). The bound does not depend on a fictitious independent law or on actualEdgeworth asanaxiom.

Qualified BV source3c44e20c9003e0b743829a5ad46ee56f12f72c9cc8fbaa6bea61c5cbb3c526b7 reportu22bubv-proof-review.md SHA0ede4b14deb562e06696b2ac0c56d63b430f41c48b21063626a4870e69090c56 complete238source4actual/fullvalues CORRECT108line, frozenPR217fd718003 parent preserved inPR221e730ce57. Complete consumed BV declaration/allY/law/Q/QY/M/T/S values read, oldproof/checks reused. SharedQuadraticCharacteristic acceptedrootv59 source8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5 exactrootmap/librarybinding; relevantrootiid_quadraticChar_factor completeinterface read, fulloldproof notreread. Pinnedmathlib807d3836b165983210ee2ecf3cd28f239436949c primaryAPI exactsource/serverbindingbeforekernel. New source/proofs/ALLactualtypes/ALLvalues/generatedowners need independent freshfullreview and recursiveAXstd3.

Current active feat/oq3-standardized-cell-comparison HEADe730ce575b5015cf5c86816427673bde6c7c362a tree721b570cdf8c99a29296881f69599ac37a36d09c; PR221 frozen publication/rootintake stackedonPR217. CC162 separateunpublished COMPLETEQUALIFIED source12cfbab4/79lines1actual full141line reportd65da3c83397fa1cc1f5175fef0839a8bae17677156f73a89b8c93313da86f53 parentread. Rootv59 receipt30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc checkedcode29c9804c552f0cc494355e6556c112aa3c36c908, mainb6bdf733/registryacceptedheadd9956f24 separate. No merge/rebase/oldcheckreplay.

ALLLean/heavyonlyserver CPU14–17/max1heavy/nativeM8192/j4/autoImplicitfalse; childlease1 noextra contexts. No localLean/cache/package/sharedwrite/math-ultra/newsidebar/crossmessages/sorry/admit/newaxiom/unsafe/native_decide/implemented_by/weakenedsettings. PreservefirstPASS exact and allfailures/warnings, no cosmeticedit/PASSreplay. All3complete exactdeclarations frozenbeforeproofimplementation; any necessary mathematicalrepresentationchange preservesv1 and freezesnewversionbeforeimplementation.

Original actualSongEdgeworth proof/quantitativeweightederror/exterior/newrhoLaplace andB-DOPEN. Sourcebound partialFourieridentity/zeroth-orderfarbound notrootproof. CorrectedA/boundedC/p54/strictthreshold/externalattribution preserved.
