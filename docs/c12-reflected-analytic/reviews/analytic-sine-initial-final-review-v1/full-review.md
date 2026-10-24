# Independent complete final review: C12 units139–141

**STATUS: CORRECT.** No critical gaps or uncovered owners within the exact frozen declarations.

The positive-time actual Brownian bridge/image interface is proved in141. Units139–140 establish the analytic preparation without assuming that interface. Original C1/C2 roots and unconditional hSmall remain OPEN; no root closure follows solely from this identification.

The reviewer is fresh and independent, configured gpt-6.1-sol/xhigh. Only this review directory is writable. The parent authorized the one-time141 extension after an actual unsealed runtime ACK. No author proof advice, child contexts, Lean commands, audit replays, remote changes, cache writes or source/freeze/receipt edits occurred. OQ3 remains user-paused.

## Exact source and certificate bindings

| Unit | Module | Source SHA256 | Object SHA256 | Freeze SHA256 | Original receipt SHA256 |
|---|---|---|---|---|---|
| 139 | Shao.C2.IntervalImageInitialProfile | 02722eb67860f55cf91d8784698ac2a3dd2ded5cd7c831cf230b97da5c8ebccf | c0683e43dd490221c3936a117cb6c602224740daaeca9b84889aed9a59929fbe | 97ada59d815e0bf2bcb29ec98c3290e14087d54e9646c52501fc2c236539729d | e1a5a25781e418ab53e14028992d69550dba7602dc15db172c34596b72b8ada7 |
| 140 | Shao.C2.IntervalSineInitialLimit | 04812fab3ee3793d76a559168484e7e4afed80bee64fbac12ae2619eb9a18453 | 5f3ae2efc7993a35a81f9504ef8f2b86f62222f1293e0e5a658b00f08ead3a5b | abbea7728d1f0693b20428f46de7fd8599964bb60773634088ee14547417d792 | 4a1ae4cd39246b07717c97a265890ceb06bdaf440ef6c587995a6deef762ed68 |
| 141 | Shao.C2.BrownianKilledSineIdentification | 739fb2a8c6c0a1c21b53f85a80527d1f1fc0770abd7e6704875cb42b859d9105 | 9e1f3d0e5c0420f709822bf99c91f7d75230651ab8ec325d7cfb635b16fe985e | c612862bfb27bf08e6d68f9bf980346b1d2c1482d84cc2543b1d72293c7f769d | 342b65447f4128a0c03e69866919290dade0a573513d7607d49ccc589c0456f1 |

All local source bytes match the remote current source and successful attempt002 snapshot. Original output objects equal the installed objects. All receipt-listed artifacts, original remote receipts and declared dependency source hashes match. Full frozen import/context/head projection equals the frozen bytes for each module; freeze records state implementation had not begun. Final production sources are UTF-8 without BOM and contain no CR bytes. Forbidden proof tokens are absent.

Pinned Lean: leanprover/lean4:v4.36.0-rc1. Pinned mathlib:807d3836b165983210ee2ecf3cd28f239436949c. Package view:cache-overlays/shared-v34/packages. Observed branch author/c12-density-heat-v71, HEAD f877ced1a830945e65ba00251d28a240bc4a3c63. All original gates used the C12 single-heavy lock, CPU14–17, -M8192 -j4; the reviewer reused their evidence.

## Complete owner, type, proof and axiom coverage

Counts are derived from the verified owner maps:3modules,11actualowners,11theorems,7public source theorems,4private source theorems,0generated declarations,0global non-theorem values,0other kinds. Complete actual type exports total25,630bytes (4,103 +12,477 +9,050); all value exports are genuinely empty. Every complete elaborated type, including all binders, universes, instances, conjunctions, filters, measures and indicator expressions, was read and compared with its frozen statement.

The original audit selects owners by env.getModuleIdxFor?, independently of declaration spelling. It includes all private/generated declarations. The complete pinned Lean.collectAxioms implementation was read: checked declaration types and values are recursively traversed; imported cached results are transitive and computed against the private checked environment. Every one of the11owner lists is exactly propext, Classical.choice, Quot.sound. No hidden project axiom, sorryAx, unsafe proof or native_decide appears.

All final proofs, preserved failed001 sources, complete kernel logs for failed001/success002, and each complete audit log were read. Each original audit log is reconstructed byte-for-byte as its complete prefix, full type export and complete suffix; final-source-observation.json records the exact byte partition. Prefixes are the shared mathlib-local-changes warning; suffixes record the exact counts and AUDIT_EXIT=0. The successful141 log also retains the letI style-linter warning. Failed changes are only elaboration/unfolding/composition fixes: no head, assumption or global value changed. No original full log was copied into the workspace.

## Unit139: Shao.C2.IntervalImageInitialProfile

### intervalImageCandidate_small_time_bounded

```lean
theorem intervalImageCandidate_small_time_bounded (a z U x : ℝ)
    (ha : 0 < a) (hz : |z| ≤ a) (hU : 0 < U) (hx : |x| ≤ a) (hsmall : U ≤ a ^ 2) :
    |intervalImageCandidate a z U x| ≤ 17 := by
```

For |x|,|z|≤a, both products (a−x)(a−z) and (a+x)(a+z) are nonnegative. Dividing their negatives by U>0 gives nonpositive exponents, hence each wall profile is ≤1 and their sum P≤2. The exact qualified small-time estimate |I−1|≤8P applies with all closed-interval and U≤a² hypotheses supplied. The triangle inequality gives |I|≤|I−1|+1≤8·2+1=17. No nonnegativity or probabilistic interpretation of I is used.

Exact source line:11. Complete declaration SHA256:1d4e2b888bc9a0100e0ff771bfdef3d64df60788202dced405cd8a8cc37a76f1. Actual full type-expression SHA256:436d4203534eac022a0a3a94f6e360dd630d748b5b04c9f8a981402e693ab4cd. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### Private exp_neg_div_initial_limit

```lean
private theorem exp_neg_div_initial_limit (F : ℝ≥0 → ℝ) (c : ℝ) (hc : 0 < c)
    (hF : Tendsto F (𝓝 0) (𝓝 c)) :
    Tendsto (fun T : ℝ≥0 => Real.exp (-F T / (T : ℝ))) (𝓝[>] 0) (𝓝 0) := by
```

The exact NNReal right-neighborhood image under coercion is the real right-neighborhood of zero. Thus 1/T→+∞ on the punctured right filter. F→c>0 on the full neighborhood restricts to that filter; the pinned pos_mul_atTop theorem gives F(T)/T→+∞, without requiring F(T)>0 at every time. Composition with the pinned exp(−r) limit gives zero. Function composition, negation and division normalization preserve the literal frozen exponent −F(T)/T. The value at T=0 is excluded by the filter.

Exact source line:36. Complete declaration SHA256:e48f861db745a18471a93ea63507db615bae3d2668b8d6dbc1f0b27201aa98a6. Actual full type-expression SHA256:cd8fa85f397f55376822b20c2fa449c6c009612af2ea538d9e4131ca29adf82c. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### intervalImageCandidate_initial_diagonal

```lean
theorem intervalImageCandidate_initial_diagonal (a z w : ℝ)
    (ha : 0 < a) (hz : |z| < a) :
    Tendsto (fun T : ℝ≥0 => intervalImageCandidate a z (T : ℝ)
      (z + Real.sqrt (T : ℝ) * w)) (𝓝[>] 0) (𝓝 1) := by
```

For each fixed real w, x(T)=z+√T·w is continuous on NNReal and tends to z. Strict |z|<a gives a−z>0 and a+z>0, so the upper and lower numerator products tend respectively to (a−z)²>0 and (a+z)²>0. Applying the private limit lemma to each makes P(a,x(T),T,z)→0. Continuity and strict interiority give eventual |x(T)|<a; a>0 gives eventual T<a²; right-neighborhood membership gives T>0. The exact small-time profile bound therefore bounds |I−1| by 8P eventually, and the metric ε proof yields I→1. This is a pointwise-in-w limit, with no uniform-in-w or boundary-center claim.

Exact source line:47. Complete declaration SHA256:5b96c8b06c3c74d2f0c2e53878c10d94991ccde7b84c662582265041083c7813. Actual full type-expression SHA256:8dbceb678e1018c265fffffda802d01ac565bc3b426f4066c111ebb6fb208881. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

## Unit140: Shao.C2.IntervalSineInitialLimit

### Private normalizedSineCandidate_measurable

```lean
private theorem normalizedSineCandidate_measurable (a z U : ℝ) (ha : 0 < a) (hU : 0 < U) :
    Measurable (normalizedSineCandidate a z U) := by
```

The normalized candidate is literally reciprocalFreeDensity(z,U,x) times the raw sine series S(a,z,U,x). The qualified global spatial derivative of the reciprocal at U>0 implies continuity at every real x. The qualified sine spatial derivative at a>0,U>0 does the same for S. Their product is continuous and measurable. There is no interval restriction, arbitrary measurable placeholder, or assumed density identity.

Exact source line:13. Complete declaration SHA256:97c786872b4bd471bf3d13e9238917602284335e373dd8b6779aebafaddbca16. Actual full type-expression SHA256:9dd5099a9f377bcb465b1d6e437468f956f663817ab8106b9826fcc4b4ec718a. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### Private sine_gaussian_test_pointwise

```lean
private theorem sine_gaussian_test_pointwise (a z w : ℝ) (ha : 0 < a) (hz : |z| < a)
    (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun T : ℝ≥0 => (Icc (-a) a).indicator
      (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
      (z + Real.sqrt (T : ℝ) * w)) (𝓝[>] 0) (𝓝 (f z)) := by
```

The affine x(T)=z+√T·w tends to z for every fixed real w, and continuity of the arbitrary real test gives f(x(T))→f(z). Unit139 gives the numerical image candidate limit1. Their product tends to f(z). Strict center |z|<a ensures eventual interior x(T); T>0 also holds eventually. At those times the Icc indicator equals its payload and the qualified ANALYTIC image/normalized-sine equality applies with both endpoint inequalities. Eventual equality transfers the product limit to the frozen indicator expression. No actual Brownian/image identity is used here.

Exact source line:21. Complete declaration SHA256:5455e7ff5ad1776d26b529c5e6d9cfd7a332e86ca1b54ed2e09bfcdaac4a4324. Actual full type-expression SHA256:e0592d2087a798325e340ef6342c652b9bc06c0b2fc2aa2ffd462cdc4f0a6a14. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### sineSeries_action_standardGaussian

```lean
theorem sineSeries_action_standardGaussian (a z : ℝ) (ha : 0 < a) (hz : |z| ≤ a)
    (T : ℝ≥0) (hT : T ≠ 0) (hsmall : (T : ℝ) ≤ a ^ 2)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hbound : ∀ x : ℝ, |f x| ≤ M) :
    Integrable (fun x => mixedSineSeries 0 0 a z (T : ℝ) x * f x)
      (volume.restrict (Icc (-a) a)) ∧
    Integrable (fun w : ℝ => (Icc (-a) a).indicator
      (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
      (z + Real.sqrt (T : ℝ) * w)) (gaussianReal 0 1) ∧
    (∀ w : ℝ, |(Icc (-a) a).indicator
      (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
      (z + Real.sqrt (T : ℝ) * w)| ≤ 17 * M) ∧
    (∫ x in Icc (-a) a, mixedSineSeries 0 0 a z (T : ℝ) x * f x) =
      ∫ w : ℝ, (Icc (-a) a).indicator
        (fun x => normalizedSineCandidate a z (T : ℝ) x * f x)
        (z + Real.sqrt (T : ℝ) * w) ∂(gaussianReal 0 1) := by
```

T≠0 in NNReal gives real T>0. The global bound on f implies M≥0 by evaluating at0. The closed-interval indicator F of normalizedSineCandidate·f is measurable. On Icc, the analytic image/sine equality and unit139 give |normalized|≤17; off Icc the indicator is exactly0. Thus |F|≤17M everywhere. The raw sine series is continuous and globally bounded by C≥0 at this fixed positive time using qualified unit136; |S·f|≤CM gives genuine integrability under the finite restricted Lebesgue measure. Measurability of the affine Gaussian map and the bound17M give genuine integrability under gaussianReal(0,1). The qualified affine HasLaw sends z+√T·w to gaussianReal(z,T), and the pinned HasLaw.integral_comp transports F. Nonzero-variance Gaussian density integration uses exactly (√(2πT))⁻¹ exp(−(x−z)²/(2T)). Squared-distance symmetry and the exact reciprocal/free cancellation yield gaussianPDFReal·normalized=S, with no missing scale or Jacobian. Splitting the indicator inside/outside and the pinned integral_indicator identity returns exactly the Lebesgue Icc integral. All four returned conjunctions, including both integrability assertions and the pointwise bound, are checked.

Exact source line:46. Complete declaration SHA256:cae7cb4d35a211b313463dcdf2bc5fa133b427aa475e4aba21905eb7d08db63b. Actual full type-expression SHA256:8a7eed346f3725cc7724efa9bde326c97865239acb268f170ad51ffeed8a17a0. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### sineSeries_initial_limit

```lean
theorem sineSeries_initial_limit (a z : ℝ) (ha : 0 < a) (hz : |z| < a)
    (f : ℝ → ℝ) (hf : Continuous f) (hbound : ∃ M : ℝ, ∀ x : ℝ, |f x| ≤ M) :
    Tendsto (fun T : ℝ≥0 => ∫ x in Icc (-a) a,
      mixedSineSeries 0 0 a z (T : ℝ) x * f x) (𝓝[>] 0) (𝓝 (f z)) := by
```

Choose the stated global bound M for f. Eventually the right-neighborhood time is nonzero and ≤a². The preceding representation gives eventual AE strong measurability, the common pointwise norm bound17M, and exact equality with the Icc sine integral. The private pointwise lemma supplies the f(z) limit for every w and hence Gaussian-almost every w. The dominating constant17M is integrable under the fixed probability measure gaussianReal(0,1). The pinned countably-generated-filter dominated-convergence theorem applies to the NNReal right neighborhood, a filter on a metrizable first-countable space, and its limiting constant integral equals f(z) because the Gaussian mass is1. Eventual representation equality transfers this limit to the required analytic sine integral. No changing Gaussian measure is used in DCT, no exchange of an unjustified infinite series and integral occurs, and no default-zero nonintegrable integral proves the result.

Exact source line:120. Complete declaration SHA256:12256c74a54da742f33b2e725d57e5de9a3dda39e7ccf07f5821ce7ae1bee9ee. Actual full type-expression SHA256:26c7935275c9e058f2dcfb3adc5861d505414b9a74afa492a1d93ed3359b931d. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

## Unit141: Shao.C2.BrownianKilledSineIdentification

### Private killed_density_data

```lean
private theorem killed_density_data {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    Continuous (fun x : ℝ => gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x) ∧
    (∃ M : ℝ, ∀ x : ℝ, |gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x| ≤ M) ∧
    (∀ x : ℝ, 0 ≤ gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x) ∧
    ∀ x : ℝ, x ∉ Icc (-a) a → gaussianPDFReal y T x *
      intervalCompletion (bridgeLaw B P) a y (T : ℝ) x = 0 := by
```

Let ν be the literal bridgeLaw(B,P), which is a probability law by qualified Brownian measurability. Qualified unit124 gives actual joint continuity of Gaussian density times the actual strict bridge survival completion at positive T, independently of any image identity; composition with x↦(y,x) gives global continuity. The actual completion lies in[0,1] and the Gaussian PDF is nonnegative. Its exponential is ≤1 since the quadratic exponent is nonpositive, so the density is nonnegative and bounded by(√(2πT))⁻¹. If x is outside Icc(−a,a), either x≤−a or a≤x; qualified strictInterval_exterior makes the actual strict bridge event empty by its terminal endpoint. The completion and density are then literally0. This helper correctly allows arbitrary real a,y; it adds no unrecorded interior or width assumption.

Exact source line:14. Complete declaration SHA256:65256f981e9cff8b61369aca22ef9ef2e8f82fc2da2a5ff82d3a7e0b912c999b. Actual full type-expression SHA256:23ef9b195bec73cc05e771ae3553cf78a24474cfeb4ca5fc9fd259a1887e66e6. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### actualIntervalKernel_sine_action_density

```lean
theorem actualIntervalKernel_sine_action_density {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a z H y : ℝ) (ha : 0 < a) (hH : 0 < H)
    (hy : |y| < a) (T : ℝ≥0) (hT : T ≠ 0) :
    Integrable (fun x : ℝ => mixedSineSeries 0 0 a z H x *
      (gaussianPDFReal y T x * intervalCompletion (bridgeLaw B P) a y (T : ℝ) x)) volume ∧
    (∫ x in Icc (-a) a, mixedSineSeries 0 0 a z H x *
      (gaussianPDFReal y T x * intervalCompletion (bridgeLaw B P) a y (T : ℝ) x)) =
      mixedSineSeries 0 0 a z (H + (T : ℝ)) y := by
```

At H>0 the raw sine series is globally continuous and bounded by C≥0. The actual killed density is nonnegative and genuinely Lebesgue-integrable by qualified unit123. Thus |S_H·density|≤C·density with continuous payload proves genuine whole-line integrability via Integrable.mono'. The exterior support established by the helper identifies the Icc integral with the full-line integral pointwise, including the zero outside. Qualified actualIntervalKernel_apply_eq_density identifies the actual kernel measure with volume.withDensity(ofReal density). The density is measurable and finite everywhere; the pinned withDensity integration theorem applies, and density≥0 permits toReal(ofReal density)=density exactly. Scalar multiplication and commutativity give the identical integrand. Qualified unit138, whose returned actual-kernel integrability and actual action have been independently accepted at the unchanged source/object, evaluates it to S(a,z,H+T,y). Its hypotheses a>0,H>0,|y|<a,T>0 are all explicit. The arbitrary real terminal parameter z is not silently restricted.

Exact source line:59. Complete declaration SHA256:0f677633cda29541e193bdcd288758aea1ea66665d9b1d1ba7c4b564d47956ba. Actual full type-expression SHA256:19cd372ab2ba30d8745fdc77e3936f82735677cd3537c5e9faf0b0ecf706f426. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### actual_killed_density_eq_sine

```lean
theorem actual_killed_density_eq_sine {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y z : ℝ) (ha : 0 < a) (hy : |y| < a) (hz : |z| < a)
    (T : ℝ≥0) (hT : T ≠ 0) :
    gaussianPDFReal y T z * intervalCompletion (bridgeLaw B P) a y (T : ℝ) z =
      mixedSineSeries 0 0 a z (T : ℝ) y := by
```

Fix positive physical T and strict interior y,z. The actual density x↦phi_T(x−y)·intervalCompletion(bridgeLaw B P,a,y,T,x) is a globally continuous and bounded test by the private helper. Unit140 therefore gives its Icc analytic sine approximate-identity limit equal to the actual density at z. For every H>0, the preceding genuine density-action theorem identifies this very same integral with S(a,z,H+T,y), consuming the actual positive-cutoff action rather than assuming a zero-cutoff identity. As H↓0 in NNReal, H+T→T. The qualified analytic time derivative of S at the fixed positive T implies continuity there, so the same expression tends to S(a,z,T,y). Uniqueness in the Hausdorff real topology identifies these two limits pointwise. There is no AE-to-pointwise leap, assumed actual/image identity, use of an unproved spectral completeness result, or hidden cutoff-removal premise.

Exact source line:108. Complete declaration SHA256:1f2d68f49d0802f4c72fc34c3a63694057b08e0fdb31119edfb2109db0b6a526. Actual full type-expression SHA256:48ce7a6c00a5674f61b4afc348d22bf0e0acd705670fb5af807039de2baf3f4a. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

### bridge_interval_eq_image

```lean
theorem bridge_interval_eq_image {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y U z : ℝ) (ha : 0 < a) (hy : |y| < a)
    (hU : 0 < U) (hz : |z| < a) :
    intervalCompletion (bridgeLaw B P) a y U z = intervalImageCandidate a z U y := by
```

Package U>0 as the exact NNReal T with underlying value U and apply the preceding actual density equality at strict interior y,z. The reciprocalFreeDensity(z,U,y) multiplies gaussianPDFReal(y,T,z) to1 by the qualified exact cancellation; the exponent here is already (z−y)²/(2U), so the parameter order and Gaussian normalization agree exactly. Multiplying the density equality yields actual intervalCompletion=reciprocal·S=normalizedSineCandidate. The independently qualified ANALYTIC image/normalized-sine identity on closed endpoints applies using the strict hypotheses weakened to ≤, and gives the claimed actual bridge/image equality. The actual bridge law and Brownian hypothesis remain in the statement. Only positive time, positive width, strict interior endpoints are claimed; this does not automatically close the original C12 root group.

Exact source line:133. Complete declaration SHA256:839d883ae91e8b1ebc9508822f15fa596a2e42d3455c23e4df4674ea17c5639b. Actual full type-expression SHA256:747cded4295a64bb9bd0fd86aa44a9ad38d3c5a43d6d230c6752f6c3476bc940. Recursive axioms:propext, Classical.choice, Quot.sound. **CORRECT.**

## Reused qualified dependencies and interaction check

Eleven current qualified producer modules have exact local/current/snapshot/output/installed source-object bindings and original artifacts checked. Their complete old reviews are reused after source/object/freeze/receipt/seal and one-for-one owner-name coverage checks;191actual producer owners are covered. BridgeDomination and BrownianBridgeLaw additionally reuse their exact historical qualified reviews, covering30and21owners, with current source/object equality and embedded released/zero-inflight evidence. These are reused owner counts, not new declarations or additional root closures. No old complete proof review was automatically repeated.

- Shao.C2.BrownianSineStoppedLimit: sine-first-loss-stopped-final-review-v1; exact complete owner coverage reused:22.
- Shao.C2.IntervalImageSmallTimeSum: interval-image-small-wall-final-review-v1; exact complete owner coverage reused:18.
- Shao.C2.CompletionFirstProfile: completion-profile-heat-final-review-v1; exact complete owner coverage reused:13.
- Shao.C2.IntervalImageCandidateSpatial: interval-image-candidate-final-review-v1; exact complete owner coverage reused:9.
- Shao.C2.IntervalImageSineIdentity: interval-poisson-joint-final-review-v1; exact complete owner coverage reused:9.
- Shao.C2.IntervalReciprocalDerivatives: interval-reciprocal-final-review-v1; exact complete owner coverage reused:61.
- Shao.C2.IntervalSineSeries: interval-sine-terms-final-review-v1; exact complete owner coverage reused:9.
- Shao.C2.IntervalSineNormalizedDerivatives: interval-sine-normalized-final-review-v1; exact complete owner coverage reused:18.
- Shao.C2.SineStoppedWallBound: brownian-sine-stopped-final-review-v1; exact complete owner coverage reused:4.
- Shao.C2.BrownianKilledEndpointDensity: bridge-law-universality-final-review-v1; exact complete owner coverage reused:19.
- Shao.C2.BrownianKilledKernel: brownian-killed-kernel-final-review-v1; exact complete owner coverage reused:9.

The137–138 final review remains exactly JSON4b6c539c788d0bb698f7e174863b6d20104a4f14e1253fbca6ac4e73d5a8f521, MD134d2a795ce60864922e562fe551684d677606e4257b508a21245d611c924a5b, release d8be46d8a4c2b0caea9e3595f0ea8144c3d1138a43211e21731aa47cb9c8f1d0, with parent acceptance QUALIFIED. Its unit138 actual sine action retains an explicit genuine integrability result and requires no actual/image identity. The exact analytical image/sine equality is numerical, not a disguised actual identification assumption. The actual-kernel continuity and withDensity producer is constructed from genuine strict bridge completion; its existing proof uses half-line continuity and the interval increment comparison, with no sine/image premise. This rules out circularity in141.

Consumed complete source heads/transparent values and elaborated interface types are bound in interfaces.json. In particular S is the actual unconditional sum of sineTerm derivatives, with sineTerm=(1/a)exp(−frequency²T/2)sin(frequency(y+a))sin(frequency(z+a)), frequency=(n+1)π/(2a). The reciprocal is sqrt(2π)sqrt(T)exp((z−y)²/(2T)). StrictInterval means both walls are monitored for every bridge time; intervalCompletion is the literal real measure of that event, and bridgeLaw is the Brownian bridge-noise pushforward. These definitions agree with the original quotient and normalization. Primitive full old actual type/value qualification is reused, not falsely represented as a new full old proof review.

## Primary interfaces, original scope and boundaries

The read-only supplement.tex was completely read at4192–4315; whole-file SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd. It defines the strict Brownian-bridge survival quotient k/phi at interior endpoints and positive time, the two wall profiles, the normalized interval image expansion, and the sine expansion of the killed heat kernel. Units139–140 supply a legitimate analytic initial condition. Unit141 now supplies the missing actual positive-time strict-interior density and image identification. This is a classical identification result within the larger formalization; no new research novelty is asserted. Existing p54 repairs and external-result attribution are preserved.

Pinned primary statements, their full needed proofs and active variable contexts were read and byte-compared against the pinned mathlib Git revision: NNReal right-neighborhood coercion, reciprocal and positive-product infinity limits, exponential decay, finite-measure bounded integrability, HasLaw integral transport, Gaussian PDF and Gaussian probability measure, Gaussian density integration, indicator integration, filter dominated convergence, and withDensity real-scalar integration. The full pinned Lean collectAxioms implementation was also read. Exact paths, hashes and ranges are in the native evidence files.

Boundary review: strict interiority is essential to139diagonal/140pointwise/141identification; representation140 permits closed endpoints. T=0 is excluded at every reciprocal and positive density call. Closed intervals and their indicators remain literal; exterior density support is exact. M≥0 is derived, not assumed. The Gaussian law has varianceT and affine scale√T; the exact density and reciprocal use the same2πand exponent. DCT is under one fixed standard Gaussian with integrable constant17M. The actual density test in141 is continuous and globally bounded, and both actual and analytic action integrals are genuinely integrable. The stated theorem is pointwise; continuity and uniqueness of two actual limits justify it without upgrading an AE identity.

No boundary-center initial limit, zero-time density/Dirac identification, arbitrary non-Brownian law, outside-endpoint actual/image claim, arbitrary uniform diagonal limit, unconditional hSmall or complete original C1/C2 theorem is certified.

## Validation, telemetry and release

full-review.json contains one-for-one11owner semantic/proof/type/recursive-axiom coverage, all exact new source/receipt/freeze/object bindings, actual counts and evidence file hashes. Deterministic final validation checks them before writer-release.json is written last. The release binds reports, validation and all review artifacts and records writer/execution released with0inflight. No edits occur after that seal.

Configured model:gpt-6.1-sol; effort:xhigh. Actual telemetry is unavailable. Input, cached input, output and reasoning-subset counts are null, not zero. No raw-token or purchased-credit estimate is presented as a subscription percentage.
