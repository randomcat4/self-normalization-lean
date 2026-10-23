# U22I independent complete review

## Immutable blind type interpretation

This section was written after reading only `u22i-actual-types.txt`, before reading the scope, implementation, dependency sources, or gate evidence. It interprets the printed type and does not yet certify its named definitions or proofs.

The sole printed declaration is `Shao.OQ3.compact_open_domain_covariance_whitened_family`.

The inputs, in quantifier order, are:

1. A measure `mu` on the real line, with an instance asserting that it is a probability measure.
2. A subset `Theta` of pairs of real numbers, assumed compact and contained in the interior of `bivariateMGFDomain mu (fun x => (x, x^2))`. The mathematical meaning of that named domain remains to be checked against its definition.
3. Five real constants `lo`, `hi`, `beta`, `c`, and `R`, satisfying `lo > 0`, `hi > 0`, `beta >= 0`, `c > 0`, and `R >= 0`.
4. For every parameter `p` in `Theta`, write `D` for `parabolaCovariance` of the actual expression `mu.tilted (fun x => p.1*x + p.2*x^2)`. For every pair of real frequencies `(xi, eta)`, the displayed quadratic form `xi^2 D00 + 2 xi eta D01 + eta^2 D11` lies between `lo*(xi^2+eta^2)` and `hi*(xi^2+eta^2)`. This is an explicit uniform covariance bound supplied by the caller, not a conclusion derived from compactness.
5. For every `p` in `Theta` and every real `(xi, eta)` of Euclidean norm greater than `R`, the norm of `jointCharacteristic` of that same actual tilted measure is at most `1 - c*r^(-beta)`, where `r = sqrt(xi^2+eta^2)` and the real power is `Real.rpow`. This is an explicit uniform weak-Cramer hypothesis on the original tilted family.

The output uses literal let-bound objects, not existentially chosen substitutes. For each `p`, let `tilt p` be the tilted measure above and `D p` its named covariance matrix. Set `s p = sqrt(D00*D11-D01^2)` and `t p = sqrt(D00+D11+2*s p)`. The literal two-by-two matrix `A p` has diagonal entries `(D11+s)/(s*t)` and `(D00+s)/(s*t)` and both off-diagonal entries `-D01/(s*t)`. Set `means p = (integral x, integral x^2)` under `tilt p`; `Y p x = A p * ((x,x^2)-means p)`; and `laws p = map (Y p) (tilt p)`, a measure on functions `Fin 2 -> R`. `Phi p xi eta` is the integral of `exp(i*(xi*y0+eta*y1))` against precisely `laws p`. Thus the stated centering is by the actual two coordinate integrals, and the matrix used in the mapped law is the same literal `A` computed from the displayed covariance entries.

The constants are fixed by the inputs: `L = 1/sqrt(hi)`, `U = 1/sqrt(lo)`, `cA = c*U^(-beta)`, and `RA = R/L`. The conclusions assert `L > 0`, `U > 0`, `cA > 0`, and `RA >= 0` and, for every `p` in `Theta`, all of the following:

- `s p > 0`, `t p > 0`, symmetry `A^T = A`, and the exact matrix identity `A*D*A = I`.
- Strict positivity of `xi*(A*(xi,eta))_0 + eta*(A*(xi,eta))_1` for every nonzero pair `(xi,eta)`.
- `laws p` is a probability measure.
- For each of its two coordinate functions, membership in `MemLp` with exponent 2 and integral equal to zero.
- For every pair of coordinates `i,j`, covariance under `laws p` equals the Kronecker delta: one when `i=j`, zero otherwise.
- For every real frequency pair of norm `r`, the transformed frequency with components `xi*A00+eta*A10` and `xi*A01+eta*A11` has norm between `L*r` and `U*r`. These are the components of the transpose action on the frequency, as required for an affine characteristic-function change of variables.
- Whenever `r > RA`, `norm(Phi p xi eta) <= 1 - cA*r^(-beta)`. The exponent `beta` is preserved, and the constants and threshold are those fixed above.

Finally, for every natural number `k`, there exists a real constant `C > 0`, allowed to depend on `k` and the fixed input family but not on `p`, such that for all `p` in `Theta` the nonnegative Euclidean radial moment function `sqrt(y0^2+y1^2)^k` is integrable under `laws p`, its integral is nonnegative, and its integral is at most `C`. The quantifier order is exactly `forall k, exists C > 0, forall p in Theta`. This asserts all natural radial moments, not a specifically stated fractional `8+delta` moment or a root theorem closure.

Blind vacuity and circularity checks: `Theta` may be empty, in which case all parameter-wise assertions and both parameter-wise hypotheses are vacuous, but the positive global constants and each positive witness `C` must still exist. No nonempty-domain premise is present. For nonempty `Theta`, the spectral lower bound supplies nondegeneracy; no separate determinant hypothesis is assumed. The zero-frequency case is included in the norm bounds but excluded from strict positivity and from the high-frequency estimate by its nonnegative threshold. Neither a probability assertion for the tilted measures nor their normalizer positivity nor moment integrability appears as a separate input; these require substantive derivation from the domain hypothesis and the definition of tilt. Since integrals in Lean can be totalized, actual integrability must be checked, not inferred merely from integral expressions. The two original-family hypotheses resemble two transformed-family conclusions, but concern the original tilted law and its covariance; whether there is a concealed circular assumption must be checked in the named definitions and implementation. No compact inverse-image assertion, reference-law implication of the original weak-Cramer hypothesis, or complete OQ3 B/D theorem is present in the printed conclusion.

End of immutable blind type interpretation.


## Freeze record, verdict, and independence

The immutable prefix is the first **5511 UTF-8 bytes**, **33 lines**, ending with “End of immutable blind type interpretation.” Its SHA256 was computed immediately after creation, before any scope/implementation/evidence read: **82d2bdb03bdfd6d980d4b31d473ec1315e3132df287516f1447fe393afd9b53a**. All later material was appended after that prefix; its bytes are preserved.

**STATUS: CORRECT.** The entire exact 120-line U22i implementation proves its frozen conditional family statement. I found no critical mathematical gap, substituted law/matrix, weakened quantifier, implicit bounded-support assumption, incorrect transpose/sign, or caller assumption containing the whitening conclusions. Acceptance is for this family interface and its one actual module-owned theorem, at source SHA256 `622601d0f8650bfc684f4dfde9a615700ad48c4911f5316734193278e115ee8e`. It does not close original OQ3 B or D.

Reviewer context: `/root/oq3_u22i_full_review`, assigned fresh independent `gpt-6.1-sol` / `xhigh` review. I did not author or change the proof, scope, dependencies, evidence, shared files, branch, package cache, or coordination status. My sole write is this report. No subagent, Lean command, build, owner audit, cache hydration, installation, or test gate was invoked. Exact existing successful gates were reused after direct read-only inspection. Actual input, cached-input, output, and reasoning-subset token telemetry is unavailable in this reviewer context; no token or subscription allocation estimate is made.

## Complete mathematical reconstruction

### Actual domain, normalized tilt, and raw moments

The definition `bivariateMGFDomain` in `Shao/Probability/BivariateLegendre.lean` is the set of parameters for which the exponential `exp(p.1*x+p.2*x^2)` is genuinely integrable against the base measure. Thus `hTheta` puts every used parameter inside that true integrability domain, with a neighborhood inside it. It is not the set of arbitrary parameters where a totalized integral has a real value. Mathlib's actual `Measure.tilted` is the measure with density `ofReal(exp(f x)/(integral exp(f) dmu))`; its nonintegrable case would be the zero measure, which is a real semantic risk but is excluded here.

At U22i lines 86–87 and 107–109 the proof applies `open_domain_quadratic_tilt_directional_cumulants` to the same base `mu`, parameter `p`, and `hTheta hp`. I read all 165 lines of that producer, including its normalization and interior-projection proofs. Its `quadratic_tilt_mgf_identity` uses the genuine integrability hypothesis to prove `Z(p)>0` and `IsProbabilityMeasure(mu.tilted f_p)`, not an arbitrary probability replacement. For a direction `d`, integrability of the tilted directional exponential is equivalent to domain membership at `p+t*d`, and its MGF is `Z(p+t*d)/Z(p)`. Continuity of that parameter line and the interior hypothesis give a genuine interval about zero of directional exponential integrability. Mathlib's interior-MGF results then give all natural directional powers integrable and in particular `x` and `x^2` in `L^2` under the actual tilt. This justifies both actual centering integrals and all products used for covariance.

For uniform raw moments, the consumed chain is `OpenDomainWeightedMoments -> OpenDomainFrechetCumulants -> OpenDomainSmoothMean -> OpenDomainCompactMoments`; I read each complete source, including all private definitions/proofs, rather than treating continuity as an unexplained premise. The weighted-moment derivative theorem first proves weighted-power integrability from the same interior-MGF argument. It shifts the quadratic parameter by a small positive `delta` still in the interior. On a parameter rectangle of radius `eps=delta/4`, the exponential is dominated by `exp(eps/2)*exp(p.1*x+(p.2+delta)*x^2)`, using `2|x|<=1+x^2`. Weighted powers at that shifted interior point dominate the derivative uniformly and are integrable; differentiation under the integral therefore applies. Derivatives of order `j` use the actual weighted moments of orders `j+1,j+2`; induction gives smoothness and hence continuity. Dividing by the positive partition function identifies the continuous tilted raw-power moments with the actual normalized integrals.

The compact raw-moment theorem bounds the continuous even moment `M(p)=E_p[x^(2k)]` on compact `Theta`. If `B` is an upper bound for its image, `|x|^k<=1+x^(2k)` gives `E_p|x|^k<=1+B<=|B|+2`. Integrability and nonnegativity are established explicitly. The positive constant is chosen before the parameter. Empty compact sets also have a bounded image; no nonempty-set selection is smuggled into this step. The inspected Frechet cumulant producer additionally confirms that the actual mean is the gradient of the same actual log-partition function and the named covariance is its Hessian. Consequently the covariance and mean here match the original R2 objects, not merely objects with suggestive names.

### The actual positive symmetric whitening matrix

By the inspected `parabolaCovariance` definition, `D=[[Var_p(x),Cov_p(x,x^2)],[Cov_p(x,x^2),Var_p(x^2)]]`, so the symmetry supplied by `rfl` at U22i line 89 is legitimate. The `L^2` facts above make these genuine finite variances/covariances; the spectral assumption does not rescue undefined moment expressions after the fact.

U22i lines 88–99 invoke the full numerical theorem `quadratic_whitening_spectral_data` on precisely `D p`. I read all 245 lines of that module, including the private algebra. Write `a=D00,b=D01,d=D11,delta=a*d-b^2`. The lower spectral bound at `(1,0)` and `(0,1)` gives `a,d>0`; at `(-b,a)` it gives `a*delta>0`, hence `delta>0`. Thus `s=sqrt(delta)>0`, `t=sqrt(a+d+2s)>0`, and division by `s*t` is valid. If `N=[[d+s,-b],[-b,a+s]]`, direct polynomial expansion with `s^2=delta` and `t^2=a+d+2s` gives `N*D*N=(s*t)^2*I`. Scaling by `1/(s*t)` proves the literal `A*D*A=I`; the matrix is symmetric by its entries.

For a nonzero frequency vector `u=(xi,eta)`, its quadratic form under `A` equals
`[s*(xi^2+eta^2)+(a*eta^2-2*b*xi*eta+d*xi^2)]/(s*t)`.
The rotated vector `(-eta,xi)` has positive squared length, so the second numerator term is positive by the same lower spectral bound. The denominator and first term are positive as well. This proves positivity of `A`, with the intended negative off-diagonal signs. It is the positive symmetric covariance-whitening construction; no arbitrary matrix satisfying an assumed whitening conclusion is supplied by the caller.

Let `v=A^T*u`. The matrix identity and symmetry give `v^T D v=|u|^2`. Applying the two spectral inequalities to `v` yields `lo*|v|^2<=|u|^2<=hi*|v|^2`; taking nonnegative square roots and dividing by positive square roots gives `L*|u|<=|v|<=U*|u|`, with the exact `L=1/sqrt(hi), U=1/sqrt(lo)`. The argument includes `u=0`, with no cancellation of `|u|`. At the two standard basis vectors the upper bound bounds the Euclidean norm of each row of `A` by `U`; each entry's absolute value is at most that row norm. This is exactly the all-entry bound projected at U22i lines 97–99, for the same literal `A p`.

### Actual mapped probability law, mean, and covariance

At U22i lines 105–117 the actual tilt is installed as a probability measure, and its proven `L^2` coordinates are passed to `centered_affine_parabola_mean_covariance`. I read that complete theorem and proof within all 495 lines of `CovarianceWhitening.lean`. The used theorem has no bounded-support premise. The separate bounded-family theorem later in that imported file is not used to obtain the unbounded-family assertions.

The helper defines `m=(E_p x,E_p x^2)`, `Z_i=W_i-m_i`, and `Y_i=sum_j A_ij Z_j`; these are definitionally the caller's `means p,Y p,laws p`. For each of the two coordinates, subtraction of a constant preserves `L^2`, the centered integral is zero, and finite linear combinations preserve `L^2`. The polynomial affine map is continuous/measurable, so its actual pushforward is a probability measure and the `L^2` coordinate facts transfer through `map`. Pullback of the coordinate integral and finite-sum integral linearity give zero actual mean.

Covariance is invariant under subtracting these constants, is bilinear for these `L^2` variables, and respects this measurable pushforward. Thus the helper proves exactly `Cov_laws(y_i,y_j)=(A*D*A^T)_ij`. Both diagonal variance identities and the reversed off-diagonal covariance identity are checked, including the finite two-coordinate expansion. U22i line 115 replaces `A^T` by the proven same `A` and then uses `A*D*A=I`; `Matrix.one_apply` supplies the exact Kronecker delta. The order of multiplication is correct. There is no unproved identification of two different mapped laws and no arbitrary centering vector.

### Uniform all-natural Euclidean moments

U22i line 100 passes the very same `A` and its uniform entry bound into `compact_open_domain_affine_parabola_moments`; line 103 returns its whole `forall k, exists C>0, forall p in Theta` result. I read all 166 lines of that source, including both private inequalities and the complete public proof, and checked the actual instantiation independently.

Let positive uniform raw bounds of orders one and two be `C1,C2`. They give `|m0|<=C1, |m1|<=C2`. For each output coordinate,
`|Y_i(x)|<=U*(|x|+x^2+C1+C2)`.
The elementary radial bound `sqrt(y0^2+y1^2)<=|y0|+|y1|`, together with `|x|<=1+x^2`, gives
`radius(Y(x))<=Q*(1+x^2)`,
where `B=C1+C2+2` and `Q=2*U*B>=0`, both uniform in the parameter. For natural `k`,
`(1+x^2)^k<=2^k*(1+|x|^(2k))`.
The proof checks this for both `x^2<=1` and `x^2>=1`, so it also covers `k=0`. Consequently
`radius(Y(x))^k<=W*(1+|x|^(2k))`, where `W=(2*Q)^k>=0`.

A uniform raw bound `Ck` for order `2k` is chosen before `p`; the actual dominating function is integrable. The proof uses measurable domination to prove the transformed radial power integrable under the tilt, then `integrable_map_measure` and `integral_map` for exactly the actual mapped law. Its nonnegative integral is at most `W*(1+Ck)`, so `W*(1+Ck)+1` is an explicitly positive uniform witness. These operations use the same `Fin 2` coordinate radius as the target, not the product space's supremum norm. `hmom.2` is therefore the complete quantified radial-moment assertion, not a parameter-dependent or non-integrable totalized bound. No continuity of `A` or of a square-root matrix as a parameter function is assumed or needed; the uniform entry bound is sufficient.

### Characteristic factor, frequency threshold, and unchanged exponent

I read all 152 lines of `AffineWeakCramer.lean`, including the exact characteristic-factor proof, and inspected the definitions `jointPhase` and `jointCharacteristic`. For `u=(xi,eta)`, the pulled-back phase is
`u dot Y = (A^T*u) dot W - (A^T*u) dot m`.
Its components are exactly `xiA=xi*A00+eta*A10` and `etaA=xi*A01+eta*A11`, as printed in U22i. Thus
`Phi_p(u)=exp(-i*((A^T*u) dot m))*jointCharacteristic(tilt p,xiA,etaA)`.
The constant phase has norm one, so it does not alter the characteristic norm. The affine map is measurable; the phase functions are continuous and bounded in norm by one. In this application the source and mapped measures are probability measures, so these characteristic integrals have their genuine integrable meanings. The sign and transpose are correct even before using symmetry.

At U22i lines 101–102 the uniform transfer helper receives `Theta, tilt, hprob, A, means, L, U, beta, c, R` in the correct positions. Let `r=|u|` and `rA=|A^T*u|`. If `r>RA=R/L`, then positivity of `L` gives `R<L*r<=rA`; as `R>=0`, both `r,rA` are positive. Therefore the original actual tilted-family weak-Cramer hypothesis is applicable at the transformed frequency. Since `rA<=U*r` and `-beta<=0`, negative-power monotonicity gives
`(U*r)^(-beta)<=rA^(-beta)`.
Multiplicativity of real powers on positive bases gives
`cA*r^(-beta)=c*(U*r)^(-beta)<=c*rA^(-beta)`.
Subtracting from one and applying the characteristic norm identity yields exactly the stated bound. The threshold uses the lower frequency constant `L`, and the cost uses the upper constant `U`; neither is interchanged. Positivity of `cA=c*U^(-beta)` and nonnegativity of `RA` follow separately. No exponent loss occurs, including the allowed `beta=0` case.

## Scope fidelity, vacuity, and original intent

I read the complete 85-line frozen scope, complete root-contract, all 523 lines of the actual original R2 report, and all 226 lines of its repair. The source hashes in the root-contract match the actual read-only R2 source. The relevant R2 passages are its actual exponential tilt at lines 38–45, retained uniform covariance/moment/weak-Cramer hypotheses at lines 47–61, standardization and frequency comparison at lines 83–92, moment discussion at lines 94–99, and the explicitly bounded single-reference-law transfer at lines 343–373. The repair's input is the standardized actual family with identity covariance, uniform eighth moment and unchanged-exponent weak-Cramer bounds; its far-field hypothesis remains separate.

U22i is a faithful conditional realization of that standardization and natural-moment input. It removes the need to assume an arbitrary replacement whitening/moment family. It retains the original actual uniform spectral and actual uniform tilted-family weak-Cramer hypotheses explicitly. It does not use the bounded density-lower-bound mechanism to claim unbounded reference-to-family stability. The original `mu` need not have bounded support or all moments before tilting. No artificial finite-support witness, independent replacement law, strong-nonlattice condition, desired local expansion, or whitening/moment conclusion is added to the inputs.

Empty `Theta` is expressly permitted, with parameter-wise statements vacuous and positive global constants/witnesses still constructed. No argument uses an element of an empty set. For nonempty `Theta`, the lower spectral hypothesis enforces nondegeneracy; there is no silent determinant premise. Parameters outside `Theta` can yield totalized let-bound expressions, but the theorem never claims their probability/moment/whitening properties. At zero frequency the two-sided norm comparison is valid; the strict-positive quadratic form is required only off zero, and the strict high-frequency threshold excludes zero. No unjustified division by a frequency is used. The theorem does not require `lo<hi` as an independent input; the inequalities, rather than a strict gap, are all the numerical algebra needs. Inconsistent caller data merely leave an ordinary implication, not a missing proof case.

The family helper allows all nonnegative `beta`; original root B still requires `0<beta<2/5` and its other hypotheses. U22i explicitly proves natural powers only. It does not yet state the original real `8+delta` moment or a Lindeberg condition, even though natural higher moments are useful toward that later bridge. It proves no mean-map inverse neighborhood, compact inverse image, global Legendre geometry, far-probability estimate, Song/Angst–Poly Edgeworth theorem, cell reconstruction or summation, boundary Laplace asymptotic, or fixed-x saddle expansion. The missing root inverse-cache object is not consumed or resolved by this unit. Corrected A and accepted bounded C scope are unaffected; B/D remain OPEN. No research-novelty or root-completion claim follows from this auxiliary result.

## Mechanical appendix: exact-source evidence reuse

All mathematical reasoning above was reconstructed from the actual statements and complete proof sources. The checks in this appendix corroborate that exact version; a successful receipt or previous review vote was not substituted for proof review.

### Read coverage and source bindings

| Item | Exact SHA256 and size | Coverage |
|---|---|---|
| Frozen `ninetieth-unit-scope.md` | `98989d04d7e77c56c7ce2e755c5bdd5b9fb1f1c635d45420fdf5e8325fa0c94a`; 6650 bytes, 85 lines | Entire file, exact frozen Lean block |
| Actual `OpenDomainWhitenedFamily.lean` | `622601d0f8650bfc684f4dfde9a615700ad48c4911f5316734193278e115ee8e`; 6892 bytes, 120 lines | ALL 120 lines; full statement and proof |
| `u22i-actual-types.txt` | `6887947e3763522a3c89137fcfc220da23d92562149912e7f8fe3daf44e1aefa`; 5188 bytes, 74 lines | Entire inventory read before freeze |
| `OpenDomainAffineMoments.lean` | `110a16cab72d655905659b30a496625f98aa70e188b004a8713006225ab9a8e3`; 8875 bytes, 166 lines | Entire file, both private helpers and public proof |
| `QuadraticWhiteningSpectralData.lean` | `83520a430712a07148396f30f7c07619ef55bda9cc9e464a98eae63e071e874e`; 10995 bytes, 245 lines | Entire private and public statements/proofs |
| `QuadraticTiltCumulants.lean` | `ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a`; 9143 bytes, 165 lines | Entire normalization/interior/cumulant chain |
| `CovarianceWhitening.lean` | `d1f90abf2ecd59032dc5f934dbedbe9c3ab9e468f73b0d4f40b24b4a7851eec8`; 24907 bytes, 495 lines | Entire file; actual generic mean/covariance theorem starts at line 212 |
| `AffineWeakCramer.lean` | `29457076f283c08b093949d3c12cfb020ea0bb496e51573ad74554114e94031f`; 7064 bytes, 152 lines | Entire factor/transfer proofs |
| `OpenDomainCompactMoments.lean` | `19946ecf589a2012df33b34ad740b4ff30190bd84fe42662bdaa194c5c545093`; 4170 bytes, 85 lines | Entire file |
| `OpenDomainSmoothMean.lean` | `d6457d90d9d0e1ccdae6d6ea041d8caef65f70b3cb6d5fa8baea1867a5bffb8e`; 5312 bytes, 103 lines | Entire file |
| `OpenDomainFrechetCumulants.lean` | `b5d48b414adbc80f7db44f37cc2b2b423d44263c54e8547a5a356768a116df72`; 9834 bytes, 190 lines | Entire file |
| `OpenDomainWeightedMoments.lean` | `f28ea2e9812d5c7702c75adf096e4fbbce82e4d2464da6cda764d2349e8c6f74`; 8930 bytes, 161 lines | Entire file |
| `RegularCovariance.lean` | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853`; 15931 bytes, 305 lines | Entire file, including actual covariance definition |
| Original R2 `report.md` | `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`; 20102 bytes, 523 lines | Entire source report |
| Original R2 `repair01.md` | `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`; 5846 bytes, 226 lines | Entire repair |

The same server worktree file was read directly and hashed again after review. The frozen archived `source-01.lean` has identical source hash/bytes/lines. A deterministic text comparison found that the entire frozen scope's Lean block equals the actual source prefix through the full declaration before `:= by`, including imports and surrounding namespace/options context. The actual printed inventory was read completely and manually matched against that frozen declaration. No assumption or quantifier changed.

I also read project `AGENTS.md`, `SERVER.md`, the current selected TEAM/REGISTRY authority/resource fields and takeover document, the required math-theorem skill and its complete prompt/workflow/Lean references, the actual domain and characteristic definitions, and the entire pinned Mathlib `MeasureTheory/Measure/Tilted.lean` source. The assigned OQ3 successor is activated after old-writer release, with one child lease and server CPU14–17/one-heavy-command limits. No ownership beyond this review report was taken.

### Kernel check and owner/transitive axiom audit

The local author receipt `u22i-receipt.json` has SHA256 `a5bda4ba653072199f182ea19908691d41b198abe75e06cfb73814fc6b903fa0`. Its exact source/scope/type bindings agree with the independently read current and archived files. Its pending-review status was a creation-time author status, not independent acceptance. The separate exact G and H complete review artifacts are available at source hashes matching those above: G report `71a03708e8f18302eb86a8bab62b62efcca9bbb80606b07e4d9ef0bdf17123c7` (21991 bytes/110 lines), H report `798641c61ab02a64dbab081f9c70f30c00efffbf6917ada8417b1b76f9f6217b` (21746 bytes/123 lines), both CORRECT. Only their compact acceptance/hash records were inspected after the relevant proof sources had already been independently reconstructed here; they were not used as mathematical votes.

| Existing evidence | Verified binding/outcome |
|---|---|
| Complete source attempt 01 | Exit 0, **6.466094164177775 seconds**, exact reviewed 120-line source; first and only complete-success attempt in history |
| Full `build-01.log` | `5c8f16769c5735227e3a8be1b810f3a950c1e396e69a46e798d99e6ea6cb8629`, 853 bytes; entire log read |
| `u22i-build-history.json` | `9a5ea77c317e928074a931fb7bcff4cb55dfa5f3041822b1094b4cd28ecdcece`; full one-attempt history read |
| First whole-owner audit | Exit 0, **5.7521367613226175 seconds**, same exact source |
| Full audit source `u22i-Audit.lean` | `9e16a6a42f642d4dac9ba32d86160aa147c87a24c727bc3c63c6ff2755af520e`, 1896 bytes/44 lines; entire source read and matched to archived `Audit.lean` |
| Full remote `audit.log` | `b45aa56d4e197461b720228e544760fd42b7d7c5f0e8039d1446036dc502e790`, 5435 bytes; entire log read |
| `u22i-audit-record.json` | `e8e959b401b5179d9b95575c734f26b15d20e95a7ff53b7b21d4622a230ff4bc`; full record read |
| `u22i-audit-environment.json` | `16fab052fc8c0b0d9744511090d1564c262edd8e37acf3dbb26b3a59efae72bd`; entire manifest read |

The audit imports the actual production module and enumerates every constant by `env.getModuleIdxFor?` actual module ownership, rather than relying on public textual theorem names. It rejects owned axioms and applies `Lean.collectAxioms` to every owned declaration, rejecting every transitive axiom outside `propext, Classical.choice, Quot.sound`. Thus private/generated owners, if present, are included; they are not filtered out by visibility or name prefix. Imported dependencies of the target are traversed transitively by `collectAxioms`. This does not pretend to enumerate all unrelated imported declarations as U22i owners.

The observed output reports zero frozen definitions, one frozen theorem, one actual theorem and one actual declaration; therefore there are no additional private/generated U22i owners left uncovered. The one declaration's printed transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`, and the final output is `U22I_AXIOM_GATE PASS`. Audit options `pp.deepTerms` and `pp.maxSteps` affect printing only. Full-source static inspection and a targeted forbidden-token scan found no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, or `implemented_by`; the implementation contains no `set_option` command.

Both successful gates record CPU14–17, native Lean memory limit 8192 MiB, four jobs, and `autoImplicit=false`. The worktree's actual `lean-toolchain` is `leanprover/lean4:v4.36.0-rc1`; its manifest pins mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The actual `lakefile.toml` retains that same revision and `autoImplicit=false`, SHA256 `444f3a3a01fd8ff99f219cff08a99b20459c0d177c4e2c884af9eead481daf44`. No settings were weakened to produce this result.

### Exact environment and limits of the evidence

Server worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`. Frozen parent: `803d8d0fbea3c2a55b8167f7c1ff4902510f1b8e`, branch `feat/oq3-open-domain-standardization`. Existing run: `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22i-20261023`. The recorded accepted-source-view is `runs/oq3/accepted-source-view`, using accepted baseline plus own newly built objects. Direct observation confirms `.lake/packages` points to the root-authorized `cache-overlays/shared-v34/packages` view.

Targeted read-only object inspection confirms the accepted-source-view links for U22i, G, H, and A point to the same lane-built objects as the worktree. Their hashes are respectively `fccdc64bc2e71f1fdc4d070c89ec0c019640d3d99379a063782776c0436314a5`, `4db6e4828491ef0f086d259e03125128d286d95ed5a35ddf387a4729549cf95a`, `e30a9e99dd2bbcd1f6cc44c7a2b577724f20f6f71cb1e555fb0173c0eabf01cd`, and `820239a2a46ae6f3fa5658c5a5f8aca431638d25fbd3a6075ab480d7616b087e`. The manifest's direct G/H source hashes match the independently read final producers. The historical `provisional_dependency_source=ea105...` field is the actual A/QuadraticTiltCumulants source hash, not a claim that G or H has that hash.

The complete build log contains Lake's accepted thin-overlay local-changes warning and two `letI` style suggestions at target lines 105 and 111. The audit log contains the same overlay warning. There is no proof failure or weakened setting in those logs. I did not run broad package `git status`, follow the entire cache symlink tree, claim whole-cache cleanliness, or mutate/hydrate packages. One additional read-only symbol-location helper failed because server `rg` is unavailable; its preceding full Mathlib Tilted source read succeeded and provided all needed definitions. That helper was not a proof/check gate and caused no uncertain mutation or missing mathematical coverage. No successful gate was repeated.

**Final review state: CORRECT; complete mathematical/source fidelity review and reused exact-source server kernel/transitive-axiom evidence both covered.** No U22i proof revision or further complete review is required merely on context replacement or root integration. Root acceptance must still check these exact hashes and any actual integration/interface changes. This report accepts the stated family helper only and leaves the explicitly excluded original B/D obligations open.
