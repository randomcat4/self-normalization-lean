# Independent complete final review: normalized sine candidate, units 84–86

STATUS: CORRECT. The three exact frozen targets are qualified within their stated analytic scope. I found no critical mathematical or evidence gap in these targets. This review covers 18 public source theorems and every one of the 45 actual defining-module-owned constants: 41 theorem constants and 4 definitions. All original C1/C2/OQ3/OQ4/OQ56 root groups remain OPEN.

The reviewer is the fresh independent `/root/interval_sine_normalized_final_review` context, separate from author chat `01a16c4c-25a6-7740-a10e-12635a13edae`. This reviewer wrote only `drafts/c12-lane/interval-sine-normalized-final-review-v1/`. No production/shared/Git/cache/remote writes, Lean/build/audit commands, successful-check replays, or child contexts were used. Requested model/effort are gpt-6.1-sol/xhigh. Independently exposed actual runtime model, effort, and input/cached-input/output/reasoning-subset usage are unavailable and recorded as null; no subscription percentage is estimated.

## Exact source and object bindings

| Item | Unit 84 | Unit 85 | Unit 86 |
|---|---|---|---|
| Module | `Shao.C2.IntervalSineNormalizedDerivatives` | `Shao.C2.IntervalSineNormalizedHighTime` | `Shao.C2.IntervalSineHighTimeProfiles` |
| Source SHA256 | `e1bad580fd72f80ce51ccfd075d55673bdbd21735f8b55d748d701af7363e91d` | `3b97f7611ac381ab743ec80bc09f3e51db28f05569dda1915f0a51d0c199242d` | `01107daeec09658fe0fff3de19f16cac388937385bf58b8a8c06d14c80cd15f5` |
| Output and installed object SHA256 | `32f36249bcf0d61ac26ec73ac4a8f2c9a59dc417603ee35b42fb1f31c32eb1c0` | `4b6a202d7720d68aeb51c3035565831aee9a191c67a66f521471f2a1c2eb1a03` | `8da80010a32e35a336f2ca0e6c934c1cf0de3bbb77994b25300baa0e97ffdc50` |
| Freeze SHA256 | `3419d01b78cdd4fd44f366c76183c7c2ede2a9c7b3a2d6e7887b4077496c8463` | `325488125de6eb34d19bc805f88c8cb458d92a703877b3f6d3a7de12e014ff12` | `d9a7bb7cac6f1d10ec6b0ebb1e6d8bc2c6408e512a5071dc3a48f6b27af08ea2` |
| Receipt SHA256 | `619803e76a6ce50f5db2b7b87f84cbfc8f81572a48dad23f80a38c7d0d62613b` | `842a46bd18afeae3a7cee6a55496b7eb2f22d31aa3a2fc1cea04f17ede27b8c0` | `35346debfd931be72e73c162036f4a0c5c45a3c2664f9089b6cf9277bfc2eabc` |
| Source bytes / object bytes | 11712 / 1238512 | 6722 / 329296 | 7714 / 271424 |
| Public / actual theorem / actual definition counts | 7 / 16 / 2 | 5 / 10 / 1 | 6 / 15 / 1 |
| Successful kernel attempt / Lean exit | 001 / 0 | 001 / 0 | 002 / 0 |
| Whole-owned transitive axiom audit exit | 0 | 0 | 0 |

Local author folders are `interval-sine-normalized-derivatives-v1`, `interval-sine-normalized-high-time-v1`, and `interval-sine-high-time-profiles-v1` below `drafts/c12-lane/`. Server root is `/root/rivermind-data/shao-lean-20261021`, production worktree `workspaces/c12-bridge-domination-v71`, and output roots are respectively `outputs/c12-interval-sine-normalized-derivatives-v71`, `outputs/c12-interval-sine-normalized-high-time-v71`, and `outputs/c12-interval-sine-high-time-profiles-v71`.

Read-only observations verified each final production source against its successful attempt snapshot and local source, each output object against its installed worktree object, the complete local/remote receipts, and every receipt-listed artifact hash and byte length. Complete maps are retained in `local-bindings.json`, `remote-bindings.json`, and the final JSON. The final sources are UTF-8 without BOM and contain zero CR bytes; the first preserved snapshots already have this format. No frozen old bytes were normalized or rewritten.

## Original source and exact accepted scope

I read the entire read-only `C:/game/shao/current/c12/supplement.tex` lines 4192–4315. Its complete-file SHA256 is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. This includes the actual quotient/survival definition, wall conventions, original two-wall profile and drift factor, derivative/PDE/Taylor statements, both image and high-time sine arguments, and the local Taylor proof. The present targets supply only the high-time analytic assembly in lines 4292–4297, with the profile scale in lines 4224–4229 and the explicit order restriction `j+l≤3`.

Write `g(z,T,y)=sqrt(2*pi)*sqrt(T)*exp((z-y)^2/(2*T))`, let `S(j,l)` be the previously qualified genuinely differentiated sine series, and let `R(i,k)` be the previously qualified reciprocal-density derivative family. The new candidate is literally `N=g*S(0,0)`, and its family is

`F(j,l) = sum_(0≤i≤j) sum_(0≤k≤l) choose(j,i)*choose(l,k)*R(i,k)*S(j-i,l-k)`.

It is a finite double binomial sum, with no default branch and no embedded analytic premise. For `a,T>0`, the new proofs establish actual mixed iterated derivatives of this candidate through total order three and their commutation. Under `T≥a²` and `|y|,|z|≤a`, they prove the corresponding norm and original-profile bounds for `N-1`. The reciprocal factor is the actual inverse of the free Gaussian density at positive time by qualified unit 82. There is no assumption or conclusion here identifying the sine series with the image expansion, a killed heat kernel, or an actual Brownian-bridge survival probability.

This distinction is material at order zero. The source uses the survival fact `|f-1|≤1`; unit 86 instead proves `|N-1|≤C(0,0)+1` from the analytic norm bound. Since the target permits an unspecified order-dependent constant, this alternative proves the same high-time profile scale for the analytic candidate without adding a probability assumption. It neither proves nor silently assumes the source's sharper survival inequality. Identification of `N` with the source's actual `f` remains an independent unpaid dependency.

## Public declaration and proof review: unit 84

1. `normalizedMixedFamily_zero`: both ranges reduce to their single zero index, both binomial coefficients are one, and the qualified exact equation `reciprocalCoefficient.eq_1` gives `R(0,0)=g`. Thus the full family value is exactly the literal candidate, for all real arguments. No positivity is needed for this algebraic identity.

2. `normalizedMixedFamily_spatial_hasDerivAt`: the six cases `(0,0),(1,0),(2,0),(0,1),(1,1),(0,2)` exhaust `j+l≤2`. Each differentiated factor is supplied by the actual reciprocal or sine `HasDerivAt` interface, at the same spatial argument and fixed `a,z,T`. Ordinary multiplication and addition rules produce the derivative. Complete function expressions, including Pi operations, are normalized before the derivative equality is concluded. Expansion of the target finite sums supplies precisely the binomial coefficients; no pointwise equality is differentiated.

3. `normalizedMixedFamily_time_hasDerivAt`: the same six cases treat time as the varying real argument and hold both endpoints and the wall fixed. Every reciprocal predecessor order is at most two, so its stated order guard is satisfied; sine transitions are available for all orders. Product derivatives match `F(j,l+1)`, including both mixed third-order targets. `T>0` is exactly the needed reciprocal/sine analytic hypothesis.

For an independent algebra check, the first families are `F10=R00*S10+R10*S00`, `F20=R00*S20+2*R10*S10+R20*S00`, `F01=R00*S01+R01*S00`, `F02=R00*S02+2*R01*S01+R02*S00`, and `F11=R00*S11+R01*S10+R10*S01+R11*S00`. Differentiation gives `F30` with coefficients `1,3,3,1`, `F03` with the same time coefficients, `F21=R00*S21+R01*S20+2*R10*S11+2*R11*S10+R20*S01+R21*S00`, and `F12=R00*S12+2*R01*S11+R02*S10+R10*S02+2*R11*S01+R12*S00`. The spatial and time routes to each shared target agree. This checks all twelve transitions, while all physical arguments remain universally quantified.

4. `normalizedMixedFamily_spatial_iteratedDeriv`: induction starts with order zero. The successor step promotes the induction hypothesis to equality of the whole spatial functions by `funext`, rewrites `iteratedDeriv_succ`, and then uses the actual derivative transition. Arithmetic supplies the predecessor guard `j+l≤2`. This proves an actual iterated derivative rather than defining a symbol called a derivative.

5. `normalizedSineCandidate_spatial_iteratedDeriv`: whole-function equality `N=F(0,0)` follows from the zero-family theorem, after which the previous spatial induction applies at `l=0`.

6. `normalizedSineCandidate_mixed_iteratedDeriv`: induction on time order has the genuine spatial result as its base. In a successor step, the induction hypothesis holds at every positive time `S`; positivity describes an open neighborhood of the fixed `T>0`. Hence the intermediate derivative function is eventually equal to `S↦F(j,l,a,z,S,y)`. `EventuallyEq.deriv_eq` legitimately transfers its derivative, then the time transition applies. Equality solely at the point is never used as a differentiation rule.

7. `normalizedSineCandidate_mixed_commutation`: the time-first inner expression equals `F(0,l)` as an entire function of the spatial variable, using the mixed theorem with `j=0` and fixed positive time. Its actual spatial iterates equal `F(j,l)`. The space-first/time-last expression has the same value by item 6. The proof therefore covers both orders, including zero indices, without assuming commutation as a premise.

## Public declaration and proof review: unit 85

The sole definition is `C(j,l)=CR * sum choose(j,i)*choose(l,k)*CS(j-i,l-k)`, where `CR=32*sqrt(2*pi)*exp(2)` and `CS` is the qualified sine constant. The complete actual values of these constants, including the spectral constant and its Gaussian summand, were read. `CS` depends on the orders and fixed numerical pi constants; no `a,z,T,y` is hidden inside it. The fixed spectral parameter `pi²/8` is positive, and the qualified spectral/sine evidence supplies the genuine convergent-series estimate.

1. `normalizedDerivativeConstant_nonneg`: each real-cast binomial coefficient is nonnegative, every sine constant is nonnegative, and the explicit reciprocal constant is nonnegative. Two finite-sum nonnegativity steps and a product give the claim for every order, with no physical-parameter premise.

2. `reciprocal_sine_product_highTime_bound`: closed-wall/high-time hypotheses give `|z-y|/sqrt(T)≤2`; positive `sqrt(T)` converts this to the precise reciprocal drift guard. Qualified reciprocal and sine bounds are multiplied using the required nonnegativity conditions. Put `q=1/sqrt(T)>0`. The factors have scales `CR*sqrt(T)*q^(i+2k)` and `CS(p,qorder)*q^(p+2qorder+1)`. The exponent identity combines these into `sqrt(T)*q^(i+p+2(k+qorder)+1)`, and exactly one `sqrt(T)*q=1` cancels. This leaves the displayed exponent `i+p+2*(k+qorder)`. No assumption `T≥1` or extra time factor enters. The reciprocal guard is only `i+k≤3`; the sine family permits arbitrary `p,qorder`, matching the public type.

3. `normalizedMixedFamily_highTime_bound`: triangle inequalities bound both finite sums. Range membership yields `i≤j,k≤l`, hence `i+k≤3` and the exact natural-subtraction identity `i+(j-i)+2*(k+(l-k))=j+2*l`. Binomial weights are nonnegative, so the product bound can be multiplied by them. Factoring the finite sum gives exactly `C(j,l)*q^(j+2*l)`. No term is lost and no nontrivial derivative order is replaced by a zero/default value.

4. `normalizedSineCandidate_mixed_highTime_bound`: substitute unit 84's actual space-first/time-last derivative identity, then apply the family bound with identical guards.

5. `normalizedSineCandidate_commuted_highTime_bound`: substitute the qualified commutation identity from unit 84 and apply item 4. Both bounds include closed endpoints, explicit positive `a,T`, and the exact high-time threshold.

## Public declaration and proof review: unit 86

Its sole definition is `CP(j,l)=exp(4)/2*(C(j,l)+1)`. This depends only on the derivative orders and is nonnegative.

1. `normalizedProfileConstant_nonneg`: the previous nonnegativity theorem and positivity of the exponential/numeral denominator prove the literal constant is nonnegative.

2. `normalizedSineCandidate_sub_one_mixed_iteratedDeriv`: the local shift lemma rewrites `f-1` as `(-1)+f` and applies the pinned unconditional `iteratedDeriv_const_add` for a strictly positive order. If `j=0`, positive total order gives `l>0` and the time constant is removed. If `j>0`, spatial constant removal holds as a whole function for every real time `S`, before outer time differentiation. The library theorem has no differentiability or positive-time assumption; thus extending this function equality to all `S` is legitimate. Unit 84 then identifies the actual derivative at positive time. The positive-total-order guard is essential and is present in the actual type.

3. `normalizedSineCandidate_sub_one_mixed_commutation`: zero spatial or time order reduces directly. If both are positive, the same unconditional constant-removal lemma supplies both whole-function equalities. Unit 84's commutation applies with the unchanged order and analytic hypotheses. The zero-total-order case is included as a tautological equality.

4. `normalizedSineCandidate_sub_one_highTime_norm_bound`: for `j+l=0`, arithmetic forces both orders to zero. Unit 85 bounds `|N|` by `C(0,0)`, and the triangle inequality bounds `|N-1|` by `C(0,0)+1`; the time power is exactly zero. For positive total order, item 2 removes the constant and unit 85 bounds the true family by `C(j,l)*q^(j+2*l)`. This is at most `(C(j,l)+1)*q^(j+2*l)` because the power is nonnegative. Both branches prove the same stated inequality without assuming `N` lies in `[0,1]`.

5. `normalizedSineCandidate_sub_one_highTime_profile`: set `R` to the actual derivative value and `B=(C(j,l)+1)*q^(j+2*l)≥0`. The exact consumed unit 78 theorem gives `|R|≤(exp(4)/2*B)*P`. Its original-profile lower bound is `P≥2*exp(-4)` on the closed walls at `T≥a²`. Regrouping yields `CP(j,l)*q^(j+2*l)*P`. The drift factor `D=1+|z-y|/sqrt(T)` is at least one; multiplying by `D^j` preserves the inequality because both the existing coefficient and the actual profile are nonnegative. The actual profile value is precisely the sum `exp(-(a-y)*(a-z)/T)+exp(-(a+y)*(a+z)/T)`, not a substitute envelope or unrelated scalar.

6. `normalizedSineCandidate_sub_one_commuted_highTime_profile`: apply item 3 to rewrite the time-first/spatial-last actual derivative and use item 5. For positive `T`, the integer inverse-square-root scale equals the source's `T^(-j/2-l)`; the derivative-order guard and physical hypotheses remain explicit.

## Full actual ownership and generated declarations

I fully read all final source/proof bytes and the frozen imports/context/18 complete public heads/4 complete surface values, all 45 complete actual types, and all 4 complete actual definition values. Type exports are 27880/14441/20724 bytes (63045 total); value exports are 1726/1276/938 bytes (3940 total). No binder, private/generated constant, namespace, matcher or definition branch was omitted.

For the three actual type streams only, reversible textual dictionary encoding reduced repeated elaborator syntax. The entire 26-entry dictionary and all three entire encoded streams were read. Reverse substitution was checked byte-for-byte against the original UTF-8 export, including whitespace and line endings. `type-roundtrip.json` binds those exact original hashes. All four actual values were also read directly in full. Selected complete old interface types/values use the same entire dictionary with separately verified exact roundtrips in `consumed-interface-bindings.json`.

Unit 84 has nine generated theorem constants: two full definition equations, two exhaustive-six-case arithmetic facts, and five predecessor/order arithmetic facts. The complete equation types agree with the two literal definitions. The arithmetic facts have exactly the explicit natural-number guards needed by the proofs, including false conclusions only under the negation of a valid arithmetic consequence.

Unit 85 has five generated theorem constants: the exponent-addition identity, two finite-range predecessor bounds, the inherited total-order bound, and the guarded natural-subtraction exponent identity. Every complete type matches the use described above; no analytic hypothesis is encoded as a generated arithmetic fact.

Unit 86 has nine generated theorem constants: two numeral `Nat.AtLeastTwo` instance proofs and seven positivity/zero-index arithmetic facts. These cover positive successor orders, nonzero-to-positive order, and both zero indices/positive alternative for a natural sum. Their exact types add no mathematical assumptions.

The three complete `OwnedAudit.lean` programs were read. Selection uses `env.getModuleIdxFor?` and `env.header.moduleNames`, testing the exact defining module; it does not filter by namespace prefix. Every actual selected constant is passed to transitive `Lean.collectAxioms`, rejecting everything outside `propext`, `Classical.choice`, `Quot.sound`. The audit JSON owner set matches every type header exactly, and its definition subset matches every complete value header. Actual counts are derived from these sets. There are no additional constant kinds. No source contains `sorry`, `admit`, a new `axiom`, `unsafe`, or `native_decide`; no actual export contains ellipsis, `sorryAx`, or unresolved metavariables.

Each entire audit log was partitioned exactly into the fully read type stream, the fully read value stream and the fully read residual warning/count text. Residuals are 213 bytes apiece. The split covers every original log byte; no log portion was discarded. The ordinary retained mathlib-local-changes warning is not a proof error. Every complete failed/successful kernel log was read from the server. Raw logs, binaries and caches were not copied into the shared workspace.

## Freeze and original execution provenance

The narrowly selected original calls and completed results in the parent's saved rollout were read. Each original freeze AddFile payload was reconstructed as its exact UTF-8 bytes and compared to the current freeze. These complete declaration/value freezes precede implementation:

| Event, UTC 2026-10-24 | Unit 84 | Unit 85 | Unit 86 |
|---|---|---|---|
| Original freeze AddFile | line 9501, 13:54:57.790 | line 9543, 13:58:04.246 | line 9623, 14:02:44.824 |
| Freeze completion | 13:55:00.141 | 13:58:06.289 | 14:02:46.023 |
| Implementation AddFile / first kernel dispatch | line 9510, 13:55:45.692 | line 9557, 13:59:07.562 | line 9634, 14:03:32.088 |
| Final successful kernel dispatch | line 9510 | line 9557 | line 9643, 14:03:58.958 |
| Whole-owned audit dispatch | line 9519, 13:56:08.960 | line 9570, 13:59:57.721 | line 9656, 14:04:32.976 |

The rollout is `C:/Users/UIO/.codex/sessions/2026/10/24/rollout-2026-10-24T13-04-52-01a16c4c-25a6-7740-a10e-12635a13edae.jsonl`. The completed original successful results explicitly say `KERNEL_EXIT=0`, and each audit result explicitly says `AUDIT_EXIT=0` with the exact whole/public/theorem/definition counts. Successful kernel shell wrappers return 1 because a subsequent `grep` finds no `error:`; this is distinct from the recorded Lean exit 0. Unit 86's first proof attempt explicitly records `KERNEL_EXIT=1` and is retained as failed evidence.

Actual commands source `activate.sh` before changing to the designated worktree, then serialize the targeted command with `flock /root/rivermind-data/shao-lean-20261021/locks/c12-heavy.lock taskset -c 14-17 lake env lean -M8192 -j4`. Successful output objects are installed before the corresponding audit imports. Pins are Lean `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`, read-only package view `cache-overlays/shared-v34/packages`. Direct read-only observations confirm these pins, branch `author/c12-interval-reciprocal-v71`, and HEAD `c21c0b4b223f4bcb5aa9ceb0ba164ec580b332b7`. No heavy command was executed by this reviewer.

Units 84 and 85 passed their first source-bound kernels and audits. Unit 86 attempt 001's complete source-to-final diff was read with the complete final source: two proof simplifications add `Nat.zero_add,Nat.mul_zero`, and the addition inequality uses `add_le_add hN (le_refl 1)` in place of the elaborator's differently ordered addition. These are proof elaboration changes only. All heads, definition values and context are exact after removing proof bodies in both attempts. The original full failed source/log hashes remain receipt-bound. There is no changed hypothesis, constant, mathematical route or claimed source scope.

Unit 86's initial receipt-helper run encountered a Python SyntaxError before any script execution. The original failed call and completed result, the correction and its completed successful result were read. Correcting that delimiter did not execute or replay a kernel/audit and did not alter any failed-proof evidence. Original release files attest all three authors' writer/execution release with `heavyInFlight=false,inFlight=[]`; their bound receipt/source/object/freeze hashes agree with the observations.

## Qualified dependencies and standard contexts

Existing complete qualified independent evidence is reused rather than commissioning or performing another complete old-proof review. Exact report bindings checked are:

- Units 82–83: JSON `02f61ff8eb6d1cb1dc1cf2e6b32f9931229686ea935cb104265d5ad0ffd8d9cc`, Markdown `7ffab0d6650af33acc793ea2db0f94410cebc23a0e7f54ea474704a76f22c89c`, release `750b760e7c515392ebd36451db9bc598edf9289172613b797c75d9a95d1fc4ab`. The complete Markdown was read once. Source/object bindings for both producers agree with this review's direct current observations.
- Units 79–81: JSON `67ff027602b2d00ffc8d6f837d67c225be8e4084032285d50fed4c882ba0e982`, Markdown `378b10a17b8f3a3baec3a27a7132cf2066b70c864b5956fea0c4598ef839e365`, release `9946f9c9fdf51787f6ceb77027ed1faa8fd47a8682d5f610f2b69586fa66a572`. Qualified coverage/release and exact source/object/export interfaces were checked.
- Units 77–78: JSON `4ac7eab2a86ff66a801d7c477c816c3eab62f996756544d7abca6dea1c7515b0`, Markdown `aad4e09e6688d1f6cd4f698ad00ddfa60efbc91a7b0ad21439a0c8cceccba8d9`, release `a9a16050d59de8b72dc000952d525cc711a996739d3d21de6d070a46ecfc5701`. The consumed original profile values from unit 30 retain source `5e378043eccc8e052ad34ba36c8c98d143270f706d285ae1c9f8750c6a0830fc`, installed object `510d5315cd625d6d49ff71bab285b4b1a1d3e73149d94c47a757a5f43161e128`, and qualified review JSON `1fcc2466a834a04850bc45b0287058b02dd89443edbaa2dc6209b5a04d13a81f`, matching the unit 78 qualified dependency binding.

I fully read the actual consumed reciprocal spatial/time transition types, zero coefficient equation, density/family values and high-time norm constant/bound; the actual sine spatial/time transition types, series/term/frequency values and high-time constant/bound; the drift and profile-absorption types; all original profile values; and the spectral constant/summand values. These selected actual exports, complete values and current production sources/installed objects are exactly hash-bound in `consumed-interface-bindings.json`. The old reciprocal coefficient matcher and unrelated old proofs are covered by the reused qualified review; no complete old-proof requalification is claimed here.

Needed pinned standard contexts were fully read with their variable and structure assumptions: ordinary `HasDerivAt`/`deriv`, multiplication/addition and constant derivative interfaces, `HasDerivAt.deriv`, the iterated-derivative definition/zero/successor, eventual derivative equality, and the unconditional positive-order constant-add theorem plus its within-domain proof. Current relevant mathlib files were compared byte-for-byte with their pinned Git blobs, and their object hashes recorded in `standard-contexts.json`. The constant-add theorem in particular requires only positive order; it does not require global smoothness at nonpositive times. The real structures in all actual consumed types agree with these interfaces.

## Boundaries and release

No obligation is uncovered within these frozen targets. The accepted result is an analytic auxiliary formalization: actual reciprocal-times-sine mixed derivatives through total order three, their high-time norm estimates, and the original two-wall `D^j*P` scale for the analytic candidate minus one in either order. It makes no claim of new research mathematics.

Image/sine equality, actual killed-kernel equality, strict Brownian-bridge survival identification, the quotient PDE, complete compensated Taylor/hSmall and root closure remain outside this qualification. The original arbitrary-order lemma is not certified by a total-order-three result. The closed-wall bounds concern the explicit whole-line analytic sine candidate; they do not assert differentiability of a zero extension across the wall. No zero-time/zero-wall result or actual probability bound is inferred. Source scope, p54 repairs and external-result attribution are preserved. Unit 87 and later work are not reviewed here.

Writer and execution authority are released in `writer-release.json`, with no heavy command or other operation in flight. The parent may reuse this exact complete independent review together with the original successful source-bound kernel/whole-owned-axiom receipts. This completed review is not a persistent continuation mechanism.
