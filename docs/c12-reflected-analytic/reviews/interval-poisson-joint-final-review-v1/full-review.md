# Independent final review: units 76, 87, 110 and 111

STATUS: CORRECT

These four exact source versions have complete independent source-to-statement and proof review. Their frozen targets are proved, with no critical gap and no uncovered declaration in the assigned scope. The existing successful server kernel and recursive whole-owned-axiom evidence is qualified for reuse. This review does not close a C1/C2 root theorem or identify either analytic series with the actual Brownian interval survival or killed heat kernel.

Reviewer: `/root/interval_poisson_joint_final_review`, a fresh context independent of author `01a16c4c-25a6-7740-a10e-12635a13edae`. The prescribed delegate configuration is `gpt-6.1-sol` / `xhigh`. Independent runtime model, effort and token telemetry are not exposed; actual telemetry fields and input, cached-input, output and reasoning-subset counts are null. No subscription-percentage inference is made. The related unit 111 was added by the parent while this same independent review was running; the reviewer gave no proof advice and made no production edit.

The sole write scope is this review directory. All production sources, freezes, old evidence, curated library, server, Git and shared cache were read-only. There were no Lean invocations, axiom-audit replays, producer recompilations, remote writes, cache mutations, children, sidebar chats, Goals or schedules. Python bytecode was disabled before review-script imports. There is no heavy or other execution in flight from this reviewer.

## Exact versions and coverage

| Unit | Module | Public source theorems | Actual owned theorems | Generated theorems | Non-theorem owners |
|---|---|---:|---:|---:|---:|
| 76 | `Shao.C2.IntervalImageJointDerivatives` | 4 | 7 | 3 | 0 |
| 87 | `Shao.C2.IntervalGaussianCosinePoisson` | 4 | 11 | 7 | 0 |
| 110 | `Shao.C2.IntervalImageSineIdentity` | 2 | 9 | 7 | 0 |
| 111 | `Shao.C2.IntervalImageSineProfiles` | 4 | 6 | 2 | 0 |
| Total | | 14 | 33 | 19 | 0 |

All four final sources, complete freezes, source-and-proof notes and all 78,726 bytes of full actual owned type exports were read. No type was elided, sampled or truncated in the completed reading. The raw exports, rather than a dictionary or a pretty-printer summary, were used. The initial combined tool output that truncated part of a failed kernel log was followed by a complete dedicated read of that log. Every actual type name matches its exact defining-module owner map; generated and any private or differently namespaced constants are selected by module ownership, not a textual namespace filter. Every map entry is a theorem. Each complete non-theorem value export is exactly zero bytes, so there is no omitted value, opaque declaration, axiom or other kind of owned constant. Local proof `let` expressions were covered in the complete proof-source reading.

The four `OwnedAudit.lean` programs use the same established template, with only the target/import, public-name array, expected public count and output path changed. They traverse `env.constants`, resolve each defining module with `getModuleIdxFor?`, and invoke `Lean.collectAxioms` on every owner. No private/generated-name exclusion occurs. The full pinned `Lean/Util/CollectAxioms.lean` implementation was read: checked constant types and values are traversed recursively, and imported entries are transitively precomputed against the private environment. Its SHA256 is `b39bd22253a76816ee6d24284e69674d0b491be343fd71f9ee9376833d1485f6`. All 33 rows use only `propext`, `Classical.choice`, and `Quot.sound`. No sorry/admit/new axiom/unsafe/native_decide occurs in the four source files.

The full JSON report contains a source-proof assessment for every public theorem and a complete per-owned-name type hash, axiom list and review assessment. The supporting binding files retain exact local and remote paths and hashes. Current live imported objects, archived objects and final source snapshots all agree with the author receipts.

## Original source and accepted meaning

The read-only original is `C:/game/shao/current/c12/supplement.tex`, whole-file SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. Lines 4192–4398 were read in full. The source defines the Brownian completion quotient, gives the interval image exponents at 4255–4282, uses the sine representation for high-time estimates at 4284–4297, and requires genuine differentiation and compensated Taylor arguments at 4298–4315. The later projection and local-envelope obligations were also read and are not inferred from this batch.

The analytic candidate has the original image exponents and ordering: `A_m = 8m²a² + 4ma(z-y)` and `B_m = 2(y+(2m+1)a)(z+(2m+1)a)`. Qualified existing source-to-statement reviews cover the finite-plus-tail implementation and its convergence. The consumed actual candidate values and derivative interfaces were read completely. The normalized sine candidate is the literal sine series multiplied by `sqrt(2π) * sqrt(T) * exp((z-y)²/(2T))`; it is not an arbitrary function satisfying a desired property.

Unit 76 establishes strict joint spatial/time differentiation of the analytic mixed image family for any spatial order and time order `l ≤ 2`, at positive time, an interior start and a closed terminal endpoint. It also establishes the actual first chain rule along `(y+θb, T-θb²)` at every valid current point. Units 87 and 110 establish genuine Gaussian/cosine Poisson summation and the exact analytic image/sine equality. Unit 111 transfers genuine iterated derivatives and the existing high-time bounds for total order at most three to the analytic image candidate. No premise is changed or silently supplied.

## Unit 76 proof review

`mixedImageCandidate_hasStrictFDerivAt` is correct. The product set `(-a,a) × (0,∞)` is an actual neighborhood of `(y,T)`. On it, the qualified spatial derivative exists with time order `l ≤ 3`, and the qualified time derivative exists with `l ≤ 2`. The required derivative functions are jointly continuous: their orders are `(j+1,l)` and `(j,l+1)`, and `l+1 ≤ 3` follows from `l ≤ 2`. The continuous linear isometry `toSpanSingletonLIE` sends the scalar derivative to the correct continuous linear map. The complete pinned `FDeriv.Partial` source and proof were read. Its hypotheses exactly require these neighborhood partial derivatives and their continuity at the point; they yield strict differentiation of the uncurried function with the coproduct map. Spatial coordinate first and time coordinate second are consistent throughout.

`intervalImageCandidate_mixed_hasStrictFDerivAt` is correct. The true iterated derivative and the explicit mixed family agree throughout the same open product neighborhood by the existing source-bound theorem. `congr_of_eventuallyEq` is used with the required orientation, from the explicit mixed function to the true derivative expression. This does not differentiate an equality known only at one point.

`mixedImageCandidate_path_hasDerivAt` and `intervalImageCandidate_mixed_path_hasDerivAt` are correct. The two affine coordinates have derivatives `b` and `-b²`. Their Fréchet product derivative, followed by composition with the joint derivative, gives the coproduct evaluated on `(b,-b²)`. The scalar derivative is the resulting continuous linear map applied to one. The complete pinned product/composition, scalar/Fréchet conversion, congruence and singleton-evaluation contexts were checked. Expansion gives exactly `b * F(j+1,l) - b² * F(j,l+1)` at the displaced space/time point. The proof covers arbitrary signs of `b`, including `b=0`, and arbitrary `θ` satisfying the displayed pointwise validity hypotheses. It needs no global segment hypothesis for this local derivative claim. It makes no assertion of a two-sided derivative at a wall.

The three generated arithmetic theorems are exactly the contradictions expressing `l≤2 ⇒ l≤3` and `l≤2 ⇒ l+1≤3`. Their complete actual types and recursive axiom lists were read.

## Unit 87 proof review

`complex_gaussian_quadratic_summable` is correct. Positive real part of `a` makes the real part of the coefficient `-πa` negative. The pinned complex quadratic decay theorem supplies a little-o estimate against `|x|^-2` on the cocompact filter. The integer embedding tends from cofinite to cocompact, and the integer inverse-square majorant is genuinely summable. `summable_of_isBigO` uses an eventual bound, so the finite exceptional point at zero causes no issue. The full composition is normalized before applying the result. The claim allows arbitrary complex linear coefficient `b`, which Gaussian decay dominates.

`shifted_gaussian_summable` is correct. Set `A=1/(πc)`, `B=-u/(πc)`, and `K=exp(-u²/c)` in the complex summability result. Under `c>0`, `Re A>0` and both denominators are nonzero. The complete-square identity is exactly `K exp(-πA n²+2πB n)=exp(-(n+u)²/c)`. Constant multiplication, pointwise congruence and the real-embedding summability equivalence establish the real series, independently of the later Poisson identity.

`gaussian_cosine_summable` is correct. With `A=πc` and `B=-iu`, the real part of the summable complex exponential is precisely `exp(-π²c n²) cos(2πnu)`. The phase has negative imaginary sign, removed by cosine evenness. Real-part summation is invoked on a proved complex `HasSum`, not on an unjustified total sum.

`shifted_gaussian_cosine_poisson` is correct. The complete pinned Gaussian Poisson and Fourier Poisson sources/proofs were read, including the Fourier-Gaussian transform context. The classical theta theorem at `A=πc`, `B=-iu` has `iB=u` and transformed exponential `exp(-(m+u)²/c)`. The full positive-real complex-power branch conversion was checked: `(πc)^(1/2)` is the real positive square root embedded in ℂ because `πc>0`. Its inverse cancels only after nonzeroness is proved. Both complex sums are genuinely summable before taking real parts; the shifted real and cosine real summability theorems are already established. Taking real parts yields the claimed orientation and factor `sqrt(πc)`. There is no use of a default value of a non-summable `tsum`.

All seven generated field-simplifier theorem types were read: nonzero numerals two, three and four; a nonzero product; nonzero natural powers under the displayed reduced-monoid hypotheses; nonzero integer powers in a group with zero; and a characteristic-zero successor cast. Their explicitly quantified premises are ordinary algebraic helper premises discharged in the application. They introduce no premise into a public target and no new axiom. The theta transformation is classical Mathlib input, not a claimed new mathematical result.

## Unit 110 proof review

`periodGaussian_eq_integer_cosine` is correct. The substitution is `c=T/(8a²)>0` and shift `u/(4a)`. The literal periodic Gaussian `exp(-(u+4ma)²/(2T))` and cosine term `exp(-π²T n²/(8a²)) cos(πnu/(2a))` match term by term. The coefficient `sqrt(2π)*sqrt(T)/(4a)` is nonnegative, and its square is `πT/(8a²)`; the positive-wall assumption prevents an omitted absolute value in the square-root identity. These equalities and unit 87 give the whole sum formula. The series are summable, independently of the equality: unit 87 supplies this for arbitrary shift after the displayed term identities, and the consumed cosine/image interfaces supply it on the later closed-endpoint application.

`intervalImageCandidate_eq_normalizedSineCandidate` is correct. The qualified image periodization gives the difference at shifts `z-y` and `z+y+2a`, multiplied by `exp((z-y)²/(2T))`. The new periodic Gaussian identity multiplies this difference by `sqrt(2π)*sqrt(T)/(4a)`. The qualified sine/cosine identity is exactly the same difference scaled by `1/(4a)`. Unfolding the existing reciprocal free density and normalized sine candidate therefore gives equality by scalar algebra. Both original image shifts, the minus sign and every factor are preserved. The allowed endpoint assumptions are closed for both `y` and `z`; the proof uses the already qualified closed-endpoint periodization rather than silently enlarging a convergence domain.

The seven generated algebraic helpers have the same complete forms as the corresponding field-simplifier helpers in unit 87 and were separately read in their exact owner export. No value or additional theorem is hidden from ownership coverage.

## Unit 111 proof review

`intervalImageCandidate_spatial_eq_normalized` is correct. At an interior start, unit 110 gives equality on a genuine open spatial neighborhood. The pinned `EventuallyEq.iteratedDeriv_eq` theorem applies to that local equality, and the already qualified sine spatial derivative identity gives the stated family value. No pointwise-only substitution is differentiated.

`mixedImageCandidate_eq_normalized` is correct. Total order at most three gives both `j≤3` and `l≤3`. For every nearby positive time, the first theorem and qualified normalized spatial identity identify the two actual spatial derivative functions. Their eventual equality in time transfers the `l`th derivative. The existing true-image mixed iterated-derivative identity and normalized mixed identity then give the claimed equality of literal families. The order is spatial derivatives followed by time derivatives, exactly as frozen. The complete pinned locality proof and necessary iterated-derivative contexts were read.

`mixedImageCandidate_highTime_bound` is correct. It rewrites the actual image family by the preceding equality and applies the qualified normalized bound with total order at most three, positive time, `a²≤T`, and both endpoint bounds. The start is deliberately retained as interior. It does not require the large-time inequality on a neighborhood because only the identity is differentiated; the estimate is applied at the final point.

`intervalImageCandidate_sub_one_highTime_profile` is correct. It forms eventual equality after subtracting one on each open spatial neighborhood, transfers the spatial derivative, forms eventual equality on the positive-time neighborhood, then transfers the time derivative. The resulting expression is exactly the already qualified normalized image-minus-one profile target. `normalizedProfileConstant`, the inverse-time power, `(1+|z-y|/sqrt(T))^j` and `intervalProfile` are unchanged. The `+1` allowance in the existing constant is an analytic subtraction allowance for order zero; no assertion that an analytic candidate is between zero and one is used. The two generated arithmetic helpers merely derive `j≤3` and `l≤3` from the frozen total-order bound.

## Frozen chronology and all attempt deltas

The selected completed parent-session events were inspected narrowly, with exact call IDs and timestamps retained in `selected-session-events-current.json` and `gate-provenance.json`.

| Unit | Substantive complete freeze completed UTC | First separate implementation UTC | Server attempts |
|---|---|---|---|
| 76 | 2026-10-24 12:57:42.837 | 2026-10-24 13:03:14.009 | 001 fail, 002 fail, 003 pass; audit pass |
| 87 | 2026-10-24 14:10:44.364 | 2026-10-24 14:12:32.548 | 001 fail, 002 pass; audit pass |
| 110 | 2026-10-24 16:29:41.276, complete freeze printed/written before the later administrative exception | 2026-10-24 16:30:17.293 | first 001 pass; audit pass |
| 111 | 2026-10-24 16:34:33.099 | 2026-10-24 16:35:16.136 | first 001 pass; audit pass |

For 110, the frozen command's `StopIteration` comes after writing and printing the complete freeze and its exact hash, while searching checkpoint metadata. It precedes proof implementation, changes neither freeze nor source, and is preserved as an administrative failure. The later checkpoint correction is not treated as a new mathematical freeze.

Units 76 and 87 were initially local unchecked drafts waiting for absent pinned standard objects. There was no accepted old kernel gate to replay. The sole root cache writer's export is `coordination/root-cache-exports/c12-standard-20261024.json`, SHA256 `f33015021c7f5149a0c1b9ebd807dfccfb0663a3d9c04692ad5914f5f0d5a794`. The exact Partial, Gaussian Poisson and Fourier Poisson source/object pairs match the current lead view. Source pins are unchanged. The new gates occur after actual availability; the lane did not compile standard modules or write the shared cache.

The complete saved final/failed sources are covered by the fully read final sources plus the complete source deltas, and every saved kernel log was read. Unit 76 attempt 001 exposes implicit uncurrying inference, the orientation of strict derivative eventual equality, scalar derivative instance/normalization, and use of the Fréchet product/composition APIs. Attempt 002 has both strict joint heads established, with the two scalar chain rules remaining at evaluation of `toSpanSingleton` at one. Attempt 003 adds that exact evaluation in both places and succeeds. All changed lines are proof-local; all four frozen heads and the context remain exact.

Unit 87 changes only the proof-local normalization `Function.comp_apply` to `Function.comp_def` between 001 and 002. This unfolds the whole composed function and preserves the mathematical summability argument. The four heads, imports and context are exact. Units 110 and 111 have no failed mathematical attempt or source revision. Known cached-checkout, deprecation and style warnings remain in the saved logs; no error is accepted as a successful result. The transport process exit is distinguished from the explicit inner `KERNEL_EXIT` or `AUDIT_EXIT`. All seven kernel and four audit outcomes are tied to their actual completed source-bound commands.

All Windows-created Lean source bytes are UTF-8 without BOM and with LF line endings before their first source gate. Historical freeze bytes and receipts were preserved.

## Dependency and server evidence reuse

Twelve consumed defining modules have exact qualified independent complete reviews. Their current source, archived successful object, live imported object, actual-type export and value export bindings were checked and all match. The read consumed interface bundle contains 25 complete actual types and 13 complete direct transparent values. Deeper already reviewed implementation proofs are reused at their exact hashes, without another automatic full-proof review. Unit 87's otherwise unused `IntervalSineHighTimeProfiles` import and unit 111's retained joint-derivative import remain exact and bound.

The reused review hashes are recorded per module in `qualified-dependency-reuse.json`. In particular, units 73–75 use `interval-image-mixed-taylor-final-review-v1` at `6a67306b468a608e24b8a4c852b55604c545e983be097ad27861fe0708c015ba`; normalized units 84–86 use `interval-sine-normalized-final-review-v1` at `71466d2ba666cb176a2e0a4044f4f42adf2623ec41987fbb68e895229d96a276`; cosine 88 uses `7f22a48e356e7460e2fdce2bf9ec4eaf9afb4a4ee1796a3a5a9b01e2b0afd27a`; periodization 89 uses `fdfc150aad772fd64d069843d0043693b12ccb79e6c877d912cea5dbcb441a31`. The source hash for each consumed type/value export agrees with its successful receipt and qualified review. All required parameter domains and function argument orderings were checked at consumption.

The observed branch is `author/c12-interval-actual-v71`, HEAD `bbc54578517f47ce0c12736189cf91208a299290`; publication may later advance the branch without changing the certified bytes. The actual toolchain file is `leanprover/lean4:v4.36.0-rc1`, and the actual Mathlib checkout revision is `807d3836b165983210ee2ecf3cd28f239436949c`. The accepted object view is `cache-overlays/shared-v34/packages`. Original source, snapshot, archive object, live imported object, freeze, receipt, audit script, owner map, type/value exports and every saved attempt artifact bind exactly. The author gate commands use the C12 lock, CPU14–17, native `-M8192 -j4`, after activation and worktree selection. The reviewer did no heavy execution.

Review helper failures were administrative read-only failures: one malformed remote hash-query dictionary, one malformed source-excerpt string, an absent remote `rg` followed by Python scanning, and an initial session-selector mismatch before selecting the actual custom-tool event type. Their available failure responses remain in this directory or the tool transcript. None wrote remote state, executed Lean, changed mathematical content, or invalidated existing source-bound evidence.

## Remaining scope and decision

The four frozen units are CORRECT and their exact-source kernel/all-owned-axiom evidence is reusable. The Poisson identity is classical and attributed; this is an analytic formalization and assembly result, with no novelty claim beyond that work.

Still open in this review's original source scope: identifying the actual Brownian interval survival/killed kernel with these analytic image/sine candidates; the full compensated Taylor/Gaussian remainder and `hSmall`; source-wide actual interval regularity and one-sided wall-trace obligations not already paid by a separately qualified result; and all original root-group obligations. The new high-time analytic derivative transfer does not discharge those separate claims. OQ3 remains paused by the human. Existing p54 repairs and external-result attribution are retained. No global root closure is claimed.
