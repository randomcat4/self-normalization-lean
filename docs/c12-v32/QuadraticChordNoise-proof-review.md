# QuadraticChordNoise independent complete proof review

STATUS: **CORRECT**.

FORMAL EVIDENCE: **LEAN_FULLY_CHECKED for the exact frozen module, using the existing successful designated-server target and module-owned audit, independently rebound read-only in this review.** No successful Lean check was repeated. This accepts four definitions and four public theorems, not the complete noise Xi or C1/C2.

Reviewer: root-assigned `source_bridge_author`, never-author of this module, its helpers or its implementation receipt. Only this report was written. No mathematical source, declaration, owner state, Git branch, cache, import or manifest was edited. The frozen source remained unchanged throughout the review.

## Exact identity and source translation

| Object | Independently recomputed SHA256 |
| --- | --- |
| `QuadraticChordNoise.lean` | `75069c06d5794a5e530e99260e6e3308656623ea39944ac70f1d958ffd40d275` |
| `FourierComparison-next-scope.md` | `912c3e001bcea85a64332c9efaf530ef55f3ddc0bf055841a762468a65a5ab44` |
| `FourierComparison-declaration-review.md` | `4d65964334493503f776db43e4aa0d1daa1de8ff0e8d35fde6c2a6396109cdc1` |
| `QuadraticChordNoise-author-receipt.md` | `07e583070194cf145112497b0f84b60cdd06f3e7b6efa97c6e804617d264f8f8` |
| `QuadraticChordNoise-source-check.py` | `b775089c89b095b03a9293af350826d07ce881b6f392edc5fea9b1d34b9ae002` |
| `QuadraticChordNoise-source-check.json` | `a739fc47660ee0bb3413734f25516a6c933865b0d20262a8a0e61b6b19a9f9b3` |
| `QuadraticChordNoise-server-result.json` | `a7d86a26ee646952b0e3913ceb7b4acb8019c5f5e92530508a6994bd96df8930` |

These local paths are under `C:/game/shao lean/drafts/c12/`. The mathematical source is25,849 bytes,544 LF lines, strict UTF8 without BOM or CR. The local draft, actual server source and Git blob at commit `32fefb4c537f96071ff576db76f268e1bb9d3b4c` are identical. Server worktree `/root/rivermind-data/shao-lean-20261021/workspaces/takeover-chord-noise`, branch `author/quadratic-chord-noise`, is clean; its sole addition relative to accepted base `22a5e1f97311ad40aa49efbcfab4f5fc67a65de3` is `Shao/Probability/QuadraticChordNoise.lean`.

I independently compared the complete four definition bodies and all four public theorem headers with the frozen Lean blocks, after whitespace normalization only. All eight match. I also inspected every binder, local let, measure, variance, support predicate, zero branch and conclusion in the actual compiled source; `autoImplicit false` is retained. This type check is tied to the exact source/olean and the actual module-owned inventory. The saved audit does not print a separate `pp.all #check` transcript, and no such extra transcript or new type-check run is claimed here.

The four definitions in source lines12–29 are the genuine triangle withDensity law, the same-law independent pair biased by `(a-a')²/(2V)`, its product with an independent triangular variable pushed forward through the two-coordinate chord map, and the actual complex characteristic integral under that map law. Both chord coordinates use the same pair and triangular variable. V is the actual variance of the original fixed nu, not its raw second moment. The positive complex phase agrees with accepted `quadraticChar`.

I read the actual original `C:/game/shao/current/c12/main.tex` lines610–625,650–721 and `supplement.tex` lines1988–2042. Their independently recomputed hashes are respectively `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` and `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. Main's biasedpair/chord/Kexact/cone/gap equations match these objects and constants exactly. Supplement supplies the same single-chord support and explicitly refers the triangle characteristic and cone calculation back to main. The stronger generic law interfaces still apply to the actual fixed cutoff rho through accepted SourceTruncationBridge; no source normalization or conditioning assumption was silently replaced.

## Public proof inspection

| Public theorem | Actual lines | Verdict and essential evidence |
| --- | --- | --- |
| `quadraticTriangle_probability_char` | 165–200 | CORRECT: actual triangle mass1 and actual integral, including t=0. |
| `quadraticChord_law_data` | 250–316 | CORRECT: genuine biased/chord probabilities, AE support and phase L1. |
| `quadraticChordChar_exact` | 395–443 | CORRECT: true Q integrability, exact expectation, imaginary0 and real[0,1]. |
| `quadraticChordChar_cone_gap` | 490–542 | CORRECT: actual closed-cone comparison with constants4/9 and4. |

**The triangular law is actually constructed and integrated.** Its real density is measurable/nonnegative, equals the compact interval indicator weight and is integrable. The weighted integral is split at zero into `(1+r)g(r)` on[-1,0] and `(1-r)g(r)` on[0,1], using the actual Lebesgue interval integrals; endpoints do not create atoms. Integrating the affine weights at g=1 gives mass1. At t=0, the probability integral is exactly1. At nonzero t, the explicit affine-exponential antiderivative with z=it is differentiated at every real point, with z nonzero before division, and the interval fundamental theorem is supplied continuous/integrable integrands. The two endpoints give `2(1-cos t)/t²`, with the imaginary terms cancelling. No density or characteristic formula is assumed as an input.

**The biased pair and independent triangle have the actual source law.** The accepted `quadratic_pair_square_moment` is used with its true pair-square integrability and `integral D²=2V`. I inspected that dependency: it derives first/second integrability from raw h3, expands the actual nu-product square and uses `V=m2-mu²`; it does not assume mean zero. Positive V makes the biased density nonnegative and its integral exactly1. The normalized pair product with the actual triangle, then the measurable polynomial map, gives the actual chord probability. No arbitrary pair joint law or independent chord-coordinate premise is introduced.

Support is transferred from nu AE to its true product, then through the withDensity absolute continuity, then to the product with triangle support, then through `ae_map_iff`. Thus an AE input is never upgraded to a pointwise input. The two coordinate bounds use `|T|<=1`, `|a-a'|<=2h` and the exact identity `a²-a'²=(a-a')(a+a')`; the second keeps the stronger relation `|Y1|<=2h|Z1|`. Probability and norm1 of a real-frequency complex phase establish genuine Bochner integrability for all u,v.

**The zero branches are correct and essential.** `triangle_kernel_quotient` first splits theta=0, then D=0, then the genuinely nonzero case before clearing denominators. At theta=0, multiplying the true triangle characteristic value1 by D²/2 gives the required D²/2 branch. At theta nonzero but D=0, the true triangle input D*theta is still0, while the pair density is0, and both resulting Q contributions are0. Neither D nor theta is cancelled on its zero set. These sets may have positive original product mass for atomic laws.

The triangle kernel is nonnegative by cos<=1 and bounded by1 through the norm bound for its actual probability characteristic integral. Multiplying by D²/2 yields `0<=Q<=D²/2` everywhere. Together with measurable piecewise Q and the accepted true pair-square L1 this proves Q integrability before its use in the exact formula. The proof pulls back the actual chord integral, applies Fubini with an explicit genuinely integrable probability phase on the pair/triangle product, evaluates the triangle characteristic at D*theta, and then applies the actual withDensity integral identity. The pointwise quotient identity gives precisely `K=ofReal((integral Q)/V)`. True Q integrability is already available, so no nonintegrable totalized-zero explanation is involved. Dividing the integral bound by positive V and using integral D²=2V gives K.re<=1; the same identity gives K.im=0 and K.re>=0. This theorem needs no bounded support, fourth moment or conditional mean zero.

**The cone constants and gap refer to the same actual characteristic function.** On the actual pair support, `|a+a'|<=2h`. With h>0 and the closed cone `|v|<=|u|/(4h)`, the proof establishes `|v(a+a')|<=|u|/2`, then `|u|/2<=|theta|<=3|u|/2`. Because u!=0, theta!=0 and both square denominators are positive. The squared bounds are exactly `u²/4<=theta²<=9u²/4`. Multiplying by the nonnegative numerator and clearing only these positive denominators gives the lower4/9 and upper4 factors. The numerator N is independently L1, bounded between0 and2; Q is already L1. Both AE comparisons therefore integrate legitimately before division by actual positive V. The accepted `quadraticChar_gap_identity` supplies the same-law identity `integral N=1-||quadraticChar nu u v||²`; I inspected its genuine product-phase integrability and actual conjugate-product derivation. No factor2 remains: the pair's2V and the triangle characteristic's2 cancel in the exact formula. Neither the gap, the characteristic function nor K is inverted.

## All private source helpers

All22 private lemmas were read, not merely their uses in public statements. Every one also appears in the actual55-owned-constant transitive audit.

| Helper(s) and source lines | Inspection |
| --- | --- |
| `triangle_weight_nonneg`31–35; `triangle_weight_measurable`37–40 | Correct nonnegative measurable piecewise density. |
| `triangle_weight_indicator`42–49; `triangle_weight_integrable`51–56 | Correct closed support and continuous compact-interval integrability. |
| `triangle_weighted_integral`58–86 | Actual indicator/set/interval conversions, split at0 and correct absolute-value signs. |
| `affine_phase_integral`88–114 | Actual derivative and interval FTC, t!=0 protects z and z². |
| `triangle_density_mass`116–143 | Both affine mass integrals are1/2; complex-to-real conversion gives actual real mass1. |
| `real_density_probability`145–151; `triangle_probability`153–155 | withDensity total mass follows from true L1/nonnegative real integral1. |
| `real_density_integral`157–163 | Official measurable finite density change-of-integral theorem and correct real-to-complex scalar conversion. |
| `biased_probability`202–210; `chord_probability`212–219 | Accepted actual pair-square identity, positive actual variance, normalized product and measurable map. |
| `triangle_support`221–229; `pair_support`231–241 | Correct zero outside triangle interval and actual measurable AE product transport. |
| `probability_phase_integrable`243–248 | Real phase norm1, measurable phase and probability supply genuine L1. |
| `triangle_kernel_bounds`318–333 | Nonnegativity plus the norm bound of the actual triangle probability integral; no circular chord bound. |
| `triangle_kernel_quotient`335–344 | theta=0 and D=0 checked before nonzero cancellation. |
| `chord_quotient_bounds`346–353; `chord_quotient_integrable`355–368 | Global Q domination, measurable zero set and actual pair-square L1. |
| `chord_kernel_integral`370–393 | True map integral and integrable product Fubini; phase algebra retains both chord coordinates. |
| `cone_theta_bounds`445–473; `cone_quotient_bounds`475–488 | Correct closed cone, theta nonzero and squared positive-denominator comparisons. |

The local priority selection `attribute [local instance 2000] NormedSpace.complexToReal` chooses the pinned official restriction-of-scalars normed space. I read its definition in `Mathlib/Analysis/Complex/Basic.lean`: `NormedSpace.restrictScalars ℝ ℂ E`. It is not a new mathematical object or an extra axiom and does not change the real/complex phase or density meaning.

## Boundary and quantifier attacks

- At u=v=0, Q=D²/2 everywhere, so the actual pair-square identity gives K(0,0)=1. The implementation does not substitute default0 for a zero quotient.
- Noncentered and atomic nu are allowed. The fair law on{0,1} has V=1/4, positive original diagonal product mass and bounded h3. Its off-diagonal biased chords satisfy Y1=Z1. At u=1,v=-1, theta vanishes on those chords and K=1; this is correctly admitted by the exact theorem and correctly excluded from h=1 cone. The implementation never adds symmetry, density or nonatomicity.
- Single-chord K is not asserted to be even in u alone. The same{0,1} example has K depending on u+v. The later two-family Xi symmetry is not smuggled into this unit.
- For a fair law on{-a,a}, a>0, with v=0,u=pi/a, the true characteristic gap and K both vanish while the cone is satisfied. The proof permits this resonance: no positive-gap, nonzero-characteristic or nonzero-D premise is used.
- The cone is closed in v. Its endpoints still leave |theta|>=|u|/2>0, so the constants and division arguments remain valid for equality. Only the final cone theorem excludes u=0.
- V=0 is explicitly excluded where biased-law probability is asserted. The total definitions outside that premise are not certified as source probability laws. A zero cutoff is likewise excluded in the cone/support public input; no hidden centered or full-moment condition is added.

## Existing actual server evidence, independently checked read-only

All nine files bound by server `logs/takeover-chord-noise/result.json` were rehashed directly and agree with the receipt, including actual source, empty target log, audit source/log, ordinary own olean, pins and both direct source dependencies. The local saved result is byte-identical to that server result. No build/check/API probe was launched by this reviewer.

| Server artifact | Recomputed SHA256 |
| --- | --- |
| `check013.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `audit.lean` | `764d8d2bf0dd6572c2bdd63a70027d51ea329adc6fb0e50ae7b7abda68f7ac85` |
| `audit001.log` | `2dbbe3d01e5b97942dac7e278bec0b59029089502cfb5c086c9e7bc65e7f8148` |
| `result.json` | `a7d86a26ee646952b0e3913ceb7b4acb8019c5f5e92530508a6994bd96df8930` |
| own `QuadraticChordNoise.olean` | `a11b4c8c4638f5692916b5bbe9b6c395480fd1144e898119160aab40c0458341` |

These log paths are under `/root/rivermind-data/shao-lean-20261021/logs/takeover-chord-noise/`; the olean is under the isolated worktree's `.lake/build/lib/lean/Shao/Probability/`. The recorded final target and audit exits are both0; check013 has exactly zero bytes/no diagnostics. The target emits a new ordinary own olean; it is not an inherited symlink. The author command explicitly places this worktree first on LEAN_PATH, and the existing audit imports that actual compiled module. Accepted predecessor outputs are read-only individual links to v28. No rejected intermediate target is substituted for check013.

The raw audit was independently parsed, rather than accepted solely from its summary. It contains190 unique imported Shao declarations and55 unique target declarations repeated in the target subinventory. The actual owner counts are FinitePath67, FiniteIID8, QuadraticCharacteristic30, LowFrequencyDamping30 and QuadraticChordNoise55. Thus190 includes the target55 and135 predecessors. Target55 comprises4 definitions and51 theorem constants:4 public+22 explicit private+25 generated. All22 private source names match the actual module-owned private names, with none missing. Every raw axiom list in both inventories is restricted to `propext`, `Classical.choice`, `Quot.sound`; all four additional public `#print axioms` results have the same whitelist, with no sorryAx. This is actual ownership through `env.getModuleIdxFor?`, not a public/namespace-only audit.

The complete actual Shao source closure has five files. All four predecessor blobs were compared directly with the accepted base and are unchanged:

| Source | SHA256 |
| --- | --- |
| `Shao/Probability/LowFrequencyDamping.lean` | `ffdeace2421a3c0fdf63def48eb96b882f9dc98014e5614d226a07f87a02bb65` |
| `Shao/Probability/QuadraticCharacteristic.lean` | `8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5` |
| `Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| `Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |

The only new direct Mathlib import is pinned `Analysis.SpecialFunctions.Integrals.Basic`. Actual `lean-toolchain` is `leanprover/lean4:v4.36.0-rc1`, SHA `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`; recorded compiler commit is `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`, Lake5.0.0-src+c9afcdd. Actual Mathlib Git HEAD and manifest revision agree at `807d3836b165983210ee2ecf3cd28f239436949c`; its tracked diff is empty. Manifest SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`. Shared packages resolve to the designated existing package directory. New source contains no occurrences of sorry/admit/axiom/unsafe/native_decide, even before excluding comments/strings. No pin, dependency-source or ownership mismatch was found.

## Acceptance boundary

CORRECT for exactly the four frozen definitions and four frozen theorems at source SHA75069c06…d40d275, with the complete helper proofs and existing actual kernel/axiom evidence above. No mathematical, source-to-statement, type-interface or evidence-binding critical gap was found. The reviewer has not rewritten any proof and has not issued an author self-review.

Root's own import/manifest/whole-library integrated ownership gate and merge are still required. Two families of J=8 copies, the independent smooth scalar law, the complete Xi product/symmetry/support/moment formulas, K/Xi derivatives, gap optimization/high-frequency damping, smoothing/Fourier inversion and time/region integration, strict-CDF desmoothing and C1/C2 remain separate open obligations. No conclusion here changes those root statuses or claims research novelty.
