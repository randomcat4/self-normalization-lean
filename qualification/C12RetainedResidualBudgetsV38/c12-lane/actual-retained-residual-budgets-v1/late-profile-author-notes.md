# Unit199 static late complete-suffix Gaussian profile author

Status: STATIC_COMPLETE_CANDIDATE; Lean, server execution and transitive axiom audit NOT_RUN. This is a source-production handoff, not an independent correctness verdict or mechanical acceptance. The parent retains full-module integration and later qualified independent source/proof review and exact-source server gates.

The only produced Lean declaration is the exact frozen private `arr_late_fixed_suffix_gaussian_bound`. All supporting facts are local `have` expressions. The frozen public prefix, declarations, imports, options and instances were not changed. No source outside the five assigned author files was written.

## Input provenance

- Frozen private head: `frozen-private-late-profile-head.lean.txt`, SHA256 `8d04b524636212b600bb5ce2bc7c207c1427e3747712e20139d91864e5f3f9b2`, 1339 bytes, UTF-8 LF. The candidate head before ` := by` is exactly the frozen head with its final LF removed.
- Exact context: prefix of `frozen-public.lean.txt`, SHA256 `9aa1ce015f0a6128b404b428dce988d84f6f9e261fb002d85f9e907ba9c0f81c`. The imports, options, namespace openings and local label-permutation measurable-space instance were read. The candidate introduces none of those constructs.
- Qualified public all-q strip: `actual-bad-interval-negative-budget-v1/ActualBadIntervalNegativeBudget.lean`, SHA256 `fe7d4311610d46c9ec948450d3f75fb6621d05fc9978414431122f2e6e44a794`; complete public head and its one-line export proof at lines1770–1788 were read. The task binds its parent qualification to `bb37f5bdd599090fc0d6bb0e3b1182cb2c66c91ce5940fd3706cbbdfd7d473e6`. The implementation consumes only `Shao.C2.ActualBadIntervalNegativeBudget.actual_large_x_true_energy_closed_strip`, no private producer name.
- Qualified generic Gaussian CDF/profile contract and complete proof were read in `library/Shao/Probability/SourceTrueWallProfile.lean`, SHA256 `c22326bc59064fcabc05de2c718bc13b7e1ed47b0e753b587eaa475b7e745449`. Its `gaussian_wall_profile_of_quadratic_closed_cdf` has no upper restriction on x.
- Exact carrier, first label, prefix-survival and singleton Gaussian definitions plus full bounded-measurability contract were read in `library/Shao/Probability/SourceIIDGaussianProfileBudget.lean`, SHA256 `44960de7f98cd219860b8619b8f07ecfc52369a678fcb73331d8c9838ce1b8c7`. Its existing `fixed_suffix_weighted_gaussian_integral` supplied the implementation pattern for bounded genuine integrability and constant extraction; its x≤1 theorem is not invoked.
- Exact `suffixD` definition was read in `library/Shao/Probability/SourceMarkedSuffixAveraging.lean`, SHA256 `879023fb756a2b6ea31fea61ffe159ffe6053aa94221302d1f09a4e2762e01c9`. The full label-square/suffix-geometry implementation patterns used here were read in `SourceTrueWallProfile.lean`.
- The complete needed unit196 conditional-profile argument, lines143–228 of `theory-actual-late-omitted-retained-v1/full-proof-candidate.md`, was read. Its accepted parent record binds proof SHA256 `d51c4a8281888a287d1f9fbc98672d437b0ad80bdcb4da9270873e61235db4ec` and independent report SHA256 `8c6a6e936e90f90117f7b4362f3b645c4911452fc2a9a13be920650623e90035`. This author does not re-review those older producers or claim their receipts validate this new candidate.

## Complete mathematical derivation

Choose Cs>0 from the qualified large-x true-energy closed strip before introducing rho or any later parameters, and choose the new universal C=9Cs. For every frozen set of input parameters let Pr=rho^r, T=energy(u), b=firstValue(u), d=prefixSum(u,t), and D=suffixD(u).

First obtain genuine L1 integrability of F. The qualified `fixed_gaussian_weight_measurable_bound` makes the joint function of (v,u) measurable and gives the pointwise bound

    |F(v)| <= card({s}) (1+sqrt(t))^3.

Compose with the measurable map v↦(v,u), and dominate by that constant on the probability measure Pr. This establishes `Integrable F Pr` before any integral bound, with no use of Lean's totalized integral on a nonintegrable function.

If not (0<T and H<=T), the transparent definition of `fixedGaussianWeight` makes F identically zero. The target W is also zero, so the conclusion follows exactly. This includes T=0 and an empty suffix; no positive-length assumption has been added.

In the selected branch T>0, H<=T, define

    wall(v) = x sqrt(T+energy(v)),
    A = {v | maxWithZero(s • v) < wall(v)},
    w(v) = wall(v) - s prefixSum(v,r),
    M = |b| + max(s d,0),
    profile(v) = exp(-(max(w(v)-M,0))^2/T).

The wall and gap are measurable, and A is measurable by the strict inequality between measurable functions. M>=0. The singleton `prefixSurvival` is exactly membership of A. The singleton sum in `gaussianProfiles` contains one exponential. Thus the carrier has the exact identity, for every v,

    F(v) = [|b|^3/(T sqrt(T)) D^3] (A.indicator profile)(v).

The complete suffix is fixed throughout. Its first actual label b remains in T, d and M, and no label is deleted, permuted or redrawn.

For every a>=0, a point of {v∈A | w(v)<=a} satisfies the public strip's closed survival condition because strict survival implies closed survival. The terminal prefix sum is one of the prefix sums controlled by `maxWithZero`; hence s prefixSum(v,r)<=wall(v). The other inequality wall(v)-a<=s prefixSum(v,r) is exactly w(v)<=a. Therefore this entire closed sublevel set is a subset of the qualified public closed strip with q=T and width a. The hypotheses r<=n and n<=2r follow from n=r+t and the frozen late-rank assumption. All original distribution, support100, mean0, variance1, n>0 and x>=16 hypotheses are passed directly to that producer, with no symmetry premise for s=-1.

Its bound is Cs(a+beta)^2/r. Since (a+beta)^2<=2(a^2+beta^2) and r>0,

    Pr.real {v | v∈A and w(v)<=a}
       <= (2Cs) [a^2/r + (beta/sqrt(r))^2].

The identity (beta/sqrt(r))^2=beta^2/r uses r>0. Apply the qualified generic Gaussian CDF/profile theorem with K=2Cs, B=beta/sqrt(r), V=r, T=T, M=M. It gives

    integral(A.indicator profile)
       <= (Cs/r) [4M^2+4T+2beta^2].

For geometry, b^2<=T is proved directly by the nonnegative energy sum when t>0, and by b=0 when t=0. Hence |b|<=sqrt(T). The selected definition gives D=1+|d|/sqrt(T), so D>=1. Either permitted sign satisfies s d<=|d|, and therefore

    0<=M<=|b|+|d|<=sqrt(T)+|d|=sqrt(T)D,
    M^2<=T D^2.

The threshold assumption supplies 4beta^2<=H<=T, and D^2>=1 implies T<=T D^2. Consequently

    4M^2+4T+2beta^2 <= 9 T D^2,
    integral(A.indicator profile) <= 9Cs T D^2/r.

The fixed coefficient |b|^3/(T sqrt(T)) D^3 is nonnegative. Extract it from the integral using the exact carrier identity, multiply the profile bound and cancel only T>0, sqrt(T)>0 and r>0. The resulting expression is

    (9Cs/r) [|b|^3/sqrt(T) D^5] = (C/r) W.

No division by b occurs, so b=0 is covered. The strict survival event is retained in the exact carrier identity and enlarged only for the upper probability bound. The CDF uses a closed sublevel, so atoms or equality at gap=a require no null-boundary claim. The Gaussian profile still has max(gap-M,0), and no sign or strict-gap substitution is made. No residual-smallness, Brownian measure, stopping index or conclusion-shaped premise is consumed.

## Static checks and remaining acceptance

Deterministic checks establish exact frozen-head equality, UTF-8 with zero CR bytes, exactly one global declaration and zero occurrences of the forbidden proof constructs. Those checks do not establish Lean elaboration or kernel correctness. The source has not been sent to the server, built, imported, axiom-audited or published. The parent must integrate the snippet under the exact frozen prefix, obtain a qualified independent complete review of the final source, and obtain its source-bound server kernel and recursive axiom receipts before acceptance.

Model accounting: requested gpt-6.1-sol/xhigh; actual backend/model/effort and input, cached input, output and reasoning-subset counts are not observable in this author context and are recorded as null, without a subscription percentage estimate.
