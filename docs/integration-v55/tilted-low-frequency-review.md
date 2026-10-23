# Independent review: actual joint tilt and low-frequency powers

STATUS: CORRECT

Reviewer `/root/common_tilted_low_review`, actual model `gpt-6.1-sol`, reasoning
effort `xhigh`, fresh context and never author of this new module. This review
uses math-theorem and the current streamlined acceptance rules. I read the
entire 489-line new source, complete proof note and source contract, both
complete frozen public heads with every let, and all six actual owned printed
types and their complete recursive axiom arrays. No mathematical assumptions
were changed. There are no blocking issues.

## Exact version and declaration freeze

- Module: `Shao.Probability.TiltedLowFrequency`.
- Commit `6dbd8394e336af1da55d6bf7c3d3bc3fd87f6a49`, parent
  `5e1a6a7fef2121bc0208798f7a0678975b44a0e9`, tree
  `b2dfc49db7517998dedecf100c05fcebbdf6476d`.
- Server worktree
  `/root/rivermind-data/shao-lean-20261021/workspaces/common-short-kernel-v51`,
  branch `feat/common-short-time-kernel`; observed clean. This commit changes
  only `Shao/Probability/TiltedLowFrequency.lean`.
- Source SHA256 `10f1dfeed068fa5f521b220f5f5d138992603dae5447dd034da0462ef44dd159`;
  object SHA256 `88ea15f9e3843de4131adeb345cf71829d9de6a2949faf0578d21e8a5de0bb1e`.
- Freeze SHA256 `72d46d31c25cc10f25902ca59e4f26362988b77bcbf6086f6f7aa818e0694ccb`;
  candidate SHA256 `17a8eb7e8cd61d1bd1896da2d1074fd304b1edccaf5dbd7627faa729b192c1a0`;
  source-contract SHA256 `253e77e48ee9add3b8ddb472d4ece3eb042cf3b8fcbf4ec78e9e19d96f4ad3d7`.

Both complete public heads are literal matches for both the root freeze and
candidate, including all 11 and 15 lets respectively. Their actual elaborated
types have the same quantifiers, original-law hypotheses, actual measures,
moments, clocks, conditional comparison and two complex-power conclusions.
There are exactly two public theorems and zero new global definitions. The
24,037 source bytes are UTF-8 without BOM, LF only, with a terminal LF. The
source scan finds no sorry, admit, new axiom, unsafe or native_decide.

## Complete new-proof review

1. Lines 11–22, `tlf_power_integrable`: actual almost-everywhere support
   bounds each signed/absolute natural power in norm by the integrable
   constant `h^k` under the probability measure. Measurability and norm bounds
   are supplied. This provides genuine L1 moments.
2. Lines 24–67, `tlf_raw_root`: the ordinary variance identity gives
   `0<V<=m2`. For `t=sqrt(m2)`, integrating the nonnegative factor
   `(|a|-t)^2*(2|a|+t)` yields `t*m2<=m3`. Mass one and `t^2=m2` are used
   correctly. It follows that `m3>0`, `gamma=m3/V>0`,
   `sqrt(m2)<=gamma`, and `m2<=gamma^2`. Every cancellation uses positive
   variance; no division-at-zero or undefined-integral shortcut occurs.
3. Lines 69–185, `tlf_mean_comparison`: from `|mu|<=V`,
   `m2<=(8/3)V`, `sqrt(V)<=gamma` and `m3=gamma*V`, the three terms in the
   mean numerator are bounded by
   `[gamma+(8/3)*lam*gamma+s*gamma^2]*sqrt(V)`. The variance lower bound
   gives `sqrt(V)<=exp(2lamh)*sqrt(Vrho)`, so the total multiplier is
   `exp(6lamh)` times this bracket. With `Gamma=8exp(8lamh)*gamma`, it is at
   most `Gamma/8+lam*Gamma/3+(lam*Gamma)^2/64`. For
   `k=(y+lam)*Gamma<=1/8`, `y>=2` gives `Gamma<=k/2` and
   `0<=lam*Gamma<=k`; the multiplier is at most
   `k/16+k/3+k^2/64<1`. All order multiplications have nonnegative factors.
   This proves the actual tilted mean and its squared bound under exactly
   the displayed smallness antecedent. No extra bound on `lam*h` is assumed.
4. Lines 188–315, generic public theorem: `nV>=1/2` pays `n>0`, `V>0`,
   while the other scaled assumptions pay `|mu|<=V` and `m2<=(8/3)V`.
   The exact qualified joint-tilt producer supplies probability, support,
   actual finite moments, actual own-mean variance identity, mean estimate,
   variance comparison and tilted third-moment ratio. Applying the new
   Lyapunov helper to this same tilted law proves
   `sqrt(m2rho)<=Gamma` and `m2rho<=Gamma^2` without Gamma-smallness. Under
   the explicit antecedent, the actual variance identity then gives
   `Vrho<=m2rho<=2Vrho`.

   For damping, the actual positive `gr=m3rho/Vrho<=Gamma` pays both
   accepted frequency restrictions by denominator monotonicity. The
   accepted theorem bounds each actual `quadraticChar rho (±u) v` by
   `exp(-Vrho*u^2/32)`. `norm_pow`, monotonicity of natural powers and
   `exp_nat_mul` prove the power estimates. The inequalities
   `exp(-4lamh)*m2<=(8/3)Vrho` and
   `exp(-4lamh)*m2/128<=Vrho/32` give precisely the stated exponent with
   denominator 128. This branch never uses the comparison-smallness
   antecedent. Natural power zero is included, with both sides one.
5. Lines 318–487, source public theorem: the measure is literally
   `cond nu0 {|z|<=epsilon/(1+x)}`, and only `nu0` is centered. The accepted
   law/variance/moment interfaces apply because
   `epsilon<=epsilon0/2<=1/2` and the literal original budget is present.
   They pay `3/4<=n*m2<=4/3`, `nV>=1/2`, and
   `n|mu|<=2R/(epsilon^2(1+x))<=epsilon/[4(1+x)]<=1/2`.
   The original half-window gives `1+y<=2(1+x)` and hence the actual
   cutoff `epsilon/(1+x)<=h=epsilon0/(1+y)`. The gamma interface gives
   `0<gamma<=2h_x<=2h<=2/3<=y`.

   The clocks are the actual `T=(n-i)*m2`, `N=q+T`, with
   `0<=T<=4/3` and `N` in the original interval. `N>=1/16` pays
   `sqrt(N)>=1/4`. For `r=y/sqrt(N)`, the assumptions give
   `0<=r<=lam` and `r<=4y`. In the nonzero s branch,
   `s=lam*r<=lam^2` uses the first bound; independently
   `s*h<=4lam*y*h<=lam` uses the second and the explicit `yh<=1/4`.
   Thus both indispensable guards are actually proved, not conflated.
   The generic theorem is applied to this same conditional law and exactly
   the natural power `n-i`. The `i=n`, `T=0` case is retained. Unused `hi`
   and `hq` preserve original context and create no extra restriction or
   false positivity claim.

## Source fidelity and qualified dependencies

I fully read original supplement 2700–2741 and 3551–3625, the conditional
moment notation and bounds at 463–531, and the low-frequency argument at
3147–3191, together with original main normalization/cutoff/budget,
epsilon/eta choices at 372–383 and half-window at 638–640. Original source
hashes match the frozen contract: supplement
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`, main
`beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`.
The source original uses raw absolute third moments and own-mean variance;
the new module preserves both. Its constants realize original absolute
constants explicitly. The `s*h` guard is the explicit payment of original
sufficiently small `yh`. The `T>=L2*gamma^2` restriction belongs to later
Fourier-region arguments and is unnecessary for this stronger local damping
conclusion.

I consumed the complete unchanged heads of
`boundedQuadraticTilt_joint_moments_normalizer`,
`quadraticChar_lowFrequency_damping`, `sourceTruncation_law_data`,
`sourceTruncation_paid_moments`, `sourceTruncation_variance_bounds` and
`sourceTruncation_gamma_bounds`, and the actual definition values of
`quadraticChar`, `truncationF` and `truncationBudget`. In particular, the
characteristic function is its actual complex exponential integral, and the
budget is `n*integral (z^2*min |z| 1)` at the original scaled variable.

All consumed library source hashes match the accepted v54 source map and the
remote consumer worktree. The upstream joint-tilt source/object are exactly
`93c302d9de61bc4bf0cb238e82a4ed5b7f66e0ddbd2e833fec5bc6bbb25a8257` /
`cd1e326090a3fce3ecab7d8b38c14d7239c6b4fcedb600f8bb8dffb14d3dc2ec`.
Its independent complete CORRECT review is qualified and hash-bound at
`3f6c037bdecb6b989040a013fe8575eac35073923b986edc22be355823c44ec8`.
I reuse that qualification; I did not re-review old full proofs or replay
accepted old checks.

## Original server execution and every owned declaration

I read the original successful check02 and audit request/return files, exact
commands, raw target log, direct exit receipts, audit source and all target
owned-type/axiom log blocks. The server artifacts and local compact copies
match. Check02 directly compiled the entire exact new source into the
identified object, then immediately retained its direct Lean exit 0; its log
contains warnings only. The earlier failed check01 is preserved. The
subsequent single owned audit also directly exited 0. Neither successful
Lean command was repeated by this reviewer.

Both original commands use the shared `root-heavy.lock`, CPU10–13,
`-M8192 -j4 -DautoImplicit=false` in the pinned environment. The observed
toolchain file is `leanprover/lean4:v4.36.0-rc1`; mathlib HEAD is
`807d3836b165983210ee2ecf3cd28f239436949c`.

The audit selects by the actual environment module owner and recursively
calls `Lean.collectAxioms` for each selected constant, rejecting every axiom
outside `propext`, `Classical.choice`, `Quot.sound`. I read every actual type
and full array, not merely their counts:

| Owned declaration | Actual type/proof coverage | Recursive axioms |
|---|---|---|
| private `tlf_power_integrable` | Complete signed/absolute natural-power L1 type and source proof | all three allowed |
| public generic theorem | Complete actual type, all lets and full source proof | all three allowed |
| private `tlf_raw_root` | Complete positive variance / raw third / root and square type and source proof | all three allowed |
| private `tlf_mean_comparison` | Complete scalar type with every hypothesis and source proof | all three allowed |
| private `tlf_mean_comparison._simp_1_1` | Complete generic semigroup associativity type `a*(b*c)=(a*b)*c`; kernel-checked generated helper | empty |
| public source theorem | Complete actual type, all lets, source payments and full source proof | all three allowed |

Thus the actual owner has six constants, all theorems: two public, three
named private helpers and one generated theorem. There are zero definitions,
so definition-value coverage is vacuous. The separate public axiom printouts
also match the allowed arrays. No uncovered actual owned declaration remains.

Durable originals remain server-only under
`/root/rivermind-data/shao-lean-20261021/outputs/common-tilted-low-frequency/`.
Target-log SHA256 is
`f854ab4c87bb0df9a719ec6ccd039dc6585c7ddf1d03f13d1a5793afcd746dee`;
owned-type/axiom-log SHA256 is
`c4871aa19affcc427aa9e301cc5ac8e049475c0d3b6af08790cef06cc17d1cc9`.
Per-file and per-owned-type bindings are in the companion review JSON and
`drafts/c12-tilted-low-frequency/review/` compact verification artifacts.

## Accepted scope and release

This exact module qualifies for the original joint-tilt part (c) moment
comparison with its explicit smallness antecedent, actual tilted raw-second
root/square bounds, and both true low-frequency characteristic powers at the
stated constants. It supplies an actual original-source corollary, rather
than taking any tilted moment, conditional centering or decay conclusion as
an input. It makes no new mathematical novelty claim.

Later prescribed-lambda/eta0 payment of `(y+lam)*Gamma<=1/8`, complex contour
shifts and growing amplitudes/kernels, iid product-law applications,
survival/Spitzer, unconditional weighted regulator second moments,
microclock/large-displacement probability budgets, desmoothing and original
C1/C2 remain OPEN. Arbitrarily large allowed lam does not automatically pay
the comparison antecedent. This review does not merge or close a root theorem.

Review complete; review write authority and reviewer slot released. Production
source, shared cache and other owners' files were not mutated. Reviewer Lean
invocations: zero. No reviewer tool or server operation is left in flight.
Next dependency for root: exact-source acceptance/publication and then the
still unpaid prescribed-lambda/complex growing-kernel source frontier.
