# Actual prefix-energy weighted regulators — independent final review

STATUS: **CORRECT**.

The exact frozen five public declarations, their entire new implementation,
all fifteen named private proofs and all thirty-five actual module-owned
theorem types (including fifteen generated declarations) have been independently
reviewed. No critical gap, changed assumption, missing integrability premise or
unpaid clock premise was found. This is an exact-source correctness verdict for
the scope below; it makes no novelty, survival, second-moment-decay or C1/C2
closure claim.

Reviewer: `/root/common_weighted_regulator_review`, fresh `gpt-6.1-sol`,
`xhigh`, never an author of this module, no subagents. The reviewer changed no
production source, frozen declaration, dependency, cache or proof. Reviewer
Lean invocations: **0**. The original successful server kernel and unique
all-owned transitive-axiom evidence were inspected and reused.

## Exact binding and declaration fidelity

Module: `Shao.Probability.SourceLindleyRegulatorEnergyWeighted`.
Server worktree: `/root/rivermind-data/shao-lean-20261021/workspaces/common-centered-characteristic-v44`;
branch `feat/common-centered-characteristic`.

| Item | Exact value |
|---|---|
| Commit | `f1cd24313487008ceae325eff12fc0f1fdbf3118` |
| Parent | `e32108dc19228e38d09f8a704a0dbaf58777181e` |
| Tree | `c1f9d8465975c17cf95298c895e78ab95a15057c` |
| Source SHA256 | `02be93da25b2c532192060bb9a38d895975dd11d72e1351d4f74c583856cabfa` |
| Original successful object SHA256 | `7e9324adb02ed9eb409313e6e64869262712e997631a8a506d7a7124a2f8edcc` |
| Root declaration freeze SHA256 | `6752fe876ac480866306938e02acc42fe57561d9326f71a57f52c5992fe69648` |
| Complete candidate SHA256 | `8b7e0972e68c2aa53efd1cd7dd4379b72588a2ecfb74d6e397eb4e4288ab29ed` |
| Complete source contract SHA256 | `ad78d4bc40e9b47933e4812b77f54c318e4f6aa834fa87fda6f82c9f7793954f` |
| Author receipt SHA256 | `012858105577e309e58417141240feee1d1e9ae5483e7742d484f138943ca141` |

The local source, server source, `attempt05.source.lean` and committed Git blob
have the same source hash. The commit changes only the one owned production
file. All 788 source lines were fully read. Bytes are UTF-8 without BOM, LF
only, 38275 bytes. Every complete public head, parameter, assumption,
conjunct and literal let binding was read, and independently found verbatim in
both the frozen candidate and root freeze. There are no syntax addenda and
zero new global definitions. The source contains none of `sorry`, `admit`,
`axiom`, `unsafe`, or `native_decide`.

## Original source and reused interfaces

The original read-only C12 source was checked directly: `main.tex` SHA256
`beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`,
lines 373–383, 544–565 and 638–640; `supplement.tex` SHA256
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`,
lines 462–535, 570–595 and the complete weighted argument 2238–2339.
The implemented objects are the original reflected recursion
`W_0=0`, `W_j=max(0,W_(j-1)+A_j)`, its actual negative reflection regulator,
and `Q_j=sum_(k<=j) A_k^2`. Zero-based `i : Fin N` is paper time `i.val+1`.

Only the needed complete upstream signatures and definition values were
consumed. Qualified unchanged upstream proofs and their successful checks
were not commissioned again:

- `BoundedQuadraticTilt`, commit `5e1a6a7fef2121bc0208798f7a0678975b44a0e9`,
  source `93c302d9de61bc4bf0cb238e82a4ed5b7f66e0ddbd2e833fec5bc6bbb25a8257`,
  object `cd1e326090a3fce3ecab7d8b38c14d7239c6b4fcedb600f8bb8dffb14d3dc2ec`.
  The qualified fresh independent complete review is CORRECT, report hash
  `3f6c037bdecb6b989040a013fe8575eac35073923b986edc22be355823c44ec8`.
  Its actual energy law, probability, finite second moment, variance upper
  bound, nonzero-mean bound and all-natural-power normalizer decay exactly
  match the consumer's arguments. The old candidate's pending-review wording
  is historical; that prerequisite is now discharged.
- `SourceLindleyRegulatorFirstMomentSums`, commit
  `e32108dc19228e38d09f8a704a0dbaf58777181e`, source
  `e0e850c95578ec741669b56acfb3721e34cc8c6f5684a8aee316f7ab1ce59fbf`,
  object `7c36447ba87dc2d4c1a41d3445cfca6fa1ff2841b6b99172d41ab9e1c6aa8f43`.
  Its qualified fresh complete CORRECT report hash is
  `7bee368009de467a924d81047ce64d07c7273fdf7ef6c0b28339b682cbc7b8f6`.
  The consumed prefix theorem needs only probability and the actual second
  moment's integrability, and retains actual mean and variance.
- Accepted `Shao.OQ3.iid_quadratic_sample_tilt`, source
  `b27ee727239ca0c31db3e3f04275eae1a13813adb1f1749edb564749df7d9bda`,
  is used with `(0,-s)` on the actual prefix, with its genuine exponential
  integrability/MGF-domain input paid in the new proof.
- Accepted `SourceTruncationBridge`, source
  `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1`,
  supplies the actual conditional probability law, AE support, raw moments,
  variance bounds and paid mean/third-moment inequalities under the exact
  original normalization and cutoff budget.

The actual values of `Path`, `prefixPath`, `lindleyState`, `lindleyRegulator`,
`prefixSquares`, `energy`, `truncationBudget`, and `bivariateMGFDomain` were
read. All 24 installed project dependency objects and their recorded source
references match the root dependency map. The exact accepted
`Mathlib.Analysis.Complex.ExponentialBounds` source/object also match its cache
receipt; no cache fetch, import smoke or proof rebuild was performed.

## Complete proof review

1. **Prefix identity and genuine change of measure, lines 14–264.**
   State induction proves chronological prefix agreement. The energy proof
   supplies a genuine bijection of prefix coordinates with the filtered long
   coordinates. The fixed injective inclusion `Fin m -> Fin N`, actual iid
   coordinate evaluations and their true coordinate laws prove the prefix
   projection measure preserving under both long product laws. Here
   `m=i.val+1`; future coordinates have probability mass one.

   The pointwise bound `0<=U<=|a_i|`, measurable recursion and transferred AE
   support dominate every natural power by `h^r`. Thus both actual product
   laws give genuine L1 of the powers. The measurable positive weight is at
   most one, so its own L1 and the weighted powers' L1 are proved before the
   expectation identities. The coordinate exponential is genuinely
   integrable and has strictly positive integral `Z`; the actual tilted
   coordinate law is a probability and inherits support by absolute
   continuity. The accepted product-tilt theorem is applied on the prefix,
   giving precisely `Z^m` and the actual prefix product of tilts.
   `integral_tilted`, the nonzero `Z^m`, and the two measure-preserving prefix
   transports give the literal long-law r=1 and r=2 identities and
   `integral W dP=Z^m`. No claim identifies the full prefix-tilted long measure
   with the full product of tilts; equality is justified only for the actual
   prefix-dependent observable. No full-path `Z^N` is substituted.

2. **Single-time weighted first moment, lines 267–322.**
   The actual energy tilt supplies a probability law and genuine second-moment
   integrability, so the accepted prefix first-moment theorem applies to that
   same law on the long product. Monotonicity of square root gives
   `sqrt(V_rho)<=B`; the mean estimate gives `|mu_rho|<=M`, with
   `B=sqrt(exp(s*h^2)*V)` and `M=|mu|+2*s*exp(s*h^2)*m3`.
   The new r=1 identity is multiplied by the scalar normalizer decay using
   the nonnegative actual tilted first moment. This proves the displayed
   weighted expectation with actual L1. Centering, symmetry, a positive
   variance or survival estimate is not assumed.

3. **Both finite clocks, lines 324–451.**
   For arbitrary weights in `[0,1]`, cumulative masses satisfy `C_k<=k`.
   Factoring the difference of their square roots proves
   `w_k/sqrt(k)<=2*(sqrt(C_k)-sqrt(C_(k-1)))`, including zero cumulative
   mass; only the positive integer-time denominator is divided out. Summing
   proves `H<=2*sqrt(G)`. Separately, `1+alpha<=exp(alpha)` telescopes to
   `alpha*G<=1-exp(-alpha*N)`, hence `t*G<=N`. Together with `G<=N`, this
   proves `G<=2*N/(1+t)`. Squaring the nonnegative half-clock inequality
   and using `(1+sqrt(t))^2<=2*(1+t)` yields the exact
   `H<=4*sqrt(N)/(1+sqrt(t))`. `N=0` is discharged before cancellation.
   No clock, monotonicity, integral comparison or decay estimate is a premise.

4. **Actual finite sums, lines 454–559.**
   Each genuine integrable weighted regulator is summed under the same
   actual long base product law. The finite-sum integral exchange is explicit.
   Nonnegative `m2`, `B`, `M` pay the signs. For `N>0`, the exact identity
   `t/N=s*m2/2` matches the clock exponent, giving
   `4*B*sqrt(N)/(1+sqrt(t))+2*N*M/(1+t)`. The empty sum is handled
   separately. Every initial restriction is an integrable nonnegative
   subsum pointwise below the full sum. Thus this is a bound on the integral
   of the actual random sum, not merely a formal list of expectation symbols.

5. **Original conditional-law specialization, lines 564–786.**
   The law is literally `cond nu0 {a | |a|<=epsilon/(1+x)}` with explicit
   original base centering and `N*integral a^2 dnu0=1`; no zero conditional
   mean is asserted. The original budget and threshold window pay its
   probability, AE support, `N*m2>=3/4`, `N*V<=4/3` and `s*h_x^2<=1`.
   Writing `a=1+x`, `b=1+y`, `A=N*|mu|`, `D=N*m3`, the proof uses
   `b<=2*a`, `epsilon^2*a*A<=2*R` and `a^3*D<=2*R` to derive
   `Lambda<=4*R/epsilon^2+16*R<=epsilon/2+2*epsilon^3<=1/2`.
   The literal Lambda is nonnegative and its smallness is a conclusion.

   With `s=kappa*y^2`, `exp(S)<=exp(1)<3`, the proof pays
   `B*sqrt(N)<=2`, `t>=(3*kappa/8)*y^2`,
   `1+sqrt(t)>=(sqrt(kappa)/2)*(1+y)` and
   `N*M<=7*Lambda/(1+y)`. The two actual generic-sum terms are at most
   `16/[sqrt(kappa)*(1+y)]` and `7/[sqrt(kappa)*(1+y)]`.
   The frozen coefficient 128 is a valid relaxation of 23, and subsums
   inherit it. Every `0<kappa<=1/16` is covered; the constant explicitly
   depends on `1/sqrt(kappa)` and is not uniform as kappa tends to zero.

All fifteen private source proofs have complete type/proof coverage: state
nonnegativity/bounds/measurability; regulator and energy measurability;
state/energy prefix agreement; prefix measure preservation and integral
transport; AE regulator bound and power L1; coordinate exponential L1;
weighted half-clock and geometric telescope. All fifteen generated actual
types were read in full: the MGF-domain equation, finite-sum distributivity,
filter/universe membership equations, three natural-bound obligations, and
the eight elementary nonzero/arithmetic/associativity clock simplifiers.
Their scopes agree with the actual source uses and introduce no hidden
mathematical premise. Per-declaration exact type hashes, full log line
ranges and recursive axiom arrays are in the JSON companion.

## Kernel, axioms and execution provenance

The original target `attempt05` and the original unique `OwnedAudit.lean`
commands were read in full. Each activates the pinned environment, changes
to the assigned worktree, and runs under `root-heavy.lock`, `taskset -c 10-13`,
`-M8192 -j4 -DautoImplicit=false`. The shell captures `rc=$?` immediately
after the actual check, before writing its direct exit. Both direct exits
and both raw return exit codes are 0. The successful target log was fully
read and contains only warnings. Lean is pinned to
`leanprover/lean4:v4.36.0-rc1`; mathlib HEAD is
`807d3836b165983210ee2ecf3cd28f239436949c`.

| Original server artifact | SHA256 |
|---|---|
| `attempt05.command.txt` | `b84cea912864495dd1d74b0fcaf0dfc783759c8aea501bb3ff779f3f5080c839` |
| `attempt05.log` | `cf3e73e0d042a8a2436e879069aecc395e02291db3a360080ded4d40895fec0f` |
| `attempt05.response.json` | `bf3adc516f1bc1599548628867915d70273530f7ec56f5d9f8206260a26a6897` |
| `owned-audit.command.txt` | `1170edfb31117049c4b359754634baa04bae2a66e1aac3ac0609eb7848397775` |
| `owned-audit.log` | `37d141ff73e8530875be59b6104f466254a87d687981ad5b9f7923fdeea7c26d` |
| `owned-audit.json` | `5063c7718cfe92145ca156073986df386f39b600f5c298240133040a313be9c9` |
| `owned-audit.response.json` | `2ced9f4625499a74789db1a7c191cf39de98716533959b53f4b06674be80e1fd` |

The entire audit program was read: its selection is `getModuleIdxFor?` equal
to the exact target module, across every environment constant, including
private/generated constants, and `Lean.collectAxioms` is transitive. Its
complete full `pp.all` types were read directly from the original server log,
without truncation. The 35 declaration names/types equal the 35 manifest
names and 35 recursive-axiom rows; all are theorems, with 5 public and 0
definitions. Thus definition-value coverage is vacuous, rather than omitted.
Every axiom array is a subset of `propext`, `Classical.choice`, `Quot.sound`.
The 115963-byte original log has no truncated type marker or missing row.
All artifact hashes agree with the author receipt; failed attempts 01–04,
their source/command/log hashes and direct exits 1 remain preserved on the
server. There was no successful-check replay. Raw logs remain server-only;
local review artifacts contain hashes, coverage and compact inspection data.

## Boundaries, accepted scope and release

The generic heads cover `s=0`, zero variance, zero raw moments, first time
`i.val=0`, and noncentered/nonsymmetric bounded laws. No variance denominator
occurs. Empty clocks and generic total sums cover `N=0`; per-time heads have
no inhabitant `i : Fin 0`. The source normalization excludes `N=0` on its
own. `K=0`, `K=N`, the half-time `K=N/2`, `t=0`, `y=1`, and the stated
closed upper cutoff/parameter boundaries are included. All divisions in the
new inequalities have their needed positivity/nonzero facts proved.

Accepted scope: genuine prefix L1 and r=1/r=2 change of measure, unconditional
weighted first moments, both proved finite clocks, actual full/initial sums,
and the first source weighted inequality with explicit
`128/(sqrt(kappa)*(1+y))`. Actual source survival, unconditional or weighted
regulator second-moment decay, the second original weighted inequality,
growing/complex kernels, inversion/desmoothing and all original root groups
remain OPEN. No new result is attributed to this module where the argument
consumes a qualified upstream theorem. Novelty was not assessed.

Review complete; reviewer write authority and slot released after writing
this report and its JSON/checkpoint. No Lean or remote operation is in flight.
Next dependency belongs to root: reuse this exact-source review plus the
original kernel/all-owned receipt for acceptance/publication/integration,
checking interactions without commissioning an unchanged proof replay.
