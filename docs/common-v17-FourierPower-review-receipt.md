# QuadraticCharacteristicPower author receipt

Status: AUTHOR IMPLEMENTATION COMPLETE; awaiting fresh independent final proof
review and coordinator acceptance of the shared iid-moment migration dependency.
This is an implementation-author receipt, not an independent correctness verdict.
Author: `/root/deletion_inequality` (authorized GPT-6.1-sol, xhigh).
Date: 2026-10-21.

## Frozen declarations and source identity

The unchanged frozen scope is

```text
drafts/c12/FourierPower-next-scope.md
SHA256 a0c19a11198fa35d63cb78ea7c066f427b2d1a91fb159f5951d5a8b0a1074943
```

Its independent declaration review was CORRECT with no changes:

```text
drafts/c12/FourierPower-declaration-review.md
SHA256 d86bc9bab7ba0983afad9d8d5dd81ffafd544f89ccaac7d5d1d573703ee4a1f2
```

The implementation has zero new public definitions and exactly the five
frozen public theorem signatures. Local and server source bytes agree:

```text
SHA256 5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8

C:/game/shao lean/drafts/c12/QuadraticCharacteristicPower.lean
/root/rivermind-data/shao-lean-20261021/workspaces/lead-c12/Shao/Probability/QuadraticCharacteristicPower.lean
```

The only author writes were this new Lean source and this separate author
receipt. No frozen scope, existing Lean source, dependency, shared import,
cache or lock was modified. All Lean API checks and compilation occurred
on the designated server; there was no local Lean execution.

## Public delivery

| Declaration | Source line | Actual content |
|---|---:|---|
| `iid_quadraticChar_power_hasDerivAt` | 125 | True first derivative of `φ(u,v)^ℓ` as the genuine sample integral `i E[S_ℓ exp(i(uS_ℓ+vQ_ℓ))]`. |
| `iid_quadraticChar_power_deriv_hasDerivAt` | 143 | True second derivative, obtained by differentiating the actual first derivative, with integral `-E[S_ℓ² exp(i(uS_ℓ+vQ_ℓ))]`. |
| `quadraticChar_power_derivative_bounds` | 358 | Bounds `sqrt(ℓV)+ℓ|μ|` and `ℓV+ℓ²μ²` for the fixed actual increment law. |
| `quadraticChar_power_derivative_scale_bounds` | 381 | With `θ≤nm2`, `n|μ|≤B`, and `ℓ≤n`, the exact bounds `sqrt(1+B²/θ)*sqrt T` and `(1+B²/θ)*T`, where `T` is literally `ℓm2`. |
| `quadraticChar_power_global_normalized` | 407 | For `θ=3/4,B=1` and every real `σ` with `|σ|=1`, actual zeroth/first/second bounds `1, 2 sqrt T, 3T` for `φ(σu,v)^ℓ`. |

All moment inputs are the frozen actual `Integrable (fun a => a^2) ν`
under the fixed probability law `ν`. The implementation adds no global
third/fourth moment, centering, bounded-support, differentiability,
positive-variance, nonzero-frequency, positive-future-length, frequency-cut
or extra normalization premise. Both `u,v` range over the entire real
plane, and the mean remains the actual integral under `ν`.

## Genuine integrability, derivative and moment payment

The true sample `S_ℓ` is L2: square-integrability of the common real law is
converted to `MemLp id 2 ν`, transported by each actual `IdentDistrib`,
then summed with the existing finite-sum L2 theorem. Probability supplies
actual L1, absolute-value L1 and square L1. All weighted exponential
integrals used in the proof are actually integrable because their real
weights are integrable and the actual real phase has norm one.

The two integral derivatives use
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on `s=univ` with
dominators `|S_ℓ|` and `S_ℓ²`. The real parameter is `u`; the fixed `vQ_ℓ`
factor does not require fourth-moment or square-energy integrability.
The original expectation is identified with the true power using the
already frozen `iid_quadraticChar_factor`. The second theorem rewrites
the actual first `deriv` at every parameter before differentiating it.

Law-only bounds use the actual canonical finite product of `ν`, with iid
and common marginal derived from `iIndepFun_pi` and
`measurePreserving_eval`. This includes the empty product without choosing
an unavailable first coordinate. The first moment is actual finite
integral linearity and actual marginal-law transport.

For the raw second moment the source directly calls the new public

```text
Shao.Probability.finite_iid_sumSquare_integral
```

It does not recreate the iid square-moment proof or introduce another
public sum convention. The private wrapper only identifies
`finiteFeatureSum` with `prefixSum` and handles the natural-subtraction
boundary at `ℓ=0`, then rewrites the accepted result as

```text
E S_ℓ² = ℓ(m2-μ²)+ℓ²μ².
```

The real variance bridge is derived from `variance_eq_sub` using the actual
L2 law, so `V=m2-μ²` is the actual variance and is nonnegative by
`variance_nonneg`. The canonical centered second moment is then obtained
through that variance bridge and the actual first/raw second moments,
giving `E(S_ℓ-ℓμ)²=ℓV`. Cauchy–Schwarz is proved from the variance identity
for the L2 real variable `|Y|`, yielding `E|Y|≤sqrt(E Y²)` with its genuine
moment integrability established first.

The drift-sensitive theorem uses
`E|S_ℓ|≤E|S_ℓ-ℓμ|+ℓ|μ|`; its second derivative uses the actual raw second
moment. For the sharper normalized theorem the proof instead uses
`E|S_ℓ|≤sqrt(E S_ℓ²)`. The private scale algebra proves from the displayed
inputs, rather than assumes,

```text
ℓ²μ² ≤ (B²/θ)(ℓm2),
E S_ℓ² ≤ (1+B²/θ)T.
```

It divides only by the explicitly positive `θ`, never by `ℓ` or `T`.
It derives the nonnegative factors needed for multiplying inequalities.
No upper normalization `nm2≤4/3` is needed for this particular payment.

For `±u`, actual scalar chain rules are established for both derivative
orders, including the two factors of `σ` for the second derivative. Their
norms reduce using `|σ|=1`. At `θ=3/4,B=1` the coefficient is exactly
`7/3`, with `sqrt(7/3)≤2` and `7/3≤3`, giving the frozen explicit constants.
No conjugation or symmetry identity is substituted for real reflection.

## Read-only dependency identity

The old frozen characteristic source stayed unchanged:

```text
Shao/Probability/QuadraticCharacteristic.lean
SHA256 8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5
```

Root supplied the shared iid-moment source and existing author-generated
artifacts to `lead-c12`; this author did not move, rewrite, compile or
fetch the dependency. The source hash was independently read on the server:

```text
Shao/Probability/FiniteIIDMoments.lean
SHA256 d2417f73424ea90a13edb10bdad267d638d66fec432c3107362a2d0246fe2bfa
```

The candidate imports only the common `Shao.Probability.FiniteIIDMoments`
entry point, never the specialized OQ5 entry point. Root reports the shared
module has seven direct Mathlib imports and no Shao project imports.
The shared migration's compatibility/consumer gates and independent final
review are coordinator-owned and were still pending when this candidate
was completed. Author target success is not reported as accepting that
separate migration or its consumers.

## Exact server gates

After sourcing `/root/rivermind-data/shao-lean-20261021/activate.sh`, then
changing to the assigned `workspaces/lead-c12`, the final exact-source gate
was:

```text
taskset -c 0-3 lake env lean \
  -o .lake/build/lib/lean/Shao/Probability/QuadraticCharacteristicPower.olean \
  Shao/Probability/QuadraticCharacteristicPower.lean
```

Result: **exit 0, stdout empty, stderr empty**, with no suppressed warnings.
Only the new target's own build artifact was produced. No whole-library
build, cache retrieval, shared cache write or unrelated target rerun was done.

A separate server `lake env lean --stdin` import checked all five exact
public signatures and printed their transitive axioms. Every public result
reported only:

```text
[propext, Classical.choice, Quot.sound]
```

The same gate enumerated every public API prefix and the new module's
private prefix, calling `Lean.collectAxioms` with a failing whitelist check
for every declaration. Generated internal declarations were included:

```text
AUDITED_NEW_DECLARATIONS 30
```

It separately audited the eight actual project semantic dependencies:

```text
Shao.Probability.quadraticChar
Shao.Probability.norm_quadraticChar_le_one
Shao.Probability.iid_quadraticChar_factor
Shao.Probability.samplePath
Shao.prefixSum
Shao.energy
Shao.Probability.finiteFeatureSum
Shao.Probability.finite_iid_sumSquare_integral

AUDITED_SEMANTIC_DEPENDENCIES 8
```

All eight also had only the accepted three axioms. Gate result: **exit 0,
empty stderr**. The server prohibited-word scan for `sorry`, `admit`,
`axiom`, `unsafe` and `native_decide` found no match in the new source.
The source sets `autoImplicit false`. The exact source hash was checked
on both server and local draft, and the frozen proposal hash was rechecked.

## Boundaries and source consumption

This implements the frozen real whole-plane input
`h:supp:powerglobal` (`supplement.tex:2614–2617`), following its actual
moment proof (`3403–3417`). Direct consumers are Region 3 at `3508–3518`
and Region 5 at `3539–3547`. The exact natural length is `ℓ=n-i` in that
application, with `T=ℓm2`; the normalization and small-bias facts must be
supplied for the source's genuine fixed conditional law.

The unnormalized results include `ℓ=0`, the zero law, constant nonzero laws
and zero variance. At `ℓ=0` the power is one, both derivatives vanish and
`T=0`; no positive-`T` shortcut was introduced. Normalized inputs imply
positive full-sample normalization; zero full sample cannot satisfy them.
The exact altered-statement counterexamples in the frozen scope still
demonstrate why the lower normalization, bounded full-sample mean and
`ℓ≤n` cannot simply be removed.

Still open: the source-specific moment specialization at cutoff `h_x`
(which is distinct from the earlier retained cutoff `1/x`), the
Gaussian-damped odd-power derivative table, actual low-frequency
variance-retention/spectral-gap damping, law-adapted cone high-frequency
noise/damping, clock probabilities, complex tilting, Fourier inversion,
oscillatory integration, and smoothing/defect payment back to the strict
CDF test `1_{q>0, |w|<t sqrt q}`. This unit neither alters those boundaries
nor claims the complete C1/C2 comparison.

Next action: fresh independent proof review of the exact candidate source
hash above, with final acceptance coordinated with the shared dependency's
separate migration gates.
