# Actual prefix-energy weighted regulators — source contract

State: `CANDIDATE_COMPLETE_NOT_FROZEN_NOT_PROVED`.
This records a candidate and its complete mathematical proof route. It is
not a compiler receipt, an independent review or acceptance of the pending
tilt producer. Only this lane's candidate directory is owned or written.

## Original source and mapping

Read-only `C:/game/shao/current/c12/supplement.tex`, SHA256
`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.
Read-only `C:/game/shao/current/c12/main.tex`, SHA256
`beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`.
Line numbers below refer to the actual files. Neither original source was
edited. The relevant full regulator source, including the unproved
survival-dependent portion, was read; the claimed new scope is narrower.

| Source lines | True claim/object | Candidate payment and boundary |
|---|---|---|
| main 373–383 | `0<ε0≤1`, `ε≤ε0/2`, `η(ε)≤ε^3/8` | Bundle 4b exposes `ε0≤1`, `ε≤ε0/2`, and the weaker consequence `R≤ε^3/8`. Strict original `R<η(ε)` implies this input. |
| main 638–640 | comparison threshold `y≥γ`, `|y-x|≤1/[2(1+x)]` | Bundle 4b uses this exact window and the weighted lemma's `y≥1`. It needs no additional `y≥γ`; omitting that unnecessary condition strengthens the auxiliary conclusion without altering the source law. |
| supplement 470–475, 523–531 | actual conditional mean, raw moments, variance, `Λ_y`; moment and budget scales | All quantities in 4b are literal integrals/variance of `cond ν0 {|a|≤ε/(1+x)}`. Accepted `SourceTruncationBridge` pays the probability, support, `3/4≤N*m2`, `N*V≤4/3` and two budget bounds. No zero mean is assigned to this conditional law. |
| 574–578 / 2137–2174 | actual cyclic first-moment argument | Reuse the exact accepted actual prefix first-moment theorem. No survival estimate is needed for this first moment. |
| 2176–2214 / second parts of 577–578 | true survival estimate and second-moment decay | **Not paid here.** Bundle 1's `r=2` is only a change-of-measure identity and L1 claim. |
| 2238–2245 | `s=κy²`, positive real `Z_s`, actual energy-tilted law | Bundles 1/2 use literal `ν.tilted (fun a => -s*a²)`. Bundle 4b substitutes `s=κy²` under the original conditional law. |
| 2246–2249 | actual threshold pays `(1+y)h_x≤ε0`, `s h_x²≤1` | Bundle 4b proves this from the exact threshold window, `ε≤ε0/2`, `ε0≤1`, and explicit `0<κ≤1/16`. No tilted probability assertion is made from an unverified normalizer. |
| 2250–2274 | normalizer, variance and mean comparisons, nonzero original mean retained | Pending frozen `boundedEnergyTilt_drift_decay` provides the exact `exp(±s h²)` variance factor and `|μ_s|≤|μ|+2s exp(s h²)m3`. These give the literal `B,M` in bundles 2/4a. |
| 2275–2285 | tilted drift/survival and first/second moments | First moment follows directly from the accepted generic cyclic bound applied to the actual tilt. Survival and second-moment decay remain **OPEN**. |
| 2287–2291 | `U_i,Q_i` see only first `i` samples; `E[U_i^r exp(-sQ_i)]=Z_s^i E_s U_i^r` | Bundle 1 proves genuine prefix agreement, measurability, base/tilted L1 for `r=1,2`, true weight L1 and normalization, equality of long tilted/prefix tilted moments, and the exact identity under the same actual long base law. |
| 2292–2298 | `Z_s^i≤exp(-s*m2*i/2)` and the source `exp(-c*s*i/N)` | Frozen energy producer supplies the scalar power inequality; bundle 2 actually multiplies it with the nonnegative true first moment. Bundle 4b pays `c=3/8` using `N*m2≥3/4`. |
| 2300–2311 | insertion into the two weighted sums | Bundles 2/4a pay the first-moment sum only. No weighted second-moment sum is asserted. |
| 2313–2326 | two deterministic clocks and integral comparisons | Bundle 3 proves the same rates with explicit constants `4` and `2`, by finite telescoping. The original integral comparison is replaced by a complete discrete proof, not introduced as a premise. |
| 2327–2332 | quantitative first weighted total after source variance payment | Bundle 4a gives `4B√N/(1+√t)+2NM/(1+t)`, `t=s*m2*N/2`. Bundle 4b pays its original parameters, with constant `128/sqrt(κ)`. |
| 2333–2339 / 588–592 | `Λ_y` absorption and restriction to half-time; weighted lemma | Bundle 4b proves the stronger full-time first sum and every initial restriction, including `K=N/2`. It derives `Λ_y≤1/2` directly from the original cutoff budget. The original second weighted inequality remains **OPEN**. |

## Exact upstream interfaces

1. `Shao.Probability.SourceLindleyRegulatorFirstMomentSums`, complete author
   source `drafts/c12-regulator-first-moment-sums/SourceLindleyRegulatorFirstMomentSums.lean`,
   SHA256 `e0e850c95578ec741669b56acfb3721e34cc8c6f5684a8aee316f7ab1ce59fbf`;
   commit `e32108dc19228e38d09f8a704a0dbaf58777181e`; object SHA256
   `7c36447ba87dc2d4c1a41d3445cfca6fa1ff2841b6b99172d41ab9e1c6aa8f43`.
   Complete fresh review is `coordination/common-regulator-first-moment-sums-review.md/json`,
   `CORRECT`. Consume `iid_lindleyRegulator_prefix_first_moment` under
   the actual energy-tilted probability law. No source or check is replayed.
2. Its accepted predecessor
   `library/Shao/Probability/SourceLindleyRegulatorFirstMoment.lean`, SHA256
   `c2dcdb409763ba20386e064e6a8ed612bf060677da80442c727289ffc7ab3108`.
   The last-step first-moment bound uses actual mean and actual variance,
   without symmetry, zero drift or positive variance assumptions.
3. Pending `Shao.Probability.BoundedQuadraticTilt`: root freeze
   `coordination/public-bounded-quadratic-tilt-declaration-freeze.md` freezes
   all three complete heads in
   `drafts/c12-bounded-quadratic-tilt/candidate-declarations.md`, SHA256
   `8cfbe112eff7822ae646f978b5eba52575e142fb81abf4e59798647861b3fcdd`.
   The exact energy head provides genuine L1, probability, transferred
   support, tilted second-moment integrability, variance and nonzero-mean
   bounds, positive `Z`, and `Z^i≤exp(-(s*m2/2)*i)` under `s*h²≤1`.
   Bundle 1 can use the general density theorem at `b=0` without that
   smallness condition. The producer is not yet accepted: its completed
   exact-source kernel/axiom receipt and independent complete review are a
   mandatory dependency gate for accepting the consumers.
4. `library/Shao/OQ3/QuadraticSampleChangeOfMeasure.lean`, SHA256
   `b27ee727239ca0c31db3e3f04275eae1a13813adb1f1749edb564749df7d9bda`.
   `Shao.OQ3.iid_quadratic_sample_tilt` proves actual product exponential L1,
   `Z^m` normalization and the literal equality of actual tilted product
   and product of actual coordinate tilts. Set `theta=(0,-s)` on the
   **prefix of length `m=i.val+1`**. Bounded support pays the actual
   bivariate MGF-domain condition. Do not re-prove or rewrite that old
   product theorem. Its cell-event theorem is not a substitute for the
   actual `U/Q` identity and is not needed here.
5. `library/Shao/Probability/SourceTruncationBridge.lean`, SHA256
   `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1`.
   `Shao.sourceTruncation_law_data`, `..._variance_bounds` and
   `..._paid_moments` use the exact same source conditional law as bundle
   4b, with the same cutoff budget. The source-law base centering is
   explicit in 4b and is not transferred to the conditional law.
   `SourceClockBridge.sourceTruncation_conditioned_sample` is the existing
   original-sample/all-coordinate-cutoff adapter to this product law when
   a later consumer works on an arbitrary sample space. This module does
   not replace its assumptions with an abstract expectation symbol.

## Complete mathematical route

This section supplies a concrete proof design for root's declaration
freeze. It does not authorize production writing or certify the result.

### Bundle 1: true prefix and exact change of law

Put `m=i.val+1`, and let `p` be the chronological prefix projection.
Induction on the actual recursion gives equality of its reflected states
with those on `p a`. Consequently

`U(a)=lindleyRegulator(p a,last(i.val))`,
`Q(a)=prefixSquares(a,m)=energy(p a)`.

Each is measurable: the state is built from zero, coordinate addition and
`max`; energy is a finite sum of coordinate squares. The pointwise bound
`0≤U(a)≤|a_i|` gives `0≤U≤h` AE under either actual long law. The tilted
support comes from the true one-coordinate tilt's absolute continuity.
Every `U^r` for `r=1,2` is thus dominated by the integrable constant `h^r`
under both genuine probability laws. `Q≥0` is pointwise, so
`0<exp(-sQ)≤1`; its L1 and the weighted powers' L1 follow without any
moment-decay premise.

The actual iid coordinate evaluation family, followed by the fixed
injective chronological inclusion `Fin m→Fin N`, makes `p` measure
preserving from the base long product to the base prefix product. The
same holds from the long product of the actual tilts to the tilted prefix
product. This can be proved locally with the already established iid
sample-map API; the accepted first-moment producer's private prefix proof
is not a public imported theorem. There is no future-coordinate tilt
normalization in the base weighted expectation: all future base coordinates
integrate to `ν(univ)=1`.

On the prefix, set `theta=(0,-s)` in accepted
`iid_quadratic_sample_tilt`. The exponent is literally `-s*energy b`, so
the actual prefix normalizer is `Z^m` and the actual prefix tilted measure
is `pi ρ`. The true positive density identity (or `integral_tilted`)
therefore gives

`∫ U_prefix^r * exp(-s*energy) d(pi ν)
 = Z^m * ∫ U_prefix^r d(pi ρ)`.

The L1 required for this equality has just been paid; it is not an
expectation equality between Bochner junk values. Transport the two sides
through their actual prefix maps to get the two long-law identities in
the head. The same argument with the constant observable gives
`∫ exp(-sQ) dP=Z^m`. This does **not** assert that tilting the long path
by its prefix energy produces the full long product of tilts: its future
coordinates would remain base-law coordinates. Only a prefix-dependent
observable has the displayed full-tilted-long expectation identity.

### Bundle 2: actual first moment under the actual energy tilt

The frozen energy producer proves that the literal law `ρ` is a
probability measure, has a finite second moment, and satisfies

`Vρ≤exp(S)*V`,
`|μρ|≤M=|μ|+2s exp(S)m3`,
`0<Z`, `Z^m≤exp(-(s*m2/2)*m)`, `S=s*h²≤1`.

Apply accepted `iid_lindleyRegulator_prefix_first_moment` to `ρ` on the
actual long product `T`. Its conclusion is the true first moment
`∫U dT≤sqrt(Vρ)/sqrt(m)+|μρ|≤B/sqrt(m)+M`, where
`B=sqrt(exp(S)*V)`. The square-root denominator is positive because
`m=i.val+1≥1`; no variance denominator occurs. Bundle 1's identity,
nonnegativity of `U`, and the scalar normalizer decay then give the stated
weighted first-moment bound. The argument covers `s=0`, `V=0` and time 1
without an added case hypothesis. It does not invoke survival.

### Bundle 3: both deterministic clocks, no new analytic premise

For `N=0`, all conclusions are `0≤0` or equal zero, including the
right-hand sides. For `N>0`, set `α=t/N≥0` and
`w_i=exp(-α*i)` for paper indices `i=1,...,N`.
Every `w_i` lies in `(0,1]`, hence `0≤G≤N`.

The elementary exponential inequality `1+α≤exp α` gives

`α*exp(-α*i) ≤ exp(-α*(i-1))-exp(-α*i)`.

This telescopes to `αG≤1-exp(-t)≤1`, so `tG≤N`. Adding the two bounds
`G≤N` and `tG≤N`, then dividing by positive `1+t`, gives
`G≤2N/(1+t)`.

For the half clock, a finite weighted square-root telescope avoids the
source's improper integral entirely. In fact for **any** numbers
`0≤w_i≤1`, put `C_k=Σ_{i=1}^k w_i`. Then `0≤C_k≤k`, and

`w_k/sqrt(k)
 ≤ 2*(sqrt(C_k)-sqrt(C_(k-1)))`.

To verify the step, its right square-root difference is nonnegative, and

`w_k=(sqrt(C_k)-sqrt(C_(k-1)))*(sqrt(C_k)+sqrt(C_(k-1)))`,
`sqrt(C_k)+sqrt(C_(k-1))≤2sqrt(k)`.

Multiply these inequalities and divide only by `sqrt(k)>0`. It remains
valid when either cumulative mass, or `w_k`, is zero. Summation gives
`H≤2sqrt(G)≤2sqrt(N)`. Finally

`H²≤4G≤8N/(1+t)`,
`(1+sqrt(t))²≤2*(1+t)`

imply `H*(1+sqrt(t))≤4sqrt(N)` by nonnegativity, hence the exact final
half-clock bound. No monotonicity hypothesis for `w` is needed, no clock
bound is assumed, and no source integral estimate is imported.

### Bundle 4a: finite sum under one long law

Every summand has the genuine L1 supplied by bundle 2. Exchange the finite
sum with its integral and sum the individual bound. With
`t=(s*m2/2)*N`, the exponential is precisely the clock exponent `-t*i/N`
when `N>0`. Here `m2≥0` is the actual integral of a nonnegative function,
so `t≥0` follows. For `N=0` the finite sum is empty and its proposed right
side is zero; no cancellation by zero is performed.

Bundle 3 gives

`Σ E[U_i exp(-sQ_i)] ≤ B*H+M*G
 ≤4B√N/(1+√t)+2NM/(1+t)`.

Both `B,M` are nonnegative by the actual variance and raw-moment
nonnegativity. Every initial restriction is pointwise between zero and
the full finite sum; its L1 follows by finite summation or domination.
The bound is therefore for the integral of the actual finite random sum,
as well as for the sum of its actual expectations. `K=N/2` selects paper
times `1≤i≤floor(N/2)`, because the zero-based condition is `i.val<K`.

### Bundle 4b: original parameter payment, with explicit `128/sqrt(κ)`

Write `a=1+x`, `h_x=ε/a`, `R=truncationBudget ν0 N x`. The source window
gives `1+y≤2a`. Because `ε≤ε0/2` and `ε0≤1`, we have `ε≤1/2` and

`(1+y)*h_x≤2ε≤ε0`,
`S=(κy²)*h_x²≤κ ε0²≤1` for `0<κ≤1/16`.

The accepted source bridge proves that the literal conditional law is a
probability measure with true AE cutoff `h_x`, finite raw moments and

`N*m2≥3/4`, `N*V≤4/3`,
`N*|μ|≤2R/(ε² a)`, `N*m3≤2R/a³`.

The conditional law's mean is not zero. In particular, with the source's
literal `Λ=(1+y)N|μ|+(1+y)³N*m3`, the original cutoff budget alone yields

`0≤Λ≤(4/ε²+16)R≤ε/2+2ε³≤1/2`.

This is why no `Λ≤constant` premise, no `η0` premise and no survival drift
premise is added to the source specialization. The original
`R<η(ε)≤ε³/8` already pays the displayed budget. The auxiliary bound is
valid on the larger explicit domain `R≤ε³/8`.

Use bundle 4a with `s=κy²`, `S≤1`, `exp(S)≤exp(1)<3`, and put
`t=s*m2*N/2`. Exact inequalities are

`B√N≤sqrt(3*(4/3))=2`,
`t≥(3κ/8)y²`,
`N*M≤N|μ|+6κy²N*m3≤(1+6κ)Λ/(1+y)≤7Λ/(1+y)`.

The proof may use the weaker consequence `κ≤1`. Then
`sqrt(3κ/8)≥sqrt(κ)/2`, since `3κ/8≥κ/4`. Consequently

`1+sqrt(t)≥(sqrt(κ)/2)*(1+y)`.

Here `sqrt(κ)≤1`, so the constant term also obeys the comparison.
For the drift term the elementary bound `1+t≥1` is enough; retaining it
avoids any unnecessary `1/κ` loss. The two terms in the generic total
bound therefore satisfy

`4B√N/(1+sqrt(t))≤16/[sqrt(κ)*(1+y)]`,
`2NM/(1+t)≤14Λ/(1+y)≤7/(1+y)
 ≤7/[sqrt(κ)*(1+y)]`.

Their sum is at most
`23/[sqrt(κ)*(1+y)]≤128/[sqrt(κ)*(1+y)]`. This gives the full actual weighted first
sum, and restriction gives every initial sum, including the original
half-time result. Fixing the sufficiently small positive `κ` used by later
kernels makes `C=128/sqrt(κ)` an absolute source constant; no bound uniform in
all `κ→0` is asserted. In particular the theorem allows a later kernel to
choose a smaller positive `κ`.

## Hazards and remaining work

- `U_i^2` has genuine L1 and exact weighted change of measure, but no
  unconditional second-moment decay is claimed. The fresh review of the
  separate explicit-survival consumer does not discharge actual source
  survival or tilted-law survival. Those original obligations remain OPEN.
- A full-path energy weight would tilt the future coordinates too and
  would normalize by `Z^N`; that is not the source weight and is not the
  candidate. The prefix normalization is exactly `Z^(i.val+1)`.
- No conditional centering, symmetry, variance lower bound, drift bound,
  large `N`, nonzero `s`, positive `V`, or clock estimate is added to the
  generic heads. Original-law centering is explicit only in bundle 4b.
- The product tilt identity is reused only on the actual prefix, with its
  genuine MGF-domain/L1 input. Its old proof/object is not modified or
  rechecked to create this candidate.
- The proof route is planned, not kernel checked. Private measurable
  prefix and finite weighted-telescope helpers may be needed after root
  freeze. Their exact owned types/proofs/axioms require the same final
  audit as the public heads; no helper may hide the proposed conclusion
  as an assumption.
- Pending producer acceptance, final implementation and independent
  complete source/proof/type review are outstanding. C1/C2 roots,
  weighted second moment, true source survival, growing kernels,
  inversion and desmoothing remain OPEN.

## Execution and ownership

Candidate work used local read-only source/interface reads and exact byte
hashes only. There was no remote write, no Lean invocation, no local Lean
installation/check, no cache write and no production source. Only
`drafts/c12-weighted-regulator/` was created. Root owns declaration freeze,
shared implementation, integration and cache. No other owner's edits
were reverted or changed.

After a full root freeze, production may use the released
`common-centered-characteristic-v44` worktree only if root activates it
after checking ownership. The future writer must normalize each new
Lean/Python source to UTF-8 LF before its first source-bound gate. All
Lean/audit work stays on the server under CPU10–13, `root-heavy.lock`,
the pinned toolchain/package view, and existing memory/job limits.
The author cannot certify its own candidate or bypass the pending
producer's qualified independent acceptance.
