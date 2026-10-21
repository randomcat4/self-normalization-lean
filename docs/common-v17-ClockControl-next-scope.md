# Actual bounded-square clock control: next shared probability unit

Status: PROPOSED FOR INDEPENDENT STATEMENT REVIEW. No target Lean source,
candidate theorem, proof or `.olean` has been created. This author owns
only this scope and read-only API probes in this unit. Existing source,
implementations, interfaces and caches are unchanged.

## Source binding and earliest missing probability step

Read-only original files, hashes actually rechecked for this proposal:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

The selected dependency is the genuine bad-clock estimate in
`supplement.tex:836–844`, `h:lem:clock`, and its proof at 3078–3150.
It is consumed immediately after the signed-block estimate at 823–833,
in particular at 849–858. Its later desmoothing consumption is at
3895–3907. The actual clock is defined at `main.tex:553–556`:

```text
Q_k = sum_{j=1}^k A_j^2, Q_0=0.
```

The source clock lemma, for the actual all-coordinate conditional sample,
asserts

```text
P_x*(Q_floor(n/2) < 1/16) + P_x*(Q_n notin [1/4,2])
    <= C Lambda_y PhiBar(y),
```

where `x in D3`, `y>=2` and `y` satisfies the source comparison-threshold
condition. This is a probability conclusion to prove, never a hypothesis.

The earliest independently closable shared step is its bounded-square
exponential/cosh argument. Ordinary Hoeffding alone loses the actual small
moment factor required here. The source applies Markov to **cosh minus
one**, not just an exponential, obtaining the factor `n m4`. The selected
batch proves that probability argument for an arbitrary genuine bounded
iid increment law and combines it into a source-ready clock bound under
the actual numerical moment budgets. It does not claim that every D3
truncation/budget bridge is already formalized.

Selected future file: `Shao/Probability/ClockControl.lean`, namespace
`Shao.Probability`, `set_option autoImplicit false`. No new definitions;
three public theorems. Use existing `samplePath`, `Shao.prefixSquares`,
`Shao.energy` and `Shao.standardNormalTail`. In particular do not define
clock energy by a variance or invent another finite-sum convention.

## Three distinct probability laws

The notation must remain separated throughout the implementation:

| Law | Actual object and source | What can be used |
|---|---|---|
| Original increment law `ν₀` | Law of `ξ=X/(σ sqrt n)` under original P; `main:425–428`, `supp:2047` | Actual finite second moment, original mean zero and `n E ξ²=1`, plus the truncated budget. No global absolute third/fourth moment is assumed. |
| Conditional increment law `η_x` | `cond ν₀ {a : abs a <= h_x}`, `h_x=ε/(1+x)`; `main:546–551` | Probability after proving positive cutoff mass; bounded support; actual conditional raw moments. Its mean need not be zero. This is the law denoted `ν` in the proposed generic interfaces when applying them to this source clock. |
| Later tilted laws | Square tilt `exp(-s a²)/Z_s` at `supp:2238–2244`; joint tilts at 2709 onward | Different genuine probability laws. Support can remain bounded, but their means, raw second/fourth moments and normalizers are different. Original conditional clock budgets do not transfer without an actual tilted-moment proof. |

The sample measure `μ` in the generic theorem is an actual probability
measure carrying measurable iid coordinates with actual marginal `ν`.
For the source it can be the true sample measure conditioned on all
coordinates being bounded, or its genuine canonical product-law image.
It is not silently the original sample measure or a tilted sample law.

## Exact proposed Lean interface

All three statements share the following binder context. It supplies
genuine law equality and independence; no desired moment identity,
exponential bound, concentration conclusion or Gaussian comparison is an
input.

```lean
namespace Shao.Probability

open MeasureTheory ProbabilityTheory

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {ν : Measure ℝ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
variable {X : Fin n → Ω → ℝ}
```

### 1. Genuine exponential integrability and the raw fourth-moment bound

```lean
theorem iid_bounded_clock_exp_integral
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h : ℝ) (hh : 0 ≤ h) (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (k : ℕ) (hk : k ≤ n) (θ : ℝ) (hθ : |θ| * h ^ 2 ≤ 1) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m4 : ℝ := ∫ a : ℝ, a ^ 4 ∂ν
    let D : Ω → ℝ := fun ω =>
      Shao.prefixSquares (samplePath X ω) k - (k : ℝ) * m2
    Integrable (fun ω => Real.exp (θ * D ω)) μ ∧
      (∫ ω, Real.exp (θ * D ω) ∂μ) ≤
        Real.exp (2 * θ ^ 2 * (k : ℝ) * m4)
```

`θ` is signed, allowing both exponential branches without separate public
theorems. It includes `θ=0` and `k=0`. Actual second/fourth moment
integrability is proved from the measurable identity and bounded support,
not imposed on the original increment law. The constant two is the
source's convenient Taylor constant; the cached elementary Taylor API
even gives a stronger pointwise coefficient one on the unit interval.

### 2. Two-sided deviation with its real cosh-excess denominator

```lean
theorem iid_bounded_clock_deviation_le
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h : ℝ) (hh : 0 ≤ h) (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (k : ℕ) (hk : k ≤ n)
    (δ θ : ℝ) (hδ : 0 < δ) (hθ : 0 < θ) (hstep : θ * h ^ 2 ≤ 1) :
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m4 : ℝ := ∫ a : ℝ, a ^ 4 ∂ν
    let D : Ω → ℝ := fun ω =>
      Shao.prefixSquares (samplePath X ω) k - (k : ℝ) * m2
    μ.real {ω | δ ≤ |D ω|} ≤
      (Real.exp (2 * θ ^ 2 * (k : ℝ) * m4) - 1) /
        (Real.cosh (θ * δ) - 1)
```

The event is the actual weak absolute deviation event. Its right side
retains the fourth-moment factor through `exp(u)-1`; there is no extra
factor two from a union bound. Cosh-excess integrability and nonnegativity
must be derived from the two actual exponential integrability outputs
and `cosh >= 1`, before applying real Markov. The denominator is strictly
positive because `θ δ > 0`; no zero-denominator convention is used.

### 3. Actual two bad-clock probabilities, paid by a conditional raw cube

```lean
theorem iid_bounded_clock_bad_probability_le
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h y : ℝ) (hh : 0 ≤ h) (hy : 2 ≤ y)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hlower : (3 / 4 : ℝ) ≤ (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν))
    (hupper : (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν) ≤ (4 / 3 : ℝ))
    (hscale : (1 + y) * h ≤ 1)
    (hstep : 8 * (1 + y) ^ 2 * h ^ 2 ≤ 1)
    (hbudget : (8 * (1 + y) ^ 2) ^ 2 * (n : ℝ) *
      (∫ a : ℝ, a ^ 4 ∂ν) ≤ (1 / 2 : ℝ)) :
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    μ.real {ω | Shao.prefixSquares (samplePath X ω) (n / 2) < (1 / 16 : ℝ)} +
      μ.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2} ≤
        2048 * Real.sqrt (2 * Real.pi) *
          ((1 + y) ^ 3 * (n : ℝ) * m3) * Shao.standardNormalTail y

end Shao.Probability
```

The three numerical hypotheses after normalization are actual support
and conditional moment budgets used in `supp:3082`, 3098–3099 and
3122–3126. `hbudget` is not the target clock probability or an assumed
MGF inequality. Its fourth moment is under the displayed bounded `ν`;
its true integrability and `m4 <= h m3` must be derived from support.
The theorem is stronger than the source in omitting the nonnegative drift
term in `Lambda_y`: after application,
`(1+y)^3 n m3 <= Lambda_y` gives the original form. The explicit constant
`2048 sqrt(2*pi)` is an auxiliary valid absolute constant, not a quotation
of a numerical constant unspecified by the source.

These three blocks are proposed signatures only, not a Lean implementation
with missing proof terms. No additional public helpers are presently
proposed; finite-index, bounded-moment and cosh algebra can remain private.

## Proof decomposition, exact constants and integral obligations

For the fixed genuine bounded law, first prove true integrability of
`a`, `a²`, `|a|³`, `a⁴` by domination by finite constants under probability.
Prove `0 <= m2 <= h²`, `m4 >= 0`, and `m4 <= h m3` by actual integral
comparison between integrable functions. This requires no global moments
under the original `ν₀`.

Set `B(a)=a²-m2`. On the actual support, `|B|<=h²`. Finite integrability
justifies

```text
Eν B = 0,
Eν B² = m4-m2² <= m4.
```

For `|θ|h²<=1`, use the true scalar Taylor bound to obtain
`Eν exp(θB) <= 1+2θ²m4`. Exponentials are actually integrable: their
norms are bounded by `exp(|θ|h²)` on the support. Transport support and
moments through the actual `IdentDistrib` inputs. The first `k` coordinates
form a fixed subfamily; independence factors the actual product
expectation, and `1+u<=exp u` gives statement 1.

The use of `prefixSquares` must include a private proof that its filtered
Fin n index set has cardinal k when `k<=n`, or an equivalent bijection
with Fin k. A saturated prefix cannot be centered by `k m2` without that
range condition. No sample-dependent selection is involved.

Average the `+θ` and `-θ` actual integrals using
`cosh z=(exp z+exp(-z))/2` and subtract the probability-one integral of
one. This gives

```text
Eμ[cosh(θD)-1] <= exp(2θ² k m4)-1.
```

Both exponential integrals, their average and the subtraction are
integrable. Cosh is even and increasing in absolute value, so on the weak
deviation event it is at least `cosh(θδ)-1`. Real Markov and the strictly
positive denominator prove statement 2. There is no appeal to the zero
value of a nonintegrable Bochner integral.

For statement 3 put `a=1+y`, `θ=8a²`, `k=floor(n/2)`. Support and hscale
give `m2<=h²<=1/9`. With `n m2>=3/4`, derive `n>=7` and then `k>=n/3`;
these are conclusions, not missing positive-sample hypotheses. Therefore

```text
k m2 >= 1/4,      3/4 <= n m2 <= 4/3.
{Q_k<1/16} subset {abs(Q_k-k m2)>=1/8},
{Q_n notin [1/4,2]} subset {abs(Q_n-n m2)>=1/8}.
```

Apply statement 2 at δ=1/8 and lengths k,n. By hbudget and k<=n,
`0<=2θ² j m4<=1`, hence `exp(2θ² j m4)-1<=4θ² n m4`.
Since `θ/8=a²>=9`, `exp(a²)>=4` and
`cosh(a²)-1>=exp(a²)/4`. Thus each deviation is at most
`16θ² n m4 exp(-a²)` and their sum is at most

```text
32θ² n m4 exp(-a²) = 2048 a⁴ n m4 exp(-a²)
 <= 2048 a³ n m3 exp(-a²),
```

where `m4<=h m3` and `a h<=1` are actually proved/used with nonnegative
factors. Finally, for every y>=0, `1+y<=exp y` implies

```text
(1+y) exp(-(1+y)²) <= exp(-y²/2).
```

The accepted actual Mills lower bound and the actual density formula give
`exp(-(1+y)²) <= sqrt(2*pi) * standardNormalTail y`. This proves exactly
the constant and actual Gaussian function in statement 3. No sample
Gaussian comparison, Berry--Esseen or abstract tail proxy is required.

## Exact relation to existing retained-law data and missing source bridges

The accepted implementations read for this proposal include

```text
RetainedMoments.lean
512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb
RetainedVariance.lean
5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6
```

`RetainedMoments` defines the cutoff as `|z|<=1/r`. It can represent the
source cutoff **exactly** by setting `r=(1+x)/ε>0` and proving
`1/r=ε/(1+x)=h_x`. Then

```text
retainedCutoffLaw ν₀ r = cond ν₀ {|a|<=h_x}.
```

No definition is changed or duplicated, and setting its parameter equal
to x without this conversion would be wrong. Existing probability/support
and conditional-integral lemmas can then be reused after proving cutoff
mass positive. Existing `truncationBudget_scale_one_le`, with `c=1/ε`,
already gives the cubic upper scaling needed to pass from `R_n(x)` to the
budget at r; no new scaling axiom is required.

However, the actual remaining source-specialization bridge must preserve
the small original `R_n(x)` factor. The existing retained raw cube bound
`n E|A|³<=2/r³` assumes only a budget at most one and is too coarse to
claim the source's `n m3<=2 R_n(x)/(1+x)³` automatically. Reuse instead
the genuine conditional integral formula, true cutoff mass lower bound
and `integral_truncation_small_three_le` at scale `1+x`, noting
`h_x<=1/(1+x)`. This is still only a truncated original cube, integrable
from the original second moment, never an original global cube.

The source proves at `supp:2047–2090` and 2091 onward that
`3/4<=n m2<=4/3`, `n m3<=2R_n(x)/(1+x)³` and `n m4<=h_x n m3`.
Existing retained second-moment bounds are reusable algebraically after
the reparameterization and size checks, but do not yet constitute a
single D3 theorem supplying these exact source budgets. In particular the
coarse upper `1+2/n` needs the relevant size bound before it becomes 4/3.
Those checks must be supplied, not treated as unconditional consequences
of the current `retainedSample` theorem at cutoff `1/x`.

For the source's constants, `main:638–640` and `supp:3082` give
`(1+y)h_x<=ε0<=1`; `supp:3099` gives θh_x²<=1. The exact fourth-moment
budget follows as in 3117–3126:

```text
θ² n m4 <= 64 ε0 (1+y)³ n m3
        <= 64 ε0 Lambda_y < 32 ε0 η0 <= 1/2.
```

Here the actual source small-parameter conditions are
`Lambda_y<η0/2`, `64ε0η0<=1` and the chosen ε0 Taylor-range bound.
They are not assumed clock probabilities. The present generic theorem
accepts their explicit support/raw-moment consequences. A follow-up D3
specialization must derive them from the genuine truncated budget and
fixed parameter definitions before claiming the whole original lemma.

`ConditionalIID.indep_cond_joint_map_eq_pi` already supplies the genuine
product law after conditioning a finite independent sample on the fixed
intersection of coordinate cutoff events, with positive joint mass.
This gives the all-bounded `P_x*` sample law; alternatively its actual
conditional independence and common marginal can instantiate these
theorems directly. The event map is a measurable finite polynomial.
There is no conditional-independence axiom or random-length iid claim.

`RetainedVariance` supplies actual centered second/cube facts for its
retained law. It is not needed for this clock proof: `B` centers `A²`,
not A. A positive variance of A is unnecessary, and replacing Q by
`sum(A-mean A)²` would introduce a different event and omitted cross terms.
The actual raw identity would be
`Q_k=sum(A-mean A)²+2 mean A sum(A-mean A)+k(mean A)²`.
Do not transfer clock thresholds through a standardization while dropping
these terms.

## OQ4 reuse boundary

Read-only inspection covered the curated OQ4 variance, killed-kernel and
overshoot modules; the current `lead-oq4` source inventory/status; and
the frozen `IntervalConcentration`/`LaplaceTail` interfaces.

- `VarianceScaling` gives deterministic energy scaling and genuine moment
  standardization. It does not control the probability of a random clock
  deviation; centered standardization changes the clock as just explained.
- `IntervalConcentration` bounds closed interval mass of an actual sum
  from an explicit Berry--Esseen/CDF approximation premise. It is not an
  exponential clock concentration theorem, and inserting that premise
  here would introduce an unrelated unproved result.
- `LaplaceTail` is a positive-part tail-integral interface with a CDF
  comparison input; killed kernels, boundary occupation and block bounds
  concern actual wall survival/occupation. Their closed-wall/strict-exit
  distinctions do not supply this squared-clock probability estimate.
- OQ4's energy-denominator E1–E6 and its full root remain explicitly open
  in the read status. A source/name search in current OQ4 found no actual
  clock or prefixSquares concentration theorem to reuse. This is a bounded
  inspected-source finding, not a claim of a universal library absence.

No OQ4 implementation import is proposed. The genuine elementary
probability and exponential APIs plus the already accepted common Gaussian
tail are sufficient. The shared finite iid moments module may support a
later small-y Chebyshev specialization for `supp:3901–3905`; that separate
desmoothing step is not included as a fourth public theorem here.

## Boundaries and failure checks

- `k=0` and `n=0` are allowed in the first two statements. D is zero,
  the exponential integral is one and the positive-threshold deviation
  event is empty. The third statement derives n>=7 from its actual
  support/normalization, so n=0 cannot satisfy its hypotheses.
- The support set is closed. The lower half-clock event remains strict
  `<1/16`; the final bad event is the complement of the closed interval
  `[1/4,2]`. Deviations are weak `>=δ`. Safe event inclusions, rather than
  atomlessness, connect them. Atoms at every threshold are allowed.
- `θ=0` is valid in statement 1. It must be excluded in statement 2:
  for a nonconstant one-coordinate Bernoulli square and positive small δ,
  the deviation probability is positive while the displayed ratio would
  become `0/0=0` in Lean. Likewise δ=0 is invalid even at k=0, since its
  event has probability one and its displayed denominator is zero.
- `k<=n` is essential. For k>n the existing prefix is saturated but the
  proposed centering `k m2` is not; no such extension is claimed.
- Constant/noncentered laws and zero variance are allowed in the first
  two statements. No use of a density, symmetry, mean zero, non-lattice
  assumption or positive variance is hidden in them.
- An original finite second moment does not supply an exponential square
  moment or global cube/fourth moment. Explicitly, give total mass
  `7*2^(-3r)` to the pair `{+2^r,-2^r}`, split equally, for integers r>=1.
  The masses sum to one, the second moment is seven, and the absolute cube,
  fourth moment and every positive exponential-square moment diverge.
  Rescaling preserves this obstruction while normalizing the second
  moment. This is why the source theorem must be applied to the actual
  conditional bounded law, not asserted for the original law.
- Cosh minus one retains a vanishing numerator when m4=0; replacing it
  by ordinary Chernoff with numerator exp(...) alone would lose this
  payment. Neither the ratio nor a bare Gaussian decay estimate can be
  declared automatically proportional to the small truncation budget.
- The later tilted law has separately changed m2,m3,m4. Support survives
  weighting, but normalization/budget hypotheses must be re-established
  under that exact law before reusing statement 3.

## Existing APIs, cache and execution evidence

Pinned versions remain Lean 4.36.0-rc1 / Mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`.
Read-only server source inspection found:

| API/source | Actual contribution |
|---|---|
| `iIndepFun.integral_fun_prod_comp`, Independence/Integration:454–466 | Actual finite independent product factorization with the required measurability. True integrability is proved separately from boundedness. |
| `Real.abs_exp_sub_one_sub_id_le`, Analysis/Complex/Exponential:538–541 | For abs t<=1, abs(exp t-1-t)<=t², stronger than the source's 2t² bound. |
| `Real.abs_exp_sub_one_le` | For abs u<=1, abs(exp u-1)<=2 abs u; gives the needed small positive exponential excess. |
| `Real.cosh_eq` | Actual exponential identity, not a proxy even function. |
| `Real.one_le_cosh`, `one_lt_cosh`, `cosh_le_cosh`, DerivHyp:431–445 | True nonnegativity/positive denominator and absolute-value monotonicity. |
| `mul_meas_ge_le_integral_of_nonneg`, Bochner/Basic:1169 | Actual real Markov inequality requiring nonnegativity and true integrability. |
| `Shao.standardNormal_mills_bounds` | Actual normal measure/density lower Mills bound used in the final scalar comparison. |

A server import/`#check` probe of the currently cached modules
`Shao.Probability.FiniteIID`, `Shao.Probability.GaussianTail`,
`Mathlib.Probability.Independence.Integration` and
`Mathlib.Analysis.Complex.Exponential` exited zero and confirmed all listed
APIs except the DerivHyp-only inequalities, which were checked directly in
their pinned source. The probe defined no candidate objects or theorems.

The shared broker intermittently returned pre-start `operation_failed`
with `operation_may_have_started=false`. The successful read-only Lean
probe used the SERVER-authorized native SSH fallback and only
`taskset -c 0-3 lake env lean --stdin` on `lead-c12`. No local Lean or
cache writes occurred.

The initial read-only artifact inventory found DerivHyp missing. The only
current cache request to the coordinator is
`Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp` and its actual
transitive dependencies. `SubGaussian` was also absent, but it is not an
import/dependency of this selected proof and is not requested. Do not
download caches or assume a missing import succeeded.

Tentative future imports are the two common modules above, Independence
Integration, Analysis/Complex/Exponential, and DerivHyp. Additional standard
Mathlib finite-sum/measurability imports may be made explicit after freeze;
no OQ module or external probability comparison is needed.

After independent statement review and coordinator freeze, the future
implementation must prove the real bounded moments, exponential/cosh
integrability, prefix cardinal identity, Markov denominator positivity,
strict/closed event inclusions and the actual normal-tail scalar bridge;
then pass targeted server compilation, full module-owned transitive axiom
audit, forbidden-token scan and fresh proof review. Current API inspection
is not proof of the proposed results.

This unit does not by itself close the all-D3 conditional-moment/budget
specialization, small-x desmoothing, original untruncated clock tails,
square/joint tilted clocks, stopped-clock/Wald estimates, Berry--Esseen,
Brownian/long-time OQ4 energy denominators or full C1/C2.
