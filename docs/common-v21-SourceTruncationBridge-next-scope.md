# Source cutoff, genuine conditional law and paid moment bridge

Status: PROPOSED FOR INDEPENDENT DECLARATION REVIEW. This file contains
analysis and exact proposed signatures only. No target Lean file, proof,
placeholder or new artifact has been created. Existing frozen source and
proposal bytes, other authors' files, imports, pins and caches are unchanged.
After an explicit freeze, the proposed new module is
`Shao/Probability/SourceTruncationBridge.lean`, namespace `Shao`,
`set_option autoImplicit false`: **zero new definitions, eight public theorems**.

## 1. Exact source and law

Read-only original SHA256 values rechecked for this proposal:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

The actual cutoff is `main.tex:423–428`, `h:eq:truncation`:

```text
xi = X/(sigma sqrt n),   h_x = epsilon/(1+x),
N_x = intersection_{j<=n} {|xi_j|<=h_x}.
```

The actual increment law after this fixed all-coordinate conditioning is
`main.tex:546–551`, `h:eq:conditionallaw`:

```text
A has law xi conditional on {|xi|<=h_x}.
The conditional mean need not be zero.
```

The original law `nu` is a probability with finite raw second moment,
original mean zero and `n integral z^2 dnu=1`; its second moment is **1/n**.
The accepted budget is exactly

```text
R = truncationBudget nu n x = n integral F((1+x)z) dnu,
F(w)=w^2 min(|w|,1).
```

Write `a=1+x`, `h=epsilon/a`, `b=a/epsilon`. The existing retained API uses
`retainedCutoffSet b={z: |z|<=1/b}`. It therefore represents the source law
exactly at **b=(1+x)/epsilon**, because `1/b=h`. The true law throughout this
proposal is `rho=ProbabilityTheory.cond nu {z: |z|<=h}`. It is not an
unconditioned original law, a centered translate, a conditional law at y,
or a later exponential/square tilt.

Source moment targets are `supplement.tex:522–533`,
`h:lem:conditionalmoments`, proved at `2045–2135`:

```text
3/4 <= n m2 <= 4/3,      1/2 <= n tau^2 <= 4/3,
n |mu| <= 2 R/(epsilon^2 a),
n m3 <= 2 R/a^3,         n m4 <= h n m3,
Lambda_y=(1+y)n|mu|+(1+y)^3 n m3
        <=20 R/epsilon^2    if y>=0 and |y-x|<=1/a.
```

Here `mu=integral z drho`, `mr=integral |z|^r drho` and
`tau^2=m2-mu^2` is the genuine variance. Even moments can be written with
`z^2,z^4`. No original global third or fourth moment is assumed.

The original parameter choices are `main.tex:372–392`:

```text
0<epsilon0<=1, eta0>0, L>=1600,
K=8(1+L), A0=4 K L,
epsilon=min{epsilon0/2,1/[4(K+1)L]},
eta(u)=min{u^3/8,u^2 eta0/40,rho_star/32,1/(4 A0)},
x in D3 implies x>=0 and R_n(x)<eta(epsilon).
```

Thus `0<epsilon<=1/2`, `R<epsilon^3/8` and
`R<epsilon^2 eta0/40` are genuine consequences, not added moment premises.
In fact the second branch of epsilon's minimum gives `epsilon<=1/8`:
`K+1>=1`, `L>=1600`, so `4(K+1)L>=6400>=8`. This uses the actual displayed
parameter construction; `epsilon<=1/8` is not inferred from
`epsilon<=epsilon0/2` and `epsilon0<=1` alone. The proposed final numeric
clock bridge uses that proved source consequence explicitly.

## 2. Exact proposed declarations

Open `MeasureTheory ProbabilityTheory`. All displayed signatures are
complete, with their own binders; the local `let` values introduce no new
global law, budget, moment or normalization definition. Weak `hR` is
intentional: the original strict D3 premise supplies it. There are no
desired conditional-moment, clock-probability, damping or variance-positive
inputs.

### 2.1 Exact measure equality and real budget scaling

```lean
theorem sourceTruncation_reparameterization
    (nu : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    let a : ℝ := 1 + x
    let b : ℝ := a / epsilon
    let B : Set ℝ := {z | |z| ≤ epsilon / a}
    let H : ℝ := (n : ℝ) * ∫ z : ℝ, truncationF (b * z) ∂nu
    1 / b = epsilon / a ∧
      retainedCutoffSet b = B ∧
      retainedCutoffLaw nu b = ProbabilityTheory.cond nu B ∧
      H = truncationBudget nu n (b - 1) ∧
      truncationBudget nu n x / epsilon ^ 2 ≤ H ∧
      H ≤ truncationBudget nu n x / epsilon ^ 3
```

This needs only a general measure and `h2`; no probability, normalization,
original centering, sample positivity or positive cutoff mass is required
for the **equality** of the actual conditional measures. Both sides use the
same Mathlib `cond` even if that general measure has zero mass on B.
Integrability of both real F kernels follows from `h2`. Scaling uses
`truncationBudget_scale_one_le` with `c=1/epsilon`; in particular the new
budget is `R_n(b-1)`, **not** `R_n(b)` and **not** `H_b<=R_n(x)`.

### 2.2 Actual reparameterized sample size and admissible cutoff budget

```lean
theorem sourceTruncation_sample_size
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let b : ℝ := (1 + x) / epsilon
    2 ≤ b ∧ b ^ 6 ≤ (n : ℝ) ∧ 64 ≤ n ∧
      (n : ℝ) * (∫ z : ℝ, truncationF (b * z) ∂nu) ≤ 1 / 8
```

No new `n>=2`, `n>0`, `R>0` or `b^6<=n` premise is allowed. Normalization
and the accepted genuine sample-size theorem derive them. The proof must
use its **middle expression**, not just its weaker `a^6<=n` corollary.

### 2.3 Original-law strict tail budgets, retaining R

```lean
theorem sourceTruncation_tail_budget
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    let a : ℝ := 1 + x
    let h : ℝ := epsilon / a
    let R : ℝ := truncationBudget nu n x
    (n : ℝ) * nu.real {z | h < |z|} ≤ R / epsilon ^ 3 ∧
      (n : ℝ) * (∫ z : ℝ, if h < |z| then |z| else 0 ∂nu) ≤
        R / (epsilon ^ 2 * a) ∧
      (n : ℝ) * (∫ z : ℝ, if h < |z| then z ^ 2 else 0 ∂nu) ≤
        R / (epsilon * a ^ 2)
```

This is before any smallness or original centering assumption. Its strict
large event is precisely B's complement. Every marked kernel in the proof
must be genuinely integrable: indicator one under probability, and the
already checked strict tail-one/tail-two kernels at cutoff parameter b.
The three bounds are derived from actual F comparisons at scale a; they
are not assumed truncated budgets. Natural `n=0` is allowed here.

### 2.4 Positive conditional law, true support and actual moments

```lean
theorem sourceTruncation_law_data
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let B : Set ℝ := {z | |z| ≤ epsilon / (1 + x)}
    let rho : Measure ℝ := ProbabilityTheory.cond nu B
    (3 / 4 : ℝ) ≤ nu.real B ∧ nu.real B ≤ 1 ∧
      IsProbabilityMeasure rho ∧
      (∀ᵐ z : ℝ ∂rho, |z| ≤ epsilon / (1 + x)) ∧
      Integrable (fun z : ℝ => z) rho ∧
      Integrable (fun z : ℝ => z ^ 2) rho ∧
      Integrable (fun z : ℝ => |z| ^ 3) rho ∧
      Integrable (fun z : ℝ => z ^ 4) rho
```

The positive mass and probability instance are conclusions. The fourth
moment is only under rho and follows from its actual bounded support;
there is no added original fourth-moment assumption. Existing retained
probability/support/integrability theorems are transported using 2.1.

### 2.5 Real drift, raw cube/fourth and centered cube payment

```lean
theorem sourceTruncation_paid_moments
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let a : ℝ := 1 + x
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ epsilon / a}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let m4 : ℝ := ∫ z : ℝ, z ^ 4 ∂rho
    let R : ℝ := truncationBudget nu n x
    (n : ℝ) * |mu| ≤ 2 * R / (epsilon ^ 2 * a) ∧
      (n : ℝ) * m3 ≤ 2 * R / a ^ 3 ∧
      (n : ℝ) * m4 ≤ (epsilon / a) * ((n : ℝ) * m3) ∧
      Integrable (fun z : ℝ => |z - mu| ^ 3) rho ∧
      (∫ z : ℝ, |z - mu| ^ 3 ∂rho) ≤ 8 * m3
```

The drift uses the original centering hypothesis. Neither the raw cube nor
fourth-moment comparison mathematically needs original centering; a private
raw-moment helper can supply those parts without it for theorem 2.8. No
new public helper is proposed. The last two clauses reuse the accepted
genuine-law centered-moment theorem, rather than identifying a raw moment
with a centered one.

### 2.6 Raw second moment and genuine positive variance

```lean
theorem sourceTruncation_variance_bounds
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
    (3 / 4 : ℝ) ≤ (n : ℝ) * m2 ∧
      (n : ℝ) * m2 ≤ (4 / 3 : ℝ) ∧
      (n : ℝ) * mu ^ 2 ≤ (1 / 4 : ℝ) ∧
      V = m2 - mu ^ 2 ∧
      V = (∫ z : ℝ, (z - mu) ^ 2 ∂rho) ∧
      0 < V ∧ (1 / 2 : ℝ) ≤ (n : ℝ) * V ∧
      (n : ℝ) * V ≤ (4 / 3 : ℝ)
```

There is no `variance>0` premise. The actual conditional probability and
square integrability make Mathlib's `variance_eq_sub` applicable. The true
centered integral is connected using `retainedCutoffLaw_centered_moments`.
This is the exact variance required by LowFrequencyDamping, not a raw-square
surrogate.

### 2.7 Neighboring thresholds and true Gaussian-weighted budget

```lean
theorem sourceTruncation_nearby_payment
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 0 ≤ y) (hneigh : |y - x| ≤ 1 / (1 + x)) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let R : ℝ := truncationBudget nu n x
    let Lambda : ℝ := (1 + y) * (n : ℝ) * |mu| +
      (1 + y) ^ 3 * (n : ℝ) * m3
    (1 + y) * (epsilon / (1 + x)) ≤ 2 * epsilon ∧
      (1 + y) ^ 3 * (n : ℝ) * m3 ≤ 16 * R ∧
      Lambda ≤ 20 * R / epsilon ^ 2 ∧
      Lambda * standardNormalTail y ≤
        (20 * Real.exp 2 * R / epsilon ^ 2) * standardNormalTail x
```

The same actual rho is fixed at x for every y. `main:639` uses the stricter
neighborhood `1/[2(1+x)]`; it safely implies the displayed weak neighborhood.
For the source's second smallness branch `R<epsilon^2 eta0/40`, the third
clause gives **Lambda<eta0/2** by positive-denominator algebra. This is not a
free moment-budget premise. The last clause consumes the existing actual
Gaussian tail comparison with `exp 2`, not an abstract tail proxy or an
assumed approximation of the sample distribution.

### 2.8 Supply all three actual ClockControl numerical hypotheses

```lean
theorem sourceTruncation_clock_inputs
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 0 ≤ y) (hneigh : |y - x| ≤ 1 / (1 + x)) :
    let h : ℝ := epsilon / (1 + x)
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ h}
    (1 + y) * h ≤ 1 ∧
      8 * (1 + y) ^ 2 * h ^ 2 ≤ 1 ∧
      (8 * (1 + y) ^ 2) ^ 2 * (n : ℝ) *
        (∫ z : ℝ, z ^ 4 ∂rho) ≤ (1 / 2 : ℝ)
```

This numeric bridge deliberately does not need original centering: the
clock centers `A^2`, not A. The actual original mean zero remains necessary
for 2.5's drift and 2.6's positive variance conclusion. Here `epsilon<=1/8`
is the explicit local scalar condition derived from the source's actual
parameter construction above. It is not silently strengthened to an
unavailable distributional or moment hypothesis.

## 3. Proof obligations and use of accepted modules

**Scaling and sample size.** With `R<=epsilon^3/8` and `epsilon<=1/2`,
`R<=1/64<=1/16`. The accepted genuine sample-size theorem at `t=x,rho=R`
gives

```text
n >= (1-R)^3 a^6/R^2.
```

Actual budget positivity is derived from normalization via the accepted
Regularity result. Since `R^2<=epsilon^6/64` and
`(1-R)^3>1/64`, it follows that

```text
b^6 R^2 = a^6 R^2/epsilon^6 <= (1-R)^3 a^6,
b^6 <= n,   b>=2,   n>=64.
```

The scaled kernel budget is at most `R/epsilon^3<=1/8`, so it genuinely
satisfies the old retained interfaces' `H_b<=1` hypothesis. There is no
replacement of `H_b` by `R_n(b)` or of b by x. This allows reuse of accepted
retained probability, support and integrability and, when needed, the
existing retained variance theorem at `j=0`. Its coarse normalized variance
upper bound two by itself does not prove the source's upper bound 4/3.

**Source tail payments.** If `|w|>epsilon` and `0<epsilon<=1`, the real
kernel obeys

```text
F(w)>=epsilon^3, F(w)>=epsilon^2 |w|, F(w)>=epsilon w^2.
```

Split at `|w|<=1` and `|w|>=1` and use the accepted exact kernel formulas.
Substitute `w=a z`, integrate against the original probability using the
true integrability just described, and multiply by nonnegative n. This
proves 2.3 directly, without discarding R through `H_b<=1`.

Put `q=nu.real {|z|>h}`, `v=n integral z^2 1_(|z|>h) dnu`.
Normalization gives `n>=1`; 2.3 and smallness give `q<=1/4`, `v<=1/4`.
Measurable complement mass is exactly `nu.real B=1-q>=3/4`.
The genuine conditional integral formula supplies

```text
mu = - integral z 1_(|z|>h) dnu / (1-q),
n m2 = (1-v)/(1-q).
```

The original identity is integrable from its finite second moment under
probability. Consequently 3/4<=n m2<=4/3 and the paid drift bound holds.
For the public mean-square clause one can either reproduce the source
tail Cauchy–Schwarz argument, or use the already paid drift:

```text
n |mu| <= 2R/(epsilon^2 a) <= epsilon/(4a) <=1/8,
n mu^2=(n|mu|)^2/n <=1/64 <=1/4.
```

This second route avoids a new Holder/cache dependency, proves at least the
frozen weak clause, and does not introduce a fake centering assumption on
rho. Combining with the raw lower bound and the accepted genuine centered
identity gives `n V>=1/2`, hence V>0 since n>0.

**Raw cube and fourth moment.** On B, `|a z|<=epsilon<=1`, so
`F(a z)=a^3 |z|^3`. Equivalently B is contained in the accepted weak-small
cutoff `|z|<=1/a`, whose marked cube integral is genuinely integrable from
h2. The accepted `integral_truncation_small_three_le` and positive
conditional normalizer give

```text
n m3 <= R/[a^3(1-q)] <=2R/a^3.
```

Support gives `z^4<=h |z|^3` rho-a.e.; both sides are genuinely integrable
under rho. No `integral` of a nonintegrable original cube/fourth moment is
used. Existing `RetainedVariance` provides the centered cube comparison
with its true conditional mean and no added Jensen premise.

**Near thresholds and Clock inputs.** Set `c=1+y`. Then `c<=2a`,
`ch<=2epsilon`, and

```text
c^3 n m3<=16R,
Lambda_y <=(4/epsilon^2+16)R<=20R/epsilon^2.
```

The actual Gaussian local comparison provides the final weighted clause
of 2.7. For 2.8 put `theta=8c^2`. The moment payment remains visible:

```text
theta^2 n m4 <=64 c^4 h n m3
                 <=128 epsilon c^3 n m3
                 <=2048 epsilon R
                 <=256 epsilon^4
                 <=1/16 <=1/2.
8c^2 h^2 <=32 epsilon^2<=1/2<=1,     ch<=2epsilon<=1.
```

These constants are verified inequalities under the displayed local
assumptions. They are not quoted as numerical constants printed by the
source. This direct route uses fewer eta0/epsilon0 side conditions than
the original proof at `supp:3117–3126`, while retaining the same real law,
cutoff, clock and budget. In particular no desired concentration bound or
fourth-moment payment is inserted as an input.

## 4. Exact Clock/Fourier consumption, not a root-completion claim

The ClockControl author confirmed the common law contract and all seven
law/support/raw-moment/numeric requirements of its third declaration;
the author reports that module's final independent review is CORRECT.
Read-only inspection of its three frozen declarations confirms that
`iid_bounded_clock_bad_probability_le` takes the actual rho marginal,
the actual bounded iid sample, raw-square normalization in [3/4,4/3],
support h, and precisely the three numeric hypotheses of 2.8. With y>=2,
2.4, 2.6 and 2.8 therefore supply its law/support/moment/numeric inputs.
The iid and actual-law transport remains the accepted fixed-event
ConditionalIID bridge; this scalar-law module does not redefine a sample
conditional measure or assume iid after a sample-dependent selection.

The existing Clock conclusion is

```text
badclock <=2048 sqrt(2 pi) [(1+y)^3 n m3] standardNormalTail y.
```

The still-to-be-implemented bridge's retained-R payment would then yield

```text
badclock <=32768 sqrt(2 pi) R standardNormalTail y
         <=32768 sqrt(2 pi) exp(2) R standardNormalTail x.
```

The composition is a checked mathematical consequence, **not a ninth
public theorem proposed or a new Lean result already certified here**.
It explains why the coarse `n m3<=2/b^3` alone is insufficient: replacing
R by one loses the small-budget factor required in this probability
payment. The original source's `C Lambda_y PhiBar(y)` form also follows
since its drift term is nonnegative. No centered clock is substituted
for `sum A_j^2`, and threshold atoms stay admissible.

LowFrequencyDamping consumes actual rho probability, its real absolute
third integrability and positive Mathlib variance, supplied by 2.4 and
2.6; its gamma remains the genuine `m3/V`, not a centered-law shortcut.
QuadraticCharacteristic/Power can consume the same law and paid drift/
variance data. The damping frequency domain still has to be instantiated
against the source's actual u,v,T restrictions; the bridge does not
convert low-frequency damping into high-frequency damping or complete
the Fourier comparison.

The source conditional-moment lemma's additional gamma comparisons
`gamma asymp n m3`, `gamma<=2h`, `m2<=gamma^2` and `n m3<=2 r_n` are not
additional frozen targets in this batch. Their elementary remaining
comparisons must be supplied if a subsequent noise construction consumes
them. Nothing here claims all of that source lemma or the noise,
regulator, smoothing, Fourier inversion, strict-CDF, zero-energy handling
or C1/C2 root is closed. Scalar square normalization excludes n=0 and a
zero second moment by deduction; no sample event is changed to remove
zero-energy paths.

## 5. Boundary and independent semantic checks

- The retained support is closed `<=h`; the deleted/tail event is strictly
  `h<|z|`. An atom at h stays inside the actual conditional law, in exact
  agreement with both source and the accepted retained API.
- x=0 is included; a=1 has no singularity. Source use may later be x>0.
  epsilon=0 is excluded exactly where division/cutoff/scaling needs it;
  epsilon=1/2, and epsilon=1/8 in 2.8, are included.
- 2.1 and 2.3 allow n=0. All normalized declarations derive n>0 and indeed
  n>=64; no divide-by-zero Bochner convention is used.
- Original finite second moment does not give a global cube or fourth
  moment. All raw high moments above are under the bounded actual rho,
  and every marked original kernel used in their proof has a true
  integrability argument.
- Original centering is essential for positive conditional variance at
  this level. A large-n point mass at `1/sqrt(n)` has square normalization,
  can have arbitrarily small R and be entirely retained, yet has variance
  zero. It violates exactly the original mean-zero premise. The proposal
  does not claim such a false noncentered generalization of 2.6.
- `n>=a^6` alone does not imply `n>=b^6` when epsilon<1. Using only that
  weakened sample-size conclusion would leave a genuine gap. The actual
  R-dependent middle expression pays the epsilon^-6 loss.
- Mere `epsilon<=1/2` and `R<=epsilon^3/8` do not justify the direct scalar
  estimate `256 epsilon^4<=1/2` (its upper endpoint gives 16). The explicit
  source-derived epsilon<=1/8 in 2.8 supplies this numeric step; the scope
  does not silently upgrade the earlier bound. This notes failure of that
  attempted estimate, not a claimed counterexample to the full clock
  probability under weaker parameters.
- A later square/exponential tilt changes the actual measure and all raw
  moments. This proposal proves no tilted-law moment-transfer assertion.

## 6. Existing API, cache and evidence gate

Candidate imports after freeze:

```text
Shao.Probability.TruncationSampleSize
Shao.Probability.RetainedVariance
Shao.Probability.GaussianTail
Mathlib.Probability.Moments.Variance
```

They already provide the needed marked-kernel integration, genuine retained
law, normalization, support, raw/centered integrability and actual Gaussian
tail. TruncationSampleSize imports the existing Regularity positivity. No
ClockControl, LowFrequencyDamping, OQ-specific import or shared migration is
needed to implement these scalar-law statements. Those modules are
consumers, not inputs that encode the proposed conclusions.

Actually inspected dependency source hashes:

```text
TruncationIntegrals d7432b7c579c6e6e0d9980af322437941f59f8f670bebd2dd4770f6cfcf1e234
TruncationSampleSize 017a62c7f2e9e8ed43259d28d145e67b7010152a0c233d671680fcc5a01635de
RetainedMoments 512cf7a51125f18f94f42b4ef855e21290a28f7a3185865a3d375bde8100d6cb
RetainedSample a507e549e2973dd04ce25f22e2c6973e0e6c491433a1d7fd2d88fbb082e86ca4
RetainedVariance 5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6
GaussianTail f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922
ClockControl c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba
```

Server-only read-only imports/API inspection used pinned Lean
`4.36.0-rc1`, Mathlib `807d3836b165983210ee2ecf3cd28f239436949c` and
`workspaces/lead-c12`. Confirmed actual types include
`truncationBudget_scale_one_le`, `truncationBudget_sample_size_lower`,
`integral_retainedCutoffLaw`, `integrable_retainedCutoffLaw_abs_cube`,
`retainedCutoffLaw_centered_moments`, `variance_eq_sub`,
`memLp_two_iff_integrable_sq`, `integral_indicator_one`,
`measureReal_compl`, `cond_isProbabilityMeasure` and the actual
`standardNormalTail_local_comparison` exponent two.

One exploratory import used the nonexistent shortened module name
`Mathlib.Probability.Variance`; the actual already cached module is
`Mathlib.Probability.Moments.Variance` (read from LowFrequencyDamping).
Exploratory guessed Cauchy–Schwarz identifier names were rejected; the
source inspection found actual Holder names, but the paid-drift route
above avoids a new Holder import. These failed probes are not target
check receipts. No cache fetch was requested or performed by this author.
No new dependency cache is currently required by the proposed route.

The final corrected read-only probe imported exactly the four candidate
imports above and checked actual positivity, conditional-integral,
retained variance, real variance and Gaussian comparison APIs. The server
command `taskset -c 0-3 lake env lean --stdin` returned **exit 0, empty
stderr**. It contained only imports/open and `#check` commands, no candidate
declarations or proofs. A preceding transient broker failure reported
`operation_may_have_started=false`; it did not constitute an execution
receipt and the corrected request was safely resubmitted.

The minimal next action is independent source-to-signature review of
these eight declarations, especially 2.2's epsilon^-6 payment, 2.6's real
conditional variance and 2.8's source-derived numeric restriction. Only
after explicit freeze should the new file be implemented, followed by
targeted server checks, all new/semantic-dependency transitive axiom
audit, forbidden-item scan, source hash freeze and independent proof
review. The frozen scope bytes must remain unchanged; progress and
receipts belong in a separate author receipt.
