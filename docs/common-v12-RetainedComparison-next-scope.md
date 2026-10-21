# Proposed next unit: the actual conditional retained comparison

Status: PROPOSED; exact signatures below await independent statement review
and coordinator freeze. No target Lean implementation has been written.
Only this scope and read-only server API probes belong to this author.

The smallest substantive next result is a genuine probability comparison,
but not yet a Gaussian estimate: on a fixed positive-probability retained
fiber, the original weak crossing probability is at most the canonical raw
retained product crossing probability at the deletion threshold. That last
probability also has an exact representation under a real standardized
product law, with the raw drift and raw square sum restored in its event.
The normalization and its actual moments are proved from the accepted raw
and centered moments, rather than supplied as assumptions.

## 1. Actual source anchors and current frontier

Read-only sources, checked at their actual bytes:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

Their absolute local root is `C:/game/shao/current/c12/`.

| Source anchor | Actual content | Proposed coverage |
|---|---|---|
| Supplement 82-99, `h:supp:xn` | Both source branches give the literal `H_x=n E F(x xi)<=1`, `x^6<=n`; the tail proof later reduces to `x>=8`. | Preserve these actual premises; the deterministic/moment helper only needs `x>=2`. |
| Supplement 126-140, `h:supp:deletion` / `h:eq:deletion` | For a fixed deleted set of size `j<n`, a weak crossing at `x` implies a weak retained crossing at `sqrt(x^2-j)`; square-sum zero is included. | Consume the already proved chronological deletion theorem. |
| Supplement 144-162 | Original random `J` is the bad/deleted set `|xi_i|>1/x`; only fixed fibers with positive probability and `j<=x^2/2` enter `h:supp:conditionalcoarse`. | New statements use the complementary good/retained set `s`, with `j=n-s.card`; no unconditional random-length iid assertion. |
| Supplement 171-185 | On a fixed fiber, the ascending retained sample has common law `xi ||xi|<=1/x`, retained size `m=n-j>=1`, and threshold `y=sqrt(x^2-j)` with `x/sqrt(2)<=y<=x`. | Assemble the actual path product law and event inequality, rather than only cite coordinate iid. |
| Supplement 187-209 | Actual conditional raw moments give the bounded-random inputs with `D=2`; then the source applies the bounded-random theorem and Mills comparison. | Raw/centered moments already exist. This unit reaches the actual canonical product event to which that still-open analysis theorem must apply. |
| Supplement 1075-1084, `h:supp:BE` | Petrov's Berry--Esseen bound uses the actual centered third moment divided by `tau^3 sqrt(m)`; strict CDF and interval consequences are needed too. | Normalize the actual law and give its true mean, square moment, integrability, and third-moment parameter. No BE conclusion is assumed. |
| Supplement 1203-1236, `h:supp:completion` | Maximum-to-final-sum comparison uses a first-passage decomposition plus Chebyshev/BE. | An open later analytic/probabilistic dependency, not a hypothesis of this unit. |
| Supplement 1240-1309, `h:supp:boundedendpoint` | Centering, exponential tilting, tilted variance/third-moment bounds, and interval BE yield the endpoint Gaussian tail with its Mills factor. | Still open; the present normalized moments alone are not this result. |
| Supplement 1313-1387, bounded-random proof | Split the actual random square sum, perform a square tilt, control tilted raw moments, and sum denominator layers including the zero-square layer. | Still open; cannot replace the random square sum by its expectation. |
| Main 421-430, `h:eq:truncation` | A different cutoff `h_x=epsilon/(1+x)` and the all-good event are used in the fine comparison. | The general fixed-fiber path-law result below applies with arbitrary measurable good set and `s=univ`. The coarse moment statements must not be silently reused at this different cutoff. |

Current checked interfaces give conditional coordinate iid, retained raw
moments, actual centered variance/third moments, and pointwise deletion.
The immediate missing bridge is their full path-law and event-level
composition. None of the proposed theorems takes the desired conditional
tail bound, a Gaussian comparison, a Berry--Esseen conclusion, positive
variance, a Jensen bound, or a global original third moment as an assumption.

## 2. Exact new definitions: one actual normalization and its law

Proposed new module: `Shao/Probability/RetainedComparison.lean`.
Imports: existing `RetainedVariance`, `RetentionEvent`, `MeasurablePath`,
and `Basic.Deletion`. No shared root import or old source is changed.

Use `open MeasureTheory ProbabilityTheory`, `autoImplicit false`, and
the following two definitions in namespace `Shao`:

```lean
noncomputable def retainedStandardize (ν : Measure ℝ) (x z : ℝ) : ℝ :=
  let μx : ℝ := ∫ u : ℝ, u ∂retainedCutoffLaw ν x
  let Vx : ℝ := ∫ u : ℝ, (u - μx) ^ 2 ∂retainedCutoffLaw ν x
  (z - μx) / Real.sqrt Vx

noncomputable def retainedStandardLaw (ν : Measure ℝ) (x : ℝ) : Measure ℝ :=
  Measure.map (retainedStandardize ν x) (retainedCutoffLaw ν x)
```

These do not redefine the retained cutoff, its mass, or its genuine conditional
law. They are an actual affine observable and its actual pushforward.
At zero variance Lean's division remains total, but no unit-variance or
inverse-normalization conclusion will be asserted there. The source
theorems below derive strictly positive variance before using its inverse.
For fixed `nu,x`, the observable is continuous (its integral/square-root
parameters are constants in `z`), even before positivity is known.

There is no new public `mean`, `variance`, `fiber`, `productMeasure`,
`GaussianTail`, or abstract normalized-law definition. All such quantities
below are explicit existing operations or local `let` expressions.

## 3. Exact public theorem proposals

Three public results are proposed. Any measurability, affine inverse, or
integral-scaling helper needed for their proofs may remain private; no
additional public mathematical hypothesis is authorized.

### 3.1 Fixed-fiber full path law, including fixed coordinate transforms

Namespace `Shao.Probability`; variables
`{n : ℕ} {Ω : Type*} [MeasurableSpace Ω]`.

```lean
theorem retained_cond_transform_path_map_eq_pi
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (s : Finset (Fin n)) (hs : 0 < s.card)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hA : μ {ω | retentionSet X B ω = s} ≠ 0)
    (g : ℝ → ℝ) (hg : Measurable g) :
    Measure.map
        (fun ω (r : Fin s.card) => g (X (Shao.retainedIndex s r) ω))
        (cond μ {ω | retentionSet X B ω = s}) =
      Measure.pi (fun _ : Fin s.card => Measure.map g (cond ν B))
```

The choice `g=id` simplifies to the full genuine raw retained-path law

```text
map (fun omega => retainedPath (samplePath X omega) s) (cond mu A_s)
  = pi_(Fin s.card) (cond nu B).
```

The choice `B=retainedCutoffSet x`, `g=retainedStandardize nu x` gives the
actual full standardized conditional path law `pi retainedStandardLaw`.
Both choices use the same increasing enumeration, not an arbitrary or
sample-dependent permutation. The common good-set mass and conditional
probability are derived using `hs` and `hA`; no independent conditional-iid
axiom or extra one-coordinate positivity input is introduced.

The theorem has no original centering, moment, cutoff-scale, or size
hypothesis, so it also supplies the main proof's all-good conditional law
for its own measurable good set and nonempty `s=univ`. It does not transfer
coarse cutoff-specific numeric bounds to that other cutoff.

### 3.2 True standardized single-coordinate moments and Lyapunov quantity

Namespace `Shao`:

```lean
theorem retainedStandardLaw_moments
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : (j : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, truncationF (x * z) ∂ν) ≤ 1) :
    IsProbabilityMeasure (retainedStandardLaw ν x) ∧
      Integrable (fun z : ℝ => z) (retainedStandardLaw ν x) ∧
      Integrable (fun z : ℝ => z ^ 2) (retainedStandardLaw ν x) ∧
      Integrable (fun z : ℝ => |z| ^ 3) (retainedStandardLaw ν x) ∧
      (∫ z : ℝ, z ∂retainedStandardLaw ν x) = 0 ∧
      (∫ z : ℝ, z ^ 2 ∂retainedStandardLaw ν x) = 1 ∧
      (∫ z : ℝ, |z| ^ 3 ∂retainedStandardLaw ν x) /
          Real.sqrt ((n - j : ℕ) : ℝ) ≤
        64 / (Real.sqrt (x ^ 2 - (j : ℝ))) ^ 3
```

This is a proved normalization of the actual law, not a measure with those
moments postulated. The original global cube is not an input. The true
conditional centered cube and variance from `RetainedVariance` suffice.
The constant 64 is the already checked reusable Lyapunov bound, not a
literal Gaussian error constant or a conclusion of an invoked BE theorem.

### 3.3 Actual conditional crossing comparison, with exact standardized event

Namespace `Shao.Probability`, with the same `n,Omega` variables as 3.1:

```lean
theorem retained_cond_upperCrossing_comparison
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (s : Finset (Fin n)) (x : ℝ)
    (hx : 2 ≤ x) (hsize : x ^ 6 ≤ (n : ℝ))
    (hj : ((n - s.card : ℕ) : ℝ) ≤ x ^ 2 / 2)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hcut : (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂ν) ≤ 1)
    (hA : μ {ω | retentionSet X (Shao.retainedCutoffSet x) ω = s} ≠ 0) :
    let A : Set Ω := {ω | retentionSet X (Shao.retainedCutoffSet x) ω = s}
    let j : ℕ := n - s.card
    let η : Measure ℝ := Shao.retainedCutoffLaw ν x
    let ζ : Measure ℝ := Shao.retainedStandardLaw ν x
    let μx : ℝ := ∫ z : ℝ, z ∂η
    let τx : ℝ := Real.sqrt (∫ z : ℝ, (z - μx) ^ 2 ∂η)
    let y : ℝ := Real.sqrt (x ^ 2 - (j : ℝ))
    ∃ hn : 0 < n, ∃ hs : 0 < s.card,
      (cond μ A) {ω | samplePath X ω ∈ Shao.upperCrossing hn x} ≤
        (Measure.pi (fun _ : Fin s.card => η)) (Shao.upperCrossing hs y) ∧
      (Measure.pi (fun _ : Fin s.card => η)) (Shao.upperCrossing hs y) =
        (Measure.pi (fun _ : Fin s.card => ζ))
          {a : Shao.Path s.card |
            (fun r : Fin s.card => μx + τx * a r) ∈ Shao.upperCrossing hs y}
```

The existential proof arguments expose derived original and retained
nonemptiness without adding them as source hypotheses. Proof irrelevance
means no event depends on a choice between proofs of the same inequality.
All three probabilities are actual `ENNReal` measure values; no `.toReal`
subtraction or probability normalization is hidden in this interface.

The first inequality is the desired event-level application of deletion
and the actual conditional product law. The equality then gives a genuine
standardized-product representation of that same raw retained event. The
first inequality is the proposed new proof obligation; no Gaussian bound or
version of that bound is assumed to obtain it.

## 4. Correct event after standardization

Let `m=s.card`, `mu=mu_x`, `tau=tau_x>0`, and
`R(a)_i=mu+tau a_i`. The rightmost event above is exactly
`R^{-1}(upperCrossing hs y)`. For a prefix `1<=k<=m`, the necessary actual
identities are

```text
prefixSum (R a) k = (k:R)*mu + tau*prefixSum a k,
energy (R a) = tau^2*energy a
               + 2*mu*tau*prefixSum a m + (m:R)*mu^2.
```

Consequently the rightmost weak event is exactly

```text
there exists k, 1<=k<=m, such that
  y * sqrt(tau^2*energy a + 2*mu*tau*prefixSum a m + m*mu^2)
    <= tau*prefixSum a k + k*mu.
```

For `k>m` the first displayed identity would need `min(k,m)` in its drift
term; this proposal only uses bounded prefixes. No incorrect unsaturated
prefix formula is assumed. Nor can the event be replaced by
`upperCrossing hs y` of the centered path: centering changes both the drift
of each prefix and its actual final square sum. Unit variance under `zeta`
does not turn its realized energy into the constant `m`.

If the restored raw energy is zero, the restored path is identically zero
and its weak crossing holds at a genuine nonempty prefix. That case remains
in the rightmost event even if the standardized coordinates themselves are
nonzero. Removing it or imposing a positive-energy hypothesis would change
the source event.

## 5. Proof decomposition without a probability-comparison assumption

1. For 3.1, derive the actual positive good-set mass and conditional iid
   family from `iid_retained_cond_retentionSet_eq`. Give the conditional
   measure its true probability instance via positive `hA`. Apply the
   already checked finite iid map-to-product theorem to the increasing
   family. Then apply the coordinate map `g` on each side; measurable
   finite-product maps and `Measure.pi_map_pi` produce the claimed complete
   transformed path law. All conditional normalizers are the existing `cond`.
2. For 3.2, derive `q_x>0`, `m>=1`, and `V_x>0` from the accepted source
   size/mass/variance results. With `tau=sqrt(V_x)>0`, the true centered
   id/square/cube are integrable. Constant scaling gives integrability of
   each composition with `retainedStandardize`; `integrable_map_measure`
   transfers it to the actual pushforward law. `integral_map` and integral
   scaling give mean zero, square `V_x/tau^2=1`, and actual cube
   `C_c/tau^3`. The existing exact bound
   `C_c/(sqrt(m)*tau^3)<=64/y^3` then gives the last output.
3. For 3.3, put `j=n-s.card`. A finite subset of `Fin n` has `s.card<=n`,
   so `n-j=s.card` follows by natural subtraction, not a signed cast.
   Apply the existing size/threshold bounds to get `n>=64`, `j<n`,
   `s.card>=1`, `x>0`, `j<x^2`, and `1<=y<=x`. For the fixed deleted
   complement `I=s^c`, derive `I.card=j` and `univ\\I=s`; chronological
   deletion gives the pointwise inclusion for every original path. Apply
   measure monotonicity under the true `cond mu A`, then use 3.1 with
   `g=id`, `B=retainedCutoffSet x` and the measurable weak crossing set.
4. Apply 3.1 again with the actual normalization `g`. Under the derived
   `tau>0`, the scalar identity
   `mu+tau*((z-mu)/tau)=z` holds everywhere, so the restored standardized
   path is exactly the raw retained path, before taking any probability.
   Measurability of affine path maps and the crossing set lets both event
   probabilities be identified with their canonical product probabilities.
   No probabilistic tail estimate enters this equality.

The already proved raw moments with `D=2` apply to the raw canonical
product law in 3.3 after substituting `n-j=s.card`. The new result is the
complete bridge to that product event; restating those same raw inequalities
as new public theorems is unnecessary.

## 6. Strict/closed, zero, and parameter boundaries

- The good cutoff is closed: `|z|<=1/x`. Its complement is strictly
  `|z|>1/x`, so equality atoms remain retained. The original source bad set
  `J` is the complement of the good `retentionSet`; it is not renamed as
  the good set without the explicit complement.
- All crossing events retain weak `>=` at nonempty prefixes. The complement
  is the strict survival event. No continuous-distribution or no-atom
  hypothesis is needed. A future BE proof must establish strict CDF bounds
  by limits instead of assuming atomlessness of the retained law.
- Generic theorem 3.1 intentionally has `hs>0`, matching the existing
  retained-coordinate interface which derives `nu B!=0`. It makes no claim
  about unit-variance or a common-law normalizer from an empty retained set.
  The empty finite-family conditioning theorem is already separate in
  `ConditionalIID`; no convention about `upperMax` on length zero is added.
- The source theorems derive `n>=64` from `x>=2` and `x^6<=n`, and then
  derive `m>=1` from `j<=x^2/2`. Thus `n=0` and `s=empty` are ruled out by
  the actual hypotheses, not excluded through an extra premise. The
  source's all-deleted case belongs to the separate large-deletion branch.
- `j=0`, `s=univ`, and equality in `j<=x^2/2` are allowed. At `j=0`,
  `m=n` and `y=x`; no threshold slack is manufactured.
- The size lemmas give `x/sqrt(2)<=y<=x`, `y>=1`, and strict positivity of
  `x,y,tau,sqrt(m)`. The source threshold relation is never changed to
  `1+x`, nor is a square root outside its nonnegative domain used.
- The law/normalization depends on the fixed original real law and `x`;
  the fixed set changes only its retained coordinates, size, and `y`.
  Neither the law nor the affine map is selected using future observations.
- On the fine-comparison main event, use 3.1 with its actual
  `B={|z|<=epsilon/(1+x)}`. Invoking 3.2/3.3 there would require a deliberate
  change of cutoff scale and fresh verification of every budget/size
  premise. This proposal makes no such identification.

## 7. Precise open analysis gates

The first still-open source conclusion after 3.3 is `h:supp:boundedrandom`:
there exists `C_D` depending only on a fixed `D>=1`, uniformly over the
sample length, threshold, and laws satisfying its actual raw moment bounds.
For orientation, using the existing Mathlib Gaussian measure, the later
goal can be stated exactly as follows. It is **not** a theorem assumed by
3.1-3.3, not part of this unit's implementation batch, and not a new axiom:

```lean
-- Later open goal only; import Mathlib.Probability.Distributions.Gaussian.Real.
theorem bounded_product_upperCrossing_normal_tail_open_goal
    (D : ℝ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) (hk : 0 < k) (y : ℝ) (hy : 1 ≤ y)
        (η : Measure ℝ) [IsProbabilityMeasure η],
        (∀ᵐ z : ℝ ∂η, |z| ≤ 1 / y) →
        Integrable (fun z : ℝ => z ^ 2) η →
        Integrable (fun z : ℝ => |z| ^ 3) η →
        ((1 / 2 : ℝ) ≤ (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂η) ∧
          (k : ℝ) * (∫ z : ℝ, z ^ 2 ∂η) ≤ 2) →
        (k : ℝ) * |∫ z : ℝ, z ∂η| ≤ D / y →
        (k : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂η) ≤ D / y ^ 3 →
        (Measure.pi (fun _ : Fin k => η)) (upperCrossing hk y) ≤
          ENNReal.ofReal (C *
            ((ProbabilityTheory.gaussianReal 0 1) (Set.Ici y)).toReal)
```

The `C` is chosen before `k,y,eta`; it cannot depend on the original law,
on the retained set, or on the sample size. Setting `D=2`, composing this
future theorem with 3.3, and then proving the Gaussian Mills ratio for
`y=sqrt(x^2-j)>=x/sqrt(2)` would yield the source's fixed-fiber bound
`C exp(j/2) PhiBar(x)`. Averaging over the random deleted set additionally
needs its binomial exponential-moment and large-deletion estimates from
supplement 144-168. None is silently certified by this scope.

The open analytic chain is substantial:

- Petrov BE, including strict-CDF and interval consequences, is an external
  source assertion at supplement 1077-1084. No matching Berry--Esseen
  theorem was found by the read-only name/text search of this pinned
  Mathlib's `Mathlib/Probability` tree, or in the current project sources.
  This is a recorded search result, not a proof that no equivalent theorem
  can exist under another name. No external theorem is introduced as an axiom.
- A BE additive error `O(y^-3)` from the new standardized third moment
  alone is not an `O(PhiBar(y))` relative tail bound for large `y`. The
  source instead uses exponential tilting and interval control, following
  completion. An exponential maximum inequality alone also does not supply
  the necessary Mills factor `1/(1+y)` at the same exponential rate.
- Even the fixed-variance endpoint result is insufficient for the random
  denominator: the source's square tilt, genuine changed probability law,
  variance/moment transfer, and layer sum remain necessary obligations.
  Replacing the actual energy by `m Var` or `m E z^2` would be incorrect.
- Spitzer's identity is a separate external gate for the earlier survival
  argument at supplement 1086-1105 (maximum including the empty prefix).
  This unit neither invokes it nor confuses that maximum with the
  nonempty-prefix crossing used here.

## 8. Read-only fixed-version API evidence and remaining requirements

All Lean API probes ran on the designated server worktree `lead-c12` with
Lean `4.36.0-rc1`, Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`.
The final probe imported only existing project modules and ran
`taskset -c 0-3 lake env lean --stdin`; exit 0. It did not add a target
definition, theorem, placeholder, source file, `.olean`, or cache artifact.

Confirmed APIs needed by this proposal:

| API | Actual requirement / use |
|---|---|
| `cond_isProbabilityMeasure` | Original measure finite and actual fiber mass nonzero. |
| `iid_retained_cond_retentionSet_eq` | Fixed measurable good event, positive fiber, nonempty ascending retained set. |
| `iid_samplePath_map_eq_pi` | Actual probability instances for conditional sample and common law. |
| `Measure.map_map`, `Measure.map_apply` | Measurable affine/coordinate maps and measurable crossing events. |
| `Measure.pi_map_pi` | Coordinate a.e. measurability and sigma-finite mapped marginals; probability provides the latter. |
| `Measure.pi` | The product-measure expression itself accepts arbitrary finite marginal measures; the statement needs no hidden probability instance for a local `let` law. Its probability meaning is proved from the source hypotheses. |
| `Measurable.of_eval` | Construct finite path-map measurability coordinatewise. |
| `integrable_map_measure`, `integral_map` | A.e. measurability of normalization and strong measurability of real polynomial observables. |
| `iIndepFun.comp`, `IdentDistrib.comp` | Available alternative direct proof of transformed iid; no new independence hypothesis. |
| `measurableSet_upperCrossing` | Existing exact weak nonempty-prefix event is measurable. |
| `upperCrossing_retainedPath_of_deletion` | Fixed deleted set, positive original/retained length, `x>0`, strict `j<x^2`; all derived in 3.3. |
| `Finset.card_compl`, `card_le_univ`, `Nat.sub_sub_self` | Preserve natural cardinalities and identify `n-(n-s.card)=s.card`. |

Exploratory checks also established that the guessed names `Measure.map_pi`
and `Measurable.pi_lambda` are not present; use the confirmed APIs above.
No target implementation is claimed to have compiled. No local Lean command
or cache download was run. The current shared cache was sufficient for these
existing-module probes. The later Gaussian gate was only read at its source
type (`gaussianReal : Real -> NNReal -> Measure Real`), not imported or proved
for this unit.

Dependency source hashes read for this proposal:

```text
ConditionalIID   855c2eb0e560ac9372505f8b41551a9895b9eb753be3ce2b3f3752be845af787
RetentionEvent   e27ec2b7f94d55cba013b1cc578dafba25b0056172a6d5c930eb62228c59bb43
RetainedSample   a507e549e2973dd04ce25f22e2c6973e0e6c491433a1d7fd2d88fbb082e86ca4
RetainedVariance 5361ad40f82d6c273135729df66c056d01a9cf090d1e9f80cffce44f61296fa6
Deletion         2bb43cdec4e7ccce21e0ca2981d1ca4178d791970c0b983665653543bee69687
```

The coordinator controls dependency acceptance and the new independent
statement review. Only after review and an explicit freeze would this author
implement the two new definitions and three public results, then perform
targeted server checks and a full transitive standard-axiom audit. No root
probability comparison, Gaussian theorem, or complete C1/C2 theorem is claimed
closed at this scope stage.
