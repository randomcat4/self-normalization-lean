# Source Fourier scale: true gamma and future-length inputs

Status: PROPOSED FOR INDEPENDENT DECLARATION REVIEW. Analysis and exact proposed signatures only. No new Lean implementation, placeholder, API probe or target check has been created for this unit. Only this owned proposal file is written. All accepted mathematical sources, imports, manifests and caches remain unchanged.

Proposed module: `Shao/Probability/SourceFourierScale.lean`; namespace `Shao`; `set_option autoImplicit false`; open `MeasureTheory ProbabilityTheory`.

The bounded proposal is **zero definitions, two public theorems**. Its nontrivial content is the actual source gamma/moment relation, including `m2<=gamma^2`, and the literal remaining-length transport from the real source time region. It does not construct or estimate triangular chord noise K, Xi or their derivatives, and does not duplicate the concurrent QuadraticChordNoise proposal.

## 1. Accepted coverage and the actual remaining gap

The actual fixed original law is nu, a probability for xi=X/(sigma sqrt n), with original centering and n integral z^2 dnu=1. In particular its raw second moment is 1/n, not one. Fix x and epsilon, put a=1+x, h=epsilon/a, and use the same genuine bounded conditional law throughout:

    rho = ProbabilityTheory.cond nu {z : |z|<=h},
    mu=integral z drho, m2=integral z^2 drho,
    m3=integral |z|^3 drho, V=variance id rho,
    gamma=m3/V, r_n=truncationBudget nu n 0.

The accepted SourceTruncationBridge already supplies rho probability, genuine support, true moment integrability, positive V, n>=64, raw 3/4<=n*m2<=4/3, true 1/2<=n*V<=4/3, n*mu^2<=1/4, V=m2-mu^2, and the real drift/raw-cube/fourth-moment payments. These will be cited directly, not reproved or replaced by new assumptions.

Two of OddPower's normalized inputs are already elementary consequences:

- Its `3/4<=n*m2` is an existing conclusion verbatim.
- Accepted drift plus R<=epsilon^3/8 gives n|mu|<=epsilon/[4(1+x)]<=1/8<=1 under epsilon<=1/2. No eta0 smallness or assumed Lambda bound is needed.
- The existing variance identity, n*mu^2<=1/4 and n*V>=1/2 give m2<=3V/2<=2V<=4V after cancelling the derived positive n. Thus the raw/variance comparison is not a missing new analytic result.

What remains genuinely absent from accepted public source-specific interfaces is the actual raw gamma bridge: positive gamma, Lyapunov m2^(3/2)<=m3, m2<=gamma^2, gamma<=2h and gamma comparable with n*m3, with n*m3<=2r_n. The older `retainedSample_lyapunov_bound` concerns a centered Berry--Esseen cube ratio for a retained row at a different reciprocal parameter; it is not this raw m3/V statement. LowFrequencyDamping and OddPower internally establish m3 positivity but do not expose the source gamma/length conclusions.

The other real gap is length. OddPower requires ell>=6 and ell<=n. Source uses ell=n-i and the regional condition T=ell*m2>=L2*gamma^2, with L2>=2J+4=20. It is invalid to infer ell>=6 from n>=64 alone: i=n gives ell=0. The proposed second statement consumes the **actual source time-region condition**, and derives the length instead of accepting the desired length as a new hypothesis.

## 2. Source provenance and exact anchors

Read-only source SHA256 values, rechecked in the immediately preceding source review and unchanged:

```text
main.tex       beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
supplement.tex b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

| Source anchor | Exact role |
|---|---|
| main:372–392 | Actual epsilon minimum and D3 budget imply 0<epsilon<=1/8<=1/2 and R_n(x)<epsilon^3/8. The local weak <= budget below is a legal weakening. |
| main:423–430, 491–499, 546–551 | True fixed cutoff h_x=epsilon/(1+x), N_x conditioning and genuine one-coordinate rho. The conditional mean need not be zero; rho is fixed as frequencies and comparison thresholds vary. |
| main:622–625; supplement:470–475 | True mu, raw moments, V=tau^2 and gamma=m3/V, not a centered cube or raw-square denominator. |
| supplement:524–531, h:eq:momentbudget1/2/3 | The still-unformalized gamma comparisons within the actual conditional moment lemma. |
| supplement:2045–2135, especially 2099–2121 | Source proof of n*m3<=2r_n, gamma comparable with n*m3, Lyapunov m2^(3/2)<=m3, m3<=h_x*m2, gamma<=2h_x and m2<=gamma^2. This entire source proof was read for this proposal. |
| supplement:2343–2357 | Actual future length ell=n-i and raw time T=ell*m2; the odd Fourier factor is (1/2)[chi(u,v)^ell-chi(-u,v)^ell]Xi. |
| supplement:2461–2462, 3437 | L2>=2J+4, T>=L2 gamma^2, m2<=gamma^2 imply ell>=L2; J=8 gives L2>=20. |
| supplement:3431–3459 | OddPower uses the same actual m2/V and n|mu| payments, and differentiates real powers at fixed rho/v/ell. |

Accepted dependencies inspected/read in this session:

```text
SourceTruncationBridge.lean
  05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1
OddPower.lean (module QuadraticCharacteristicOddPower)
  d526459c86cab6fdd8d4fc207e4950e03993bac0a26e7c2c6a7567f747b1b838
OddPower frozen scope
  005abcc7752ff48345617c7e946dc616494907ad57637017abff82b6ef989c3d
OddPower final independent proof review
  315da0389898c0e6caea7dcd39f7c28d49d6cb02e3ecbf133405fbaea387cb82
```

The OddPower implementation is already fully reviewed CORRECT; its scope/review explicitly left the present gamma and length instantiation open. This new module need only import SourceTruncationBridge and already available elementary integral/sqrt facts; it need not import the downstream OddPower consumer or any chord-noise module.

## 3. Exact proposed declarations

### 3.1 Actual source gamma, raw Lyapunov moment and r_n payment

```lean
theorem sourceTruncation_gamma_bounds
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8) :
    let h : ℝ := epsilon / (1 + x)
    let rho : Measure ℝ := ProbabilityTheory.cond nu {z | |z| ≤ h}
    let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
    let gamma : ℝ := m3 / V
    let r : ℝ := truncationBudget nu n 0
    0 < m3 ∧ 0 < gamma ∧
      Real.sqrt m2 * m2 ≤ m3 ∧
      m2 ≤ gamma ^ 2 ∧ gamma ≤ 2 * h ∧
      (3 / 4 : ℝ) * (n : ℝ) * m3 ≤ gamma ∧
      gamma ≤ 2 * (n : ℝ) * m3 ∧
      (n : ℝ) * m3 ≤ 2 * r ∧ gamma ≤ 4 * r
```

These are statements about the true fixed-x conditional law. No scalar probability/support, global original third moment, positive V, positive gamma, m2<=gamma^2, drift bound or r_n payment is added as an input. Probability/integrability/V positivity come from the accepted original-input bridge. `sqrt m2 * m2` expresses the real nonnegative m2^(3/2) without introducing an arbitrary real-power convention or a new definition.

### 3.2 Derive actual OddPower length/bias/variance inputs from the source region

```lean
theorem sourceTruncation_oddPower_scale_inputs
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : truncationBudget nu n x ≤ epsilon ^ 3 / 8)
    (i : ℕ) (hi : i ≤ n) (L2 : ℝ) (hL2 : 20 ≤ L2)
    (hT :
      let rho : Measure ℝ :=
        ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
      let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
      let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂rho) /
        ProbabilityTheory.variance (id : ℝ → ℝ) rho
      L2 * gamma ^ 2 ≤ ((n - i : ℕ) : ℝ) * m2) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    let m2 : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
    let V : ℝ := ProbabilityTheory.variance (id : ℝ → ℝ) rho
    let ell : ℕ := n - i
    L2 ≤ (ell : ℝ) ∧ 6 ≤ ell ∧ ell ≤ n ∧
      (n : ℝ) * |mu| ≤ 1 ∧ m2 ≤ 4 * V
```

The hT premise is the original Fourier time-region definition T>=L2 gamma^2, evaluated using the exact conditional law and literal Nat subtraction. It is not an assumption of the desired ell>=6, of an odd-power estimate, of m2<=gamma^2 or of positive gamma. L2 is the actual fixed real source constant, with source J=8 giving hL2. The extra source choice kappa sqrt(L2)>=1 and regional time upper bounds are not needed for these particular scale conclusions and are neither assumed as substitute evidence nor claimed here.

The conclusion's first clause in fact preserves the stronger real source lower bound ell>=L2>=20; the second exposes the precise Nat ell>=6 needed by the accepted OddPower signature. ell<=n follows from the actual remaining length. No conversion to the real expression n-i occurs before the natural subtraction.

## 4. Checkable mathematical route

### Reuse before new proof

Use accepted sourceTruncation_law_data for probability, support and h2/h3 under rho; accepted sourceTruncation_sample_size for n>=64; and sourceTruncation_variance_bounds for the true positive V, V=m2-mu^2, nV in [1/2,4/3] and nmu^2<=1/4. None of these proofs or their generic conditioning machinery is copied.

From existing data, n>0 and V>0. Moreover

    nmu^2<=1/4<=(nV)/2,
    m2=V+mu^2<=3V/2<=2V,
    V<=m2,

with cancellation justified by the derived positive n. This supplies the ratio used below and is stronger than the OddPower comparison m2<=4V. It is routine transport of accepted facts rather than a new variance premise.

### Genuine raw Lyapunov inequality without a new cache dependency

Set b=sqrt(m2), so b>=0 and b^2=m2. For t=|z|>=0 the elementary factorization gives

    0<=(t-b)^2(2t+b)=2t^3-3bt^2+b^3,
    3b z^2<=2|z|^3+b^3.

All three terms are truly rho-integrable: accepted raw second/absolute-third integrability plus a probability constant. Integrating and using b^2=m2 yields

    3b*m2<=2m3+b^3,
    b*m2=b^3<=m3.

This is the exact raw Lyapunov payment sqrt(m2)*m2<=m3. It avoids importing or reproving a generic Holder/Jensen subsystem, and requires no original global cube. Since 0<V<=m2, it gives m2>0, b>0 and m3>0 before using gamma's denominator or positivity.

Then bV<=b*m2<=m3 and V>0 imply b<=gamma=m3/V. Squaring nonnegative sides gives m2<=gamma^2. For the upper side, actual support yields |z|^3<=h z^2 rho-a.e.; both sides are integrable, hence m3<=h*m2<=2hV and gamma<=2h. No centered cube is substituted for m3.

### Actual r_n and gamma comparisons

The accepted paid raw cube gives

    n*m3<=2R_n(x)/(1+x)^3.

Reuse accepted truncationBudget_scale_one_le with t=0 and c=1+x>=1. Its actual upper expression is R_n(x)<=(1+x)^3 R_n(0), so positive-denominator algebra gives n*m3<=2r_n. This reuses the accepted real kernel scaling and never assumes a global original third moment or identifies R_n(x) with r_n.

The exact identity gamma*(nV)=n*m3, with positive V and n, together with 1/2<=nV<=4/3 gives

    (3/4)n*m3<=gamma<=2n*m3<=4r_n.

No division by r_n or m3 is needed. All end inequalities allow equality at the frozen weak budget/epsilon endpoints.

### Future length and the remaining OddPower inputs

Let ell=n-i in Nat, and use the first theorem's gamma>0 and m2<=gamma^2. In the literal source time region,

    L2*gamma^2<=ell*m2<=ell*gamma^2.

Since gamma^2>0, cancellation gives L2<=(ell:Real). With L2>=20 this implies the natural ell>=20 and hence ell>=6. Nat.sub_le already gives ell<=n. The i=n (or zero remaining length) boundary cannot satisfy hT because L2>0 and gamma>0; it is excluded by the real region, not by a secretly added length premise.

For bias, accepted sourceTruncation_paid_moments gives

    n|mu|<=2R/(epsilon^2 a)
           <=epsilon/(4a)<=1/8<=1,

using only a>=1, 0<epsilon<=1/2, R<=epsilon^3/8 and positive denominators. Thus no new eta0/epsilon0 or assumed Lambda payment is necessary. The existing variance comparisons already yield m2<=4V as above.

To apply accepted OddPower to rho with ell=n-i, directly cite sourceTruncation_law_data's probability and h3, sourceTruncation_variance_bounds' positive V and 3/4<=n*m2, then the second theorem's ell/bias/comparison outputs. Its frequency premises remain the genuine closed strip |u|<=1/(128gamma), |v|<=|u|/(128gamma) with this same fixed rho and actual raw gamma. There is no claim that all u,v satisfy that strip.

## 5. Boundaries, independence and remaining work

- Normalization excludes n=0; accepted sample size derives n>=64. No n>0 or positive V/gamma premise is added. gamma positivity is established before cancelling gamma^2 or V.
- x=0, epsilon=1/2 and R=epsilon^3/8 remain valid local endpoints. The actual source has the smaller epsilon<=1/8 and strict D3 budget, which supply these weak hypotheses. h>0 and a>=1 protect the actual cutoff.
- Atomic and noncentered conditional laws are allowed. Original mean zero does not imply conditional mean zero; V remains the true variance, while m2/m3 are the original-point raw moments under rho.
- All future lengths are literal Nat n-i. hT is essential source-region data; it is not silently replaced by desired ell>=6 or inferred merely from large n. Empty future is incompatible with hT, while regions with T<L2 gamma^2 remain outside the second theorem.
- This source gamma is m3/V, not m3/m2, a centered absolute cube/V, a Berry--Esseen ratio involving sqrt(n), or a freely chosen positive scale. These substitutions could change the real frequency domain and are not permitted.
- No sample iid, fixed-event conditional sample transport or clock probability is reproved; accepted SourceClockBridge and ConditionalIID remain separate consumers. No noise support/moment, triangular K, Xi identity, full noise differentiation or chord construction appears here.
- These two statements deliver only missing scalar Fourier scale/length inputs. They do not prove high-frequency or cone bounds, complex shifts/tilts, oscillatory inversion, regional integrals, smoothing/noise construction, desmoothing contraction or C1/C2 roots.

This proposal followed source/code reading only. No Lean process or package/cache action was run for it. After independent declaration review and root freeze, any implementation must preserve these exact signatures, prove true integrability/positivity and Nat casts, pass the new target on the designated server, enumerate all module-owned public/private/generated constants and transitive whitelist dependencies, and receive a new independent proof/source review.
