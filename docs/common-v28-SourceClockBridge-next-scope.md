# Source fixed-event conditional sample and paid clock probability

Status: PROPOSED FOR INDEPENDENT DECLARATION REVIEW. Analysis and exact signatures only. No SourceClockBridge Lean implementation, placeholder, target check or new mathematical definition has been created. The accepted SourceTruncationBridge source is unchanged at SHA256 05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1. Root owns freeze, shared imports/manifest/cache and integration.

Proposed module: `Shao/Probability/SourceClockBridge.lean`.
Namespace `Shao.Probability`; `set_option autoImplicit false`; open `MeasureTheory ProbabilityTheory`. The bounded unit is **zero new definitions, three public theorems**. All local `let` expressions below use actual existing measures, coordinates and path statistics.

## 1. Coverage check and next missing dependency

Read-only inventory of the observed server origin/main c7f54caf9d43d6ee149c9d11aa0cb88d552d0b1b, the current local accepted drafts, and the new SourceTruncationBridge author commit d472d38f39f7a68025a9409a47c2a11a55e0e8c1 found no existing direct source-clock theorem. No new source-clock proposal was found elsewhere in drafts/c12. The actual public clock names are exactly the three generic ClockControl results.

- `ConditionalIID.indep_cond_joint_map_eq_pi` proves a generic true conditional vector law **assuming** a nonzero fixed-coordinate event. Its retained-sample corollary handles a specified positive-probability mixed retention event. Neither proves the actual source N_x event has positive mass from R_n(x), nor pays its clock probabilities.
- `SourceTruncationBridge` supplies genuine scalar law/support, raw moments, true variance, retained-R payments and all three numerical ClockControl inputs. It has no sample space, original iid sample, N_x conditional sample measure or probability of a clock event.
- `ClockControl.iid_bounded_clock_bad_probability_le` proves the actual pair of bad-clock probabilities for an already supplied bounded iid sample and law. Its hypotheses still require that conditional iid law, support, raw normalization and three numerical bounds.
- `FiniteIIDMoments` contains actual finite sum/pair moment identities, but no source cutoff or bad-clock statement. The all-x final-clock result below can use Mathlib's existing independent-sum variance and Chebyshev APIs directly; this proposal does not duplicate a generic finite-moment module.
- `LindleySignedBlock` pays an entire history-localized signed late block by P(E), with constant one. It does not bound the actual low-clock probability. The first event paid below is precisely the E used in supplement:847–858; no termwise `(n-k) P(E)` loss is introduced.

Thus this is a missing direct application bridge, not another generic exponential/deviation inequality or a restatement of the scalar inputs. The third declaration also closes the actual clock cost b_x used by desmoothing, including the separate small-x source branch. It does not construct smoothing noise or prove the Fourier comparison, desmoothing sandwich/contraction, untruncated bad-large term or C1/C2 roots.

## 2. Source provenance and law contract

Source bytes were rehashed for this analysis:

```text
C:/game/shao/current/c12/main.tex
beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06
C:/game/shao/current/c12/supplement.tex
b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd
```

| Source anchor | Role in this unit |
|---|---|
| main:372–392, h:eq:proofparameters and h:eq:1 | Actual D3 parameters imply epsilon>0, epsilon<=1/8 and R_n(x)<epsilon^3/8. The epsilon<=1/8 consequence uses the second minimum branch 1/[4(K+1)L], not merely epsilon<=epsilon0/2. |
| main:423–430, h:eq:truncation | xi=X/(sigma sqrt n); h_x=epsilon/(1+x); N_x is the intersection of all n closed coordinate cutoff events. |
| main:440–455, h:eq:truncationprob and h:eq:conditioningprob | Original-law union bound gives P(N_x^c)<=epsilon^(-3) R_n(x), hence positive true conditioning mass. |
| main:491–499, h:eq:conditional-law-measure | P_x^*=cond P N_x, with N_x fixed as the comparison threshold varies. |
| main:546–556, h:eq:conditionallaw and h:eq:boundedstatistics | Under P_x^*, A_j=xi_j are iid with rho=cond nu {|z|<=h_x}; Q_j is the actual sum of A_i^2. The conditional mean need not vanish. |
| main:624–640, h:eq:Lambda and h:eq:comparisonthresholds | Lambda_y=(1+y)n|mu|+(1+y)^3 n m3; actual source thresholds have y>=gamma and abs(y-x)<=1/[2(1+x)]. |
| supplement:836–846, h:lem:clock and h:eq:clock | For those source thresholds with y>=2, pay P_x^*(Q_floor(n/2)<1/16)+P_x^*(Q_n outside [1/4,2]). |
| supplement:3078–3150, h:supp:clock-proof | Genuine centered-square exponential/cosh excess, small fourth moment, strict/closed event inclusions and normal-tail payment. These are already implemented generically by ClockControl; this unit composes their actual source inputs. |
| supplement:847–858 | Consume the low-half-clock probability to pay the entire signed late block. |
| main:763–782, h:eq:delta and h:eq:sandwichcost; supplement:3894–3907 | b_x=P_x^*(Q_n outside [1/4,2]); large x uses clock at y=x, while 0<x<2 uses Var(Q_n)<=n m4 and Chebyshev b_x<=4 n m4. The resulting b_x<=C R_n(x) Tail(x) is required in removing smoothing. |

For all signatures, X denotes the already normalized **original** coordinates xi_j on the original sample space, not a newly centered version and not iid coordinates assumed under an unexplained conditional law. Their actual common original law nu is a probability with n integral z^2 dnu=1, so its raw second moment is 1/n, not one. Original mean zero is retained in declarations 2 and 3 to consume the accepted raw-second-moment/variance bridge and match the actual source assumptions. It is not a conditional-mean-zero assumption.

Write a=1+x, h=epsilon/a, B={z:|z|<=h}, A=N_x=intersection_i X_i^{-1}(B), mu_x=cond mu A, rho=cond nu B, R=truncationBudget nu n x. The very same A, mu_x and rho are used for every y. No sample-dependent selection, additional conditioning on a clock, translated law or exponential/square/joint tilt appears.

## 3. Exact proposed signatures

### 3.1 Derive the actual fixed source conditional sample

```lean
theorem sourceTruncation_conditioned_sample
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hR : Shao.truncationBudget ν n x ≤ epsilon ^ 3 / 8) :
    let h : ℝ := epsilon / (1 + x)
    let B : Set ℝ := {z | |z| ≤ h}
    let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
    let μx : Measure Ω := ProbabilityTheory.cond μ A
    let rho : Measure ℝ := ProbabilityTheory.cond ν B
    μ.real (Aᶜ) ≤ Shao.truncationBudget ν n x / epsilon ^ 3 ∧
      (7 / 8 : ℝ) ≤ μ.real A ∧
      IsProbabilityMeasure μx ∧
      Measure.map (samplePath X) μx = Measure.pi (fun _ : Fin n => rho) ∧
      iIndepFun X μx ∧
      (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μx rho)
```

This statement has no original normalization, centering, n>0 or conditioning-mass premise. The complement mass follows from the accepted strict source tail budget, marginal laws and the finite union bound; 7/8 is the actual consequence of the displayed weak hR and strengthens the source's sufficient 3/4. The probability instance, true conditional iid and true marginals are outputs.

The n=0 case is intentionally admitted: A is the whole sample space, mu_x=mu, all coordinate/marginal clauses are empty, and the vector law is the empty product probability. It does **not** assert IsProbabilityMeasure rho when n=0, since B may have zero mass in that general unnormalized case. For n>0, an actual index and positive A imply nu(B)>0 before any conditional marginal is used as a probability. Declarations 2 and 3 derive n>=64 and scalar rho probability from the accepted normalized bridge.

### 3.2 Source bad-clock pair with the real small-moment and R factors

```lean
theorem sourceTruncation_clock_bad_probability_le
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hR : Shao.truncationBudget ν n x ≤ epsilon ^ 3 / 8)
    (y : ℝ) (hy : 2 ≤ y)
    (hneigh : |y - x| ≤ 1 / (2 * (1 + x))) :
    let h : ℝ := epsilon / (1 + x)
    let B : Set ℝ := {z | |z| ≤ h}
    let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
    let μx : Measure Ω := ProbabilityTheory.cond μ A
    let rho : Measure ℝ := ProbabilityTheory.cond ν B
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let R : ℝ := Shao.truncationBudget ν n x
    let bad : ℝ :=
      μx.real {ω | Shao.prefixSquares (samplePath X ω) (n / 2) < (1 / 16 : ℝ)} +
        μx.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2}
    bad ≤ 2048 * Real.sqrt (2 * Real.pi) *
        ((1 + y) ^ 3 * (n : ℝ) * m3) * Shao.standardNormalTail y ∧
      bad ≤ 32768 * Real.sqrt (2 * Real.pi) * R * Shao.standardNormalTail y ∧
      bad ≤ 32768 * Real.sqrt (2 * Real.pi) * Real.exp 2 *
        R * Shao.standardNormalTail x
```

The first clause preserves the actual conditional raw cube, not merely a bare exponential or a constant probability. Since the drift contribution to the source Lambda_y is nonnegative, it also gives the source h:lem:clock form with constant 2048 sqrt(2 pi). The second and third clauses retain the genuinely small original R factor; 32768=2048*16.

The source's exact smaller neighborhood 1/[2(1+x)] is written in the signature. It implies the accepted weak 1/(1+x) neighborhood by positive-denominator algebra. The final probability estimate remains explicitly restricted to y>=2. It does not extend the generic cosh/normal-tail argument to y<2.

The source also asks y>=gamma. The clock proof itself does not need this lower bound once y>=2 and the bounded-law inputs are supplied; the proposed theorem is valid for the larger displayed range and therefore covers every source-admissible y. This is a strengthening of the conclusion's applicability, not an extra root assumption or an identification of gamma with zero. If an explicit check is desired, accepted true variance bounds and support already give gamma=m3/Var_rho(id)<=8h/3<=1/3<2 here: m3<=h*m2, n*m2<=4/3, n*Var>=1/2 and n>0. The tighter source gamma<=2h is not needed or claimed by this unit.

### 3.3 Actual final-clock Chebyshev payment and all-x source cost

```lean
theorem sourceTruncation_final_clock_probability_le
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
    (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnorm : (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂ν) = 1)
    (hmean : (∫ z : ℝ, z ∂ν) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hR : Shao.truncationBudget ν n x ≤ epsilon ^ 3 / 8) :
    let h : ℝ := epsilon / (1 + x)
    let B : Set ℝ := {z | |z| ≤ h}
    let A : Set Ω := ⋂ i : Fin n, X i ⁻¹' B
    let μx : Measure Ω := ProbabilityTheory.cond μ A
    let rho : Measure ℝ := ProbabilityTheory.cond ν B
    let R : ℝ := Shao.truncationBudget ν n x
    let bad : ℝ :=
      μx.real {ω | Shao.energy (samplePath X ω) ∉ Set.Icc (1 / 4 : ℝ) 2}
    bad ≤ 4 * (n : ℝ) * (∫ z : ℝ, z ^ 4 ∂rho) ∧
      bad ≤ 8 * epsilon * R / (1 + x) ^ 4 ∧
      bad ≤ (32768 * Real.sqrt (2 * Real.pi) +
        1 / Shao.standardNormalTail 2) * R * Shao.standardNormalTail x
```

No positive-x premise is needed: the source uses 0<x<2 for the small branch, but x=0 is a valid harmless endpoint of this standalone clock estimate. The first two clauses are valid for all displayed x, rather than being inferred by extending the y>=2 clock theorem below its allowed range. The last clause is a single explicit universal constant multiplying the actual source weight R Tail(x), uniform over the displayed epsilon range. It does not assume or claim a complete desmoothing result.

## 4. Proof obligations and exact payment chain

### Actual event positivity and conditioning, declaration 1

B is closed and each original X_i is measurable. Thus A and A^c are measurable, and

```text
A^c = union_i {omega : h < |X_i(omega)|},
mu.real(A^c) <= sum_i nu.real{|z|>h}
            = n nu.real{|z|>h} <= R/epsilon^3 <=1/8.
```

The marginal identity uses original IdentDistrib, not conditional iid. Probability complement mass then gives mu.real(A)>=7/8>0 and mu(A)!=0. Only now invoke `cond_isProbabilityMeasure` and the already accepted `indep_cond_joint_map_eq_pi` with the literal constant coordinate sets B_i=B. Original map(X_i)mu=nu identifies its right side with the genuine product rho^n.

Recover the actual coordinate marginals by mapping evaluation through this equality, and then recover independence using the existing `iIndepFun_iff_map_fun_eq_pi_map`. This is a finite law/evaluation transport, not a reproduction of the generic conditional independence proof. If n>0, positive A and one actual coordinate imply nu(B)>0; if n=0, deal with the empty family before introducing scalar probability instances. The fully increasing retained selector is not needed for this all-coordinate event and no sample-dependent permutation is substituted.

### Source numeric inputs and genuine cube payment, declaration 2

From declaration 1 install IsProbabilityMeasure mu_x and the true conditioned iid/marginal laws. From SourceTruncationBridge install IsProbabilityMeasure rho and true support |z|<=h. Its variance-bounds result gives the raw-square normalization 3/4<=n*m2<=4/3; the actual centered variance is not substituted for m2.

The same accepted module supplies all three actual ClockControl numeric hypotheses:

```text
(1+y)h<=1,
8(1+y)^2 h^2<=1,
[8(1+y)^2]^2 n*m4<=1/2.
```

These are proved consequences of the original h2/hnorm/hmean/cutoff/R inputs, not new assumptions in this proposal. Original global third/fourth moments, exp-square moments, mean zero under rho, positive variance, n>=7/64 and clock probability bounds are not premises.

Call the accepted generic iid_bounded_clock_bad_probability_le on exactly (mu_x,rho,X,h,y). Then use sourceTruncation_nearby_payment at the same fixed x law:

```text
(1+y)^3 n*m3 <=16 R,
bad <=2048 sqrt(2 pi) [(1+y)^3 n*m3] Tail(y)
    <=32768 sqrt(2 pi) R Tail(y)
    <=32768 sqrt(2 pi) exp(2) R Tail(x).
```

Every multiplied factor is nonnegative. The final step is the accepted actual GaussianTail local comparison. There is no abstract tail proxy, no change of cutoff to y, and no discarded R due to the coarser reparameterized H<=1 budget.

### Small threshold and all-x final-clock payment, declaration 3

Under the real mu_x law, let Q=energy(samplePath X). Conditional iid, support and true fourth integrability give Q in L2 and

```text
E_mu_x Q = n*m2 in [3/4,4/3],
Var_mu_x Q = n*(m4-m2^2) <= n*m4.
```

Use Mathlib's actual independent-sum variance theorem (or expand the actual square of the centered-square sum), not independence of Q and the increments and not a false centered-A energy. With center in [3/4,4/3],

```text
{Q outside [1/4,2]} subset {|Q-E Q|>=1/2}.
```

Chebyshev at the positive threshold 1/2 yields bad<=4 Var(Q)<=4n*m4. Every coordinate squared is genuinely L2 because rho has a fourth moment from its bounded support. No global fourth moment of nu is introduced.

Accepted paid moments give

```text
n*m4 <=h*n*m3 <= (epsilon/a)*(2R/a^3),
bad <=8 epsilon R/a^4 <=R,
```

using a>=1 and 8epsilon<=1. For 0<=x<2, actual Tail(x)>=Tail(2)>0, hence

```text
bad <= [1/Tail(2)] R Tail(x).
```

For x>=2, declaration 2 at y=x gives

```text
bad <=32768 sqrt(2 pi) R Tail(x),
```

since each bad-clock summand is nonnegative. The stated sum of the two positive constants dominates either branch. No exp(2) cost is needed at y=x. The endpoint x=2 may be assigned to the large branch; both estimates remain valid. Neither branch divides by R, m3 or n.

## 5. Audited scope and failure checks

- N_x is fixed before y varies, and mu_x is the actual normalized restriction of the original sample measure. Its probability instance, iid and common marginal are conclusions; none are assumed to bypass conditioning.
- First theorem permits n=0, and does not claim probability for the scalar zero-mass cutoff law in that case. The normalized theorems derive n>=64, positivity of the scalar cutoff law and true positive conditional variance from accepted source inputs.
- Original n E_nu z^2=1 and E_nu z=0 stay explicit. Conditional E_rho z may be nonzero. The raw clock is sum X_i^2; it is never replaced by sum (X_i-E_rho X_i)^2.
- The actual half clock uses natural `n / 2`; the lower event is strict `<1/16`. The final good interval is closed `Icc (1/4) 2`, so only values below 1/4 or above 2 are bad. Atoms at the cutoffs and clock thresholds remain admissible.
- The pair-clock result keeps y>=2 and the actual smaller source neighborhood. The all-x final result uses a separately proved Chebyshev branch, not an invalid low-y use of ClockControl.
- Small epsilon is the explicit source consequence epsilon<=1/8. No eta0-dependent desired moment payment, gamma bound, positive variance or clock hypothesis is added as a premise. The source gamma restriction is covered as explained above; no complete conditional gamma/noise construction is claimed.
- The genuine conditional cube factor appears explicitly before R conversion. A bare exp(-c y^2) without the small fourth/cube factor would not suffice and is not proposed.
- Later square/joint tilted laws require new moment/normalizer proofs. Nothing here transfers the original conditional clock estimates through such tilts.
- For the low-clock late block, this unit pays P(E); the already accepted historical signed-block identity is still required. No sum of individual absolute defects is silently used to claim a constant-one whole-block bound.
- This unit proves the b_x portion of the source sandwich cost. The independent noise, its actual gamma/r_n moments, deterministic sandwich, smooth kernel derivatives/Fourier restrictions and final contraction remain separate dependencies.

## 6. Dependencies and execution boundaries

Read-only accepted source hashes checked in this analysis or inherited from the exact frozen author artifact:

```text
SourceTruncationBridge 05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1
ClockControl c7782d17c1b6dec827cde84d1d44f9b6cb7a7d8dd166bee2183cac4d2dd5cdba
ConditionalIID 855c2eb0e560ac9372505f8b41551a9895b9eb753be3ce2b3f3752be845af787
FiniteIID d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b
FinitePath 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb
GaussianTail f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922
```

Actual pinned Mathlib source API inspection confirmed:

- `ProbabilityTheory.cond_isProbabilityMeasure`: finite measure plus actual nonzero event implies the normalized restriction is a probability.
- `iIndepFun_iff_map_fun_eq_pi_map`, Independence/Basic:866–889: recover actual independence from the true joint product law once the coordinate marginals are identified.
- `measurePreserving_eval`, MeasureTheory/Constructions/Pi:402–407: actual pi-coordinate marginal identity for probability marginals. Empty n is handled separately before requiring scalar rho probability.
- `ProbabilityTheory.IndepFun.variance_sum`, Moments/Variance:424–447: exact variance of a finite independent sum, requiring actual coordinate L2.
- `ProbabilityTheory.meas_ge_le_variance_div_sq`, Moments/Variance:396–405: actual Chebyshev with positive real threshold and true L2.
- Accepted `standardNormalTail_basic`: actual tail positivity and antitonicity; no numerical approximation to Tail(2) is needed.

Tentative new imports are accepted SourceTruncationBridge, ClockControl, ConditionalIID, appropriate existing path-measurability facts and the already-used Mathlib variance API. No OQ-specific dependency, package/version change, full Mathlib build or cache download is proposed. Root will decide explicit imports after freeze and independent declaration review.

This was source/code/API reading and mathematical analysis only. No local or server Lean process was run for this proposed unit, and no file except this owned proposal was authored. After a fresh independent declaration review and root freeze, implementation would still require actual target compilation, every module-owned/public/private/generated constant's transitive axiom audit, forbidden-token scan and a new independent full proof/source review. Current exact signatures are not a claimed Lean result.
