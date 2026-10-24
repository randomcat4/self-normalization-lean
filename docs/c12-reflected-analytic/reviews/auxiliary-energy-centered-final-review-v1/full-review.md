# Complete independent review: C12 auxiliary energy units 152 and 153

**STATUS: CORRECT.** Both exact frozen modules pass complete independent source-to-statement, proof, actual-type, consumed-interface, all-owner recursive-axiom and receipt review. No critical gap remains inside the five frozen theorem targets. This is scoped auxiliary-law acceptance; original C1/C2 roots remain OPEN.

Reviewer: `/root/auxiliary_energy_centered_final_review`, fresh configured `gpt-6.1-sol` / `xhigh`, separate from the author. Actual token/model telemetry is not exposed; input, cached input, output and reasoning-subset counts are null. Only this review directory was written. No production edit, Lean/audit execution, server write, child agent, Goal, schedule, sidebar chat or cross-thread message was made. Unit 153 was the one explicitly authorized immediately dependent extension before this seal; no further extension is included.

## Exact bindings

| Unit | Module | Source SHA256 | Object SHA256 | Receipt SHA256 | Frozen SHA256 |
|---|---|---|---|---|---|
| 152 | `Shao.C2.AuxiliaryEnergyCentered` | `465e3efe00bab80dea7207acb6da86198d6c28a4551908d035c51446aba8fd38` | `102b9e26587ecd4db4acd77030a6603afc6e776a4a13d754462e8ebb2882d505` | `b9a41a3b0767a5c279478fb7c89f744d55083b7944aa3a1b219aaef3d6501572` | `f6c3759a4593a2f16a8947da768e08ca5df25c45b72c63a5594db89ae5ed839e` |
| 153 | `Shao.C2.AuxiliaryEnergyLaplace` | `1c9e826d38c38ba5d7ec0938b05dd61dd60740db914ba96a7c39cdb0fb65c552` | `74eaa6b29b63ff5d4b52e92278639a1b42d58a0fa6e7c820b92784e15fafc472` | `46366b5c2e52f48636481123598a8005b809f36d5b1825c73902588697eee7a8` | `c5c4ba5bbae140c9ebe3c863c8b7ea498a92f09c475efb01787fe4382cc30716` |

Counts are derived from the actual owner maps and exact source declarations: 2 modules, 5 public theorems, 5 actual owned constants, all theorems; zero private/generated theorem owners and zero global non-theorem values. Complete actual-type exports total **41,215 bytes** (152: 19,628; 153: 21,587); both definition-value exports are genuinely empty. Each of the five owner rows has exactly the allowed recursive axiom set `propext`, `Classical.choice`, `Quot.sound`.

The complete import/context prefixes and exact theorem heads were independently compared against the substantive preimplementation freezes, including every quantifier, instance, hypothesis, let, conjunction, integrand and numerical constant. Both production files are UTF-8 without BOM and have LF line endings. No `sorry`, `admit`, new axiom, `unsafe` or `native_decide` occurs.

## Original source and law scope

Read-only originals were checked by full-file SHA256: supplement `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`; main `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`. The full relevant passage supplement 5094–5120 was read, with the auxiliary-law origin at main 1210–1216, supplement 4978–4983 and 5078–5080. Main 149–155 and 233–244 were also read to check that the original sample laws require only centered finite nonzero second moment.

Here `nu` is the auxiliary centered, preprocessed law with second moment one. Its absolute third moment is `beta = integral |z|^3 dnu`. The literal native tilted measure is `rho = nu.tilted (fun z => -s*z^2)`, whose density is `exp(-s*z^2)/phi(s)`, and `mu` is its actual identity integral. The formal fragments are valid without the auxiliary bounded-support restriction, provided the explicit square and absolute-cube integrability hypotheses hold. Those hypotheses are confined to this auxiliary law and are not imposed on the original finite-second-moment targets 145/147.

Unit 152 pays the variance interval and centered third-moment portion of supplement 5103–5107 plus the simplified drift of 5098. Its condition is `s*beta^2 <= 1/128`; beta positivity is proved, so this is the source inverse-beta-square condition. The proof uses `sqrt(s)*beta <= 1/8`, which suffices for the final interval. It does not assert the separately printed `.01` intermediate estimate or the `.99` raw second-moment estimate. Unit 153 pays only the single-law Laplace ingredients at 5113–5120, with general parameters `a,s,q`. It does not choose the source specific `q`, form a product law or assert a Chernoff probability bound.

## Exact frozen declarations

### Unit 152

```lean
import Shao.C2.AuxiliaryEnergyMoments

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryEnergyCentered
open MeasureTheory ProbabilityTheory

theorem auxiliary_absolute_third_moment_ge_one
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1) :
    1 ≤ ∫ z : ℝ, |z| ^ 3 ∂nu := by

theorem auxiliary_energy_tilt_small_parameter
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s : ℝ) (hs : 0 ≤ s)
    (hsmall : s * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 128) :
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let mu : ℝ := ∫ z : ℝ, z ∂rho
    IsProbabilityMeasure rho ∧
      Integrable (id : ℝ → ℝ) rho ∧
      Integrable (fun z : ℝ => z - mu) rho ∧
      (∫ z : ℝ, z - mu ∂rho) = 0 ∧
      Integrable (fun z : ℝ => (z - mu) ^ 2) rho ∧
      Integrable (fun z : ℝ => |z - mu| ^ 3) rho ∧
      |mu| ≤ 2 * s * beta ∧
      1 / 2 ≤ variance (id : ℝ → ℝ) rho ∧
      variance (id : ℝ → ℝ) rho ≤ 2 ∧
      (∫ z : ℝ, |z - mu| ^ 3 ∂rho) ≤ 12 * beta := by

end Shao.C2.AuxiliaryEnergyCentered
```

### Unit 153

```lean
import Shao.C2.AuxiliaryEnergyCentered

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.C2.AuxiliaryEnergyLaplace
open MeasureTheory ProbabilityTheory

theorem auxiliary_energy_laplace_loss
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    a - a * Real.sqrt a * beta ≤
      1 - ∫ z : ℝ, Real.exp (-a * z ^ 2) ∂nu := by

theorem auxiliary_energy_laplace_decay
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (a : ℝ) (ha : 0 ≤ a)
    (hsmall : a * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 64) :
    (∫ z : ℝ, Real.exp (-a * z ^ 2) ∂nu) ≤ Real.exp (-(7 / 8) * a) := by

theorem auxiliary_tilted_energy_laplace
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hnorm : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (s q : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hsq : s ≤ q)
    (hsmall : (s + q) * (∫ z : ℝ, |z| ^ 3 ∂nu) ^ 2 ≤ 1 / 64) :
    let rho : Measure ℝ := nu.tilted (fun z => -s * z ^ 2)
    Integrable (fun z : ℝ => Real.exp (-q * z ^ 2)) rho ∧
      (∫ z : ℝ, Real.exp (-q * z ^ 2) ∂rho) ≤ Real.exp (-(3 / 4) * q) := by

end Shao.C2.AuxiliaryEnergyLaplace
```

## Per-owner independent proof and type review

### `Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one`

**Semantic scope.** All real probability measures nu with integrable square and absolute cube and integral square1 imply beta>=1. No centering, bounded support or beta lower bound is assumed.

**Complete actual type.** Complete pp.all type read; Real measurable space and standard real instances, nu measure and probability instance; h2 square2 integrability, h3 absolute cube3 integrability, hnorm genuine integral square=1, conclusion genuine beta>=1; no hidden parameters or premises.

**Proof.**

For a=|z|>=0, (a-1)^2*(2a+1)>=0 equals1+2a^3-3a^2. sq_abs replaces a^2 by z^2. h2/h3 and finite probability constant give both integrable functions for integral_mono. Pi.add_apply exposes pointwise sum; integral_const_mul/add, hnorm and probability mass1 give3<=1+2beta, hence beta>=1.

**Consumed interfaces.** integral_mono requires both displayed functions integrable and pointwise inequality; supplied. integral_add supplied constant and cube integrability; integral_const real mass1.

**Coverage.** Complete statement/proof/type/interface and recursive-axiom coverage for this exact owner. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

### `Shao.C2.AuxiliaryEnergyCentered.auxiliary_energy_tilt_small_parameter`

**Semantic scope.** Exactly frozen nu,probability,h2,h3,hmean0,hnorm1,s,hs and hsmall. Literal let rho,beta,mu; ten conjunctions: probability, id integrability, centered first integrability, centered mean0, centered square integrability, centered absolute cube integrability, drift<=2s beta, actual variance>=1/2, actual variance<=2, centered cube integral<=12 beta.

**Complete actual type.** All19628-byte export read across both owners. Real universe0, native standard measurable/integral/abs/power/division instances; no abstract substituted law or covariance surrogate. Every nat2/nat3 and real rational1/128,1/2,2,12 is the intended type. Three let-bound values unfold to exact frozen rho,beta,mu.

**Proof.**

Consume exact unchanged150 at identical nu,h2,h3,hmean,hnorm,s,hs: true rho probability and id integrability and |mu|<=D=s exp(s) beta. Consume unchanged151 with identical arguments: raw square/cube integrability, E_rho|z|^3<=exp(s)beta, actual Var lower1-sqrt(s)beta-D^2 and upperexp(s). No use of the desired152 conclusions as assumptions.

First theorem gives beta>=1; hence beta>=0,beta^2>=1. From s>=0 and hsmall, s<=1/128. Native exp_bound_div_one_sub_of_interval has premises0<=s,s<1; both proved. 1-s>0 makes the reciprocal comparison valid and gives exp(s)<=2, including s0.

(sqrt(s) beta)^2=s beta^2<=1/128 and sqrt(s)beta>=0 yield sqrt(s)beta<=1/8; no division by sqrt(s). s beta<=s beta^2<=1/128 follows from nonnegative s beta times beta-1. D>=0,D<=2s beta<=1/64, and (1/64-D)(1/64+D)>=0 provesD^2<=1/4096.

Inherited Var>=1-sqrt(s)beta-D^2>=1-1/8-1/4096=3583/4096>1/2, while Var<=exp(s)<=2. Inherited |mu|<=D gives drift<=2s beta and |mu|<=1/64; monotone cube gives |mu|^3<=1<=beta.

Triangle inequality gives |z-mu|<=|z|+|mu|; both nonnegative, so cube monotonicity applies. With a=|z|,b=|mu|,4(a^3+b^3)-(a+b)^3=3(a+b)(a-b)^2>=0. The resulting pointwise bound4(|z|^3+|mu|^3) is integrable under probability rho. Integrable.mono' is supplied continuous/AEStronglyMeasurable centered cube and its nonnegative norm bound, so centered cube is genuinely integrable before monotone integration.

Integral expansion uses raw cube integrability, constant integrability and mass1, with final rfl only unfolding rho. Integral centered cube<=4(E_rho|z|^3+|mu|^3)<=4(2beta+beta)=12beta.

Centered first integrability is hId minus an integrable constant. The typed integral_sub consumes that exact id under rho; constant integral=mu and definition mu=integral id give centered mean0. measurable_id and raw square integrability give MemLp id2 rho, subtracting memLp_const mu gives genuine centered square integrability. Final tuple preserves the ten-conjunct order.

**Consumed interfaces.** Native exp interval, nonnegative sqrt/sq_sqrt, power monotonicity, triangle inequality, integrable domination, true Bochner integral linearity, finite probability constants, L2 equivalence/subtraction/integrable_sq; every domain, sign, finite-measure and measurability condition accounted for. Native tilted and variance meanings reread; prior150151 full proof reviews reused rather than repeated.

**Coverage.** Complete statement/proof/type/interface and recursive-axiom coverage for this exact owner. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

### `Shao.C2.AuxiliaryEnergyLaplace.auxiliary_energy_laplace_loss`

**Semantic scope.** Probabilitynu,integrable square/cube,mean0,secondmoment1 and everya>=0. beta=integral absolute cube. Conclusion is the genuine normalizer losslowerbound. Centering is explicit though unnecessary to the pointwise inequality; it is passed to unchanged150for bounded-weight integrability.

**Complete actual type.** Complete pp.all type read: standard Real universe0 and measurable space; native Integrable/Bochnerintegral/abs/Nat2/Nat3, genuine hmean0/hnorm1, reala>=0 and letbeta exact; no hidden smallness or support hypothesis.

**Proof.**

Use150with parameter a>=0 for genuine integrability ofV(z)=exp(-a z^2). For each realz putt=sqrt(a)|z|>=0. sq_sqrt ha and sq_abs give t^2=a z^2; the algebraic cube identity gives t^3=a sqrt(a)|z|^3.

If t<=1, t^2<=1 follows from t>=0. Atx=-t^2 native abs_exp_sub_one_sub_id_le applies because |x|=t^2<=1, and gives exp(-t^2)-1+t^2<=t^4. Multiplying t<=1 by t^3>=0 gives t^4<=t^3. Rearrangement yields t^2-t^3<=1-exp(-t^2). If t>1, t^2( t-1)>=0 gives t^2-t^3<=0, and exp(-t^2)<=1 gives the nonnegative right side. These branches include t0,t1, both signs ofz and all a>=0.

Convert back pointwise. The lower function is integrable by h2.const_mul minus h3.const_mul; the upper function1-V is integrable by finite-probability constant minus hVI. integral_mono is therefore legitimate. Actual integral_sub/const_mul, hnorm and probability mass1 yield exactlya-a sqrt(a)beta<=1-phi(a).

**Consumed interfaces.** Real.sqrt_nonneg/sq_sqrt withha; native exponential remainder has exact |x|<=1 premise and coefficient1, verified. exp_le_one_iff at nonpositive exponent. integral_mono/sub/constant identities have explicit integrability.

**Coverage.** Complete statement/proof/type/interface and recursive-axiom coverage for this exact owner. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

### `Shao.C2.AuxiliaryEnergyLaplace.auxiliary_energy_laplace_decay`

**Semantic scope.** Same auxiliary law, a>=0 and exactlya*beta^2<=1/64 imply actualphi(a)<=exp(-(7/8)a). No assumed Laplace estimate.

**Complete actual type.** Complete pp.all type read: same explicit law and h2/h3/hmean/hnorm, reala/ha, literal real1/64smallness andexp(-(7/8)*a). No surrogatephi function or extra premise.

**Proof.**

The absolute-cube integral beta is nonnegative by integral_nonneg (h3 already makes it finite). Nonnegative sqrt(a)beta has squarea beta^2<=1/64, so it is<=1/8. Multiply by a>=0 and apply the newly proved loss theorem to getphi(a)<=1-7a/8. Native global add_one_le_exp atx=-(7/8)a gives1-7a/8<=exp(-7a/8). No division bybeta,a orsqrt(a) occurs.

**Consumed interfaces.** sqrt square identity usesha; multiplication preserves order becausea>=0; global exponential tangent has no interval restriction. Local previous theorem is the exact source-bound first153owner, not an unproved assumption.

**Coverage.** Complete statement/proof/type/interface and recursive-axiom coverage for this exact owner. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

### `Shao.C2.AuxiliaryEnergyLaplace.auxiliary_tilted_energy_laplace`

**Semantic scope.** For exact literal rho tilt and parameters0<=s<=q withq>=0 and(s+q)beta^2<=1/64, the exponential-square observable is genuinely integrable under rho and its actual expectation<=exp(-3q/4). This is one-law only.

**Complete actual type.** Complete pp.all type read: original nu/probability/h2/h3/hmean0/hnorm1, realsq with three explicit order hypotheses and real1/64smallness, native let-rho tilt, and exactly the Integrable-and-real-integral inequality. No product, stopping, conditional law, assumed normalizer or hidden finite-variance premise. Rational3/4 is Real.

**Proof.**

Use exact150at s>=0 to obtain the true weight integrability, Z=phi(s)>0 andZ>=exp(-s). Use150at s+q>=0 for integrable combined weight. Pointwise exp_add and ring identify exp(-s z^2)*exp(-q z^2)=exp(-(s+q)z^2). Native integrable_tilted_iff(hV,g) withg=exp(-qz^2) therefore proves genuine tilted-observable integrability before any numerical integral interpretation.

Native integral_tilted gives the integral of(exp(-s z^2)/Z)*exp(-q z^2) undernu. Pointwise exp_add/ring identifies it with exp(-(s+q)z^2)/Z; integral_div pulls out the constant. Hence the actual tilted expectation equalsphi(s+q)/phi(s). Zpositivity and all relevant integrabilities are independently proved, so no zero/undefined-integral fallback is exploited.

Apply the second153theorem at a=s+q with the exact hsmall. Division byZ>0 preserves its numerator bound. Since the exponential numerator is nonnegative andZ>=exp(-s)>0, denominator comparison yields exp(-7(s+q)/8)/exp(-s)=exp(s-7(s+q)/8). Finallys<=q implies s/8-7q/8<=-3q/4; native exponential monotonicity gives the target. No division byq orbeta and no strict positivity ofq is used.

**Consumed interfaces.** Literal native tilted definition, integrable_tilted_iff, unconditional integral_tilted identity and integral_div; every measure/genuine-integrability/normalizer sign condition accounted for. exp_add/exp_neg and exp monotonicity at real arguments; division order conditions are exactly hZpos and exp_pos. Exact150interface rechecked; full unchanged150151proof reviews reused.

**Coverage.** Complete statement/proof/type/interface and recursive-axiom coverage for this exact owner. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Native interfaces and unchanged dependency reuse

The qualified unchanged 150/151 proof reviews are reused, rather than repeated. Their complete review JSON/Markdown/release SHA256s are respectively `30fdf44aeba9ad1c27a38de2ba445bd2fb14f094644f4713f9bd73812dba0068`, `47cd757107ad37b900e2cc5835fbc1c184f75cbbeadd490eb1fc06cf85d84dab`, and `678c79bcb2fb4892c4657becf7e2c8b114757687299e9f3b726e847a8a10a825`. The prior parent acceptance is present and hash-bound to those reports. Their source and installed object pairs were freshly rehashed: 150 source `8ea1547baf4beb388faea8d4d8ded12cab83c098f5bb41b2995d79675abd91ca`, object `31ef9fa4d5bd0289a315e973c72ede5e7a222100e68e0fc622a59d0550de00ba`; 151 source `5a9b156d0f7ad1c41f15b361b1cea008e7f47716e23d86c0f57db04ac54498d3`, object `54613db5670afca311a3d37420c388ef5cc44773e48e0deabf39ff3e3481bff2`.

Their complete consumed theorem interfaces were read in this context. All arguments and local values coincide: same real probability law, square/cube integrability, mean zero, unit second moment, nonnegative parameter, and literal `rho,beta,mu`. Unit 150 supplies actual weight integrability, a strictly positive normalizer and its exponential lower bound, probability, first integrability and drift. Unit 151 supplies genuine raw moments and the actual native variance lower/upper bounds. Unit 153 imports exact 152 but its proof bodies directly consume 150 and the local preceding 153 lemmas; there is no hidden assumption of a desired new result.

Relevant native source bytes equal pinned mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. Newly checked native interfaces include the interval exponential reciprocal bound, the exponential remainder with exact `|x| <= 1` premise, the nonnegative real square root and its square identity, monotone natural powers, and the generated additive norm triangle inequality. The integrable domination interface requires the displayed measurable target and AE norm envelope, both present. The L2 equivalence, finite-measure constant, subtraction and square-integrability interfaces pay the centered square.

Native `Measure.tilted` was read as its actual `withDensity` construction. `integrable_tilted_iff` was read with its exact integrable exponential-weight premise; `integral_tilted` gives the actual density integral and `integral_div` the constant denominator. Actual integrability and normalizer positivity are established before their numerical use. Native variance is `toReal` of centered-square `evariance`; actual MemLp2 excludes the infinite-variance fallback. All integral addition/subtraction/monotonicity applications supply the genuine integrability required by their native signatures. No surrogate law or assumed variance/Laplace conclusion is used.

## Original server gates, owner selection and recursive axioms

The original kernel command for each target sources the accepted server environment, changes to `workspaces/c12-bridge-domination-v71`, and runs targeted Lean under `flock .../locks/c12-heavy.lock`, `taskset -c 14-17`, `-M8192 -j4`. Both receipts bind branch `author/c12-compact-relative-v71`, head `9f7d39c69b78ae4436e5ed06d34e9d7efae5387e`, Lean `leanprover/lean4:v4.36.0-rc1` and the accepted shared-v34 package view. This review did not run Lean or an audit again.

All original command text and full kernel logs were read. Unit 152 attempt001 failed at three elaboration expressions: pointwise function addition before an integral rewrite, a final definitional equality after the cubic-integral expansion, and the identity/measure annotation for `integral_sub`. The exact source diff changes only those proof expressions. Attempt002 passes and retains the harmless `letI` style hint. The failed source/command/log remain intact. Unit 153 has one attempt, attempt001, which passes with no failed attempt. The generic mathlib local-changes warning is preserved; every relevant native source inspected here matches the pinned Git bytes.

Both original all-owner audit programs were fully read. They enumerate `env.constants.toList`, use `env.getModuleIdxFor?` and the actual header module map, and select by exact module ownership. This includes any private/generated/other owner; it is not a namespace whitelist. They then call fully qualified `Lean.collectAxioms` on every selected name and reject any axiom outside the three-item whitelist. Actual maps contain exactly two and three theorem owners respectively and no other owner kinds.

The pinned collector implementation was fully read. It follows checked declaration types and values, including theorem, definition and opaque values, constructor/recursor/inductive dependencies, uses a recursion-cycle sentinel, and reuses recursively computed exported axiom data for imported declarations. Export collection and public collection use the private environment to see bodies. The native owner lookup reads `const2ModIdx`. Fresh collector/Environment source hashes match the already qualified provenance. This is transitive dependency audit, not a direct-reference text scan.

Both original complete audit logs are accounted for byte-for-byte: the warning prefix, the exact already fully read complete actual-type export, and the owned-count/exit footer. No text, generated type, private owner or definition value is omitted. Empty value exports are justified by the exhaustive owner maps, not assumed from source names. Original receipt-generation code and its complete 153 delta were inspected; output objects match installed imported objects.

## Boundary and interaction review

- s=0 allowed; exponential interval lemma handles equality0; no division bys,mu,beta orsqrt(s). rho=nu and mu0 as expected.
- hsmall equality included; beta=1 possible, e.g. symmetric +/-1. Probability and second moment1 exclude zero law; beta positivity paid.
- Arbitrary atoms, asymmetry and both signs ofz allowed; no density, symmetry, continuity, nonlattice, sample independence or boundedness assumption added.
- All relevant first/square/absolute-cube integrability assertions are established, so total-integral or infinite-variance fallback is not used.
- All finite3 assumptions belong only to the preprocessed auxiliary law; original finite2 targets145147 and all original roots retain their previous scope.
- a=0 andt=0 are covered without division. t=1 is in the firstbranch and both pointwise arguments remain valid.
- hsmall equality permitted, ands=q permitted. q=0 forces s=0; expected observable1/integral1/upper1 is consistent.
- All signs ofz and asymmetric/atomic laws allowed. Finite3is only auxiliary-law scope, never imposed on original finite2 sample law.
- The actual tilted observable is bounded/nonnegative but its integrability is still proved via the native weighted iff. Actual normalizerZ>0 prevents invalid division.
- The statements do not assert a deterministic product-length law, Chernoff tail, specific inversebeta^2 choice, rank transport, rare-suffix estimate or root closure.

The new dependency graph is acyclic: accepted 150 -> accepted 151 -> reviewed 152 -> reviewed 153 by imports. No shared definitions, pins, root imports or original-law declarations were changed. Nonnegative parameters include zero and equality boundaries; no proof divides by `s`, `q`, `a`, `beta` or a square root. The only probability-ratio denominator is the actual strictly positive normalizer.

## Final observation, limits and handoff

At 2026-10-24T21:06:35.465893+00:00, a fresh read-only observation checked **56 distinct remote bindings**, all exact, including output/installed new sources and objects, receipts and original artifacts, unchanged 150/151 source/object dependencies, relevant pinned native files and collector provenance. No target-152/153 Lean or Lake process was observed in flight. This narrow observation does not freeze the global worktree; the author may work on a separately owned next module. `readonlyfinal-observation.json` binds this observation with SHA256 `d65f9585c413d0c051c4cf7c8bf99f473b2b94dc6347d99a11ff2971e10c967c`.

One reviewer-only final-observation query initially failed to parse because of the typo `else3`. That short failure is preserved in `readonly-query-failure.json`; the corrected query only read metadata/source and did not execute a proof check or write to the server. It is not a proof result.

The complete JSON report contains each unit’s exact frozen declarations, per-owner semantic/proof/type/interface/axiom findings, author release/receipt, local artifact hashes and prior evidence bindings. Deterministic validation binds these artifacts but is not itself a mathematical proof. The final writer release is written last and binds both reports, the validation and final observation; no edits follow it.

The centered law’s own C1 budget and reflected-law legality at supplement 5108–5111, the source specific inverse-beta-square parameter choice, deterministic product-length Chernoff/low-energy probability, rank transport, quantitative rare-suffix machinery and all original C1/C2 roots remain open. The finite-third-moment condition has not been added to the original finite-second-moment problem. OQ3 remains PAUSED_BY_USER. Preserve all prior scoped results, p54 repairs and external-result attribution. No new mathematical novelty is claimed for these auxiliary source consequences.

Both exact units are ready for the parent’s full-report acceptance. This review ends after its sealed release; it does not imply persistent runtime continuation.
