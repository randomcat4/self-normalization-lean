# Units 150–151 independent complete final review

STATUS: CORRECT

The exact frozen theorem `Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift` is correct. This is a complete independent source-to-statement, proof, actual-type, native-interface and recursive-axiom review of unit150 and its explicitly authorized immediately dependent unit151. Unit150 is detailed first; the full151review follows. No critical gap or uncovered part of its frozen target was found. The original C1/C2 roots remain **OPEN**.

The reviewer is a fresh `gpt-6.1-sol` / `xhigh` context, separate from the author. Configuration is explicitly supplied by the task; backend model telemetry and all usage counts are unavailable and recorded as null. I made no production-source changes, gave no author proof implementation, ran no Lean/audit checks, wrote nothing on the server, and created no other context, chat, goal or schedule. All local writes are confined to this review directory. The author had released the exact unit's writer/execution authority before review; ongoing work in other files is outside this review.

## Exact target and scope

For a probability measure `nu` on the ordinary measurable real line, assume integrability of `z²` and `|z|³`, `∫z dnu=0`, and `∫z² dnu=1`. For every real `s≥0`, put

```
V(z) = exp(-s*z²)
Z = integral V dnu
rho = nu.tilted (fun z => -s*z²)
beta = integral |z|³ dnu
```

The seven frozen conclusions are: `Integrable V nu`, `0<Z`, `exp(-s)≤Z`, `Z≤1`, `IsProbabilityMeasure rho`, `Integrable id rho`, and `|∫z drho|≤s*exp(s)*beta`.

This is the energy-only auxiliary tilt in supplement.tex5094–5101, specifically its density, the lower normalizer bound and the first `exp(s)*s*beta` mean bound. The source also prints `≤2sβ`, bounds involving `t,l,K,L,x`, and later variance/third-moment and rare-suffix conclusions; none is silently included in this unit. The frozen theorem is a valid more general single-law fragment for all `s≥0`, with no bounded-support or global `s*support²` restriction.

The original source is the read-only `C:/game/shao/current/c12` snapshot. Main SHA256 is `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`; supplement SHA256 is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`. Main149–155 and233–244 state the original finite-second-moment scope; main1210–1216 explicitly identifies the later centered bounded law as auxiliary. Supplement4692–4697 specifies centered/unit-second-moment/β notation, 4978–4990 gives the residual bounded-law regime, and5078–5080 explicitly says the rare-budget proof uses bounded product laws. I read the exact tilt paragraph and its surrounding argument, including5001–5136. Therefore the explicit finite absolute third moment here belongs to the bounded/preprocessed auxiliary law; it is not an added assumption on the original laws of145/147. No sample-law adapter or rare-suffix assembly is proved by this lemma.

## Complete proof review

1. **Weight, measurability, integrability, positive normalizer and upper bound** (production lines 26–43). For each real z, exp(-s*z^2)>0. Since s>=0 and z^2>=0, V(z)<=1. Continuity/measurability of the polynomial and exponential supplies measurable V. Probability makes the constant 1 integrable; norm domination gives Integrable V. integral_exp_pos applies because a probability measure is nonzero. integral_mono and integral 1=1 give Z<=1. No support or smallness condition is used.

2. **Integrated exponential tangent** (production lines 44–66). Real.add_one_le_exp at s-s*z^2, multiplied by exp(-s)>0, gives exp(-s)*(1+s-s*z^2)<=V(z). The left side is integrable by h2. Its integral is exp(-s)*(1+s-s*1)=exp(-s), using probability mass one and hnorm. Integral monotonicity gives exp(-s)<=Z. This proves the Jensen consequence directly; Jensen is not an additional assumption or axiom.

3. **Literal tilted probability and integrable identity** (production lines 67–78). isProbabilityMeasure_tilted consumes hV and NonZero nu. memLp_two_iff_integrable_sq applies to the measurable real identity; h2 implies MemLp id 2, and finite measure plus 1<=2 gives integrable id. The weighted identity V(z)*z is integrable since |V(z)*z|<=|z|. integrable_tilted_iff, instantiated with f(z)=-s*z^2 and g=id, transports this to the literal rho=nu.tilted f. Thus the later first moment is a genuine integrable Bochner integral.

4. **Native density formula and centered numerator** (production lines 79–94). integral_tilted is the actual density formula with exp(f(z))/integral exp(f), not a surrogate tilt. Scalar multiplication over the reals becomes multiplication; integral_div moves the constant Z outside. hProd and hId justify integral subtraction. hmean=0 rewrites integral V(z)*z as integral z*(V(z)-1), with pointwise commutative-ring equalities and integrable centered integrand.

5. **Pointwise cubic and integrated numerator estimate** (production lines 95–111). Real.one_sub_le_exp_neg at s*z^2 gives 1-s*z^2<=V(z). Combined with V<=1 this yields 0<=1-V<=s*z^2. Hence |z*(V-1)|=|z|*(1-V)<=s*|z|^3 for both signs of z, using z^2=|z|^2. hCentInt.abs and h3.const_mul s justify integral_mono, and abs_integral_le_integral_abs gives numerator absolute value at most s*beta. beta>=0 follows from nonnegative integrand.

6. **Positive denominator and final conjunction** (production lines 112–121). Use the native tilted mean identity and centered numerator, and |Z|=Z from Z>0. Divide the numerator bound by Z>0. Since s*beta>=0 and exp(-s)<=Z, denominator monotonicity gives (s*beta)/Z<=(s*beta)/exp(-s)=s*exp(s)*beta. The final constructor supplies all seven frozen conjuncts in their original order; no additional condition or excluded branch occurs.

All integrals used in subtraction and monotone comparison have their required integrability proofs. The numerator is not an assumed residual bound. The original source's Jensen consequence is derived by an integrated exponential tangent using the unit second moment, with no extra Jensen axiom. The literal native tilted measure, not an abstract probability substitute, is used throughout.

At `s=0`, `V=1`, `Z=1`, `rho=nu`, and the centered mean bound is zero. Every finite large `s≥0` is included, with strict positive normalizer. Both signs of `z`, asymmetric laws, and atoms are covered; no law symmetry/density/nonlattice premise is present. Probability makes `nu` nonzero, while the unit second moment rules out an all-zero variable. The proof requires no β lower bound. There is no hidden dependence on future samples or a stopping-time/event convention in this single-law statement.

## Actual type, global values and native interfaces

- All 8643 bytes of the pp.all actual-type export were read without truncation and reconstructed exactly from the original 8868-byte owned-audit.log. No ellipsis, sorryAx or unresolved metavariable marker occurs.

- nu is exactly Measure Real on Real.measurableSpace at universe 0. The sole anonymous instance is IsProbabilityMeasure nu. All generated normed/topological/inner-product structures are standard real structures; no extra domain, measure or sample-law parameter appears.

- h2 is Integrable (fun z : Real => z^2) nu; h3 is Integrable (fun z => |z|^3) nu. hmean is the actual real Bochner integral of z under nu equal to 0, and hnorm is that of z^2 equal to 1. s is any real and hs exactly 0<=s. There are no hidden bounded-support, small-s, iid, symmetry, density, or sample-size binders.

- The four local type lets are V(z)=exp((-s)*z^2), Z=integral V under nu, rho=Measure.tilted nu (fun z => (-s)*z^2), and beta=integral |z|^3 under nu. They are local lets, not global non-theorem values or new hypotheses.

- The actual nested And has exactly: Integrable V nu; 0<Z; exp(-s)<=Z; Z<=1; IsProbabilityMeasure rho; Integrable id rho; |integral z under rho|<=((s*exp(s))*beta). Left-associated real multiplication and negative exponent agree with the frozen source. All binders, universes, coercions, standard instances and seven conjuncts were inspected.

The owner map contains exactly one actual module-owned declaration: the public theorem above. There are zero private/generated theorems and zero global non-theorem values. The full value export is empty (SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The four local `let` expressions are fully reviewed in the actual type; they are not unreviewed global definitions.

I read the native source signatures and relevant surrounding proofs/contexts at the pinned Mathlib commit, including `Tilted.lean` lines1–340:

- **MeasureTheory.Measure.tilted**, `Mathlib/MeasureTheory/Measure/Tilted.lean`:36–43. `nu.withDensity (fun z => ENNReal.ofReal (exp (f z) / integral exp(f) dnu))`. f(z)=-s*z^2. The weight is exactly exp(-s*z^2), and hV and hZpos prevent the native zero/integral-undefined fallback.

- **MeasureTheory.isProbabilityMeasure_tilted**, `Mathlib/MeasureTheory/Measure/Tilted.lean`:126–136. `[NeZero nu] -> Integrable (fun z => exp(f z)) nu -> IsProbabilityMeasure (nu.tilted f)`. NeZero nu follows from IsProbabilityMeasure nu; hV is the required exponential integrability.

- **MeasureTheory.integrable_tilted_iff**, `Mathlib/MeasureTheory/Measure/Tilted.lean`:293–312. `Integrable exp(f) nu -> (Integrable g (nu.tilted f) iff Integrable (fun z => exp(f z) • g z) nu)`. E=Real, f(z)=-s*z^2, g=id; hProd is the right-hand side, with real smul converted to multiplication. No bounded-support premise or additional tilted law is introduced.

- **MeasureTheory.integral_tilted**, `Mathlib/MeasureTheory/Measure/Tilted.lean`:192–232. `integral g d(nu.tilted f) = integral ((exp(f z)/integral exp(f) dnu) • g z) dnu`. E=Real, g=id. The theorem is unconditional as a total integral identity, but this proof independently establishes integrability on both sides and Z>0 before using its numerical meaning.

- **MeasureTheory.integral_exp_pos**, `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`:792–798. `[NeZero nu] -> Integrable exp(f) nu -> 0 < integral exp(f) dnu`. Nonzero probability nu and hV meet the exact conditions.

- **MeasureTheory.memLp_two_iff_integrable_sq**, `Mathlib/MeasureTheory/Function/L2Space.lean`:40–55. `AEStronglyMeasurable f nu -> (MemLp f 2 nu iff Integrable (fun z => f(z)^2) nu)`. f=id on Real; measurable_id gives the measurability premise, and h2 is the square integrability.

- **MeasureTheory.MemLp.integrable**, `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`:646–648. `1<=q -> [IsFiniteMeasure nu] -> MemLp f q nu -> Integrable f nu`. q=2 with 1<=2; probability implies finite measure. There is no unproved first-moment assertion.

- **Real.add_one_le_exp / Real.one_sub_le_exp_neg**, `Mathlib/Analysis/Complex/Exponential.lean`:624–642. `forall x : Real, x+1<=exp(x); forall x : Real, 1-x<=exp(-x)`. First with x=s-s*z^2 for the integrated tangent; second with x=s*z^2 for the cubic numerator. Neither requires a smallness bound.

All four direct import source files and all consumed native interface files inspected are byte-equal to their contents at pinned Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The probability/finite-measure/nonzero and real normed-space requirements are met. Unit150 imports no project module; `dependencySourceSHA256={}` accurately means zero project dependencies. Taylor/variance imports do not introduce assumed project estimates.

## Exact freeze, server and axiom provenance

The complete production file (all imports, context, declaration and proof) is 5979 bytes, SHA256 `8ea1547baf4beb388faea8d4d8ded12cab83c098f5bb41b2995d79675abd91ca`. Its frozen import/context/head file is1105 bytes, SHA256 `9ad91ee964dc78e31334a7ed40310874e6545974bea41a9d640ada7938693b60`. Removing only the proof body reproduces the frozen bytes exactly. The freeze record states implementation had not begun at20:39:01.389065Z; remote frozen upload precedes source upload and attempt001. The record and timestamps are provenance evidence, not external cryptographic timestamping.

The server production source and preserved attempt001 source are byte-identical to the reviewed local source. The output object and actual imported build object are identical at SHA256 `31ef9fa4d5bd0289a315e973c72ede5e7a222100e68e0fc622a59d0550de00ba`. The receipt is SHA256 `a71f6b39db6270df21c9baccf0d1175b1711a9b38b85327e9f6296b1d0dd8039`, and the local and remote author release are identical at SHA256 `80e6ac5c3ae988f76ba88e178eaa8b854e30fcb5dd6a8e805139857e0998b734`. The complete binding map is in full-review.json and server-artifacts.json. The release binds the exact source/object/receipt/freeze and records writerReleased=true, executionReleased=true, heavyInFlight=false, inFlight=[].

The original attempt001 command and full165-byte kernel log were read. There is exactly one attempt directory and `KERNEL_EXIT=0`. The command activates the accepted server environment, uses `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`, holds `c12-heavy.lock`, pins CPU14–17, and runs targeted `lake env lean -M8192 -j4` on AuxiliaryEnergyTilt.lean. The preserved object is the one the audit imports. Lean is `leanprover/lean4:v4.36.0-rc1`; the observed Mathlib head is the pinned commit. The historical author branch/head are `author/c12-compact-relative-v71` / `9f7d39c69b78ae4436e5ed06d34e9d7efae5387e` and remained so at observation.

The complete original8868-byte owned-audit.log and complete OwnedAudit.lean were read. The audit enumerates **all actual module owners** via `env.getModuleIdxFor?`, resolving indices through `env.header.moduleNames`, rather than matching a namespace or only a handpicked public list. The public list is only an additional coverage check. It prints complete `pp.all` types for every owner and values for every owned definition. Here the exact map is1owner/1public theorem/0other values. Its final marker is `AUDITED_TARGET_CONSTANTS 1 PUBLIC 1 THEOREMS 1 DEFINITIONS 0`, followed by `AUDIT_EXIT=0`.

I also read the installed pinned Lean `getModuleIdxFor?` implementation and **the complete CollectAxioms implementation**. Ownership uses the environment's `const2ModIdx`. Axiom collection traverses checked declaration types and proof/definition/opaque values, recursively includes used constants, and uses recursively computed export entries for imports; export computes through a private environment so private bodies are visible. It is genuinely transitive, not merely a scan of direct references. The single owner's complete recursive axiom set is exactly `[propext, Classical.choice, Quot.sound]`, all allowed. Production source contains no sorry/admit/new axiom/unsafe/native_decide.

The sole kernel/audit-log warning is that the shared Mathlib repository has local changes. It is not an error; the inspected direct imports and consumed native source bytes independently match the pinned commit. No successful Lean or audit gate was replayed. The author receipt-finishing script was read in full: it checks exact source/object equality, counts, successful markers, LF encoding, and reconstructs the full type/empty value exports. Although it reuses a metadata template, the unit150 paths, sources, object, ownership, counts and commands were independently checked here.

The original logs remain on the server. Their full text was read, but only hashes/markers, the exact type export and necessary metadata are retained locally. The first read-only remote query encountered missing `rg`; its failure is preserved and a bounded Python search completed the read-only observation. Two initial conventional Lean-source paths were absent; I followed the actual configured elan toolchain source directory. These were read-only discovery adaptations, not Lean/audit attempts.

## Decision and remaining scope

This review qualifies the exact one-theorem unit150 source as **CORRECT**, with complete original-fragment semantic, production proof, actual type, all global-value, native-interface and recursive-axiom coverage. No novelty is claimed. Parent qualification requires reading this complete report and the JSON plus checking the final sealed bindings; I do not grant a merge/publication/root-closure decision.

At the unit150 boundary, moment and variance estimates are subsequent dependencies. The explicit bounded extension151 below pays raw square/cube and variance estimates. The extra `≤2sβ` simplification, rank/parameter bounds, centered third moment, fixed numerical variance interval, legal C1 application, low-energy and rare-suffix budgets remain separate dependencies. Original C1/C2 roots remain OPEN. OQ3 remains PAUSED_BY_USER; p54 repairs and external attribution are unchanged.

Final exact read-only observation is final-observation.json. Deterministic binding/count/freeze validation is validation.json. writer-release.json is written last and seals this MD, full-review.json, validation and final observation. No local or server artifact is changed after the seal.

## Explicit bounded extension: unit 151

STATUS: CORRECT

Before any seal, the parent explicitly authorized only the immediately dependent unit151 and supplied its completed author release. Runtime extension acknowledgement is runtime-extension-151-ack.json. The same fresh independent reviewer and same exclusive output directory are retained; no new context or Lean/audit run occurred. No further extension is included.

The complete frozen theorem is `Shao.C2.AuxiliaryEnergyMoments.auxiliary_energy_tilt_moments_and_variance`. It has exactly the same auxiliary-law assumptions as150 and local `rho,beta,mu` described above. Its nine conclusions are probability rho, genuine square and absolute-cube integrability under rho, square moment in `[1-sqrt(s)*beta, exp(s)]`, raw absolute cube at most `exp(s)*beta`, the actual native variance identity `variance id rho = E_rho z²-mu²`, and variance in `[1-sqrt(s)*beta-(s*exp(s)*beta)², exp(s)]`.

This faithfully proves the general estimates behind supplement5103–5107 for every `s≥0`. It does not claim source numeric `[1/2,2]`, centered absolute-third-moment `C*beta`, legal centered-law C1 input or rare-suffix budgets. The original finite-second-moment laws remain unchanged.

### Complete production proof and interface review

1. **Exact unit150 dependency and literal probability instance** (production lines29–35). The sole project import and consumed theorem are the exact reviewed unit150 source/object. Its seven conclusions give V integrability, exp(-s)<=Z<=1, positive Z, literal rho probability and |mu|<=s*exp(s)*beta. The local letI merely installs the proved probability instance; the retained style warning concerns proof representation, not a premise.

2. **Weighted and genuine tilted moments and density identity** (production lines36–70). V is positive measurable and at most 1 for s>=0. Pointwise norm domination by z^2 and |z|^3 establishes weighted integrability from h2/h3. integrable_tilted_iff gives genuine square and absolute-cube integrability under the same literal rho. integral_tilted and integral_div give the exact weighted integral divided by Z for any real g; later moment uses have the requisite integrability.

3. **Square-root pointwise loss and its integral** (production lines71–96). Set t=sqrt(s)*|z|>=0. Real.sq_sqrt uses hs, so t^2=s*z^2. The exponential tangent gives 1-V<=t^2. If t<=1, nonnegativity gives t^2<=t; otherwise t>=1 and V>0 give 1-V<=1<=t. Thus z^2*(1-V)<=sqrt(s)*|z|^3 for every z. The loss is integrable by the difference of integrable square and weighted square, and integral_mono yields loss<=sqrt(s)*beta.

4. **Lower tilted square moment with a sign-correct normalization** (production lines97–112). Using integral_sub and hnorm, the raw weighted-square numerator N2 is at least 1-sqrt(s)*beta. N2 is independently nonnegative. Since 0<Z<=1, N2<=N2/Z; combining yields the lower tilted square bound even when 1-sqrt(s)*beta is negative. The proof does not improperly divide a possibly negative lower bound by Z.

5. **Upper tilted square and absolute cube** (production lines113–137). Domination V<=1 gives N2<=1 and N3<=beta. Positivity of Z permits division. With beta>=0 and exp(-s)<=Z, 1/Z<=exp(s) and beta/Z<=exp(s)*beta. These prove the actual raw tilted second/cube upper bounds. No centered-cube estimate is claimed.

6. **Actual finite variance identity and bounds** (production lines138–154). Genuine square integrability and measurable identity give MemLp id 2 rho. The proved probability instance meets variance_eq_sub, yielding actual native variance=id-square expectation minus mu^2. Set D=s*exp(s)*beta>=0. From the reviewed unit150 |mu|<=D, the nonnegative product (D-|mu|)(D+|mu|) gives mu^2<=D^2. Subtract it from the square lower bound to obtain the stated variance lower bound, and use mu^2>=0 with the square upper bound for the upper variance bound. All nine frozen conjuncts are supplied.

### Complete actual type and value coverage

- All 12674 bytes of the pp.all actual-type export were read in full, then compared with the exact original audit type block. There are no omissions, unresolved metavariables or additional binders.

- The domain, universe-0 real measure, real measurable/topological/normed instances and sole IsProbabilityMeasure nu binder are exactly those in unit150. h2, h3, hmean, hnorm, real s and hs:0<=s retain exactly the same meanings, without a support, smallness or variance hypothesis.

- The type has exactly three local lets: rho is the native energy tilt, beta is the original auxiliary absolute-cube expectation, and mu is the actual identity expectation under rho. No local value is a global module-owned non-theorem definition.

- The nested actual And contains exactly nine conclusions: probability rho; square integrability rho; absolute-cube integrability rho; 1-sqrt(s)*beta<=E_rho z^2; E_rho z^2<=exp(s); E_rho |z|^3<=exp(s)*beta; ProbabilityTheory.variance id rho=E_rho z^2-mu^2; 1-sqrt(s)*beta-(s*exp(s)*beta)^2<=variance id rho; variance id rho<=exp(s). All products, square powers, sqrt, measure arguments, coercions and standard instances match the frozen head.

- The final variance is the actual native ProbabilityTheory.variance, not a named residual, a supplied surrogate, or an assumed finite value. The proof establishes MemLp2 before the identity, excluding the toReal-infinity/undefined-integral loophole.

The single151owner is one public theorem, with zero private/generated theorems and zero global non-theorem values. All12674 actual-type bytes were read; the empty full value export is verified. The entire original12899-byte audit log is accounted for by the exact type block and complete warning/count/exit remainder.

- **Shao.C2.AuxiliaryEnergyTilt.auxiliary_energy_tilt_normalizer_and_drift**. Complete exact source/proof/type/interface/axiom review is included above. All hypotheses coincide, with definitionally identical rho,beta,V,Z. No second independent re-review of an unchanged dependency is needed.

- **MeasureTheory.integrable_tilted_iff / integral_tilted**. Same pinned native signatures and context reviewed for150, now instantiated with g(z)=z^2 and |z|^3. Weighted integrability is proved explicitly; the true positive normalizer is inherited exactly.

- **Real.one_sub_le_exp_neg / Real.sqrt_nonneg / Real.sq_sqrt**. The global exponential tangent is already reviewed. sqrt is the nonnegative real square root; hs gives (sqrt s)^2=s. The t<=1/t>1 split exhausts the cases including t=0 and t=1.

- **MeasureTheory.memLp_two_iff_integrable_sq**. Same native signature reviewed above; id is measurable under rho and the proved h2Rho is exactly its square integrability.

- **ProbabilityTheory.variance / evariance / variance_eq_sub**. Read native definitions and lines1-240, including evariance finiteness for MemLp2, and exact variance_eq_sub proof. The instance is the proved hRho and hL2 is derived, so no variance-finiteness or centering premise is hidden. Native source bytes equal the pinned commit.

The additional native variance definitions, finiteness interface and variance_eq_sub signature/proof/context were read at Variance.lean1–240. That exact native source SHA256 is `0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e`, equal to the pinned commit bytes. The proof installs the proved probability instance and derives genuine MemLp2; it cannot obtain the variance identity by totalizing an infinite variance to zero.

### Freeze, attempts, dependency and axiom provenance

Unit151 exact source SHA256 is `5a9b156d0f7ad1c41f15b361b1cea008e7f47716e23d86c0f57db04ac54498d3`, frozen SHA256 `78befb89d52d6d62818b667b54ad59254435440e81b586a26c2dbf6fde913b8d`, output/imported-object SHA256 `54613db5670afca311a3d37420c388ef5cc44773e48e0deabf39ff3e3481bff2`, receipt SHA256 `3ef8b12465dfa20cc03765cee96bc41f37a58abecb90e4879443491e8ab482f5`, and author-release SHA256 `5928200fb792b87f8a9c919f0298788bcd8956ff4d5b6e4042ed58453dfa3417`. Both attempt001 and002 preserve the complete frozen imports/context/head exactly. The full source/proof, original command/log for each attempt and the precise source diff were reviewed. The two repairs are only replacing the nonexistent absolute-cube measurable expression with `fun_prop` and unfolding the function subtraction before `ring`. There is no changed mathematical premise or declaration.

Attempt001 is honestly preserved with `KERNEL_EXIT=1`; attempt002 has `KERNEL_EXIT=0` and only the shared Mathlib warning plus the retained local `letI` style hint. The exact successful object is the one imported by the all-owner audit. The all-owner audit code is fully read and uses the same actual ownership/transitive axiom mechanism verified above, now restricted to AuxiliaryEnergyMoments. Its exact single recursive axiom set is again `[propext, Classical.choice, Quot.sound]`; audit exit0. No forbidden production token is present. No failed or successful proof gate was replayed by this reviewer.

The only project dependency is the exact unit150 source SHA256 `8ea1547baf4beb388faea8d4d8ded12cab83c098f5bb41b2995d79675abd91ca` and imported object SHA256 `31ef9fa4d5bd0289a315e973c72ede5e7a222100e68e0fc622a59d0550de00ba`, both observed unchanged during151review. The complete150review above qualifies that source within this same packet; the151dependency has no scope or type gap. Parent may qualify both only after reading the complete reports and sealed exact binds. No source152or any later unit is included.

At `s=0`, the moment and variance bounds recover second moment/variance1 and raw cube beta. At large s the lower bounds may be negative, which is legitimate. All real signs and atomic/asymmetric laws are covered. No fixed positive variance lower bound or centered-cube estimate is inferred without the subsequent small-s work.

**Final combined verdict: CORRECT for both exact frozen units150 and151, two public/actual theorems, zero private/generated owners and zero global non-theorem values.** Original C1/C2 roots remain OPEN. There are no critical gaps within these frozen targets. final-observation.json and validation.json check both exact packets; writer-release.json seals the combined full reports and is written last.

The exact additional square-root interfaces are `Real.sqrt_nonneg (x : Real) : 0 <= sqrt x` and `Real.sq_sqrt (h : 0 <= x) : (sqrt x)^2=x`, read with namespace/context at Mathlib/Analysis/Real/Sqrt.lean143–149 and176–177. That native file SHA256 is `1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204`, byte-equal to the pinned commit. The first conventional Data/Real/Sqrt path was a compatibility wrapper; the actual Real signatures were located and read before sealing.
