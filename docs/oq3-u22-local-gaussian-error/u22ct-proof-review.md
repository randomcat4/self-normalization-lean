# OQ3 U22ct / CT179 independent complete proof review

STATUS: CORRECT

Statement/source fidelity: CORRECT. The entire proof and all statement/proof values: CORRECT. The exact-source saved server kernel and actual-whole-module recursive-axiom evidence were verified and are reusable. No critical mathematical, translation, dependency-qualification, or evidence gap remains within the frozen auxiliary scope. No implementation repair is requested.

Reviewer: fresh independent NON-AUTHOR context `/root/oq3_u22ct_full_review`, prescribed/configured dispatch `gpt-6.1-sol` / `xhigh`, 2026-10-24 Asia/Singapore. I authored or repaired none of the reviewed source or frozen declaration. Sole write ownership is this report. Separate input, cached-input, output and reasoning-subset usage counters and independent model/billing attestations are unavailable; no numerical usage or subscription-percentage allocation is inferred.

## Authority and complete immutable coverage

I applied math-theorem, its verification role and Lean protocol, AGENTS.md, SERVER.md, selected current TEAM/REGISTRY ownership fields, takeover/restart constraints, and streamlined-acceptance-current.md. The OQ3 owner is activated with the old writer released, one child lease, server CPU14-17, one heavy command, native8192MiB/j4. This reviewer spawned no context and ran no Lean/build/axiom/publication command. All remote operations were bounded read-only inspections through tools/server.py's transport; inner exit codes were inspected. One read-only search returned exit1 because remote rg is absent; a Python source-reading fallback succeeded. This was no proof/check failure and caused no Lean replay.

Complete reviewed artifacts, with SHA256:

- `u22ct-source.lean`: `7ac1a07ae4812d32b8f2af6d2a01bf369aeaf8a749926a6c86ad35815ffe92c3`, all77 lines/3413B, including imports and every proof expression.
- `hundred-seventy-ninth-unit-scope.md`: `a4f4b99c7e9acbfa73c6732585e9615cb1edb5262f633e6601fa69f34efc5706`, all31 lines/3601B, including the complete declaration and seven let-values.
- `u22ct-receipt.json`: `4926966814c858a830f0c974237a8b30b7a67bcf3bf2cdb15aa381b8978076b2`, all89 lines/3821B.
- `u22ct-actual-types.txt`: `87896e3c917f1453db637c28eacb493225b941b7a3d14d85a1b88ed26cf992d6`, all18 lines/1187B, without an omitted/truncated declaration.
- `u22ct-Audit.lean`: `2f432fe538cf4c369b3b65ed39ac0ae53917715c3027b08d4bcd1c5be7d9ea92`, all47 lines/2001B.
- Environment `10fcfdabe1fda76affb8c71daad204835670a845fb46b60a2fa140499133fa41`; dependency binding `e6068d27b94d649b8b2a721a4a6226162d54e4ab060728dd3eb06bd7848c7eed`; history `8b12d2a44412252d45f1a1606360b26d2eb010e914ca60435c81d229ff9200f6`; audit record `2ab549fcc4b88a99a8bab085f59a7148de0b46d369b756bcab8914bdb5ef6374` were read completely.

The full Lean declaration preceding `:= by` equals the frozen code block exactly after removal of trailing whitespace. Freeze-before-implementation is recorded in the frozen scope and original history. Saved source-01, current production source and local source have the same SHA; source bytes are UTF-8, LF, no BOM and no CR. There is one complete first-success version, no repair or post-PASS source change. The actual owner/type output agrees with this complete frozen declaration, including all parameters, hypotheses, seven lets and three conclusions.

## Exact mathematical statement and values

The theorem is `Shao.OQ3.iid_parabola_fin2_characteristic_factor`. Its quantifiers are arbitrary scalar probability nu; n natural with 1<=n; arbitrary real 2x2 matrix A; arbitrary b:Fin2->Real; a continuous real linear equivalence E on Real x Real; and the literal hypothesis, for EVERY real x,

`E ((x,x^2) - (b 0,b 1)) = ((A *v (![x,x^2]-b)) 0, (A *v (![x,x^2]-b)) 1)`.

Then EVERY real xi,eta is covered. The hypothesis is coordinate action on the same centered parabola, not a hypothesis of equality of laws, Fourier transforms, error bounds, or the desired characteristic-power conclusion. No finite moments, zero mean, identity covariance, density, atomlessness, weak-Cramer bound, frequency gap, or uniform-family assumption is present. E's invertibility/continuity are honest supplied structure. The theorem does not assert existence of E for arbitrary A,b, or that b is the actual mean.

All seven statement lets and all seven proof aliases in lines32-42 were read and matched definitionally, with no shadowed replacement:

| Let | Exact value and semantic check |
| --- | --- |
| Y | `x -> A *v (![x,x^2]-b)`, a genuine Fin2-valued function of a single scalar observation. |
| law | `nu.map Y`, the actual distribution of that SAME Y, rather than a supplied comparison law. |
| Phi | Integral under law of `exp(I*(u*y0+v*y1))`; real-to-complex coercion and positive imaginary phase are preserved. |
| Q | `Measure.pi (fun _ : Fin n => nu)` on `Shao.Path n`, the actual product law of n scalar observations. |
| M | `z -> ((sum_i z i)/n, Shao.energy z/n)`, both actual empirical parabola coordinates. |
| T | `z -> sqrt(n) smul E(M z-(b0,b1))`, using exactly the supplied E and center. |
| rho | `Q.map T`, the actual raw-scalar iid standardized sample law, not a newly chosen pair-iid proxy. |

The three conclusions are: IsProbabilityMeasure law; IsProbabilityMeasure rho; and the exact equality

`integral exp(I*(xi*w1+eta*w2)) d rho = (Phi (xi/sqrt(n)) (eta/sqrt(n)))^n`.

The exponent is the natural n and both frequencies are scaled by the same positive sqrt(n). No absolute value, asymptotic, finite-only enumeration, or one-sided inequality replaces this equality. The n>=1 restriction covers n=1 and excludes zero-denominator semantics. Atomic and nonintegrable-moment scalar laws remain permitted: characteristic integrands have norm1 and all relevant laws are finite probabilities.

Actual foundational definitions were read: `Shao.Path n := Fin n -> Real`; `Shao.energy z := sum_i (z i)^2` in FinitePath source `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`, matching server bytes. Energy is not an expectation, variance or surrogate. Matrix.mulVec is the literal finite row sum in pinned Mathlib/Data/Matrix/Mul.lean. No ordinary-Prod max norm is treated as a Euclidean norm or an inner-product structure.

## Complete proof review

Lines1-8 import the qualified iid characteristic module and actual Matrix API, open notation, and introduce a noncomputable section. They introduce no mathematical assumptions or proof-trust changes. Lines9-30 are exactly the complete frozen statement. Line31 only unfolds statement lets; lines32-42 reintroduce their identical values for the proof. Every value is covered above.

Lines43-49 prove genuine Continuity Y, rather than assuming it. Continuous_pi reduces to each output coordinate i. The changed expression is exactly `sum_j A i j * (![x,x^2]-b) j`. Continuous_finsetSum reduces to its two summands; fin_cases on j covers both 0 and1. Simplification and fun_prop prove continuity of a constant coefficient times x-b0 or x^2-b1. No regularity of nu is used. This works for every fixed A,b.

Lines50-51 derive hlaw using the actual pinned `Measure.isProbabilityMeasure_map_iff`: AEMeasurable Y implies probability of nu.map Y iff probability of nu. Continuity supplies measurability and aemeasurability. Thus the law is neither Lean's nonmeasurable-map zero default nor an assumed probability law. The supplied instance on nu proves the right side.

Line52 constructs the first conjunction component from hlaw. The second component is `.2.1` of qualified BV `iid_parabola_affine_standardized_law nu n hn (b0,b1) E`. The full consumed interface has conclusion probability law AND probability `(Q.map T)` AND the pointwise iid-sum identity AND equality with the iid pair-sum law. The projection therefore supplies precisely probability of this rho. All its nu,n,hn,y,E arguments and Q,M,T definitions match; it does not use an unrelated E or center.

Lines53-70 prove hPhi for ALL real u,v. The left integral is the genuine scalar-nu integral of the pair phase of `E((x,x^2)-(b0,b1))`; the right is the actual Fin2-law Phi. Lines59-62 instantiate the actual pinned Bochner integral_map using Y's aemeasurability and continuity of the Fin2 phase, hence its AEStronglyMeasurable property under nu.map Y. The API's direction is `integral f d(nu.map Y) = integral f(Y x) d nu`. Lines63-65 unfold law and rewrite that mapped-law integral on the RIGHT to the scalar integral. Integral_map requires no separate finite-moment assumption. It does not bypass a missing measurability obligation.

Lines66-70 use integral_congr_ae with a pointwise proof valid for every x. The local hx is exactly hpoint x; after changing its notation, it reads `E(centered parabola x) = (Y x 0,Y x 1)`. Rewriting hx makes the two complex integrands identical, including the signs, real coefficients, complex coercion and I. There is no appeal to an equality of expectations in place of pointwise action, and no null-set restriction introduced into hpoint.

Lines71-74 obtain qualified CD `iid_parabola_standardized_characteristic_factor nu n hn (b0,b1) E xi eta`. Its complete Y,Q,M,T,rho,Phi lets were read: CD's Y is the actual pair E(centered parabola), and CD's Phi is the scalar-nu integral of that Y. Its Q,M,T,rho agree exactly with CT. Dsimp only exposes these values. Rewriting with hPhi at the scaled frequencies changes only the one-observation scalar integral to this Fin2 Phi. The left-hand rho and power n are retained; exact hf closes the final goal. There are no remaining cases or missing integrability, independence, normalization, or representation interfaces.

## Qualified dependency reuse and original-source fidelity

I read the COMPLETE consumed CD and BV interfaces, including all their quantified parameters, hypotheses, conclusions and let-values. Their old whole proofs/reports were not rereviewed. Exact qualifications were checked using source/report/receipt hashes, qualified report verdict/coverage metadata, and the current source-object bindings:

- CD NormalizedIIDPairCharacteristic source `22120e1075826e4a26411834c4aff8e645dbff2a59b4ed539d5067e0080ac6ca`; receipt `2cfbe8184271b2af0fbbed9f6855a6613b87a65bb76caffe012cb858c7783df8`; final complete independent report `9adffbf22ebf3fa1e2b6fe0dacfb1a2d9ff670716f6c16cd502d44452a503eeb` /123lines, CORRECT and recorded COMPLETE_QUALIFIED. Its 3public/4actual including1generated coverage is preserved. Original object `7d38557eb5bf06f58609aeb3428960f7e79690147b36f06ef663766cfb7dcb50` /246312B matches current server and accepted-source-view resolution.
- BV ParabolaIIDStandardizedLaw source `3c44e20c9003e0b743829a5ad46ee56f12f72c9cc8fbaa6bea61c5cbb3c526b7`; receipt `cc96202bba1795effea51e1ab5ed75c31eef7d0a179e92050b1c0283b7d41133`; joint BU/BV final complete independent report `0ede4b14deb562e06696b2ac0c56d63b430f41c48b21063626a4870e69090c56` /108lines, CORRECT with complete exact-source kernel/whole-owner evidence. Its BV 2public/3actual including1generated coverage is preserved. Original object `5ac5eba2999d340b7d7c35c62ed7fa811aa5200f8edb540fcedc91944865d3b6` /213576B matches current server and accepted-source-view resolution.

Both source hashes also match local accepted v61 library bytes and CT's pre-first-kernel binding. Immutable original receipts retain their historical AUTHOR_PASS_PENDING strings; qualification comes from the later exact independent reports/accepted records, not from treating that historical string as current. No old failed proof, successful check, review or publication was replayed or rewritten.

I read original read-only OQ3 R2 report lines83-92 and139-157, and the source/root-contract and low-frequency intake context. The source uses standardized parabola Y and `n^(-1/2) sum Y_i`, whose characteristic function is the nth power at frequency divided by sqrt(n). CT expresses the raw-sample pushforward with the corresponding empirical M. Qualified BV/CD provide precisely that normalization and scalar iid factorization. This is a source-faithful representation bridge, not the source's full Edgeworth/Fourier theorem.

The canonical application is concrete: the qualified BU/CP producer supplies literal A, means, Fin2 Y and laws, and ONE E on Theta with `E p(centered parabola x)=(Y p x 0,Y p x 1)`. I inspected CP's relevant full A/means/Y/laws/Phi definitions, E binder and exact pointwise-action component. Substituting nu=tilt p, A=A p, b=means p and E=that SAME E p satisfies CT's hpoint. CT itself neither chooses E nor compares independent choices. Canonical mean0/covarianceI and moment results remain producer facts, not extra CT premises or consequences. This interface is directly usable by the actual raw-iid Gaussian consumer; that consumer is outside CT's review.

## Saved server kernel, ownership and recursive axioms

Server run is `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22ct-20261023`; worktree is `workspaces/lead-oq3`. Saved scope, source-01, receipt, actual-types, Audit.lean, environment, dependency binding, history and audit record have exactly the local hashes above. I read both saved logs completely and verified their bytes/hashes rather than rerunning them.

- First complete kernel attempt01: exit0, 4.965782763436437s, source `7ac1a07a...ffe92c3`; log `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626` /133B. Its entire content is the recorded Lake warning that the mathlib repository has local changes. No Lean error or proof warning is hidden. Source remains the first-PASS version.
- First actual-owner audit: exit0, 5.719596493989229s; log `1e1e920e2716cf6d6066dc8262dce867173ad6e056820bff2c859d3d3f151fc6` /1439B. It prints the complete18-line actual theorem type/axioms/kind and counts: frozen definitions0; frozen theorems1; all theorems1; all declarations1; U22CT_AXIOM_GATE PASS.

The complete audit loops ALL environment constants and selects actual module ownership via getModuleIdxFor?, not a namespace/public-name prefix. Therefore private, generated and externally named module-owned declarations would be included. It rejects new module axioms and recursively collects every owned declaration's transitive axioms. Exact actual ownership consists solely of `Shao.OQ3.iid_parabola_fin2_characteristic_factor`: one public theorem, zero definitions, zero private/generated theorems or other owned declarations. Each actual owned type is covered; there is no unreviewed definition value. Recursive axioms are exactly `[propext, Classical.choice, Quot.sound]`, all whitelisted. The audit's pp.deepTerms/pp.maxSteps options affect printing, not proof trust.

Source/proof inspection finds no sorry, admit, added axiom, unsafe, native_decide, implemented_by or proof-setting weakening. The saved gates use CPU14-17, native -M8192, -j4 and autoImplicit=false. Current Lean pin is `leanprover/lean4:v4.36.0-rc1`; Mathlib manifest and actual checkout agree on `807d3836b165983210ee2ecf3cd28f239436949c`. The package link resolves to accepted shared-v34/packages. Current CT original object is `b81154b93a4baae704295752da8f7e031e54e726e2877219f624545b0b1c2e97` /127344B, and accepted-source-view resolves to that same object. No cache/package or object was copied/modified by this reviewer.

Current branch remains `feat/oq3-low-frequency-and-inversion`, HEAD `9c8680b44f12d634bd74d9251ec2f26caac921e8`, tree `d0a6f95c0b3dc46353c07f9a0025c42fb4084ecb` (frozen PR228); CT is continuation outside that PR. Root v61 receipt `915bdc06612c6d5a54c234e7f7ea75662e717d59fc3bd362ba55d0d41b801cc3` checks commit `78a8cfa78bb7ad4a58f6dc747b2260220f5e439a` /tree `ea2f84f8da9d1e64913418334c6a73f90c865027`; these are distinct from the recorded published/accepted snapshot identifiers af94328d/fc7b79eb/tree10144eb4. This review does not claim CT was included in v61 or PR228.

## Verdict and scope limit

CORRECT for the COMPLETE frozen CT179 auxiliary theorem, all77 source lines, all seven statement lets and proof aliases/values, the entire proof and all18 actual-type lines, with exact-source server kernel and whole-owner recursive-axiom receipt verified and reusable. Acceptance requires no additional CT proof check or old-unit rereview for unchanged bytes; root retains ordinary exact-hash/interface/integration responsibility.

This closes only the same-E Fin2-law/raw-scalar iid probability and exact characteristic-power bridge. It proves no local Gaussian estimate, Edgeworth expansion, derivative estimate, Fourier integral or inversion, weighted probability error, exterior control, or new-rho Laplace theorem. Original OQ3 B/D remain OPEN; corrected A and bounded C retain their previously accepted scope. The original strict beta<2/5 boundary, p54 repairs and external Song/Angst-Poly attribution are unchanged. Correctness of this elementary interface is not a novelty or original-root completion claim.
