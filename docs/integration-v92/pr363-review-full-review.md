# Independent complete final review: actual regular retained probability

STATUS: CORRECT

The exact new module proves the advertised regular, pre-first-hit retained-remainder probability bill for a canonical centered unit-variance iid population with finite absolute third moment and the same independent uniform labelled permutation. It proves measurability, genuine Bochner integrability, and both the stronger `C * delta * exp (-x^2)` bound and the `C * delta * standardNormalTail x` bound. I found no critical mathematical, source-translation, frozen-interface, or exact-evidence gap in that scope.

This is a fresh final review by `/root/regular_retained_probability_final_review`, separate from the source author `/root/permutation_reveal_candidate`. The author had released source writing and target execution before this review. I did not implement or repair the subject, run Lean/lake/kernel/axiom commands, install anything, change caches or shared files, publish, merge, or spawn another context. All reviewer writes are in this directory. Root alone decides qualification and integration.

This verdict closes this particular probability producer. It does not close original C2, C12, OQ56, the rare/record/strip branches, separated overshoots, terminal/omitted tails, or the return from an auxiliary law to the original finite-moment law. Original C1 has its separate immutable accepted evidence; OQ3 remains paused by the human.

## Exact subject and complete coverage

The source-only subject is PR363, `https://github.com/randomcat4/shao-lean/pull/363`, head `eeea753812879602a6439958d7033bb692fa3a7e`, tree `3239af5efcb4f5b5a10a4187fbae043f8cfcfed1`, blob `96894cc08c64108339af34a91c72b1ce91f24fbf`.

* Source: `Shao.Probability.SourceRegularRetainedProbability`, 61,737 bytes, 1,056 lines, SHA256 `0bd5cd311d2db9d181a42073ebcddf35682c20028af0e20e36f00021fccb7b68`.
* Original whole020 object: `937bb5e3a33244fa20f77ec62a473e0f366f45779ea0fd10bba4a11883d615dd`, 3,840,544 bytes.
* Immutable author receipt: `6a00a585ffec84afa238a6215390fe4cbfdf75f0c5c3b01724024bbc1691c282`; author release: `3405e61acad1e65ae26683f491b050e283597f26a4ffb97b0e6faa64a4340e4e`.
* Full actual owner export: `5099a8fd6b4553537ed6f3bd68edbd1fc6830e07f1b04622a2f1d24b0ce67fa1`, 114,095 bytes, 1,604 lines. This is byte-identical to the original owned-audit001 log.

I completely read source lines 1–1056, every unelided actual TYPE in export lines 1–1604, and the complete values of both actual non-theorem owners. The owner count is derived from the actual audit map and checked against exported names: 44 owners, 42 theorems, 2 definitions. These consist of the one public theorem, two source-private theorems, 39 generated theorem owners, the local measurable-space instance, and the generated three-domain matcher. There are no omitted owners selected by a lexical prefix shortcut.

The two non-theorem values were read in full, including the elaborated universe/typeclass arguments: `labelPermMeasurableSpace` is exactly the top measurable space on finite label permutations, and public theorem `match_1` is exactly `MonitoredDomain.casesOn` with the upper, lower, interval branches in that order. It adds no assumption, state, oracle, or alternative derivative. Every generated theorem TYPE was read, including the natural-subtraction bijection/inclusion obligations and generic simp equalities. Their mathematical roles agree with the source arithmetic and measurability proofs. `coverage.json` records each of the 44 names, actual kind, complete type coverage, type hash, and required full value coverage individually.

The entire new proof bodies read are source 43–193, 220–768, and 813–1054. Accepted old proof bodies were not commissioned or reread wholesale merely because this review is fresh; their exact qualified evidence is reused. Complete consumed contracts and necessary definition values were read. All 85 declaration fragments in the supplied full contract capsule occur in their exact native source after whitespace normalization; additional contracts actually introduced during implementation were read from native source. This comparison is in `native-contract-comparison.json`.

## Frozen declarations and source fidelity

I independently compared the three actual source heads to the frozen heads, including their complete ambient context. All are exact:

| Declaration | Literal statement lets | Exact head SHA256 |
| --- | ---: | --- |
| `rrp_unsummed_cubic_grid` | 4 | `01ce91c996aafecd0a6a7c14579b4b1b09a560b61e84f2f616b1c19fd0fbd0ae` |
| `rrp_damped_energy_grid` | 7 | `470d8279d9a9bf82a6e8efddcf7958b99f4966cf63fccffc6df2ea570728cdb1` |
| `iid_actual_regular_retained_probability_budget` | 10 | `ee8cfae126615c8446e747155b7821146fb73bbc8727b6f7341993696f48b411` |

The public V2 context hash is `e7bdb4b09b04714c9a0e04fe2096e724f6aca1f0277f491cf94f5585d0452a6d`; the private freeze is `92badd0a452cf93517670e4a86dfce071de3c503bdd9b0a2bef76810d601759b`. The approved context amendment only adds `Elab.async false` and `maxHeartbeats 5000000`; it does not alter mathematical assumptions, conclusion, imports, or the local instance value. The two private declarations were substantively frozen before their bodies. The public constant is existentially quantified before Brownian realization, population law, sample size, and level.

The first two source comment lines retain historical mathematics-only/qualification-pending wording from the frozen candidate. That comment is superseded by the actual activation and PR355 qualification. It is not an assumption or unresolved mathematical dependency, and I did not rewrite frozen bytes to modernize it.

I read the original `C:/game/shao/current/c12/supplement.tex` passages 4682–4697, 4750–4778, 4810–4865, and 4906–4935, together with main.tex 1411–1438 and the candidate's complete scope/adaptive-application notes. The supplement hash is `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

The original state is preserved: `EX=0`, `EX^2=1`, `beta=E|X|^3`, `delta=beta/sqrt n`, `h0=4 beta^2`, actual total square sum `Q`, actual `T=Q-Q_r`, actual remaining sum `d`, and next actual label. The regular local source statement at supplement 4810–4817 and its summation at 4858–4864 are exactly the obligations being assembled. The new unit uses the p=3 unsummed component of the damped grids and existing early/late moment producers; it does not claim to newly prove every p/grid statement in supplement 4906–4930.

Finite third moment is an explicit assumption of this auxiliary producer. Nothing here silently changes the hypotheses of the original C2 theorem, whose truncation, centering, normalization, residual branches and law transfer are separate obligations. Bounded auxiliary laws produced by that later chain can instantiate this theorem. This theorem alone does not perform that chain.

## Probability space, selected bill, and boundary conventions

The raw population law in the public head is literally `P = Measure.pi (fun _ : Fin n => rho)`. The reveal law is literally `P.prod (uniformPermutationLaw n)`, where the permutation law is inverse cardinal times counting measure on label permutations. Repeated values keep their labels and their multiplicities. The same population and the same `sigma` are used in all three retained remainders and in `nu`; no fresh suffix, second permutation, or conditional product-law premise is inserted.

The stopping rule is exactly `nu a sigma = energyCutoff a h0 sigma`, the first remaining-energy value strictly below h0. Thus active ranks retain the closed condition `h0 <= T`. The selected bill is the finite sum over all `r : Fin n` of the absolute interval-minus-upper-minus-lower retained remainder under three simultaneous guards: `r < nu`, every prefix through r lies strictly inside the actual wall, and the regular displacement satisfies the closed inequality `|d| <= 3*x*sqrt(T)/2`. The first discrete crossing step is included because survival is required only through the pre-step rank r. There is no assumption that the random actual-energy wall is a natural iid stopping boundary.

The source retained remainder still contains each domain's actual `sourceAlive`, endpoint, positive-energy and rank guards and its original small-step projection/full-large-step convention. Those definitions were read in full. The public guard does not replace them with an artificial common endpoint mask. PR355 pays their actual combination, including exterior and equality endpoints.

`beta >= 1` gives positive h0, so every active T is positive; the zero-total-energy path has nu=0 and contributes zero. Equality T=h0 is retained. The regular-cone equality is retained. A prefix exactly on the wall fails strict survival; this agrees with the complement of the weak multiplication event and does not discard an atom by an unjustified null-set claim. n=0 is explicitly excluded; n=1 and the singleton suffix are covered. Rank r=0 is included, r=n is not, and the last actual label is r=n-1. No division by an unguarded active zero T is used. Reachable zero *future* time after consuming a large step belongs to the consumed qualified local theorem, whose full contract includes that actual branch rather than assuming future time positive.

## First private proof: the genuinely unsummed ordinary cubic grid

Source 25–42 states one universal K before the law and all N. It supplies measurability and genuine integrability of each selected `(m+1)`-label ordinary marked cubic and a bound for every finite sum m<N, including m=0 (suffix length one).

The proof consumes the qualified ordinary inverse-moment master at p=q=3. It does not replace the ordinary selected weight by an exponential-marked target premise. With H=4 beta^2, the pointwise inequality

`z^2 <= z^2 * 1_{z^2<=H} + |z|^3/(2 beta)`

gives retained second moment at least 1/2 by actual integrability and the unit second moment. Both the truncated square and the cubic divided by `2 beta` are integrable. The complement implication `z^2>4 beta^2 => |z|>=2 beta` is used with beta positive. This supplies the negative branch gamma=-c of the old master, with `c=(1-exp(-2))/8>0` and c<1.

The resulting actual kernel is `s^(1/2) A(s/2) exp(-c s m)` on `0<s<1/H`, where `A(u)=E[|X|^3 exp(-u X^2)]`. The old master provides genuine selected and kernel integrability. The new proof proves the elementary finite geometric bound `sum_{m<N} exp(-c s m) <= 2/(c s)` using c*s<1, positivity, the telescoping geometric identity, and `exp(c*s)>=1+c*s`. It separately proves `0<=A(s/2)<=beta` with an integrable cubic dominator.

The integral `integral_0^(1/H) s^(-1/2) ds = 1/beta` is evaluated with the interval-integrable rpow theorem, Ioc-to-Ioo equality for Lebesgue measure, and `sqrt H=2 beta`. All parameters are positive, and the singularity at zero is integrable. Finite sums and integrals commute using the actual master integrability; no infinite sum/Fubini assumption is smuggled in. The product of the bounds is `CI*(2 beta/c)*(1/beta)=2 CI/c`, so K is law-independent. This pays exactly the full unsummed ordinary cubic grid needed in the bad-prefix term.

## Second private proof: actual total-energy damping

Source 195–219 keeps the cutoff H=4 beta^2 inside the actual G and the exponent `-x^2 * energy(a) / T(a,r)`. The conclusion includes measurability and genuine integrability of the whole finite rank sum, as well as its universal `K delta exp(-x^2)` budget.

The proof defines the old normalized-law budget R0 from `map (z / sqrt n) rho` and the lower comparison cutoff h=4*n*R0^2. It proves R0<=delta directly from the pointwise `truncationF(u)<=|u|^3`, actual map integrals and finite-third-moment integrability. Hence h<=H. This only enlarges nonnegative comparison weights: the actual stopped rank and the cutoff in G remain H throughout.

The ordinary suffix weight W has the actual H guard and `(1+|d|/sqrt T)^3`. The old early comparison E has the lower h guard and `1+|d|^3/(T sqrt T)`. The proof establishes `W<=4 E` from `(1+u)^3<=4(1+u^3)` for u>=0 and `sqrt(T)^3=T sqrt(T)`. Existing early cubic integrability and its CE*R0 bound can then be used without a residual-smallness premise.

For each r the map `split r a = (head a r, tail a r)` is actually measure preserving from rho^n to rho^r times rho^(n-r), via the finite sum index equivalence and the native pi/product contracts. Both factors are probability measures, so their SigmaFinite requirements hold. This is unconditional raw iid head/tail independence, applied after all first-hit, energy-cutoff and regular-path selectors have been removed from the comparison grid. The proof never treats a path-selected suffix as independent of its selected prefix.

The consumed `gaussian_weight_source_state` supplies only actual identities of energy, sum, total energy and first suffix label. Its full native head and `firstValue` value were read, and its exact source/object qualification is bound below. In particular, the suffix begins at the original label r, not at r+1 or a resampled mark. The actual relation is `energy suffix + energy prefix = energy whole`, and every suffix has positive length since r<n.

The equality `G = W(suffix) * exp(-x^2 * energy whole/T)` is proved before estimating. Since `T<=energy whole`, it gives `G<=W(suffix)*exp(-x^2)` on positive T; the other branch has W=0. This supplies per-rank integrability from the first private theorem, transported by the actual tail map. Measurability is proved explicitly, including the cutoff guards. Thus later integral inequalities do not exploit Lean's default value for a nonintegrable integral.

For early ranks r<=floor(n/2), the suffix length t=n-r ranges bijectively over `ceil(n/2)..n`. The old CE budget and R0<=delta pay their integral sum, including the even midpoint exactly once.

For strict late ranks r>floor(n/2), the proof divides according to whether actual prefix energy is below r/2. On the good set, prefix energy is at least n/4, so total energy is at least T+n/4. Since x^2>=1,

`exp(-x^2 * energy whole/T) <= exp(-x^2) exp(-n/(4T)) <= exp(-x^2) * 4T/n`.

The last inequality follows from the elementary exponential lower bound at w=n/(4T)>0. The factor `(T/n) W` is then pointwise bounded by the lower-h marked late weight: `T/n<=T/r+Rprefix^2`, and D^3<=D^5 because D>=1. The qualified marked averaging theorem proves both integrability and equality with the averaged actual late weight. It is transported through the suffix law; the accepted p=5 late CT*R0 budget then applies. No claim of pointwise marked/average equality is used.

On the bad-prefix set, define the measurable integrable indicator I=1_{energy prefix<r/2}. The proof consumes the *exponential moment* part of qualified `auxiliary_tilted_product_low_energy` at s=0 and q=1/(128 beta^2). The actual tilted law reduces to rho by `tilted_const`, and `(s+q) beta^2=1/128<=1/64`. The consumed moment is

`E exp(-q Q_r) <= exp(-(3/4) q r)`.

The new proof itself establishes `I<=exp(q r/2) exp(-q Q_r)`, integrates, and obtains `E I<=exp(-q r/4)`. It does not use the old theorem's different r/8 tail. Strict late r gives n<=2r, hence

`exp(-q r/4) <= exp(-n/(1024 beta^2)) = exp(-1/(1024 delta^2)) <= 32 delta`.

The final elementary inequality is proved from `exp(u^2)>=1+u^2>=u` with u=1/(32 delta), and delta>0. The product split yields the true bad-prefix probability times the ordinary suffix integral. Here both factors are already integrable (`I` is bounded and W comes from the first private proof); the composed product is also explicitly integrable. The native product-integral identity is correctly applied under the actual product law.

The strict-late bijection is `t=1..floor((n-1)/2)`. That domain is enlarged to the old `1..floor(n/2)` late budget only using nonnegativity; it does not count an even midpoint twice. The bad suffix integrals over late ranks are bounded by the all-rank unsummed KU grid, reindexed with m=n-1-r. The small n cases follow within these finite identities: empty late sets stay empty and t=1 remains in the all-rank grid. No informal large-n exception is left open.

Finally, finite rank integrability justifies exchanging integral and sum. The combined constant is `4 CE+4 CT+32 KU`, chosen before the law, n, and x. Every coefficient multiplication uses the required nonnegativity. This proves the exact frozen damped-grid statement.

## Public proof: physical kernels and the same actual permutation

The proof constructs the real bridge law from arbitrary Brownian B under PB, and proves it is a probability measure. It obtains the two halfline reflection identities from the accepted upper/lower identification theorems. It obtains interval spatial differentiability from the accepted actual image derivative theorem and feeds these contracts into the actual halfline/interval kernel data. Thus measurable FY and KernelBounds at constant 4 are outputs of physical Brownian producers, not oracle premises added to the public head.

Each actual energy cutoff section is measurable. The qualified `source_parts_measurable_integrable` applies separately to the three actual domains, giving per-rank retained measurability and genuine reveal-law integrability before subtraction. The guard's strict prefix event is a finite intersection through r; cutoff and closed regular-cone events are measurable. The countable finite label space has its exact top measurable instance. The bill is measurable and integrable by finite summation and domination by each actual retained absolute value. This establishes the analytic obligation independently of the later sharper bound.

The grid S is defined on raw iid paths with actual total energy. The raw coordinate family has the actual law rho, is iid, and is measurable. The accepted `iid_randomPermutation_map_eq_pi` is applied to these actual coordinates under P, with the *independent uniform* label permutation. The resulting reordered path has precisely P. Its IdentDistrib contract transfers both integrability of S after reordering and equality of integrals. There is no pointwise assertion that a path maximum, prefix event or stopping rank is permutation invariant; only total energy and total sum are proved invariant at the appropriate algebraic identification step.

For a selected rank, `energy_cutoff_data` gives T>=h0>0 from the same nu and same sigma. At that active rank, replacing the cutoff argument of `sourceRetainedRemainder` by `(fun _=>n)` changes no actual value: both rank tests are true, while all domain, endpoint, clock and projection data remain the same. This allows the complete qualified PR355 local bound to be instantiated with the actual population, actual r, actual sigma, strict survival and closed regular displacement. Total-energy and total-sum permutation identities then identify its right side exactly with `CL * G0(reorder population sigma,r)`; the wall square is exactly `x^2 * energy population`. Inactive ranks contribute zero and are dominated by a nonnegative grid term.

The finite pointwise domination `bill<=CL*S(reordered path)`, genuine integrability of both sides, and IdentDistrib integral equality yield the stronger budget `CL*KG*delta*exp(-x^2)`. All stochastic dependence in the selected bill has been preserved up to that pointwise bound, and is discarded only by nonnegative domination.

The last conversion uses the qualified Mills lower bound `density(x)/(1+x)<=Psi(x)` and the actual Gaussian density. For x>=16, `x<=exp(x^2/2)` and `(1+x)exp(-x^2/2)<=2`. Consequently `exp(-x^2)<=2 sqrt(2*pi) Psi(x)`. The proof establishes all positivity needed to multiply/divide, including positive Psi. Choosing `C=CL*KG*(1+2 sqrt(2*pi))` before Brownian/law/n/x pays both requested bounds with one positive universal constant.

## Qualified dependencies and exact execution evidence reused

The current read-only server observation confirms the subject source and its native committed content both have the frozen source hash, with exactly the head/tree/blob above. Git tracked files are clean; the sole untracked file is the existing `OwnedAudit.lean`. The installed subject object is the original whole020 object. The package view is the accepted read-only `cache-overlays/shared-v34/packages`; Lean is pinned to `leanprover/lean4:v4.36.0-rc1` and mathlib HEAD to `807d3836b165983210ee2ecf3cd28f239436949c`.

The 40-file author manifest was independently rehashed with no missing/size/hash failures. The existing complete 211-row actual import ACK is reused as source-bound successful evidence. Fourteen directly consumed native modules were selectively checked now: local curated source bytes match their frozen rows, actual server source (or exact qualified producer source where intentionally absent from the old base worktree) matches, and current installed import objects match their bound original objects. There was no new traversal of all old modules, recompilation, axiom replay or cache write. `consumed-native-binding-map.json`, `local-binding-validation.json` and `server-readonly-observation002.json` contain the exact rows and paths.

The especially material reused qualifications are:

* `SourceActualRegularLocal`: source `ce0236e9d4809297944000e12205214384b81ecbb64dc328f975c7210fc1547a`; object `e980ad71155d1aafb6e14e7493393545b380886972344795ccdbaa1cc4c5e386`; Root PR355 qualification `2ab7d5a4394aad0d95468251394336fcd75d77a4e9c5908676d72fff8a800fca`. Its exact complete independent review remains qualified and is reused.
* `SourceSuffixMomentBudgets`: source `c0457040fec0cee18355f5028c7731e0ad8525deee28185aa0cf3b7a088d3c7b`; object `feb6b5c085f1be3dc9e5ccbc5a8414a1b99a022a9a238abf87a063d7092bb08f`. Its complete ordinary inverse, early cubic, late fifth/cubic and raw budget geometry contracts were consumed with their actual parameters.
* `AuxiliaryTiltedProductEnergy`: source `034312b3e8ec9b4f3f77f8c0d008216e1ba86df69f6951ba1073cb825fd5ccc3`; object `ecf76a2967398b42e29342ad67036b0762d37324b2f2a4fd15a368df7531f6e9`. The qualified PR339 complete review covers the exponential-moment contract. The r/2 Markov deduction is new and was reviewed in this source.
* `SourceIIDGaussianProfileBudget`: source `44960de7f98cd219860b8619b8f07ecfc52369a678fcb73331d8c9838ce1b8c7`; object `0ebfa854fef5807edce7a1847be00df146a684a802d915c7265047e766cb8f62`; Root qualification `54eaccc55c356213d3e511e576c22303afa9ffff299ef14aa5afb0b334434c8b`. The additional native `gaussian_weight_source_state` contract was completely read, and only its first four state identities are consumed. No Gaussian probability estimate or old proof is rerun.

All these qualification/reference hashes, including prior independent review JSON/Markdown hashes where applicable, were verified in `bindings.json`; no qualified review binding failed. The Gaussian-state source and object are explicitly present in the current 14-row server import check, not merely assumed from an abbreviated name.

The original whole020 kernel receipt is RC0 with exact source/object, CPU40–43, native `-M8192 -j4`, and the standard root-heavy lock. Its complete original 13,790-byte log was read losslessly from the server; it contains style/deprecation/unused-tactic warnings, no hidden target error. Its SHA256 is `5cb064f064e2b56e77689c325a43564e6fe10f6b4cccde9ba55805e334f34f6a`.

The original unique owned-audit command is RC0 on the same original object. I read its complete driver, checked its SHA256 `a1f63bac6bdb46cc596457f40bc6735653acdeabfd185aa01c0d8eb113a1e582`, and read the original log through the byte-identical complete local export. Selection traverses `env.constants` and compares the actual `env.getModuleIdxFor?` owner to the exact target module. It includes private and generated constants in every namespace and invokes recursive `Lean.collectAxioms` for every owner. No prefix filtering occurs. The driver enforces the standard whitelist `propext`, `Classical.choice`, `Quot.sound`; the actual exhaustive JSON map has no other axiom. The full source has no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide` token. The audit driver and original object/import bindings were verified read-only rather than replayed.

The numbered author chronology has 20 attempts but 13 actual Lean invocations: 10 failures, two partial successes, one whole success; seven busy-lock results ran no Lean. There is one actual owned audit. Historical failed/interrupted attempts and publication push124/effect/API recovery evidence remain immutable. They were not treated as proof negatives requiring reruns. The source-only PR/native commit identity is preserved by the exact publication evidence and current committed content.

My first read-only observation failed when it assumed the qualified PR355 source existed in the old-base subject worktree. The original import binding had deliberately exported its object while the source remains in the qualified producer worktree. The failure is preserved in `server-readonly-observation.raw.json`; the corrected read-only observation uses the exact source path from the existing owner map and passes all 14 rows. This was not a failed mathematical check, uncertain write, or replay of a running command. A separate read-only attempt found server `rg` unavailable and used ordinary Python file reading; no system change was made.

The successful observation shows no subject Lean/audit process. No reviewer heavy command or target execution is in flight. The earlier historical resource affinity names in frozen archives do not authorize new execution; this review ran no heavy computation and touched no external workload.

## Verdict, limits and handoff

The theorem statement is faithful to the selected original regular-retained scope, the two new private proofs close their literal universal finite-sum obligations, and the public proof correctly links the real local physical bound to the actual canonical iid/permutation probability cost. All analytic integrability, product-law transport, finite summation, strict/closed boundaries, small n, singleton suffix and zero-energy issues relevant to this statement are paid. There is no remaining critical gap for this exact producer.

Correctness and novelty are separate: this is an original-source formalization/assembly result using already qualified local and moment producers, not a claim of a new mathematical theorem or completion of the research roots. The precise remaining downstream interface is a same-stopping-rank assembly with the separately owned rare/record/strip and terminal/omitted/residual bills, followed by any required auxiliary-to-original-law transfer. This reviewer does not write or assume that interface.

Requested reviewer model/effort: `gpt-6.1-sol` / `xhigh`, as prescribed by Root. Actual platform model and effort are not exposed to this context and are recorded as null. Input, cached input, output, and reasoning-subset usage are separately null; no subscription/quota inference is made.

Root must read this complete new report once before qualifying it, verify its exact subject and coverage bindings, and decide any integration-specific interface/name interaction. Reuse this exact successful source-bound review at intake; a new complete local-proof review is needed only for a real mathematical delta, uncovered scope or evidence gap. This report does not authorize publication or merging.
