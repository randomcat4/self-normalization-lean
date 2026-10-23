STATUS: CORRECT

Fresh independent reviewer `/root/common_outside_review`, gpt-6.1-sol/xhigh, read all 441 source lines, all 18 actual module-owned types (including private/generated declarations), and the complete source-to-statement/proof relationships. The reviewer changed no source, ran no Lean/build/axiom-collection command, and spawned no agent. This review owns only this report and its JSON companion.

The two public statements exactly match the frozen candidate after whitespace removal. The original supplement ranges 3508–3518, 3539–3547, 2420–2422 and 2444–2455 were read completely, together with the D/E definitions and source setup. Original source hashes remain supplement `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`, main `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5d62bb132122d06`.

| Version-bound item | SHA256 / identity |
|---|---|
| Author commit | `415ae51c2bd42227894747f5d59b051e7d19631a` |
| Source, 23958 bytes | `7be205e1bff4747e2ac3976b61cb06bcd3d3d6e2cd45cd9edba8169ed7cd979d` |
| Object | `fb0362b6f0943eeffcc675689a5e9ce029e0cdf82d55d0b3fcd432fb8e1e63de` |
| Author receipt | `729d39336b7ccbe744dbd5d49f3f5455460ce30b2a21b175c5cddafd5fcc0336` |
| Actual types / values / axioms log | `28eb5cf58c543025ff672fbd04141377e8e1dd3f3d7899e0d2b566ab2b3d437d` |
| All-owned audit | `4a050b42eb062a15465d1c8d356488bda5930e16967dd05f7c9e8d95ba50eb03` |
| Audit source | `cde68faa36c9ed81346d166df6152e48b834c3ceee1474a9e12c9fd63ff10846` |
| Successful targeted log | `e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b` |

Read-only server checks confirmed the working source and local draft equal this commit's source; the commit adds only this module and its target working tree is clean. All receipt artifact hashes match. Source/object/type-log hashes were checked again at 2026-10-23T07:35:20.692889+00:00. Source has 441 LF and no CR bytes or forbidden proof tokens. The successful targeted receipt records exit 0; its log contains only the inherited accepted mathlib package warning. Lean is pinned to v4.36.0-rc1 and mathlib to `807d3836b165983210ee2ecf3cd28f239436949c`; actual server mathlib HEAD matches.

The audit source selects every constant by actual owning module, exports actual types and any definition values, and uses transitive `Lean.collectAxioms`. The 18 unique names exactly match the audit JSON: 18 theorems, 2 public, 0 definitions. Both independent public prints equal their owned types. All axioms are within `propext`, `Classical.choice`, `Quot.sound`. Full type reading used 38 repeated balanced-subexpression abbreviations: every expansion and residual type was read, and reverse expansion exactly recovered every normalized actual type. Individual type hashes and axiom sets are in the JSON.

The mathematical proof pays gamma>0 through the accepted actual-source gamma theorem, derives h>0 from epsilon/(1+x)<=h, and proves T>=0 directly. It retains the original law cond nu0 {|a|<=epsilon/(1+x)}, original n-normalization, original mean-zero input for nu0, truncation budget, m=n-i, T=m*m2 and gamma=m3/variance. It never assumes a centered conditional law, positive T, L2, kappa>=1, arbitrary D/E, or a supplied oscillatory estimate. Thus m=0 and T=0 remain covered.

For the low outside section, the exact fixed-v domain is |u|<=kappa/gamma and kappa*|u|/gamma<|v|. With b=gamma/kappa>0, the actual weight equals (1+|u|/b)^(-31). A central interval plus both tails gives integrable zeroth/first profiles bounded by 4b and 4b^2. The accepted global producer bounds the actual nested derivatives by C(T+h*gamma) and C(sqrt(T)+gamma+|u|(T+h*gamma)); `measurable_deriv` followed by norm proves their measurability. Domination proves the actual weighted functions IntegrableOn before comparing integrals. C_low=4*C_global is chosen before every source parameter and kappa.

For the high outside section, the exact fixed-v domain is kappa/gamma<=|u| and |u|/(4h)<|v|. Set a=kappa/gamma>0 and d=4h>0. The weight is bounded by d^31*|u|^(-31). The genuine two-sided tails have exact integrals a^(-30)/15 and 2*a^(-29)/29, hence the stated larger bounds. Substituting a^(-1)=gamma/kappa yields precisely (4h)^31 times b^30 and b^29. Both signs, the cutoff equality and every kappa factor remain explicit; C_high=C_global precedes kappa. Empty v=0 sections, low u=0 where admitted, and both endpoint m cases pose no missing branch.

The following table covers every actual owned declaration. `P` abbreviates `_private.Shao.Probability.QuadraticFullNoiseOutsideWeights.0.Shao.Probability`; public names have prefix `Shao.Probability`. Every row is CORRECT, with its full actual type and proof/generated relation reviewed.

| Declaration | Source lines | Verified relation |
|---|---:|---|
| P.abs_tail_rpow | 18–61 | Integrability and exact reflected double-tail rpow integral, a>0,p<-1. |
| P.abs_tail_rpow._simp_1_2 | 34/40 | Union membership equals the disjunction. |
| P.abs_tail_rpow._simp_1_3 | 34/40 | Iic membership equals x<=b. |
| P.abs_tail_rpow._simp_1_4 | 34/40 | Ici membership equals b<=x. |
| P.profile_bounds | 63–74 | Profile nonnegative, <=1, and <=b^31/t^31 for t>0. |
| P.profile_moments | 76–173 | Actual full-line profiles integrable; moments <=4b and 4b^2. |
| P.profile_compare | 175–205 | Measurable nonnegative F comparison and actual IntegrableOn, then integral bound. |
| P.power_tail_moments | 207–222 | Genuine -31/-30 two-sided tails bounded by a^-30/a^-29. |
| P.tail_profile_compare | 224–264 | Actual profile comparison on a measurable subset of positive-cutoff tails. |
| P.tail_profile_compare._simp_1_1 | 248 | Nonzero numeral 2: proposition 2=0 equals False. |
| P.tail_profile_compare._simp_1_2 | 248 | Nonzero numeral 3: proposition 3=0 equals False. |
| P.tail_profile_compare._simp_1_3 | 248 | Nonzero numeral 4: proposition 4=0 equals False. |
| P.tail_profile_compare._simp_1_4 | 248 | NoZeroDivisors and nonzero a,b imply proposition ab=0 equals False. |
| P.tail_profile_compare._simp_1_5 | 248 | Reduced monoid with zero: nonzero base has nonzero natural powers. |
| P.tail_profile_compare._simp_1_6 | 248 | Group with zero: nonzero base has nonzero integer powers. |
| P.tail_profile_compare._simp_1_7 | 248 | Characteristic zero: proposition (n:R)+1=0 equals False. |
| sourceTruncation_odd_even_fullNoise_lowOutside_weighted_integrals | 266–354 | Exact actual-law low outside derivative integrability and b/b^2 bounds. |
| sourceTruncation_odd_even_fullNoise_highOutside_weighted_integrals | 356–439 | Exact actual-law high outside derivative integrability and (4h)^31 b^30/b^29 bounds. |

The direct global producer is reused at accepted source `7256c6f101d86a76f78f713f06c031cba4ec75c7174bb9d73d0fdb629956008c`, commit `06bc9ebf05fef8db62d1e74e16b516c1b1fe9c68`, object `999cf81e1044a178f038875d1902fcc474b93bd2b5c0a17860a0c8a1dfe40dde`, with its unique CORRECT independent review. The exact consumed global declaration and gamma interface were read; accepted older proof internals were not re-reviewed. Necessary accepted dependency sources were rehashed against the v46 binding. The three directly used mathlib source files match pinned Git blobs; the actual derivative-measurability, improper-power-integral and negation-integral interfaces were checked. No whole-package cleanliness claim is made.

This accepts only the two frozen deterministic-envelope u-integrals. The original source low/high outside regions and coefficient powers are faithfully represented. Original y/scale restrictions have not been discharged for any actual marked-v assertion: these theorems have no y because they only concern the chosen deterministic envelopes. Actual marked-v bounds with their original scale payments, composition with the moving domain, integration by parts and boundary terms, the y^-2 factor, Fourier inversion, Region3/5 probability contributions, and C1/C2 remain OPEN. No root theorem or aggregate main integration is certified here.
