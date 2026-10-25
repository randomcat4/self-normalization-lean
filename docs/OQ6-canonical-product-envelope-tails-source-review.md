# Unit191 independent complete source review

STATUS: CORRECT — SOURCE PHASE ONLY

Qualification: **false**. No Lean command, server command, network operation, Git/API action, upload, cache action, or source edit was performed by this reviewer. The exact new-source kernel receipt, original object, module-index ownership inventory, every owned full TYPE, every owned non-theorem FULLVALUE, and recursive axiom evidence have not yet been supplied to this reviewer. This is the source phase of the same final review, not a second review or a claim of machine acceptance.

Reviewer: `/root/oq56_tails191_final_review`, fresh prescribed `gpt-6.1-sol` / `xhigh`. Author: `/root/oq56_tails191_stage1`; author/reviewer separation retained. Actual token usage is unavailable: input, cached input, output, and reasoning-subset fields are null. The runtime ACK records observed local execution and exact inputs. Exclusive writes are confined to this review directory. No subagents were created.

## Exact bytes and independent comparison

The complete 885-line source was read, including every proof, header, local initializer, and end command:

- `drafts/oq56/unit191/author-01/stage2/CanonicalProductEnvelopeTails.lean`: SHA256 `a0a7bedab29133ca664a556e6137f239b7f8e88cdbc6f290ecc9434d31925f59`; 39,793 bytes; 885 LF; zero CR; UTF-8; no BOM.
- Parent freeze: `1d22e604cf92beafaf5de491b08d83d74ee70e1048161507d891b8f5d517b5fc`.
- Author stage2 manifest: `11aabb5617bb612b3a95d8cd7fd8ce187b42ffd81b1de1c6469c2cc265798db7`.
- Author stage2 RELEASE: `6ec73679a3d0fc49f7cf11bd968925063ac56a3f0b2e35e861c2f9b6b4bd1ace`, with zero writers/executions/inflight and no uncertain writes.
- Authoritative corrected ordered plan: `6ed87224644b940c8eefa8b82a59f64a3b890ff77c65733b6836df42c7bafe23`.
- Capture erratum: `170b0e7c9d432b3c22a2635938ce269a726d7816d13febdcfc436fc45b470f78`.

The independently executed read-only `review_static.py` derives 25 source heads, 7 definitions and 18 theorems from the source, rather than copying a descriptive count. All 25 complete header strings and all 7 definition RHS values equal the freeze exactly. Every source `let` / `letI` is enumerated independently: 44 steps, comprising 32 non-instance lets (31 non-Prop values and explicit Prop `hw`) and 12 instance occurrences. Each type, RHS, order, declaration parameter scope, earlier-local scope and exact capture binding matches the authoritative plan. No new substantive local data appears. The source contains none of `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide`.

I independently compared the original ordered plan with the corrected plan. Exactly three JSON leaves differ, all in declaration index15 / local step4 / capture `hw`: its source changes from a declaration parameter to the earlier local; its type changes from the accidentally matched header `hW` nonnegativity proposition to `AEStronglyMeasurable w ν`; its value changes from `parameter` to the actual earlier proof initializer. No header, assumption, declaration/global RHS, local RHS, order, or other capture changes. The Lean source at lines322–323 uses the correct earlier `hw` case-sensitively.

`static-evidence.json` preserves every source-derived row and hash check. Those deterministic checks support the mathematical review; they are not Lean elaboration or an ownership inventory.

## Source-to-statement scope independently derived

The actual source read was `C:/game/shao/current/oq56/inputs02/p44.md`, with the relevant p51 S18 and p54 repairs read for the consumer boundary. Source p44 defines

\[
F_n=\sum_{i<j}r(O_i,O_j),\qquad
\psi_i=\sum_{j\ne i}r(O_i,O_j),\qquad
\Lambda_n=\|\psi\|_2.
\]

The producer actual FULLVALUEs identify `originalUpper`, `originalRows`, `sampleLaw`, and `pairedEnergy` with these unmodified statistics and their actual finite product laws. Unit191 establishes the p44 **(7) moment bounds and (8) strict tail bounds** from the already qualified p44 (4)/(5)/(6) producer interfaces. A dispatch description mentioned “p44(5)/(9)”; the actual original tags (5) and (9) are respectively the preceding scalar ghost moment bound and the separate bounded-envelope variant. Unit191 does not prove the bounded-envelope (9) branch. This is a scope-label correction in this review, not a change to any mathematical statement or source byte. The frozen unit191 scope itself correctly says (7)–(8).

For arbitrary measurable Ω and an actual probability measure ν, the public source assumes `0 < α ≤ 2`, `τ > 0`, `M ≥ 1`, ν-AE nonnegative w, actual integrability of `exp(τ*w^α)` and its actual integral ≤ M. The kernel assumptions are product measurability and L1, both marginal canonical identities ν-AE, and the product-AE envelope `|r(a,b)| ≤ w(a)w(b)`. Scalar results additionally retain explicit pointwise symmetry of r; the standalone row results do not require it. There is no added topology on Ω, no `Measurable w` premise, no pointwise canonical premise, no diagonal-zero premise, no assumption that observed values are distinct, and no independence assumption involving any projection g and w.

The measurable version `v = hw.mk w` is proof-local. Its AE equality to w is transferred under every actual paired sample coordinate before returning the energy L1/integral statement to the original `pairedEnergy n w`. Public F and row events are always the original `originalUpper` and `originalRows` under `sampleLaw n ν`. No representative or proxy replaces those events.

Writing `C = envelopeMomentScale α τ M` and `s=2/α`, the exact outputs are

\[
\|F_n\|_q\le 8Cq(n+q^s),\qquad
\|\Lambda_n\|_q\le 2C\sqrt q(n+q^s),
\]

with actual power integrability. For the combined q/2q statement, the common constant is

\[
C_7=\max(8C,\;2\sqrt2\,2^{2/\alpha}C).
\]

For `q ≥ 2` and `2*q ≤ n^(α/2)`, the strict original tails use

\[
C_F=16eC,\quad C_L=32e^2C^2,\quad C_T=\max(C_F,C_L),
\]

and satisfy `P(C_T*n*q < |F_n|) ≤ exp(-q)`, `P(C_T*n^2*q < Λ_n^2) ≤ exp(-2q)`, and the sum ≤ `2*exp(-q)`. The α=2/3 corollary has exactly `q ≤ n^(1/3)/2`. This supplies the perturbation concentration input described in p51 S18; it does not prove the entire DC theorem, its Shao–Zhou base-kernel concentration input, Studentizer comparison, or the source random-interval theorem. p54 conditional-p-moment and atomic-threshold repairs remain in force. No new priority claim is made; Shao–Zhou attribution is retained. C2/C12/OQ56 remain OPEN, OQ3 remains user-paused, and the 124 mechanism is not made a prerequisite.

## Declaration-by-declaration complete proof review

Line numbers refer to the exact bound source. Every item has its complete frozen header checked; the following records the independent mathematical justification, including private heads.

| Head | Source lines | Independent assessment |
|---|---:|---|
| `rootRecovery` (private def) | 20–24 | Exactly `t ↦ Real.rpow t (1/α)`, total on ℝ. No hidden domain restriction is encoded in the definition. Recovery is invoked only on nonnegative w. |
| `pairSquare` (private def) | 26–31 | Exactly `(v p.1 + v p.2)^2`; nonnegative pointwise regardless of the chosen version's values on null sets. |
| `envelopeMomentScale` | 33–38 | Exactly `sumMomentScale (α/2) (τ/2^α) (M^2)`. These are the actual paired seed parameters, not free concentration inputs. |
| `commonMomentScale` | 40–45 | Exactly the maximum of `8*C` and `2*sqrt2*2^(2/α)*C`, sufficient respectively for the q scalar and 2q row bounds. |
| `scalarTailScale` | 47–52 | Exactly `16*exp1*C`; e times the scalar Lq bound after the tail-window reduction. |
| `rowTailScale` | 54–59 | Exactly `32*(exp1)^2*C^2`; the square of `4*exp1*sqrt(2q)*C*n` after factoring out `n^2*q`. |
| `tailScale` | 61–66 | Exactly the maximum of the preceding two thresholds. Event enlargement has the correct direction when replacing each scale by this larger common scale. |
| `continuous_rootRecovery` (private) | 68–73 | `1/α ≥ 0` follows from α>0. The pinned `Real.continuous_rpow_const` therefore gives continuity on all ℝ; conversion between `Real.rpow` and real power notation is exact. No topology on Ω occurs. |
| `rootRecovery_rpow` (private) | 75–82 | Applies `Real.rpow_rpow_inv` with a≥0 and α≠0. Both hypotheses are explicit, including at a=0. The `one_div` rewrite has the correct exponent. |
| `aestronglyMeasurable_of_exp_moment` (private) | 84–105 | Integrability of the exponential gives its AE measurability. The nonzero τ API recovers AE measurability of `w^α`; standard real codomain structures give AE strong measurability. Composing with the continuous root and using w≥0 ν-AE recovers w ν-AE. The congruence orientation is rootedEnvelope=w, as required. No global measurability or nonnegativity of w is assumed. |
| `sum_rpow_le_product_seed_scale` (private) | 107–133 | Splits a≤b or b≤a, bounds a+b by twice the larger, uses monotonicity for α>0 and nonnegative bases, expands `(2*a)^α` or `(2*b)^α`, and adds the nonnegative missing term. This deliberately loose `2^α` bound is valid for the full α>0 range. |
| `pair_exponential_domination` (private) | 135–166 | For a,b≥0, `((a+b)^2)^(α/2)=(a+b)^α` by real-power multiplication. Multiply the preceding inequality by positive `τ/2^α`, cancel the strictly positive denominator, apply monotonic exp, and factor exp of a sum. No illegitimate real-power law on a negative base is used. |
| `paired_seed_exponential_moment` (private) | 168–229 | The paired seed is measurable from measurable v. E's product is L1 by `Integrable.mul_prod`. Both projection maps preserve the actual product probability, pulling ν-AE nonnegativity to the pair. The exponential domination supplies norm domination because G>0. Actual integral monotonicity and `integral_prod_mul` yield `(∫E)^2`; `0≤∫E≤M` and M≥1 give ≤M². This proves the seed premise, rather than assuming the desired moment/tail conclusion. |
| `paired_energy_representative_ae` (private) | 231–267 | Product projections composed with each finite Pi evaluation preserve the indicated measures. Pull w=v back to both members of every paired coordinate and take the finite conjunction. Expanding actual `pairedEnergy`, `weightEnergy`, `ghostWeight`, `coordinateSum`, and `pairSquare` makes the two finite sums equal. No null set depending on an uncountable index is intersected. |
| `envelope_scales_pos` | 269–296 | M≥1 gives M>0; all paired scale factors in actual `sumMomentScale` / `scalarMomentScale` are positive for α,τ>0. The common and tail maxima have positive lower terms. The positivity of the squared row scale follows from C>0. No extra positivity premise is appended to public tails. |
| `paired_energy_real_moment_from_exp` | 298–396 | Constructs the actual measurable v using the recovered `hw`; transports nonnegativity, exponential L1 and its integral bound by w=v ν-AE. β=α/2 lies in (0,1], τPair>0, MPair=M²≥1. Constant coordinate laws are ν.prodν and coordinate seeds are `pairSquare v`, measurable and pointwise nonnegative. Instantiating actual183 at p≥1 gives the coordinate-sum L1 and root moment. The independently proved paired AE equality transfers both back to the original energy. The exponent identity `1/(α/2)=2/α` uses α≠0. No division by n or energy occurs. |
| `canonical_row_product_envelope_moment` | 398–437 | Uses the energy result at p=q≥2, then exactly the actual188 `canonical_row_qmoment_bound` with the same r,w,ν and exponent. Multiplication by `2*sqrt q≥0` preserves the bound. All canonical/product-AE assumptions align; symmetry is absent. |
| `canonical_scalar_product_envelope_moment` | 439–479 | Uses the energy result at q and the actual qualified190 scalar theorem, including hsym in the actual producer argument order. Multiplies by `8*q≥0` and rearranges. The factor is 8q, not a guessed constant or a normalized F. |
| `canonical_product_envelope_moments` | 481–568 | Calls scalar at q and row at 2q. Since s=2/α≥0, `2^s≥1`; product real-power law holds with q≥0, so `n+(2q)^s ≤ 2^s(n+q^s)`. The nonnegative square-root identity is derived by squaring. The two maximum coefficients then bound the scalar and row expressions. Both integrability statements are retained. α≤2 is used upstream for the energy theorem; no stronger α restriction is introduced. |
| `strict_moment_markov` (private) | 570–623 | From nonnegative X, actual L1 of X^p, p>0 and positive K, infer `I=∫X^p≥0` and raise the root-moment inequality to p to obtain I≤K^p, using the inverse law even when I=0. With ε=(eK)^p>0, the strict X event is contained in the closed power event. Actual Markov gives ε times the latter measure ≤I. Finite μ makes `measureReal_mono` valid. Finally ε*exp(-p)=K^p; positive cancellation yields the strict-event bound. X itself need not be globally measurable, and no boundary atom hypothesis is used. |
| `tail_window_power_bounds` (private) | 625–655 | At n=0, positive α makes n^(α/2)=0, contradicting q≥2 and the window; hence n>0. Raising `2q≤n^(α/2)` to `2/α>0` is order preserving, and real-power multiplication on n≥0 cancels the exponent. Since 0≤q≤2q, q^(2/α)≤(2q)^(2/α)≤n. |
| `canonical_scalar_product_envelope_tail` | 657–709 | Instantiates actual sample probability/finite instances. Window bounds give n>0, q>0 and hence KScalar=16*C*n*q>0. The scalar moment is ≤8*C*q*(n+n)=KScalar. Apply strict Markov to absolute actual F at p=q. Commutative rearrangement identifies e*KScalar with scalarTailScale*n*q. |
| `canonical_row_product_envelope_tail` | 711–781 | Uses the row moment at 2q and the (2q)^s≤n window bound. KRow=4*sqrt(2q)*C*n is strictly positive. Strict Markov gives the actual norm tail with exp(-2q). Squaring e*KRow gives rowTailScale*n²*q exactly. Nonnegativity of the norm and threshold proves the strict squared-event inclusion; there is no squaring across a negative threshold. |
| `canonical_product_envelope_tails` | 783–846 | Positive q and n≥0 allow multiplying the two scale-to-maximum inequalities. Larger thresholds give subsets of the respective already proved strict events. Finite measure monotonicity yields both bounds. Since q≥0, exp(-2q)≤exp(-q); adding bounds gives ≤2exp(-q). This is a sum of actual tail probabilities, not a claim of event independence. |
| `canonical_product_envelope_two_thirds_tails` | 848–882 | Numeric α=2/3 satisfies both α hypotheses. The exact arithmetic identity `(2/3)/2=1/3` and the supplied half-window imply `2q≤n^(α/2)`. It calls the general theorem with identical original laws, kernels, envelope and exponential moments. No asymptotic, integer-q or larger-window substitution is made. |

## Named local data, instances, and captured environment

All 44 source let/letI rows, not just their names, are preserved in `static-evidence.json`. Their complete types/RHS values were read in the source and compared with the frozen typed scopes. The following group review states the substantive role of every named non-instance row:

- Lines96–97: `powerEnvelope : Ω→ℝ = fun a => w(a)^α` and `rootedEnvelope : Ω→ℝ = fun a => rootRecovery α (w(a)^α)` capture only their stated Ω,w,α. They are total functions, with recovery justified only on the AE nonnegative set.
- Lines187–192: `E : Ω→ℝ`, `Y : Ω×Ω→ℝ`, `G : Ω×Ω→ℝ`, `B : Ω×Ω→ℝ`, `firstProjection`, and `secondProjection` have exactly the recorded actual exponential, squared pair, product and projection values. G sees the earlier Y; B sees the earlier E. No future local or unrelated declaration is in scope.
- Lines243–245: `pairEval`, `firstEval`, `secondEval` have full types `Fin n → (Fin n→Ω×Ω) → (...)` and return the actual selected coordinate or its first/second component. Fin n's finite instance is the canonical one. Coordinate maps are not independently sampled data.
- Lines322–329: explicit Prop `hw`, then `v`, `β`, `τPair`, `MPair`, `μPair`, and `YPair` are initialized in that order (with the intervening coordinate probability instance). v uses the earlier `hw` with type `AEStronglyMeasurable w ν`, not header hW. μPair captures ν; YPair captures v. Their types and RHSs are exactly those used in the actual183 specialization.
- Line511: `s : ℝ = 2/α`, using the same α as the public assumptions and scale.
- Lines584–588: `powerX`, `momentIntegral`, `epsilon`, `strictEvent`, `closedPowerEvent` are actual functions/integral/sets from the private Markov header. `closedPowerEvent` sees the already defined epsilon. No tail-probability bound or desired moment is smuggled in as data.
- Lines687–689 and740–742: the two `C : ℝ` locals are independently scoped copies of the same envelope scale; `scalarAbs` and `rowNorm` are the actual original statistic's absolute value/norm; `KScalar` and `KRow` have precisely the positive moment thresholds justified in the respective proofs. Neither context captures data from its sibling theorem.
- Lines815–816: `FEvent` and `LEvent` are the original strict events at the common scale. Their type is `Set (Fin n→Ω)` and they capture precisely n,Ω,α,τ,M,q,r; there is no hidden good event, normalization, proxy statistic or independence premise.

The five frozen instance templates have 12 actual occurrences: paired probability at lines186,241,320; paired Pi probability at242,321; coordinate probability at328; sample probability at685,738,813; sample finiteness at686,739,814. All are inferred from actual header probability hν and the already visible local instances. `inferInstanceAs` initializers do not see themselves or later instances; the coordinate instance has μPair already in scope. Probability implies finiteness/SFinite where the raw primary theorem needs it. No instance is a newly assumed mathematical hypothesis. The complete per-occurrence header parameter and before-scope lists match the authoritative plan.

Every ordinary Prop `have` proof and branch in the 18 proofs was read, including all inequalities later passed to `linarith`, `nlinarith`, `positivity`, `ring`, `field_simp`, `fun_prop`, and finite/AE filters. Their ordinary Prop status does not exempt their mathematical reasoning from this review. The explicit Prop `hw` that supports choice data is separately frozen and checked.

## All 16 frozen anonymous-function families

The bound anonymous templates describe elaborated integral/set notation as well as literal lambda expressions. A plain substring checker intentionally does not treat notation or upstream theorem specialization as textual lambda equality. The ten nonliteral cases are checked semantically below; they are not ten missing source declarations.

| Template | Complete type and capture review | Source realization |
|---|---|---|
| `exp-w` | Ω→ℝ; Ω,τ,w,α | Literal function in hExp/hExpBound; no r or g capture. |
| `exp-w-two-thirds` | Ω→ℝ; Ω,τ,w | Literal function at lines868–869; fixed exponent 2/3. |
| `right-canonical-section` | Ω→Ω→ℝ with binder order a,b; Ω,r | The outer AE binder a followed by `∫ b, r a b`; exactly the right marginal canonical identity, not pointwise canonicality. |
| `left-canonical-section` | Ω→Ω→ℝ with binder order b,a; Ω,r | The outer AE binder b followed by `∫ a, r a b`; variables are not interchanged inside r. |
| `energy-power` | (Fin n→Ω×Ω)→ℝ; n,Ω,w,p | Literal original-energy power at lines317–318. |
| `row-power` | (Fin n→Ω)→ℝ; n,Ω,r,q | Literal originalRows norm power at lines423–424. |
| `row-twice-power` | (Fin n→Ω)→ℝ; n,Ω,r,q | Literal `(2*q)` power in combined moment at508–510 and row-tail moment under rowNorm at752–757. |
| `scalar-power` | (Fin n→Ω)→ℝ; n,Ω,r,q | Literal originalUpper absolute power at465–466,507–509. |
| `scalar-strict-predicate` | (Fin n→Ω)→Prop; n,Ω,α,τ,M,q,r | Set-builder at684; scalarTailScale*n*q < actual |F|. |
| `row-strict-predicate` | Same predicate type/captures | Set-builder at737; rowTailScale*n²*q < actual row norm². |
| `common-scalar-event` | Same predicate type/captures | Set-builders at810,812,815; tailScale*n*q < actual |F|. |
| `common-row-event` | Same predicate type/captures | Set-builders at811–812,816; tailScale*n²*q < actual row norm². |
| `special-scalar-event` | Same predicate type; n,Ω,τ,M,q,r | Set-builder at872,874; α fixed to2/3. |
| `special-row-event` | Same predicate type; n,Ω,τ,M,q,r | Set-builder at873–874; α fixed to2/3. |
| `energy-power-at-q` | (Fin n→Ω×Ω)→ℝ; n,Ω,w,q | Actual energy producer specialized at q in425–427 and467–470; integrals at431 and474 are notation for the same lambda. Tail theorem consumes the resulting scalar moment. |
| `energy-power-at-twice-q` | Same type; n,Ω,w,q | Exact nested row-moment specialization at2q in518–519 and748–749; its energy input is the same paired energy at2q, not energy^q or a second independent draw. |

Anonymous expression binders are scoped to their own expression. Their complete parent parameter environments are exactly the compared frozen heads. No anonymous initialization gains access to a later local, sibling theorem local or global Ω topology. The ordinary lambdas inside Prop proof steps and the named data RHSs were also fully read; the 16-family count is not an inferred count of actual generated constants.

## Primary APIs and accepted producer interfaces

I read all 50 complete primary API declarations used by the frozen binding packet and their chronological scope events. The independent union, retaining per-source identity, has 215 raw scope events in 14 source files. All bound packets have matching hashes; each selected complete raw declaration occurs in its bound source packet. These are actual pinned sources, not guessed modern signatures. Lean pin is `leanprover/lean4:v4.36.0-rc1`; mathlib pin is `807d3836b165983210ee2ecf3cd28f239436949c`. No toolchain probing or Lean execution was performed locally.

The raw scope review preserves section/namespace entry and exit, explicit/implicit variable mode, and one-command `open ... in`, `omit ... in`, and `include` commands. In particular:

- AE strong measurability has distinct possible m and m₀; this source uses both as mΩ. The topological/Borel/pseudometrizable/second-countable requirements are on ℝ, not on Ω. The named mk/measurable_mk/ae_eq_mk APIs have exactly the used argument order.
- Pi evaluation is on actual `Measure.pi`; the actual primary `omit [∀ i, SigmaFinite (μ i)] in` belongs to its following command rather than permanently deleting a requirement from the file. In any event the supplied coordinate probabilities discharge required finiteness.
- Product fst/snd preserve the indicated marginal when the other factor is probability. SFinite declarations and local one-command omissions are not flattened into a fictitious ambient type. Here both marginals are the same actual probability ν.
- Integral product/multiplication is for real L1 factors. Actual real-power `Pow ℝ ℝ` is the instance wrapping `Real.rpow`; the actual definition and `rpow_eq_pow` were read. Nonnegative-base hypotheses are paid before every multiplication/inversion/monotonicity step.
- The actual Markov head requires AE nonnegative f, actual Integrable f, and real ε, and proves ε*μ.real{ε≤f}≤∫f. It requires neither the desired tail premise nor nonatomicity. `measureReal_mono` has a finiteness side condition; the private helper's explicit finite measure instance and the public sample probability make it available.
- The actual sqrt source is in namespace Real after ending NNReal. Its variables x,y are real, and `sqrt_eq_iff_mul_self_eq` requires nonnegativity on both sides, which is explicitly supplied. There is no guessed sqrt multiplication interface.

I fully read the actual selected producer TYPEs and every selected non-theorem FULLVALUE: 11 TYPEs and 9 VALUEs from183/188/187/186, plus2 TYPEs and1 VALUE from qualified190. The script compares each to the identically named unique entry in the exact producer metadata, rather than finding a type text elsewhere or using a namespace-prefix approximation. All13 names/types and all10 non-theorem values match, and the selected recursive axiom lists use only propext/Classical.choice/Quot.sound.

Key source/object bindings reused exactly:

| Producer | Source SHA256 | Original object SHA256 |
|---|---|---|
| 183 real sum moments | `9ffdbe105b2cbdc5552acdc11d8942dd08372e8d55574bd65dcad8c186344470` | `65cf3bd6489e09be794ffa6b8686b0ab15df5cf56d27baf192691dfff0b7d6d3` |
| 188 actual row moments | `0b7f38c8840ffefb15fc9185c8f54c2c6907da96cc49bd5e7ee3c5ed512250fc` | `039bdc5ca03a7505762d852b8e6464c7f88de90c5b68914e6aaf6e6cb3a50d85` |
| 190 actual scalar moments | `17790c480efcab2d11cb5d00ccd215a6853e289fb078b5b041ae3bba972ab68c` | `0df8c568f2c6cba15ebd8877afa7e6d7a58110567c7786ffa787cb5769780a95` |

Accepted independent producer proof qualification is reused by exact hash:183 parent `a1d033ddcc9da864d965d77e7e2555f9c74d6f12c64b24fad90f43130e265427` / independent `e81c3d47330b8fd69661c43170dffe1e00c26c377a0f477eb81c1fc0f583f8e3`;188 parent `31b7d87357171a72ba7854bc32a0ad662ed8f0d2e39180e7c349ac195b25af02` / independent `7ba2e14da10e199831e5a7794a66e4df11fdd33dff2ac36388aea0e51d17f1d1`;190 parent `871c74c9d0c68a04901aa1852c94c0bf229abbc2d6100fa6d4c8c745eb66fb00` / independent `c069ae9b0d759690c43767ca395ea196fc3b5bdf56f9efab6b199aa67ea0ddf4`. No accepted old producer proof was re-reviewed or recompiled. The historical pending190 field in the old stage1 explanation is superseded only by the exact parent-qualified190 binding `46f6d58d0be394d0f93e78ed6d9772639427e366f71f3377056ec1bc8788b317`; it is not a remaining mathematical premise.

Actual183 accepts β∈(0,1], τPair>0, MPair≥1, n, the real coordinate probability family, measurable nonnegative-AE YPair, seed exponential L1/bound, and p≥1. Unit191 proves every premise with those exact substitutions. Actual188 gives `2*sqrt(q)*||pairedEnergy||q` with no symmetry requirement; actual190 gives `8*q*||pairedEnergy||q` with explicit hsym. Their probability laws, unnormalized F/row values and paired energies match the unit191 heads. Actual full values of sampleLaw, pairedLaw, pairedEnergy, ghostWeight, weightEnergy, coordinateSum and originalUpper/originalRows prevent a normalization or event mismatch.

## Boundary and adversarial checks

- **w=0, zero energy, zero statistics:** Recovery at0 and powers with p≥1 are valid; no division by energy occurs. All scales remain positive under frozen α,τ,M assumptions, so strict tails of zero statistics are empty.
- **n=0:** The actual finite sums are empty; original moments are zero, and the tail window is impossible. The energy moment proof does not divide by n.
- **n=1:** F has no upper-triangular pair, and each row omits its same-index term; original F/row moments are zero. The paired energy need not be zero, which is harmless as an upper bound. The tail window contradicts 2q≥4 and 1^(α/2)=1.
- **Atoms and repeated observations:** Distinct indices may have equal observed values. The definitions omit the index diagonal, not the event of equal values. Product-AE assumptions are consumed via the qualified actual sample-law producers; no value-diagonal zero or distinctness assumption is introduced.
- **Null-set changes in w:** Only the measurable seed uses v. Coordinate pullback covers both entries of all finite pairs, and the original w energy is restored by actual AE congruence before consumption by188/190.
- **Strict boundary atoms:** The Markov argument uses an event inclusion into a closed powered event and a strictly positive threshold. It never changes strict probability to closed probability by an equality or assumes zero mass at the threshold.
- **Endpoints:** α=2 gives β=1 and is allowed; α=2/3 specializes exactly. Constants can depend on α,τ,M; there is no uniform α→0 claim. Frozen τ>0 and M≥1 exclude τ=0/M=0; no such case is silently admitted or used as a division exception.
- **Real exponents:** p and q are real, not silently restricted to integers. Only inherited actual183 handles the real sum moment, and this source instantiates it at p, q or2q within its exact range.
- **Correlation and root scope:** No projection g is introduced. This tool can therefore be used where g and w come from the same observation, but does not prove the rest of the DC argument or close a root group.

No precise mathematical gap, source/freeze deviation, added premise, circular tail input, or event mismatch was found in this exact source. The remaining qualification work is strictly the new module's exact native/original-object evidence and complete actual ownership/type/non-theorem-value/recursive-axiom review. The same independent reviewer should perform that evidence phase on the exact bytes, preserving this source report and all failed/interrupted server receipts.
