# Actual Region 4 derivatives and u tails: independent complete review

STATUS: **CORRECT**

Reviewer `/root/common_region4_review`, gpt-6.1-sol/xhigh, fresh context, reviewed all 472 lines of `Shao/Probability/QuadraticFullNoiseRegionFour.lean`, all 14 actual module-owned declaration types (including every private/generated theorem), and every source-to-statement/proof relationship. The reviewer authored/edited no implementation, spawned no agents, and owns only this report and its JSON companion. Review completed against the read-only server observation at `2026-10-23T06:52:26Z`.

This closes the frozen actual D/W pointwise derivative and fixed-v u-tail obligations. It does not close the Region 4 probability contribution or C1/C2. No finding requires a source change.

## Exact version and reused mechanical evidence

Author commit `b57ea397d8a1d0f60d6c0cc7126080483240a3e8` adds only the reviewed module. Its source blob equals the current source, and the target has no working-tree changes. Server tree: `/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44`; evidence directory: `/root/rivermind-data/shao-lean-20261021/outputs/common-cone-derivatives-v44/`.

| Evidence | SHA256 |
|---|---|
| New source | `9b09880a917b973ea52854fd04906f67cc8a7952e69ab46238a852b79b342ecf` |
| New object | `ea60703c33a6b503f835607153b84311549a8234eea52b8f2aa20f16039a91b5` |
| `drafts/c12-cone-derivatives/region4-author-receipt.json` | `f02ed5fd06e36ed718527984f537b03e041db003dfcf2195cb01ae17311e2791` |
| `region4-targeted-07.log` | `e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b` |
| `region4-owned-audit.json` | `e8be6649520a07ac7083d1a42825d0ef167c4511f2b53f08765554ab281cd8c8` |
| `region4-actual-owned-types-values-and-axioms.log` | `6746c43326b148b7b588f190e88e0357e5f9bacc4bd27414272965ceae22ca30` |
| `Region4OwnedAudit.lean` | `f03d22c4c1eb6ea64f0ca6e3da750e83f571fd7e3db5b14b6f8f33565b1af5c8` |
| `borrowed-object-links-region4.json` | `e14353680cb3151f49d645d5e73557e76806c8b1de5cf6376dbca2218dda7c6a` |
| Declaration freeze | `650840f8d618ad6e1a5ed54b6616c435d395eb73e8852793b728d99c1f69eb06` |
| Complete candidate declarations | `065e63b222ee5295fdb729547778feb2ce4f7c97bfc39d95b38ff63d114cf48e` |
| Complete source contract | `440dbac4f63f32e1e71c51e8b9c7387b096fe0a625424e7da8b3bb16a8b47145` |

The author receipt records targeted exit 0 and actual-owner/transitive-axiom PASS. The targeted log contains only the inherited accepted package-view warning, with no new-source diagnostic. The audit source was read: it selects by actual owning module, visits all constants including private/generated ones, exports `info.type`, exports all definition values when applicable, and uses transitive `Lean.collectAxioms`. The actual 14 unique names exactly match its JSON; all 14 are theorems, with 2 public theorems and 0 definitions. The two separately printed public types equal their corresponding actual owned types. All transitive axioms belong to `propext`, `Classical.choice`, `Quot.sound`. The new source has no `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide` token.

Full actual-type reading used a lossless dictionary of 54 repeated balanced subexpressions. Every dictionary expansion and all 14 residual types were read; reverse expansion reproduced all whitespace-normalized actual types exactly. No mathematical argument, instance, quantifier, or declaration type was elided. Their individual normalized type hashes are in the JSON report. Source/object/type-log hashes were checked again at review end. No Lean, build, or axiom-collection command was rerun by this reviewer.

Pinned versions are `leanprover/lean4:v4.36.0-rc1` and mathlib `807d3836b165983210ee2ecf3cd28f239436949c`. The recorded author execution used CPU10–13, `-M8192 -j4 -DautoImplicit=false`, and the shared `root-heavy.lock`. The frozen module is `LEAN_FULLY_CHECKED` through this exact successful server evidence; that status is limited to this module and its frozen claims.

## Source fidelity and proof checks

The freeze, both complete candidate declarations and source contract were fully read. Both public source signatures match their frozen candidates exactly after whitespace removal. Original supplement 2354–2357, 2593, 3520–3537 and 2642–2645 were read in full, with setup 1973–1983, 2381–2382, 2461–2475, 2568–2589 and 3420–3437. Main 151, 547–551 and 660–679 verify the original normalized law, possibly nonzero conditional mean, and actual characteristic/noise definitions. Both read-only source hashes were checked: supplement `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`; main `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`.

The public inputs retain the original normalized outer probability law, its mean zero, finite second moment and truncation budget; the actual conditional law is `cond ν0 {|a|≤epsilon/(1+x)}`. The new endpoints use actual `m=n-i`, raw second moment `m2`, variance `V`, `gamma=m3/V`, and `T=m*m2`. They add no conditional mean-zero or symmetry assumption. D is precisely `(phi(r,v)^m-phi(-r,v)^m)*Xi(r,v)/2`, E uses the plus sign, and W is `r*E(r)`. No free D/E, derivative conclusion, or oscillatory bound is a public premise.

Lines 19–36 construct the actual finite product probability space and use its coordinate laws/independence to obtain the genuine characteristic-power derivative at every real r. The whole-plane actual Xi derivative interface supplies the other factor. Accepted source data provide probability, support and moments, positive V and gamma, and `gamma≤2*cutoff`; cutoff positivity follows from epsilon>0 and x≥0. Thus the global differentiation assumptions are paid by original data. Also `h≥cutoff>0`, and `T≥L2*gamma²>0`. The accepted full(c) adapter supplies the remaining-length guards, including `m≥20`, without adding them as public hypotheses.

Lines 49–110 use global identities for D', E' and W'. The identities for derivative functions hold everywhere, hence in a full neighborhood of a cone boundary point. The proof does not infer that nearby points remain inside the closed cone. The true formula is `W''=2E'+uE''`; both terms remain in the proof. Internal general p/q calculus is instantiated with the actual signed products, rather than used as an unproved target interface.

Lines 148–231 consume both signs of the accepted full(c) bound. With its universal C, `c1=C*sqrt(T)/(T^6*|u|^12)` and `c2=C*T/(T^6*|u|^12)`. Positive gamma permits multiplication of `kappa/gamma≤|u|`; squaring this and `1≤kappa*sqrt(L2)`, and using `L2*gamma²≤T`, gives `1≤|u|*sqrt(T)`. Therefore `sqrt(T)≤|u|*T`. This pays the full `2c1` term, while `|u|c2` supplies the other term; `3C` bounds D'' and W'' by the exact frozen powers. The constant is chosen before every law and kappa.

Lines 233–276 prove a genuine two-sided Lebesgue improper integral for every a>0 and p<-1. The positive half-line uses the library rpow integral; negation preserves Lebesgue measure and supplies the negative half-line. The closed half-lines are disjoint because a>0, and changing an endpoint singleton does not alter the integral. The exact result is `2*(-a^(p+1)/(p+1))`, together with absolute integrability.

Lines 278–343 split `(1+sqrt(y*|u|))/|u|^k` into powers `-(k:ℝ)` and `1/2-k`, with y≥0 and |u|>0. For k≥3 both exponents are below -1. The resulting positive denominators k-1 and k-3/2 are at least 1; bounding them by 1 is valid. For k=12 these are 11 and 21/2, and for k=11 they are 10 and 19/2. Their cutoff powers become `a^(-(k-1))` and `a^(-(k-3/2))`, not integer-rounded substitutes.

Lines 345–371 prove comparison integrability, not just an inequality between potentially undefined integrals: measurability, nonnegativity and domination first yield `IntegrableOn F A`; monotonicity then enlarges A to the full two tails and evaluates the envelope.

Lines 415–470 instantiate that argument with the actual nested derivative norms. The fixed-v cone section A is closed/measurable, is contained in the full tails at positive `a=kappa/gamma`, and excludes u=0. `measurable_deriv` proves measurability of the actual derivative functions, without assuming it. The norm-weight integrands are nonnegative, and their `IntegrableOn` conclusions are absolute Lebesgue integrability. Both original short-time guards `0<y≤2` and `T<y²` remain explicit. The proof only needs y>0, which is stronger internally and does not alter the frozen statement; source `gamma<y` also follows from positive gamma, L2≥20 and these guards. Substituting `a⁻¹=gamma/kappa=b` yields exactly the frozen odd `b^11+sqrt(y)*b^10*sqrt(b)` and even `b^10+sqrt(y)*b^9*sqrt(b)`. Kappa dependence is never absorbed into a constant that precedes kappa.

## Complete declaration coverage

`P` abbreviates `_private.Shao.Probability.QuadraticFullNoiseRegionFour.0.Shao.Probability`; public names have prefix `Shao.Probability`. `W` means all three whitelisted axioms; `E` means only `propext`; `EQ` means `propext, Quot.sound`. Every row is CORRECT, with its full actual type and source/proof or generated relation reviewed.

| Actual declaration | Source lines / verified content and proof relation | Axioms |
|---|---|---|
| `P.actual_product_first` | 19–36; global actual signed phi-power times actual Xi derivative, all m/σ/v/r, original moment/support inputs paid | W |
| `P.half_add_bound` | 38–43; complex half-sum norm bound from the two norm bounds | W |
| `P.half_sub_bound` | 45–47; half-difference bound by negating the second term | W |
| `P.odd_even_calculus` | 49–110; global first derivative identities, point second differentiability, D'' bound and full `2E'+uE''` bound | W |
| `sourceTruncation_odd_even_fullNoise_highFrequency_derivatives` | 112–231; exact frozen actual-source statement, four differentiability conclusions, two derivative bounds, all original guards and universal constant | W |
| `P.abs_tail_rpow` | 233–276; absolute integrability and exact double-sided rpow integral, a>0, p<-1 | W |
| `P.abs_tail_rpow._simp_1_2` | 249/255; all types/sets: union membership proposition equals the disjunction of memberships | E |
| `P.abs_tail_rpow._simp_1_3` | 249/255; all preorders: `x∈Iic b` proposition equals `x≤b` | E |
| `P.abs_tail_rpow._simp_1_4` | 249/255; all preorders: `x∈Ici b` proposition equals `b≤x` | E |
| `P.tail_envelope` | 278–343; complete nonnegative weighted-power tail integrability and bound, all a>0/y≥0/k≥3 | W |
| `P.tail_envelope._proof_1_1` | 303–305; all Nat k≥3, `¬(1≤k)` implies False; generated Nat.cast_sub obligation | EQ |
| `P.tail_envelope._proof_1_2` | 307–309; all Nat k≥3, `¬(2≤k)` implies False; generated Nat.cast_sub obligation | EQ |
| `P.compare_tail` | 345–371; measurable nonnegative dominated F on measurable tail subset has absolute integrability and the asserted bound | W |
| `sourceTruncation_odd_even_fullNoise_highFrequency_tails` | 373–470; exact frozen actual D/W norm-weight integrals on actual closed fixed-v cone section; original y/T guards and both inverse-kappa power families retained | W |

There are no actual owned definition values to inspect. The generated propositions are elementary set-membership or Nat-order relations used at the indicated proof steps; they add no target assumption.

## Accepted dependencies and boundary

Full(c) source/object remain exactly `086b822ad26233d97955ac2264e388379593a5821c95c8b4a8218bea3eee66e2` / `c5aa9254f1ac89eb6bf3c72877dc6c9b879566d6983725a15ef4803e75021929`, author `46c5b42c97b0ebc88e8e78705a627fa1c900ec6c`. Its sole qualified complete review is CORRECT (`common-fullc-review.md/json`) and root scope acceptance was read. Only interfaces/interactions were checked here; its internal proofs and unchanged accepted K/Xi/power/source producers were not re-reviewed. The power source `026a4057…` acceptance and v45/v41 bindings are inherited through that accepted dependency.

The separately consumed older `QuadraticCharacteristicPower` source is `5a51275c796d3bd0cc59b496a15b21e1c6bd5afd101b72f66a4c5e83511164c8`, matching v41. Both borrowed objects and actual links match the region4 manifest. SourceTruncationBridge, SourceFourierScale and global Xi derivative source hashes match their accepted bindings. The three newly used library sources (measurable derivatives, improper integrals, Lebesgue reflection) equal their pinned mathlib Git blobs despite the inherited package-view warning; no whole-package cleanliness is asserted.

Still open: the actual marksine v-integral with its actual amplitude; the complete double Fourier integral; the y^-2 integration-by-parts identity and its boundary terms; inversion; the Region 4 odd/even probability-kernel contribution; shortregions; the smoothed comparison/desmoothing chain; C1/C2 and the other open root groups. This report does not certify aggregate/main acceptance of this newly added module. Reuse this review and successful server evidence for these exact hashes; additional full proof review is needed only for an affected mathematical change, uncovered scope, evidence gap, or material integration risk.
