# Full high-frequency (c): independent complete review

STATUS: **CORRECT**

Reviewed only the new `Shao/Probability/QuadraticFullNoiseHighFrequency.lean`, author commit `46c5b42c97b0ebc88e8e78705a627fa1c900ec6c`, all 518 source lines, all 29 actual owned declaration types, the unique definition value, and their full source-to-statement/proof relationships. Reviewer `/root/common_fullc_review`, gpt-6.1-sol/xhigh, fresh context, did not author or edit implementation and spawned no agents. Existing qualified reviews and exact server receipts were reused; no Lean command or axiom collection was repeated.

## Exact evidence

| Item | SHA256 |
|---|---|
| New source | `086b822ad26233d97955ac2264e388379593a5821c95c8b4a8218bea3eee66e2` |
| New object | `c5aa9254f1ac89eb6bf3c72877dc6c9b879566d6983725a15ef4803e75021929` |
| Author receipt, `drafts/c12-cone-derivatives/highfreq-author-receipt.json` | `ba4c1e6e9341c7584807a791d0f44a47ff34f5668090672a939989e771281f16` |
| Actual owned types/value/axioms log | `61fdd673c31fd8cf79c5e218115e88ae8309511544907f25dff119da3247f8a6` |
| Owned audit JSON | `e7bf8e3bedebbc677f84c8f3a4468b10d837f6afb669906e617103ff80eb85d8` |
| Audit source | `16d041edd9d4d40c9ad6169458e672b6b28fde256fe5b6c0b741220710b08d97` |
| Successful targeted-06 log | `e737184c2f87adf2667327bab4abebab172f4f20d49ec8e12bd6dc6246ad139b` |
| Borrowed-object manifest | `39e29d290c9645cb7720d13353b825a50904f71c4a5710f6f0a73af8bd75b12a` |

Remote workspace is `/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44`; evidence is in `/root/rivermind-data/shao-lean-20261021/outputs/common-cone-derivatives-v44/`. Read-only server hashing confirmed source and object bytes, all evidence hashes, HEAD, and the source blob at the exact author commit. The author receipt records targeted exit 0 and all-owned transitive-axiom PASS. Its targeted log contains only the inherited package-view warning, with no new-source diagnostic. Lean is `leanprover/lean4:v4.36.0-rc1`, mathlib `807d3836b165983210ee2ecf3cd28f239436949c`.

The audit source selects every constant by its actual owning module, including private/generated declarations, prints `info.type`, prints every `.defnInfo` value, and calls transitive `Lean.collectAxioms` on each. Its 29 unique names equal the JSON's 29-name set; counts are 28 theorems + 1 definition, including 2 public theorems. Both separately printed public types equal their owned-type exports. All transitive axioms are among `propext`, `Classical.choice`, `Quot.sound`; the source has no banned token. Full type reading used exact repeated-subterm abbreviations, including the complete expansion dictionary; a deterministic expansion roundtrip reproduced the whitespace-normalized complete log. No declaration type or definition value was elided.

Freeze/candidate/contract were fully read and hashes match: freeze `00cee040a673ea6f4bbd18b6241acf60ffbda0c96ff9c476acee07b8a6b5fd00`, candidate `b2d3700f5262344f4b6458433a1d97883446129b27524c6097ff429edda30df3`, contract `c5d798f69b8d21c53a2638ae564dd7c053f8bf55c63a13df2eb9a60985b5d6cd`. Both public signatures exactly preserve the frozen objects, quantifier order, guards, and conclusions.

## Source fidelity and proof

Fully read original supplement 2595–2617 and 3358–3401, relevant setup 2381–2382/2461–2475, main 151/547–551/695–712, and the accepted interfaces actually consumed. Original files are read-only `C:/game/shao/current/c12/main.tex` SHA `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` and `supplement.tex` SHA `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`.

The function in both public endpoints is the actual uncentered `quadraticChar ν (σ*r) v ^ m * quadraticFullNoiseChar ν r v`. The first factor is the integral of `exp(i*(u*a+v*a²))`; the second is the characteristic integral of the actual full-noise law with two eight-chord families and scalar noise scaled by the actual `gamma=m3/V`. It is not a free multiplier. Centering changes only the linear phase and leaves `v*a²` intact. `|σ|=1` covers both signs; `|v|≤|u|/(4h)` includes the cone boundary.

Lines 20–85 prove the ordinary first/nested-second product formulas and weighted norm bounds. The first derivatives of both factors are available globally in `r`, so the derivative-function identity holds in a full neighborhood even on the closed cone boundary. In the application (266–269), the centered-power interface supplies global differentiability; the accepted whole-plane Xi derivative interface supplies the noise differentiability after the new `gamma_payment` has derived its required moment condition. No claim that nearby points stay in the cone is used.

Lines 137–175 derive finite second moment and `gamma≤2h`: the numerical mean guard gives `m*μ²≤16V`, hence `μ²≤V` for `m≥16`; therefore `m2=V+μ²≤2V`, while bounded support gives `m3≤h*m2`. This is an internal proof, not an extra premise or a disguised derivative bound.

Lines 177–215 use the signed cone gap and the other K-family's bound by one to prove
`R=K(u,v)^6*K(-u,v)^6 ≤ 4^6*g^6/(V^6*|u|^12)`.
The retained weight and the gap may be zero: neither is divided out. Lines 265–307 multiply the accepted signed centered-power bounds by this weight and combine them with the actual retained Xi derivative bounds. With `D=4^6*P/(S^6*|u|^12)`, `S=mV`, this gives centered-product bounds `D`, `D*(1+2A)*sqrt(S)`, and `D*(1+4A+4B)*S`. The explicit frequency guard pays `1/|u|≤2sqrt(S)` and its square.

Lines 87–134 and 318–365 restore the actual mean phase `exp(i*m*σ*μ*r)` globally. Its norm is 1, first-derivative norm is `|mσμ|≤4sqrt(S)`, and second-derivative norm is `(mσμ)²≤16S`. The full second product rule gives precisely the coefficient `25+20A+4B`; `C=4^6*P*(25+20A+4B)>0` is chosen before every law, support, integer, and frequency parameter. Both standard differentiability conclusions are proved. The law is neither assumed centered nor symmetric.

Lines 379–516 instantiate the original fixed-cutoff conditional law `ρ=cond ν0 {|a|≤epsilon/(1+x)}`, with `m=n-i`, the actual raw `m2`, actual positive variance `V`, actual `gamma=m3/V`, and `T=m*m2`. Only the outer normalized law has the source's mean-zero assumption. Accepted source interfaces pay probability, support, moments, `V=m2-μ²>0`, `3/4≤n*m2`, `n|μ|≤1`, `m2≤4V`, positive gamma, and `L2≤m`. Thus `m≥20≥16`, `m>0`, `h>0`, `S>0`, `T>0`, and `S≤T≤4S` are proved.

The actual mean payment is sound: `(n|μ|)²≤1` and `3/4≤n*m2` give `n*μ²≤(4/3)*m2`; `m≤n` then gives `(m|μ|)²≤(4/3)*T≤(16/3)*S`, which pays `m|μ|≤4sqrt(S)`. No conditional mean-zero assumption appears. For frequency, positive gamma and `κ/γ≤|u|`, together with `κsqrt(L2)≥1` and `L2*γ²≤T`, imply `1≤|u|²*T≤4|u|²*S`; nonnegative square roots pay `1≤2|u|sqrt(S)`. Finally `T≤4S` converts inverse sixth powers with factor `4^6`, and `S≤T` converts the first/second derivative numerators. The adapter constant `4^6*C` remains universal. The zero remaining-length case is excluded by proved source inequalities, not silently omitted.

## Declaration coverage

Every row below has its complete actual type read and its source/proof relation checked. In names, `Q` abbreviates the public prefix `Shao.Probability.quadraticChar_power_fullNoise_cone_scale_bounds`; `F` abbreviates `Shao.Probability.sourceTruncation_fullNoise_highFrequency_derivatives`; `P` abbreviates `_private.Shao.Probability.QuadraticFullNoiseHighFrequency.0.Shao.Probability`. `W` means all three allowed axioms, `E` means `propext`, and `EQ` means `propext, Quot.sound`.

| Actual owned declaration | Source / complete type content and relation | Axioms |
|---|---|---|
| `P.second_mul` | 20–31; global first derivatives + point second differentiability imply actual derivative-of-product-derivative, including both mixed terms | W |
| `P.weighted_mul` | 34–85; actual derivative bounds after weighted multiplication; no division by R | W |
| `P.linearPhase` | 87–88; type `ℝ→ℝ→ℂ`; actual value `fun b r => Complex.exp (((b*r:ℝ):ℂ)*I)` | W |
| `P.linearPhase.eq_1` | generated equation theorem for exactly that value | W |
| `P.phase_first` | 90–97; actual phase derivative `(b*I)*phase` | W |
| `P.phase_second` | 99–104; derivative of actual first-derivative function `(b*I)^2*phase` | W |
| `P.phase_bounds` | 106–115; actual norm/first/second derivative norms `1,|b|,b²` | W |
| `P.restore_mean` | 117–134; actual phase times actual centered power equals uncentered power, all ν/m/σ/r/v | W |
| `P.gamma_payment` | 137–175; finite second moment and actual `m3/V≤2h` from written law/support/mean conditions | W |
| `P.retained_gap` | 177–215; actual signed gap controls both retained sixth powers | W |
| `Q` | 217–365; frozen actual-law product, two differentiability conclusions and 0/1/2 S-scale bounds | W |
| `P.change_clock` | 367–377; nonnegative numerator, positive S/T/a and T≤4S imply inverse-power bound | W |
| `F` | 379–516; frozen original conditional law, actual n/i/T/gamma and 0/1/2 T-scale bounds | W |
| `P.retained_gap._simp_1_1` | field-simplifier: under Zero/OfNat/NeZero, `(2=0)=False` | E |
| `P.retained_gap._simp_1_2` | same complete generic type for 3 | E |
| `P.retained_gap._simp_1_3` | same complete generic type for 4 | E |
| `P.retained_gap._simp_1_4` | NoZeroDivisors, a≠0,b≠0 imply `(a*b=0)=False` | E |
| `P.retained_gap._simp_1_5` | MonoidWithZero/IsReduced, a≠0 imply `(a^n=0)=False`, all Nat n | E |
| `P.retained_gap._simp_1_6` | GroupWithZero, a≠0 imply `(a^n=0)=False`, all Int n | W |
| `P.retained_gap._simp_1_7` | AddMonoidWithOne/CharZero, all Nat n: `(↑n+1=0)=False` | E |
| `Q._simp_1_2` | field-simplifier generic nonzero-numeral type for 2 | E |
| `Q._simp_1_3` | same complete generic type for 3 | E |
| `Q._simp_1_4` | same complete generic type for 4 | E |
| `Q._simp_1_5` | same complete generic nonzero-product type as retained-gap helper | E |
| `Q._simp_1_6` | same complete generic nonzero-natural-power type | E |
| `Q._simp_1_7` | same complete generic nonzero-integer-power type | W |
| `Q._simp_1_8` | same complete generic characteristic-zero cast-plus-one type | E |
| `Q._proof_1_1` | 257; all Nat m, 16≤m, ¬(0<m) imply False | EQ |
| `F._proof_1_1` | 445; all Nat n/i, 16≤n-i, ¬(0<n-i) imply False | EQ |

The generated simplifier declarations only support denominator arithmetic in the enclosing `field_simp` calls; the generated positivity proofs justify the explicit Nat-to-real positivity steps. Their polymorphic actual types introduce no target assumptions.

## Reused interfaces and acceptance boundary

The new signed-power producer is independently CORRECT and root-accepted at commit `baef8950b5c30ff3fb49b7ebe1cc755b91f7eaca`, source `026a4057455df3647b139acf3fbcd673b0940007a687b3d1ee6ea13c6d695fc6`, object `356c79ce4975dd6c42b7ea45ac5471f9f8df2845b532734fcf460b3336ef9e56`; `common-power-review.json` SHA `c043916a0818bce9b5ac7b90f91fc74eff77ae581b93794a9ab37e1a868837d1` and root scope-acceptance SHA `c205180cb69c958b248603fd4583a720e07362f23a40738db8f1d00213f95036` match. Read its full public interface and reused its complete internal-proof review rather than re-reviewing it.

K/retained Xi/centered source and canonical object hashes equal the accepted v45 receipt (`d5868c98c500917746bbe9adfb1a34570be8e3bf588a8f31766d224a90871dce`). Global Xi derivatives and original truncation/scale interfaces also match accepted source hashes. All 13 borrowed objects match their manifest and actual imported links. Selected new-use mathlib files for derivative multiplication/composition, complex exponentials, variance and Bochner integral Basic equal their pinned Git blobs, despite the inherited package-view warning. These checks do not assert whole-package cleanliness or a new aggregate build.

The complete source highderivatives(c), for derivative orders 0,1,2 and both signs in the recorded original fixed-cutoff regime, is covered by the new adapter, not merely by a finite identity or a conditional conclusion assumed as input. This permits mathematical closure of that explicitly frozen (c) unit after root checks exact interfaces/integration. It does **not** close Fourier inversion, regional integration, desmoothing, the smoothed comparison theorem, C1/C2, any other open root group, or historical novelty. Main/aggregate integration is the coordinator's separate remaining gate. Reuse this review only for the exact source/object/interface hashes; extend it only for an affected mathematical delta or uncovered integration risk.
