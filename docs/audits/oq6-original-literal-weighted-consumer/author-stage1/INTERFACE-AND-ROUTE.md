# Unit228 Stage1 interface proposal

Status: CANDIDATE_ONLY_NOT_FROZEN. This is an author proposal, not a proof, independent review, or Lean acceptance. The proposed source has one public theorem and no new private/top-level helpers, auxiliary Prop definitions, classes, axioms, or callbacks supplied by a caller. All new mathematical hypotheses are forbidden. `CANDIDATE-DECLARATION.txt` is the complete proposed signature; its proof body is deliberately absent.

## Witness and quantifier contract

The only outer mathematical witness is `(m₀,hm₀,hcg)` extracted ONCE from qualified226 `actual_original_literal_remainder_envelope μ h hh hh2 hhsymm hcenter hprojectionsecond`. It precedes every `n,C0,z,k`. This witness is not compared with, equated to, or replaced by an existential witness independently obtained from224/221. The implementation must not apply224/221 again to choose another reduced space.

`g,r,v,rho` are evaluated using original `mΩ,μ` before the local instance changes to `m₀`. The exact same `μ₀=μ.trim hm₀`, `P₀`, original `P`, `ν`, `q`, `ξ`, and canonical `c` occur for every k. All full and deleted objects retain `Fin n`, original n in D/Ddelete, and `(n-2)^2` in J/Jdelete through the accepted definitions. Clipping uses y=1. The free threshold z only affects Qε, H/Hdelete, and the analytic weights.

The sequence is fixed to `ε k = 1/(8*sqrt(n)*((k:ℝ)+1))`. Its **explicit fixed-law extraction point is k=0**, with `ε 0=1/(8*sqrt(n))`; it is not a separate epsilon-star. Invoke the current-epsilon226 supplier at `(n,hn,C0,hC0,z,hz,K,hK,ε 0,hε0,hεsmall0)` to obtain fixed-law facts. Invoke that SAME supplier at ε k for each k to obtain the k-dependent normalization, scalar factorization and literal envelope clauses. Facts inside226's epsilon-universal may only be projected after one of these valid epsilon arguments is supplied. The candidate exposes the resulting sequence theorem, not a stronger theorem for arbitrary epsilon.

`K : ℝ := 4*sqrt(n)` is deterministic ordinary data, not a hypothesis or an arbitrary nonnegative parameter. `0<K` follows from hn. Ring rearrangement is needed between `K*ε k` and `4*ε k*sqrt(n)`; no inequality or change of coefficient is hidden here.

The remaining existential witnesses are only:

- `Ffull : (Fin n → ℝ) → ℝ × ℝ × ℝ`, separately inside each k. Its right side is `(M k,Anew k,B)` at the exact `C k`.
- `Fdelete : ({j : Fin n // j ≠ i} → ℝ) → ℝ × ℝ × ℝ`, separately inside k,i. Its right side is `(Mdelete k i,AdeleteNew k i,Bdelete i)` at the same retained η coordinates. No global deleted-witness family is chosen.
- `G1,G2 : (Fin n → ℝ) → ℝ`, separately inside each k, giving `Dη k` and `D2∘q`. They are projected from the current ε k scalar packet. No equality between witnesses at different k is asserted.

Each witness carries real-vector Borel measurability and an every-sample equation. They are conclusions, never input callbacks. The deleted subtype contains indices, not observations. There is no Ω filler, Nonempty Ω, or choice of an observation.

## Ambient and instance captures

1. Original inputs: `Ω : Type u`, `[mΩ : MeasurableSpace Ω]`, `μ : @Measure Ω mΩ`, `[IsProbabilityMeasure μ]`; Ω has no topology/StandardBorel/countably-generated/nonempty premise. `hh,hh2,hhsymm,hcenter,hprojectionsecond` have exactly226's types.
2. After the sole reduced witness: local `[MeasurableSpace Ω] := m₀`, local `[MeasurableSpace.CountablyGenerated Ω] := hcg`; `μ₀ : @Measure Ω m₀`. A proof-local `letI : IsProbabilityMeasure μ₀ := hμ₀prob` is allowed only after extracting the base226 conjunction.
3. `mN` and `mN₀` are explicit pi structures from mΩ and m₀. P and P₀ use their respective structures, even though both carriers are `Fin n→Ω`.
4. `mAugLocal=m₀.prod(borel ℝ)` and `mAug=pi (fun _=>mAugLocal)`. Inference on `Ω×ℝ`/full sample is definitionally these structures. For a future explicit instantiation, `@... (Fin n→Ω×ℝ) mAug ν hνprob ...` avoids accidental original-space inference. The canonical c uses the natGeneratingSequence of this exact reduced product space.
5. Probability instances in the future proof are `[IsProbabilityMeasure μ₀]`, `[IsProbabilityMeasure lambda01]` from scalar-code API, `[∀i,IsProbabilityMeasure(νlocal i)]`, `[IsProbabilityMeasure ν]`, `[ @IsProbabilityMeasure (Fin n→Ω) mN₀ P₀ ]` from the same packet. None are assumptions of the new theorem.
6. Fin n and each retained subtype use their existing Fintype, finite, DecidableEq and measurable-pi instances. No `Inhabited Ω` is requested. ℝ uses canonical real structures and borel ℝ. Finite real vectors and triples use canonical Borel structures; `BorelSpace.measurable_eq` is an equality of these standard structures, not a new premise.
7. Classical reasoning is scoped by the preamble and future `classical`; no new logical premise results. Future kernel/AX acceptance is still required, with whitelist propext/Classical.choice/Quot.sound.

## Exact mean-zero join, using the same law

The minimal missing fact is the augmented coordinate mean, not a moment premise. Let `f_i : (Fin n→Ω)→ℝ := fun ζ => gcoord i (O i ζ)` in226 notation; this is definitionally the candidate `ξ0 i`. Qualified226 retained clauses provide:

```
hO i : Measurable[mN₀,m₀] (O i) ∧ MeasurePreserving (O i) P₀ μ₀
hgcoord i : Measurable[m₀,borel ℝ] (gcoord i) ∧
  MemLp[mN₀] f_i 2 P₀ ∧ (∫ ζ, f_i ζ ∂P₀)=0 ∧
  (∫ ζ, (f_i ζ)^2 ∂P₀)=1/(n:ℝ)
hq : @MeasurePreserving (Fin n→Ω×ℝ) (Fin n→Ω) mAug mN₀ q ν P₀
```

The required proof-local Props, with no new assumptions, are:

```
hfiMeas i : Measurable[mN₀,borel ℝ] (ξ0 i)
hfiMapAESM i : AEStronglyMeasurable
  (ξ0 i) (@Measure.map (Fin n→Ω×ℝ) (Fin n→Ω) mAug mN₀ q ν)
hξmeanTransport i : (∫ x, ξ i x ∂ν) = (∫ ζ, ξ0 i ζ ∂P₀)
hξmean : ∀ i:Fin n, (∫ x, ξ i x ∂ν)=0
```

The first is `((hgcoord i).1).comp (hO i).1`. For the second, rewrite the target measure by `hq.map_eq`, then use `hfiMeas.aestronglyMeasurable`. Call `integral_map hq.aemeasurable (hfiMapAESM i)`; its orientation is target-map integral equals composed-source integral. Rewrite map_eq and reverse it to obtain hξmeanTransport. The composition is definitionally `ξ i` after unfolding q,ξ0,ξlocal,N/O/gcoord. Finish using `(hgcoord i).2.2.1`. This repeats the *shape* of accepted226:453–481's square transport with the first-power function; it does not replay any check or reprove226.

The target AE strong measurability is under the exact `ν.map q`, not under ν. Real measurable functions are strongly/a.e. strongly measurable without adding a countably-generated target-law hypothesis. No target integrability assumption is used by integral_map. Integrability of ξ follows from its already retained L² property and the same ν probability law.

## Canonical quantization join

At the same μ₀/hcg, invoke:

```
Shao.OQ6.ScalarObservationCoding.countable_uniform_augmented_base_four_code μ₀
```

under the reduced Ω instance. The c returned is definitionally the candidate `c i` for every i. Relevant exact outputs are `IsProbabilityMeasure lambda01`, `IsProbabilityMeasure (μ₀.prod lambda01)`, `∀t,1/3≤c i t ∧ c i t≤2/3`, `Measurable[mAugLocal,borel ℝ] (c i)`, and `comap (c i) (borel ℝ)=mAugLocal`. No injectivity of Ω or StandardBorel Ω is used. The full API also supplies summability, baseFourOneSet recovery, snd-fiber recovery and level-nullness; it is read, but only the stated fields are required for the new hY/herr join.

For every k,i the exact call is:

```
Shao.OQ6.QuantizedObservationCoding.quantized_observation_spec
  (ξlocal i) (c i) hξlocalMeas hc hrange hcomap (ε k) (hε k)
```

Here `hξlocalMeas : ∀i, Measurable[mAugLocal,borel ℝ] (ξlocal i)` comes from reduced gcoord measurability composed with measurable_fst. Let `Ddecode : ℕ→ℝ→ℝ := fun k y => y/ε k - (Int.floor(y/ε k):ℝ)` only as the exact API output let, not as an additional top-level helper. The complete per-k,i output type is:

```
Measurable (Ylocal k i) ∧ Measurable (Ddecode k) ∧
(∀t:Ω×ℝ, |Ylocal k i t - ξlocal i t|≤ε k) ∧
(∀t:Ω×ℝ, Int.floor(Ylocal k i t/ε k)=Int.floor(ξlocal i t/ε k)) ∧
(∀t:Ω×ℝ, Ddecode k (Ylocal k i t)=c i t) ∧
MeasurableSpace.comap (Ylocal k i) (borel ℝ)=mAugLocal ∧
(∀ν':@Measure (Ω×ℝ) mAugLocal,
  (∀t:ℝ, ν' {x|c i x=t}=0) → ∀t:ℝ, ν' {x|Ylocal k i x=t}=0)
```

Compose `(Ylocal k i)` with coordinate evaluation `measurable_pi_apply i` to obtain hY on mAug, and evaluate the pointwise error at x i. The accepted API bound is ε, not the paper's informal 2ε/3; the weaker API bound suffices for the frozen normalization and K.

## Qε join and normalized-statistic scope

Primary p51 S22 defines exactly the candidate Qε; S23 is its signed threshold identity. Dη is written in226's original association `D1+W-Wη+...`, and the candidate explicitly asserts equality to `D1∘q+Qε`. The new normalized-error bound is obtained by:

```
Shao.OQ6.NormalizedRemainderEnvelope.actual_normalized_remainder_envelope_spec
  ν n hn1 ξ (Y k) hξ hξ2 hξmean hξenergy (hY k)
  (fun x => D1(q x)) (fun x => D2(q x)) A B Adelete Bdelete
  hD1 hD2 hA hB hAnonneg hBnonneg hD1A hD2B hAint hBint
  (ε k) (hε k) (hεsmall k) (herr k) z hz
```

All measurability/L1/nonnegativity/majorization arguments are retained226 fields at explicit k=0. `hD1A` is equality because A=|D1∘q|. `hD2B` is226's clipping bound. hn1 is a consequence of hn:4≤n. The API's Dη is definitionally the candidate Dη; its bound is `|Dη-D1∘q|≤(4*ε k*sqrt(n))*H`. Algebra and the explicit Dη= D1+Qε identify this with `|Qε|≤M k`. The API also gives integrability of Dη−D1 and its absolute value and the integral bound, hence candidate Qε's genuine **unweighted** L¹ convergence by squeeze and ε→0. No new premise `|Qε|≤M` is accepted.

The original clipped statistic T0 keeps the `projectionV=0 → 0` branch. Tη keeps226's ordinary real division: if Vη=0 its value is0; its denominator is positive only almost surely. No event probability is obtained by cancelling a potentially zero denominator pointwise. The candidate retains the every-sample signed identity and the null/positive-denominator normalization facts, but adds no CDF or zero-event estimate.

## Exact generic227 argument map

Instantiate `literal_deleted_weighted_cost_limits` with carrier `(Fin n→Ω×ℝ)`, measurable space mAug, probability ν from the explicit k=0 packet, original n and hn1, and the candidate ξ,Y,ε. The ordered explicit arguments are:

```
ν n hn1 ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
A B Adelete Bdelete hA hB hAdelete hBdelete
hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
hAint hBint hAdeleteint hBdeleteint z hz K hK
```

This is the complete public input list. ξ meas/L²/energy, A/B/full/deleted meas/L¹ and signs are all226 fields; augmented ξ mean is the derived join above; hY/herr are the exact quantizer join. No integrability of a target product is passed as input. In the output, Anew=A+KεH and AdeleteNew=Adelete+KεHdelete are exactly the candidate definitions. Both sides of each literal deletion difference change, and full/deleted exponential ratios both use full Iη. Erased-energy Hdelete and erased exponent Sηminus use the same original Fin n and erase i. The compact cost contains the unchanged Lcompact term and z*∫B; neither may be dropped.

Use227's product integrability, signed-integral limits, ratios, and finite sourceCost/compactCost limits. The candidate copies only these requested consequences and the literal unweighted L¹ envelope information. It does not claim L¹ convergence of `(fullTestη*exp Sη)` or `(deletedTestη*exp Sηminus)` to the corresponding limits. Such a stronger theorem is outside this proposal even if it could later be proved.

For the every-sample Ffull/Fdelete conclusions, at each k use226's envelope factorization with its current epsilon=ε k, K=4sqrt(n), and θ=ε k. These are not obtained from227, which supplies no scalar factorization. Likewise G1/G2 and η normalization facts are current-packet226 projections.

## Same-law original RHS transport

The limiting RHS uses original P on mN, not a new224 witness and not another augmented law. Build the following proof-local derived Props:

```
hidΩ : Measurable[mΩ,m₀] (id:Ω→Ω)
hidN : Measurable[mN,mN₀] (id:(Fin n→Ω)→(Fin n→Ω))
hId : @MeasurePreserving (Fin n→Ω) (Fin n→Ω) mN mN₀ id P P₀
```

`hidΩ = measurable_id'' hm₀`; hidN is pi-coordinate measurability with hidΩ and original evaluation. `MeasurePreserving.mk id P P₀ hidN hP₀map.symm` is the accepted224:382–392 constructor pattern. These are consequences, never new hypotheses.

The only generic proof-local callbacks proposed for freeze are:

```
hIntEq : ∀ (f:(Fin n→Ω)→ℝ), Measurable[mN₀,borel ℝ] f →
  (∫x, f(q x) ∂ν) = (∫ζ, f ζ ∂P)
hIntFromν : ∀ (f:(Fin n→Ω)→ℝ), Measurable[mN₀,borel ℝ] f →
  Integrable[mAug] (fun x => f(q x)) ν → Integrable[mN] f P
```

They capture **only** Ω,n,mΩ,m₀,mN,mN₀,mAug,P,P₀,ν,q,hq,hId. To derive hIntEq, apply integral_map to hq and hId, each with the SAME reduced target f and its AE strong measurability under the respective pushforward; rewrite both map_eq equalities, then compose the equalities. To derive hIntFromν, use `(hq.integrable_comp hf.aestronglyMeasurable).1` followed by `hId.integrable_comp_of_integrable`. This exact generic transport pattern is present in accepted CanonicalSequenceAnalyticCosts:322–333, but that theorem and its ambient assumptions are NOT applied here.

All required f arguments are explicit finite combinations of ξ0,A0,B0,A0delete,B0delete already measurable under mN₀:

| f : (Fin n→Ω)→ℝ | Purpose |
| --- | --- |
| `fun ζ=>Real.exp(S0 ζ)` | I limit and I0 positivity |
| `fun ζ=>fullTest0 ζ*Real.exp(S0 ζ)` | full product L¹ and signed integral/ratio RHS |
| `fun ζ=>deletedTest0 i ζ*Real.exp(S0minus i ζ)` | each partial weighted RHS |
| `compactDeletedTest0 i` | compact deleted integral RHS |
| `A0`, `B0` | compact unweighted one-term RHS |
| `fun ζ=>((1+z)*ξ0 i ζ)^2*min |(1+z)*ξ0 i ζ| 1` | each Lcompact summand |

Finite sum/ring normalization identifies the227 limits with `sourceCost0` and `compactCost0` as written. hIntEq requires only measurability, while hIntFromν is used only when the required pullback product is already integrable from227. No higher moments, integrability of V²B, Eg⁴, or E(g²r²) enter.

## Proof-local Prop inventory boundary and obstacles

Besides the explicitly typed mean/quantization/transport facts above, the remaining local proof names may only be propositions projecting226/227/existing envelope APIs, positivity/smallness/Tendsto of the fixed sequence, algebraic equality of the displayed RHSs, measurable finite sums/products/min/absolute-values, or finite-conjunction assembly. No local ordinary function/measure/type/witness/instance beyond this file and the declaration may be added without lead freeze. No proof body has been written.

There is no mathematical counterexample or necessary extra assumption identified by this Stage1 inspection. Remaining **unverified** obligations are elaboration of the explicit instance paths, exact projection/destructuring of the large226 conjunction, the first-power integral_map join, and algebraic/transport assembly of227's RHS. They are proof obligations, not accepted results. Lead must first freeze the signature and inventories; future complete proof needs independent full source/proof review and source-bound server native/same-original-object all-owned TYPE/required VALUE/transitive-AX evidence. The p51 repair itself remains UNCERTIFIED_REPAIR_CANDIDATE and its p54 repairs/named Shao–Zhou2016 attribution remain unchanged.
