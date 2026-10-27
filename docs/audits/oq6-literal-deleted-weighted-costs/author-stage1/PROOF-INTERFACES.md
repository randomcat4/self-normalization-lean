# Complete proof-local interfaces and route

This is an author proposal, not an implemented or independently verified proof. The public declaration is completely specified in `CANDIDATE-DECLARATION.txt`. No theorem proof body or `.lean` file is supplied. All displayed `have` signatures below specify proof-local obligations after the parent freezes that declaration; none is an additional public premise.

## Exact primary calls and proposition witnesses

Use the following three accepted APIs at the SAME arguments, in this order. The only scalar change between those calls is that unit225 calls its threshold argument z, which is instantiated to x here. No call uses a different Y, ν, ξ, ε, n or deletion convention.

```text
have hOld :=
  Shao.OQ6.NormalizedAnalyticCostLimits.actual_normalized_remainder_analytic_cost_limits
    ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr
    A B Adelete Bdelete hA hB hAdelete hBdelete
    hAnonneg hBnonneg hAdeletenonneg hBdeletenonneg
    hAint hBint hAdeleteint hBdeleteint x hx

have h225 :=
  Shao.OQ6.LiteralDeletedRemainderEnvelope.literal_deleted_remainder_envelope_spec
    ν n hn ξ hξ hξ2 hξenergy B Bdelete hB hBdelete
    hBnonneg hBdeletenonneg hBint hBdeleteint x hx

have hProj :=
  Shao.OQ6.NormalizedAnalyticCostLimits.actual_projection_tilt_and_truncated_cost_limits
    ν n hn ξ hξ hξ2 hξmean hξenergy Y hY ε hε hεsmall hεlim herr x
```

These are theorem invocations through already accepted imported artifacts, not instructions to rebuild/review the old proofs or replay their axiom audits. Unit225's exact source, original object, independent final review and full actual TYPE are bound in `INPUT-BINDINGS.json`. The full public TYPE has been read as API evidence, without commissioning an old proof review.

Introduce the following ordinary proof-local data; the public η/V/H/Hdelete and other public lets remain in scope unchanged:

```text
let c0 : ℝ := 4 * Real.sqrt (n : ℝ)
let d : ℝ := |K - c0|
let Aold : ℕ → Ω → ℝ := fun k ω => A ω + (4 * ε k * Real.sqrt (n : ℝ)) * H ω
let fullOld : ℕ → Ω → ℝ := fun k ω => x * Aold k ω + x ^ 2 * B ω
let deletedOld : ℕ → Fin n → Ω → ℝ := fun k i ω =>
  capη k i ω * (|Aold k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
let compactOld : ℕ → Fin n → Ω → ℝ := fun k i ω =>
  compactCapη k i ω * (|Aold k ω - Adelete i ω| + x * |B ω - Bdelete i ω|)
let F0 : Ω → ℝ := fun ω => fullTest ω * Real.exp (S ω)
let Fo : ℕ → Ω → ℝ := fun k ω => fullOld k ω * Real.exp (Sη k ω)
let Fn : ℕ → Ω → ℝ := fun k ω => fullTestη k ω * Real.exp (Sη k ω)
let D0 : Fin n → Ω → ℝ := fun i ω => deletedTest i ω * Real.exp (Sminus i ω)
let Do : ℕ → Fin n → Ω → ℝ := fun k i ω => deletedOld k i ω * Real.exp (Sηminus k i ω)
let Dn : ℕ → Fin n → Ω → ℝ := fun k i ω => deletedTestη k i ω * Real.exp (Sηminus k i ω)
let C0 : Fin n → Ω → ℝ := compactDeletedTest
let Co : ℕ → Fin n → Ω → ℝ := compactOld
let Cn : ℕ → Fin n → Ω → ℝ := compactDeletedTestη
let Efull : ℝ := Real.exp ((n : ℝ) / 2)
let Edel : ℝ := Real.exp (((n - 1 : ℕ) : ℝ) / 2)
let b : ℝ := (1 + x)⁻¹
let P : Fin n → Ω → ℝ := fun i ω => d * H ω + K * Hdelete i ω
let Qfull : Ω → ℝ := fun ω => Efull * (x * d * H ω)
let Qdel : Fin n → Ω → ℝ := fun i ω => Edel * P i ω
let Qcompact : Fin n → Ω → ℝ := fun i ω => b * P i ω
let mH : ℝ := ∫ ω, H ω ∂ν
let mHdelete : Fin n → ℝ := fun i => ∫ ω, Hdelete i ω ∂ν
let Cfull : ℝ := Efull * (x * d * mH)
let Cdel : Fin n → ℝ := fun i => Edel * (d * mH + K * mHdelete i)
let Ccompact : Fin n → ℝ := fun i => b * (d * mH + K * mHdelete i)
let compactCostOld : ℕ → ℝ := fun k =>
  Lcompactη k + (∫ ω, Aold k ω ∂ν) + x * (∫ ω, B ω ∂ν) +
    ∑ i : Fin n, ∫ ω, Co k i ω ∂ν
let CcompactTotal : ℝ := d * mH + ∑ i : Fin n, Ccompact i
```

`Aold` uses exactly the old rho expression, rather than identifying a newly chosen coefficient with it. The identity `(4 * ε k * sqrt n) = c0 * ε k` is algebra proved locally by ring normalization. Public base F0/D0/C0 and I/Iη are definitionally the old packet's data. The OLD deleted side is `Adelete`, not `AdeleteNew`, and no accepted statement is reinterpreted.

Destructure `hOld` into its exact nineteen top-level conjuncts in order:

```text
rcases hOld with
  ⟨hOldHint, hAoldSpec, hAoldL1zero,
   hF0I, hFoI, hD0I, hDoI, hC0I, hCoI,
   hOldFullDom, hOldDelDom, hOldCompactDom,
   hFoLim, hDoLim, hFoRatio, hDoRatio, hCoLim,
   hOldSourceLim, hOldCompactLim⟩
```

The complete typed interfaces of these witnesses, using the data above, are:

```text
hOldHint : Integrable H ν
hAoldSpec : ∀ k : ℕ, Integrable (Aold k) ν ∧
  ∀ ω : Ω, 0 ≤ Aold k ω ∧ Aold k ω ≤ A ω + H ω
hAoldL1zero : Filter.Tendsto (fun k : ℕ => ∫ ω, |Aold k ω - A ω| ∂ν)
  Filter.atTop (nhds (0 : ℝ))
hF0I : Integrable F0 ν
hFoI : ∀ k : ℕ, Integrable (Fo k) ν
hD0I : ∀ i : Fin n, Integrable (D0 i) ν
hDoI : ∀ (k : ℕ) (i : Fin n), Integrable (Do k i) ν
hC0I : ∀ i : Fin n, Integrable (C0 i) ν
hCoI : ∀ (k : ℕ) (i : Fin n), Integrable (Co k i) ν
hOldFullDom : ∀ (k : ℕ) (ω : Ω), |Fo k ω| ≤
  Efull * (x * (A ω + H ω) + x ^ 2 * B ω)
hOldDelDom : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Do k i ω| ≤
  Edel * (|A ω - Adelete i ω| + H ω + x * |B ω - Bdelete i ω|)
hOldCompactDom : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Co k i ω| ≤
  b * (|A ω - Adelete i ω| + H ω + x * |B ω - Bdelete i ω|)
hFoLim : Filter.Tendsto (fun k : ℕ => ∫ ω, Fo k ω ∂ν)
  Filter.atTop (nhds (∫ ω, F0 ω ∂ν))
hDoLim : ∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, Do k i ω ∂ν)
  Filter.atTop (nhds (∫ ω, D0 i ω ∂ν))
hFoRatio : Filter.Tendsto (fun k : ℕ => (∫ ω, Fo k ω ∂ν) / Iη k)
  Filter.atTop (nhds ((∫ ω, F0 ω ∂ν) / I))
hDoRatio : ∀ i : Fin n, Filter.Tendsto
  (fun k : ℕ => (∫ ω, Do k i ω ∂ν) / Iη k)
  Filter.atTop (nhds ((∫ ω, D0 i ω ∂ν) / I))
hCoLim : ∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, Co k i ω ∂ν)
  Filter.atTop (nhds (∫ ω, C0 i ω ∂ν))
hOldSourceLim : Filter.Tendsto
  (fun k : ℕ => ((∫ ω, Fo k ω ∂ν) + ∑ i : Fin n, ∫ ω, Do k i ω ∂ν) / Iη k)
  Filter.atTop (nhds sourceCost)
hOldCompactLim : Filter.Tendsto compactCostOld Filter.atTop (nhds compactCost)
```

Only `hF0I/hFoI/hD0I/hDoI/hC0I/hCoI`, `hAoldSpec`'s integrability, `hFoLim/hDoLim/hCoLim` and `hOldCompactLim` are needed to close the candidate. The old domination, old Aold bound and old normalized/source limits are recorded precisely but may be discarded during implementation. In particular, `hAoldSpec` is never applied to Anew.

For unit225, destructure only the prefix needed, then discard its remaining proposition tail without naming additional witnesses:

```text
rcases h225 with
  ⟨_, _, _, _, _, _, _, hHm, hHint, hHdeleteSpec, hHpos, hHdeletePos, _⟩

hHm : Measurable H
hHint : Integrable H ν
hHdeleteSpec : ∀ i : Fin n, Measurable (Hdelete i) ∧ Integrable (Hdelete i) ν
hHpos : ∀ ω : Ω, 0 < H ω
hHdeletePos : ∀ (i : Fin n) (ω : Ω), 0 < Hdelete i ω
```

Unit225's H coincides literally with the old H after setting z=x. Its Hdelete is at the original n and original law; it uses `univ.erase i` but retains `sqrt n`. No unit225 M/rho/kappa conclusion is silently rescaled or used to claim Qepsilon domination. Free K scalar multiplication uses its H/Hdelete L1 fields directly.

For the accepted projection packet, destructure only this prefix, discarding the later unused proposition tail:

```text
rcases hProj with
  ⟨_, _, _, hIpos, hIηSpec, _, _, hSB, hSBη, hJB, hJBη, _, _, _, _, hIlim, _⟩

hIpos : 0 < I
hIηSpec : ∀ k : ℕ, Integrable (fun ω => Real.exp (Sη k ω)) ν ∧ 0 < Iη k
hSB : ∀ ω : Ω, Real.exp (S ω) ≤ Efull
hSBη : ∀ (k : ℕ) (ω : Ω), Real.exp (Sη k ω) ≤ Efull
hJB : ∀ (i : Fin n) (ω : Ω), Real.exp (Sminus i ω) ≤ Edel
hJBη : ∀ (k : ℕ) (i : Fin n) (ω : Ω), Real.exp (Sηminus k i ω) ≤ Edel
hIlim : Filter.Tendsto Iη Filter.atTop (nhds I)
```

These exact public bounds come from scalar `t - t^2/2 ≤ 1/2`; their original source usage273–292 was read only for the related API pattern. They hold for all real coordinates and all k. No independence, tail cutoff, moment beyond L2, or smallness of Kε is used.

## Measurability, ordinary derived data and ambient captures

The sole ambient variable types/instances are `{Ω : Type u}`, `[mΩ : MeasurableSpace Ω]`, `(ν : Measure Ω)` and `[hν : IsProbabilityMeasure ν]`. Real measurable/topological/normed/Bochner structures and the canonical `Fin n` fintype/decidable equality are inferred. `hν` supplies the probability/finite-measure facts used by the accepted APIs. There is no new product-space, measurable-fiber, independent-family, standard-Borel, atomless or kernel instance. `open scoped Classical` supplies decidability only, not additional mathematical data.

All public ordinary lets are supplied in full in the candidate head. Their computational captures are:

| Data | Captures besides Ω and canonical real/finite structures |
| --- | --- |
| η | mΩ, ν, n, Y; actual mean and scale are deterministic Bochner integrals of that SAME Y |
| V, Vdelete | n, ξ |
| H | n, ξ, B, x |
| Hdelete | n, ξ, Bdelete, x |
| Anew, AdeleteNew | respectively A/H or Adelete/Hdelete, K, ε |
| ℓ, ℓη, S, Sη, Sminus, Sηminus | x, ξ or η, original n/erase i |
| I, Iη | S/Sη, mΩ, ν |
| cap, capη, compactCap, compactCapη | x, ξ or η |
| fullTest, fullTestη | x, A or Anew, B |
| deletedTest/compactDeletedTest | original A/Adelete/B/Bdelete plus corresponding base cap |
| deletedTestη/compactDeletedTestη | Anew/AdeleteNew/B/Bdelete plus corresponding normalized cap |
| δcompact, δcompactη, Lcompact, Lcompactη | x, ξ or η, mΩ, ν, original n |
| sourceCost/sourceCostη | their exact full/deleted integrands, I/Iη, mΩ, ν, original n |
| compactCost/compactCostη | Lcompact/Lcompactη, original B and A/Anew, compact deleted data, mΩ, ν, original n |

Integrals computationally capture mΩ and ν, not the proof hν. Measurable propositions capture mΩ and the target real measurable structure. Integrable propositions and their finite values capture ν and mΩ. None of hn/hξ/hξ2/hξmean/hξenergy/hY/hε/hεsmall/hεlim/herr/hA/hB/.../hx/hK is a computational argument of these ordinary lets. Those are proof premises used to establish their Prop conclusions. No proof witness is used to choose a Y, η, ε, law, K or deletion.

For proof-local data: c0 captures n; d captures n,K; Aold captures A,ε,H,n; fullOld/deletedOld/compactOld capture their displayed functions/caps and x; F0/Fo/Fn, D0/Do/Dn, C0/Co/Cn capture their displayed integrands; Efull/Edel capture n; b captures x; P captures d,H,K,Hdelete; Qfull/Qdel/Qcompact capture their displayed scalars/functions; mH/mHdelete capture H/Hdelete,ν,mΩ; Cfull/Cdel/Ccompact capture the displayed scalar integrals; compactCostOld captures the displayed old data/Lcompactη/ν/mΩ; CcompactTotal captures d,mH,Ccompact,n. No proof-local ordinary datum has any unlisted choice/proof callback capture.

Measurability witnesses, with complete types, are:

```text
hηm : ∀ (k : ℕ) (i : Fin n), Measurable (η k i)
hAnewM : ∀ k : ℕ, Measurable (Anew k)
hAdnewM : ∀ (k : ℕ) (i : Fin n), Measurable (AdeleteNew k i)
hAoldM : ∀ k : ℕ, Measurable (Aold k)
hFoM : ∀ k : ℕ, Measurable (Fo k)
hFnM : ∀ k : ℕ, Measurable (Fn k)
hDoM : ∀ (k : ℕ) (i : Fin n), Measurable (Do k i)
hDnM : ∀ (k : ℕ) (i : Fin n), Measurable (Dn k i)
hCoM : ∀ (k : ℕ) (i : Fin n), Measurable (Co k i)
hCnM : ∀ (k : ℕ) (i : Fin n), Measurable (Cn k i)
hPI : ∀ i : Fin n, Integrable (P i) ν
hPnonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ P i ω
hQfullI : Integrable Qfull ν
hQdelI : ∀ i : Fin n, Integrable (Qdel i) ν
hQcompactI : ∀ i : Fin n, Integrable (Qcompact i) ν
hQfullNonneg : ∀ ω : Ω, 0 ≤ Qfull ω
hQdelNonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Qdel i ω
hQcompactNonneg : ∀ (i : Fin n) (ω : Ω), 0 ≤ Qcompact i ω
```

`hηm` follows directly from the public deterministic affine definition: `(Y k i ω - actualCoordinateMean ν (Y k) i) / actualNormalizationScale ν (Y k)`. The mean and scale are constants with respect to ω; use `(hY k i).sub measurable_const` followed by `Measurable.div_const`. This does not require a separate normalization-sequence API call or a nonzero scale for measurability. All remaining measurable fields use add/sub/mul/abs/min/pow/exp and finite measurable sums. `hPI` is `(hHint.const_mul d).add ((hHdeleteSpec i).2.const_mul K)`; the three Q-integrability fields are constant multiples of H or P. No product of two merely-L1 functions is used.

All constant/sign witnesses needed below have these types:

```text
hd : 0 ≤ d
hb : 0 ≤ b
hmH : 0 ≤ mH
hmHdelete : ∀ i : Fin n, 0 ≤ mHdelete i
hCfull : 0 ≤ Cfull
hCdel : ∀ i : Fin n, 0 ≤ Cdel i
hCcompact : ∀ i : Fin n, 0 ≤ Ccompact i
hCcompactTotal : 0 ≤ CcompactTotal
hQfullIntegral : (∫ ω, Qfull ω ∂ν) = Cfull
hQdelIntegral : ∀ i : Fin n, (∫ ω, Qdel i ω ∂ν) = Cdel i
hQcompactIntegral : ∀ i : Fin n, (∫ ω, Qcompact i ω ∂ν) = Ccompact i
```

Use hHpos/hHdeletePos, `integral_nonneg`, `integral_const_mul`, and `integral_add` with hHint and hHdeleteSpec. `1+x>0` follows from hx, so b≥0 even at x=0. Every C is finite because its underlying function is integrable; no uniformity over models, n or x is asserted.

## Pointwise comparison and boundary checks

The exact derived propositions are:

```text
hAcompare : ∀ (k : ℕ) (ω : Ω),
  |Anew k ω - Aold k ω| = |ε k| * (d * H ω)
hFeeCompare : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
  ||Anew k ω - AdeleteNew k i ω| - |Aold k ω - Adelete i ω|| ≤ |ε k| * P i ω
hFullCompare : ∀ (k : ℕ) (ω : Ω),
  |Fn k ω - Fo k ω| ≤ |ε k| * Qfull ω
hDelCompare : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
  |Dn k i ω - Do k i ω| ≤ |ε k| * Qdel i ω
hCompactCompare : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
  |Cn k i ω - Co k i ω| ≤ |ε k| * Qcompact i ω
```

Proof of hAcompare: expand Anew/Aold, subtract A, and ring-normalize to `ε k * ((K-c0)*H ω)`. Apply `abs_mul` and `abs_of_nonneg (hHpos ω).le`; d is the absolute signed coefficient, not K-c0 itself. In hFeeCompare set `u=Anew-Adnew` and `v=Aold-Adelete`. Algebra gives `u-v=ε k*((K-c0)*H-K*Hdelete)`. The real reverse triangle inequality bounds `||u|-|v||` by `|u-v|`; the triangle inequality bounds the latter by `|ε k|*(d*H+K*Hdelete)`, using K,H,Hdelete≥0. This derivation contains no assumption on the sign of K-c0.

In hFullCompare the `x^2*B` term cancels, so the difference is `x*(Anew-Aold)*exp(Sη)`. Use x≥0, exp>0 and hSBη. In hDelCompare and hCompactCompare the `x*|B-Bdelete|` term cancels before taking absolute values; the SAME capη (or compactCapη) is common to both expressions. For all k,i,ω,

```text
0 ≤ capη k i ω ∧ capη k i ω ≤ 1
0 ≤ compactCapη k i ω ∧ compactCapη k i ω ≤ b
```

follow directly from min bounds and nonnegativity of abs/b. Multiply hFeeCompare by that cap, and by the positive deleted exponential for hDelCompare. Apply hJBη. The proof is valid also when n=1: the erased sum is empty, Edel=exp(0)=1 and Vdelete=0. It uses no `n-1` replacement in Hdelete. It is valid for K=0, K<c0, K=c0 and K>c0. At x=0, Fn/Fo and the x-weighted deleted tests have zero full/cap factors; compactCap remains valid with b=1. None of the arguments divides by K or x.

## Complete typed callbacks, integrability and error bounds

One proof-local callback can package the repeated elementary integral estimate. Its entire interface is:

```text
hPerturb : ∀ (f g Q : Ω → ℝ) (r : ℝ),
  Measurable f → Measurable g → Integrable g ν →
  Integrable Q ν → (∀ ω : Ω, 0 ≤ Q ω) → 0 ≤ r →
  (∀ ω : Ω, |f ω - g ω| ≤ r * Q ω) →
  Integrable f ν ∧
  Integrable (fun ω : Ω => |f ω - g ω|) ν ∧
  (∫ ω, |f ω - g ω| ∂ν) ≤ r * (∫ ω, Q ω ∂ν) ∧
  |(∫ ω, f ω ∂ν) - (∫ ω, g ω ∂ν)| ≤ r * (∫ ω, Q ω ∂ν)
```

This is a locally proved implication, not a supplied mathematical premise or a public global declaration. It captures Ω,mΩ,ν and canonical real structures only. To prove it, `(hf.sub hg).aestronglyMeasurable` and `(hQI.const_mul r).mono'` give integrability of `f-g` from the stated absolute bound. Its `.abs` is genuine L1. Add g back to get integrable f. `integral_mono` bounds the absolute integral by the integral of rQ, which `integral_const_mul` evaluates. `integral_sub` with the proved f/g integrability identifies the difference of signed integrals, and `norm_integral_le_integral_norm` for that real difference yields its bound. No integral of a nonintegrable function is used in an inference. The nonnegative Q/r assumptions hold explicitly for all calls.

Use it exactly as follows (the algebraic Q-integral equalities turn the last two conclusions into constants C):

```text
hPerturb (Fn k) (Fo k) Qfull |ε k|
  (hFnM k) (hFoM k) (hFoI k) hQfullI hQfullNonneg (abs_nonneg _) (hFullCompare k)
hPerturb (Dn k i) (Do k i) (Qdel i) |ε k|
  (hDnM k i) (hDoM k i) (hDoI k i) (hQdelI i)
  (hQdelNonneg i) (abs_nonneg _) (hDelCompare k i)
hPerturb (Cn k i) (Co k i) (Qcompact i) |ε k|
  (hCnM k i) (hCoM k i) (hCoI k i) (hQcompactI i)
  (hQcompactNonneg i) (abs_nonneg _) (hCompactCompare k i)
hPerturb (Anew k) (Aold k) (fun ω : Ω => d * H ω) |ε k|
  (hAnewM k) (hAoldM k) (hAoldSpec k).1 (hHint.const_mul d)
  (fun ω : Ω => mul_nonneg hd (hHpos ω).le) (abs_nonneg _)
  (fun ω : Ω => (hAcompare k ω).le)
```

The resulting full mathematical interfaces, for all k and i, include:

```text
hFnI : ∀ k : ℕ, Integrable (Fn k) ν
hDnI : ∀ (k : ℕ) (i : Fin n), Integrable (Dn k i) ν
hCnI : ∀ (k : ℕ) (i : Fin n), Integrable (Cn k i) ν
hFullL1Error : ∀ k : ℕ, Integrable (fun ω : Ω => |Fn k ω - Fo k ω|) ν ∧
  (∫ ω, |Fn k ω - Fo k ω| ∂ν) ≤ |ε k| * Cfull
hDelL1Error : ∀ (k : ℕ) (i : Fin n), Integrable (fun ω : Ω => |Dn k i ω - Do k i ω|) ν ∧
  (∫ ω, |Dn k i ω - Do k i ω| ∂ν) ≤ |ε k| * Cdel i
hCompactL1Error : ∀ (k : ℕ) (i : Fin n), Integrable (fun ω : Ω => |Cn k i ω - Co k i ω|) ν ∧
  (∫ ω, |Cn k i ω - Co k i ω| ∂ν) ≤ |ε k| * Ccompact i
hFullIntegralError : ∀ k : ℕ,
  |(∫ ω, Fn k ω ∂ν) - (∫ ω, Fo k ω ∂ν)| ≤ |ε k| * Cfull
hDelIntegralError : ∀ (k : ℕ) (i : Fin n),
  |(∫ ω, Dn k i ω ∂ν) - (∫ ω, Do k i ω ∂ν)| ≤ |ε k| * Cdel i
hCompactIntegralError : ∀ (k : ℕ) (i : Fin n),
  |(∫ ω, Cn k i ω ∂ν) - (∫ ω, Co k i ω ∂ν)| ≤ |ε k| * Ccompact i
hAoldNewIntegralError : ∀ k : ℕ,
  |(∫ ω, Anew k ω ∂ν) - (∫ ω, Aold k ω ∂ν)| ≤ |ε k| * (d * mH)
hFullErrorZero : Filter.Tendsto
  (fun k : ℕ => ∫ ω, |Fn k ω - Fo k ω| ∂ν) Filter.atTop (nhds (0 : ℝ))
hDelErrorZero : ∀ i : Fin n, Filter.Tendsto
  (fun k : ℕ => ∫ ω, |Dn k i ω - Do k i ω| ∂ν) Filter.atTop (nhds (0 : ℝ))
hCompactErrorZero : ∀ i : Fin n, Filter.Tendsto
  (fun k : ℕ => ∫ ω, |Cn k i ω - Co k i ω| ∂ν) Filter.atTop (nhds (0 : ℝ))
hAnewI : ∀ k : ℕ, Integrable (Anew k) ν
hAdnewI : ∀ (k : ℕ) (i : Fin n), Integrable (AdeleteNew k i) ν
hAnewNonneg : ∀ (k : ℕ) (ω : Ω), 0 ≤ Anew k ω
hAdnewNonneg : ∀ (k : ℕ) (i : Fin n) (ω : Ω), 0 ≤ AdeleteNew k i ω
```

In particular the three new-minus-old absolute integrals tend to zero, by squeezing between zero and their fixed nonnegative C times |ε|. These are proof-local true L1 perturbation limits; no old-product-to-limiting-product L1 convergence is needed or exported.

For the public new-envelope fields, hAnewI is `hAint.add (hHint.const_mul (K*ε k))`, and hAdnewI is `(hAdeleteint i).add ((hHdeleteSpec i).2.const_mul (K*ε k))`. Their nonnegativity follows from hK, hε and the envelope signs, plus the original A/Adelete signs. Expand `Anew-A` and `Adnew-Adelete`, then `abs_mul`, `abs_of_nonneg hK`, `abs_of_nonneg H`, and `integral_const_mul` prove the two exact absolute-integral identities in the public head. Thus their zero limits use `hεlim.abs` multiplied by the fixed nonnegative real K times the relevant envelope integral. This avoids dividing by c0, K, or ε and avoids using any all-k upper bound on Kε.

The local scalar transfer callback has this entire interface:

```text
hTransfer : ∀ (f g : ℕ → ℝ) (L C : ℝ),
  0 ≤ C →
  (∀ k : ℕ, |f k - g k| ≤ |ε k| * C) →
  Filter.Tendsto g Filter.atTop (nhds L) →
  Filter.Tendsto f Filter.atTop (nhds L)
```

Its captures are ε,hεlim and canonical real/filter structures only; it does not capture ν or a probability assumption. For its proof, `(hεlim.abs).mul_const C` has limit zero after rewriting `abs_zero` and `zero_mul`; squeeze `|f-g|` to zero by nonnegativity of abs and the displayed bound. `tendsto_iff_norm_sub_tendsto_zero` for the scalar difference gives `f-g→0`. Add the given `g→L` and simplify `(f-g)+g=f`. This callback introduces no new convergence premise into the public theorem.

Apply hTransfer to `(∫Fn,∫Fo,∫F0,Cfull,hCfull,hFullIntegralError,hFoLim)`; apply it per i to `(∫Dn_i,∫Do_i,∫D0_i,Cdel_i,hCdel_i,hDelIntegralError_i,hDoLim_i)` and `(∫Cn_i,∫Co_i,∫C0_i,Ccompact_i,hCcompact_i,hCompactIntegralError_i,hCoLim_i)`. Each tuple here denotes the exact correspondingly ordered callback arguments, with no extra quantified object. These give exactly the three signed integral limits in the public head.

## Normalized finite sums and compact passage

The obtained signed limits have the complete interfaces

```text
hFnLim : Filter.Tendsto (fun k : ℕ => ∫ ω, Fn k ω ∂ν)
  Filter.atTop (nhds (∫ ω, F0 ω ∂ν))
hDnLim : ∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, Dn k i ω ∂ν)
  Filter.atTop (nhds (∫ ω, D0 i ω ∂ν))
hCnLim : ∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, Cn k i ω ∂ν)
  Filter.atTop (nhds (∫ ω, C0 i ω ∂ν))
```

The public normalized limits are `hFnLim.div hIlim hIpos.ne'` and `(hDnLim i).div hIlim hIpos.ne'`. This divides only by the positive limiting normalizer I; the all-k positivity follows from hIηSpec and is exported. No all-k uniform lower bound on Iη is claimed.

The exact finite sourceCost conclusion follows from

```text
(hFnLim.add (tendsto_finsetSum Finset.univ (fun i _ => hDnLim i))).div hIlim hIpos.ne'
```

after unfolding the public sourceCost/sourceCostη definitions. Every integral in that formula is already L1 and each finite sum uses exactly Fin n. The SAME normalization denominator Iη k divides both full and deleted sums; no normalization by deleted Jη is introduced.

For compactCost, directly transfer the accepted hOldCompactLim. Algebra cancels the SAME Lcompactη k and x∫B terms; `Finset.sum_sub_distrib` and the scalar finite-sum triangle inequality with hAoldNewIntegralError and hCompactIntegralError yield

```text
hCompactCostCompare : ∀ k : ℕ,
  |compactCostη k - compactCostOld k| ≤ |ε k| * CcompactTotal
```

Then use

```text
hTransfer compactCostη compactCostOld compactCost CcompactTotal
  hCcompactTotal hCompactCostCompare hOldCompactLim
```

This reuses the old exact compact truncated-budget limit. No new projection call at 1+x, no new truncated-budget proof and no strict-budget persistence assertion is needed. It also avoids proving a redundant new limit for ∫Aold. The individual compact deleted integral limits already came from hCoLim and the corresponding perturbation bounds.

## Mathematical completion and evidence boundary

The candidate route is complete at the mathematical/API specification level: each additional integrability claim has an explicit integrable majorant and measurable target, every signed-limit transfer has a typed fixed-error bound, the finite sums and positive limiting denominator are identified, and the public envelope identities are direct scalar integrations. There is no missing mathematical interface for this generic theorem. Lean elaboration/kernel/recursive-axiom verification and independent complete review remain future work after parent freeze. No claim of PROVED or LEAN_CHECKED is made for unit227.
