# CD163 read-only characteristic API intake

Status: API route resolved; advisory statement only, NOT frozen/implemented/Lean-checked.
Scope owner: OQ3 lead 01a1669a-bca1-75e0-9d87-d07baee7b90a; this child owns only this report. No Lean/build/kernel/axiom probes, package/cache/shared-source writes, Git writes, children, or cross-thread messages occurred.
Prescribed delegated model/effort: gpt-6.1-sol/xhigh. Tool-visible usage counters: input unavailable; cached-input unavailable; output unavailable; reasoning-subset unavailable. No subscription allocation inferred.
Read AGENTS constraints, math-theorem references, SERVER, current TEAM authority, TAKEOVER, restart entry and streamlined acceptance. OQ3 old writer released/new owner active, child lease1; read-only server Python used activation then CPU14–17.

## Exact binding and consumed interfaces

Observed server branch `feat/oq3-standardized-cell-comparison`, HEAD `e730ce575b5015cf5c86816427673bde6c7c362a`; pinned mathlib `807d3836b165983210ee2ecf3cd28f239436949c`.
Root-v59 receipt SHA256 `30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc`, PASS; checked code `29c9804c552f0cc494355e6556c112aa3c36c908`, checked tree `3105ddcd9ee08c67da77f150f9392e140061a98c`.
These are distinct from main `b6bdf7333a514f9f908c838ddd0161b5617e422e` and accepted head `d9956f24a088a74d7265c6266db1746685be9d35`.
The v59 source map, curated local source and live server bytes agree on:
- `Shao/Probability/QuadraticCharacteristic.lean`: `8fd7815191dbd1ba9180159effe8c353d8b82d998d4d0d50bb6f957355b628f5`.
- `Shao/Probability/FiniteIID.lean`: `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`.
- `Shao/Basic/FinitePath.lean`: `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`.
Qualified BV is PR217 ancestry, not a claimed v59 map member: local/live `ParabolaIIDStandardizedLaw.lean` SHA `3c44e20c9003e0b743829a5ad46ee56f12f72c9cc8fbaa6bea61c5cbb3c526b7`; bound final review `u22bubv-proof-review.md` SHA `0ede4b14deb562e06696b2ac0c56d63b430f41c48b21063626a4870e69090c56`.
Qualified CC local/live `ActualStandardizedIIDCellTest.lean` SHA `12cfbab4cfe060d1d8f007d900e30489c8288fa3a0f850fe8eacc38c19e5588f`; bound final review `u22cc-proof-review.md` SHA `d65da3c83397fa1cc1f5175fef0839a8bae17677156f73a89b8c93313da86f53` (141 lines). Review bytes hashed; old proofs/reports not re-reviewed or rechecked.
Read complete BV and CC declaration statements and every introduced let-value; neither module introduces a named definition. BV `iid_parabola_affine_standardized_law` takes exactly probability ν, n≥1, arbitrary y and real-pair CLEquiv E, and returns `IsProbabilityMeasure law ∧ IsProbabilityMeasure (Q.map T) ∧ (∀ z, T z = S (fun i => Y (z i))) ∧ Q.map T = QY.map S`.
Its actual values are `Y x = E ((x,x^2)-y)`, `law=ν.map Y`, `Q=pi (fun _ : Fin n => ν)`, `QY=pi (fun _ : Fin n => law)`, `M z=((∑i,z i)/n,energy z/n)`, `T z=√n • E(M z-y)`, `S v=(√n)⁻¹ • ∑i,v i`.
CC's probability ν and identical ρ are actual tilted ν and `ρ=Q.map T`; it supplies the same `ρ=QY.map SN`. Use that probability instance to specialize the generic next result, with no transfer of unrelated old-ρ estimates.
Root `quadraticChar ν u v := ∫a, Complex.exp (((u*a+v*a^2 : ℝ):ℂ)*I) ∂ν` (line21). Read its complete value and the complete existing factor signature (line93):
```lean
Shao.Probability.iid_quadraticChar_factor
  {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ν : Measure ℝ}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : Fin n → Ω → ℝ}
  (hX : ∀ i, Measurable (X i)) (hIndep : iIndepFun X μ)
  (hLaw : ∀ i, IdentDistrib (X i) (id : ℝ → ℝ) μ ν) (u v : ℝ) :
  (∫ω, Complex.exp (((u * Shao.prefixSum (samplePath X ω) n +
    v * Shao.energy (samplePath X ω) : ℝ) : ℂ) * Complex.I) ∂μ) =
  (Shao.Probability.quadraticChar ν u v)^n
```
`samplePath X ω := fun i => X i ω`; `Path n := Fin n → ℝ`; `prefixSum z k := ∑i ∈ univ.filter (fun i => i.val<k), z i`; `energy z := ∑i,(z i)^2`; existing `prefixSum_length` removes the saturated prefix at n. No moment hypotheses occur in this factor theorem.

## One recommended next statement (advisory, not a freeze)

Use actual coordinate Fourier integrals on the MAX-norm pair; this single statement exposes precisely the n-th-power interface:
```lean
(ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (hn : 1 ≤ n)
(y t : ℝ × ℝ) (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
let r : ℝ := Real.sqrt (n : ℝ)
let Y : ℝ → (ℝ × ℝ) := fun x => E ((x, x^2) - y)
let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => ν)
let M : Shao.Path n → (ℝ × ℝ) := fun z =>
  ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
let ρ : Measure (ℝ × ℝ) := Q.map (fun z => r • E (M z - y))
let K : (ℝ × ℝ) → ℂ := fun v =>
  Complex.exp (((t.1*v.1+t.2*v.2 : ℝ) : ℂ) * Complex.I)
(∫ v, K v ∂ρ) = (∫ x : ℝ, K (r⁻¹ • Y x) ∂ν)^n
```
The single factor is exactly the Fourier integral of `law=ν.map Y` at frequency `r⁻¹ • t`.
For its scalar/root-facing form set `D v=t.1*v.1+t.2*v.2`, `a=D(E(1,0))`, `b=D(E(0,1))`, `c=D(E y)`.
Then that factor is `Complex.exp (((-c/r : ℝ):ℂ)*I) * quadraticChar ν (a/r) (b/r)`; hence its n-th power is the corresponding expression raised to n, equivalently `exp (((-r*c : ℝ):ℂ)*I) * (quadraticChar ν (a/r) (b/r))^n` because n/r=r.
The dual frequency is `(a,b)`, i.e. coefficients of `D ∘ E` (matrix transpose direction); it is neither `E t` nor `E.symm t` in general. Arbitrary y is retained: c need not be a mean; no covariance, moment, centering or tilt assumption is silently added.

## Exact API bundle in the pinned primary sources

All paths below are under the live worktree `.lake/packages/mathlib/`.
1. `Mathlib/Probability/Independence/Basic.lean:889–906`, namespace `ProbabilityTheory`:
```lean
{ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
{μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
{Z : ι → Type*} [∀ i, MeasurableSpace (Z i)] {X : (i : ι) → Ω i → Z i}
iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) :
  iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ)
```
Instantiate `X := fun _ => id`, `mX := fun _ => aemeasurable_id`: actual evaluations are i.i.d.-independent.
2. `Mathlib/MeasureTheory/Constructions/Pi.lean:402–407`:
```lean
MeasureTheory.measurePreserving_eval [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
  MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i)
```
The exact evaluation law is `(measurePreserving_eval (fun _ : Fin n => ν) i).map_eq`.
`Measure.pi_map_eval [DecidableEq ι] (i : ι)` (line376) is the more general σ-finite formula `(pi μ).map (Function.eval i) = (∏ j ∈ univ.erase i, μ j univ) • μ i`; use the probability version above to avoid extraneous factors.
`ProbabilityTheory.IdentDistrib` (`Probability/IdentDistrib.lean:68–73`) has fields `aemeasurable_fst`, `aemeasurable_snd`, `map_eq : μ.map f = ν.map g`. Thus construct eval-vs-id with `⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id, by simpa using (measurePreserving_eval (fun _ : Fin n => ν) i).map_eq⟩`; `Measure.map_id` (`Measure/Map.lean:199`) supplies the RHS simplification.
3. Preferred direct factorization, `Mathlib/MeasureTheory/Integral/Pi.lean:106–122`, namespace `MeasureTheory`, `[Fintype ι] [RCLike 𝕜]`:
```lean
integral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
  {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
  [∀ i, SigmaFinite (μ i)] :
  (∫ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫ x, f i x ∂μ i
integral_fintype_prod_eq_pow {E : Type*} (f : E → 𝕜) {mE : MeasurableSpace E}
  {μ : Measure E} [SigmaFinite μ] :
  (∫ x : ι → E, ∏ i, f (x i) ∂Measure.pi (fun _ => μ)) =
    (∫ x, f x ∂μ) ^ Fintype.card ι
```
Neither equality has a measurability/integrability premise. Probability gives σ-finiteness. If an explicit product-integrability result is wanted, `Integrable.fintype_prod` (line67) takes `[NormedCommRing 𝕜] [∀i,SigmaFinite (μ i)]` and `hf : ∀i,Integrable (f i) (μ i)` and returns integrability of the coordinate product under `pi μ` (same E for every coordinate).
4. `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1076–1078`, specialized to complex output:
```lean
MeasureTheory.integral_map {β} [MeasurableSpace β] {φ : α → β}
  (hφ : AEMeasurable φ μ) {f : β → ℂ}
  (hfm : AEStronglyMeasurable f (μ.map φ)) :
  (∫ y, f y ∂μ.map φ) = ∫ x, f (φ x) ∂μ
```
No integrability premise here either. For continuous K (or K∘scaling), use `Continuous.aestronglyMeasurable`; all actual Y,S,T are continuous. `integral_map_of_stronglyMeasurable` (line1065) is the measurable/strongly-measurable variant.
`Complex.norm_exp_ofReal_mul_I (x : ℝ) : ‖Complex.exp ((x : ℂ)*I)‖=1` is at `Analysis/Complex/Trigonometric.lean:952`; the reversed-order version `norm_exp_I_mul_ofReal` is line956. A probability-space complex kernel is integrable using `(integrable_const (1:ℝ)).mono'` with continuous/AEStronglyMeasurable kernel and this norm equality. No moments required.
`integral_const_mul (r : ℂ) (f : α → ℂ) : (∫a,r*f a ∂μ)=r*∫a,f a ∂μ` is Bochner/Basic line288, with no integrability premise; use it for the centered phase.
5. Finite algebra APIs (actual declarations/generation read):
- `Complex.exp_sum (s : Finset ι) (f : ι → ℂ) : exp (∑i∈s,f i)=∏i∈s,exp(f i)`, `Analysis/Complex/Exponential.lean:146`; `exp_nsmul (x : ℂ) (n : ℕ) : exp (n • x)=exp x^n`, line150.
- `Complex.ofReal_sum (s : Finset ι) (f : ι → ℝ) : ((∑i∈s,f i : ℝ):ℂ)=∑i∈s,(f i:ℂ)`, `Basic/Complex/BigOperators.lean:22–30` (explicit s before f).
- `Finset.sum_mul (s) (f) (a) : (∑i∈s,f i)*a=∑i∈s,f i*a`; `Finset.mul_sum (s) (f) (a)` is the left-multiplication analogue, `Algebra/BigOperators/Ring/Finset.lean:56–60`.
- `Finset.smul_sum {f : ι → N} {s : Finset ι} : r • (∑x∈s,f x)=∑x∈s,r • f x`, `[AddCommMonoid N] [DistribSMul R N]`, `Algebra/BigOperators/GroupWithZero/Action.lean:51–58`.
- `Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} : (∑i∈s,f i) • x=∑i∈s,f i • x`, `[Semiring R] [AddCommMonoid M] [Module R M]`, `Algebra/Module/BigOperators.lean:23–38`.
- `Prod.fst_sum` and `Prod.snd_sum` are generated additive versions of `fst_prod`/`snd_prod` at `Algebra/BigOperators/Pi.lean:150–160`; they rewrite `(∑i∈s,f i).1/.2` to coordinate sums. `Fin.prod_const (n) (x) : (∏i:Fin n,x)=x^n` is `Algebra/BigOperators/Fin.lean:150`; or the pow integral API already gives `Fintype.card (Fin n)`.

## Feasible implementation plan, no new analytic dependency

1. Import qualified BV plus the accepted root QuadraticCharacteristic and `Mathlib.MeasureTheory.Integral.Pi` if not already transitively present. Apply BV to the exact ν,n,hn,y,E; install `IsProbabilityMeasure law` from its first component; rewrite actual ρ as `QY.map S` using its last component.
2. Apply `integral_map` to S and continuous K. Pointwise expand `K(S v)=∏i:Fin n,K(r⁻¹ • v i)` via coordinate sum/scalar rewrites, `Complex.ofReal_sum`, `Finset.sum_mul`, `Complex.exp_sum`; no norm conversion or Euclidean inner product occurs.
3. Use `integral_fintype_prod_eq_pow (ι := Fin n)` for `f v := K(r⁻¹ • v)` under actual law. Apply `integral_map` once more to `law=ν.map Y`; simplify `card_fin`. This proves the recommended actual factorization directly without constructing independence witnesses.
4. For the displayed scalar form, use real linearity of E on `(x,x²)=x • (1,0)+x² • (0,1)` and subtraction, obtaining `D(Y x)=a*x+b*x²-c`. Split exp via `Complex.exp_add`, extract the constant phase with `integral_const_mul`, unfold the accepted `quadraticChar` value. Frequency/center coefficients are explicit and normalization is r⁻¹; n≥1 supplies r>0 for division normalization. This is only algebra on actual integrands.
5. The already accepted `iid_quadraticChar_factor` is a fallback for the same raw-sum expression using the exact eval independence/IdentDistrib bundle above; no old proof/check needs replay. Prefer steps1–4 because BV already supplies the full finite-iid pushforward and the direct integral API removes the extra witnesses.
No essential API is missing. `charFunDual_pi` (CharacteristicFunction/Basic.lean:436–442) also supports Banach spaces via `StrongDual`, hence MAX-norm pairs, but adds an unnecessary functional wrapper. Do not use Hilbert `charFun`/inner-product formulas on the raw max pair. The present API intake is not a new independent proof review or kernel/axiom receipt.
Original Song/Edgeworth, quantitative weighted error/exterior, new-ρ Laplace and original B/C/D closure remain OPEN; an exact finite Fourier factorization closes only its stated dependency.

## Primary excerpt byte fingerprints

`Probability/Independence/Basic.lean` `93990423a0c169d9e45b19ae98f3f3ada7605d8541577daf815311aa43567769`; `Probability/IdentDistrib.lean` `6b570dd12c3fb9fb6adf0b9fd77189a1b6cd5e6c2648f4005f8dd9e82f3cd227`.
`MeasureTheory/Constructions/Pi.lean` `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`; `MeasureTheory/Integral/Pi.lean` `43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9`.
`MeasureTheory/Integral/Bochner/Basic.lean` `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`; `MeasureTheory/Measure/Map.lean` `7bae8f174146d4ef4055f79757c2a0a3af6a9090dda3d28ea17fbd54540e9593`.
`Analysis/Complex/Exponential.lean` `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`; `Analysis/Complex/Trigonometric.lean` `f6f2c2bb6da4d7dac960bef8d07dc2e337c474b417726c1fd15e30c6b74caafb`.
`Basic/Complex/BigOperators.lean` `3f4b675c1064ea9972ecf75d3247820ddacc6abc27611c31129d05f00c3dff1d`; `Algebra/BigOperators/Pi.lean` `0749ca84a35b19180bab5b2899893de40ac12db26d64678a595bb2628b767c59`.
`Algebra/BigOperators/GroupWithZero/Action.lean` `0bf8fff06fd5339c2f8ec50fd91df5e9eb98b106b91d1344e311a261af160dc6`; `Algebra/Module/BigOperators.lean` `57c80a0c6041ebb4a52445e6c5f27b1b363754b353358106c6a8802c7db2d3f9`.
`Algebra/BigOperators/Ring/Finset.lean` `fea364f581c3617c70802adff7fcddc40f5d60b53aa97541b418e4f33fac9a34`; `Algebra/BigOperators/Fin.lean` `b68854ca28f56de8a58284ae90ae2fc07887b75c720ad6e3a81fd58e6340da50`.
`MeasureTheory/Measure/CharacteristicFunction/Basic.lean` `3f90bba2eb49b295a4dd7bb80f5434f66c31ebdd2801a0bc82e5c9476c9b54e4`.
