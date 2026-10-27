# Unit 230 primary source map and implementation route

This records a Stage 1 route, not a new proof implementation or a new review of
the qualified old producer. Only the unit 230 candidate is proposed for a new
freeze. The literal truncation argument throughout is `z*ξ_i`.

## Primary source read and scope

The entire local primary `C:/game/shao/current/oq56/inputs02/p51.md`, all 355
LF-terminated lines, was read. It is itself marked
`UNCERTIFIED_REPAIR_CANDIDATE`; this unit proves a precisely delimited
elementary quantitative ingredient rather than upgrading that document's
other claims. Existing external Shao-Zhou attribution remains intact.

| Primary portion | Candidate assertion or restriction |
| --- | --- |
| S1, `Eg=0, Eg²=1` in the original model | Context for later consumers; neither is needed for this generic budget theorem, so neither is added. |
| S3, displayed S19, `L_{n,y} ≤ β_p y^p n^{-(p-2)/2}` | The unconditional rate, with the same source threshold denoted `z`. |
| S19, `max_i δ_{i,y}=L_{n,y}/n` | Each coordinate has the same marginal scalar integral and `L=n*δ_i`, under the literal finite IID product. |
| S19, shrinking c to leave budget room | An explicit model-independent `c=(min(1/2,cBudget)/2)^(1/p)` and strict inequalities, rather than taking the desired margins as assumptions. |
| S19, `1 ≤ y ≤ c β_p^{-1/p} n^{(p-2)/(2p)}` | The positive-beta branch uses this exact closed source-z window. |
| S4, `ξ_i=g_i/√n`, actual source `F` and strict original margins | The exact original normalized coordinates and source budget are exposed; no encoded sequence or epsilon-transfer conclusion is asserted. |
| S4, `F(t)=t² 1_{|t|>1}+|t|³ 1_{|t|≤1}` | Qualified `Shao.truncationF t=t²*min |t| 1` has these same values and boundary convention. |
| S5 compact `1+z` cost | Kept distinct. `OriginalCompactPMomentCost` is only a related qualified reference and is not the source-z producer. |

## Exact qualified scalar API used

The complete actual public declaration below was read in the curated source.
Its existing qualification is reused, with no new review or old Lean replay.
The source hash is bound in `INPUT-BINDINGS.json` and matches unit170's
qualified source. The imported file contains unrelated stronger consumers;
unit 230 calls only this unconditional scalar theorem.

```lean
theorem Shao.OQ6.ActualPhysicalCompactCDF.normalized_observation_truncation_budget_le_rpow_moment
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (p : ℝ) (hp2 : 2 ≤ p) (hp3 : p ≤ 3)
    (hgp : Integrable (fun o => Real.rpow |g o| p) μ)
    (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 0 ≤ y) :
    let N : ℝ := (n : ℝ)
    let q : ℝ := Real.sqrt N
    let β : ℝ := ∫ o, Real.rpow |g o| p ∂μ
    let L : ℝ := N * (∫ o, Shao.truncationF ((1 + y) * (g o / q)) ∂μ)
    Integrable (fun o => Shao.truncationF ((1 + y) * (g o / q))) μ ∧
      L ≤ β * Real.rpow (1 + y) p * N / Real.rpow q p ∧
      L ≤ β * Real.rpow (1 + y) p /
        Real.rpow N ((p - 2) / 2)
```

The exact intended arguments are
`μ g hg hg2 p hp2.le hp3 hgp n hn (z - 1) hy`, where `hy : 0 ≤ z-1`
comes from `1 ≤ z`. The arithmetic identity `1+(z-1)=z` changes both the
integrability assertion and final rate to the source-z scale. The scalar
API's `N` is `(n:ℝ)` and its `q` is the candidate's `N=√n`; these names
must not be confused. Its middle denominator estimate is not needed.

`Shao.Probability.TruncationIntegrals` supplies the genuine scalar budget
integration layer, not a special IID marginal theorem. Its complete source
was read. In particular its exact definition and public integrability API are:

```lean
noncomputable def Shao.truncationBudget
    (ν : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * ∫ z : ℝ, Shao.truncationF ((1 + t) * z) ∂ν

theorem Shao.integrable_truncationF_mul (ν : Measure ℝ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (a : ℝ) :
    Integrable (fun z : ℝ => Shao.truncationF (a * z)) ν
```

The complete genuine pointwise definition read in
`Shao.Basic.TruncationBudget` is
`def Shao.truncationF (z : ℝ) : ℝ := z^2 * min |z| 1`.
Its qualified `truncationF_nonneg (z : ℝ) : 0 ≤ Shao.truncationF z`
is used for every coordinate and total nonnegativity. The scalar theorem
already packages the needed L2 and p-moment domination; no compact CDF
assumption or hSZ callback is needed.

## Exact finite-product transport route

Let `f : Ω → ℝ := fun o => Shao.truncationF (z*(g o/N))`, with its entire
typed right-hand side. Its measurability follows from qualified continuity of
`truncationF` and `(hg.div_const N).const_mul z`; its integrability is the
first component of the scalar API call just described.

For each `i : Fin n`, use the standard product construction with the exact
invocation `measurePreserving_eval (μ := fun _ : Fin n => μ) i`. Its result
is `MeasurePreserving (fun ω : Fin n → Ω => ω i) P μ`. Its
`integrable_comp_of_integrable` applied to the genuine scalar integrability
gives the required integrability of `f(ω_i)`. The map identity is the same
result's `.map_eq`. The integral identity is `integral_map` applied to the
coordinate map's `.measurable.aemeasurable` and `f`'s
`.aestronglyMeasurable`, followed by that `.map_eq`. This exact transport
pattern is present in the qualified `ActualUncenteredCompactCDF` source,
lines 270-279, and qualified `QuadraticFullNoise`, lines 211-216. No
standard-Borel condition is required.

Definitional reduction of `ξ,projectionTest,δ,scalarBudget` therefore gives
`δ_i=scalarBudget`. Summing a constant over `Fin n` with
`Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`, and
`nsmul_eq_mul` gives `L=n*scalarBudget`; substituting each marginal identity
gives `L=n*δ_i`. `Shao.truncationF_nonneg` with `integral_nonneg` gives
each `0≤δ_i`, and `Finset.sum_nonneg` gives `0≤L`. The scalar API's final
bound now applies to exactly this `L`.

The useful summand comparison is `δ_i ≤ L`, obtained by
`Finset.single_le_sum` and the other summands' nonnegativity (or by
`L=n*δ_i`, `n≥1`). This does not divide by `L` or `δ_i`.

## Real-power route and checked API names

These are actual mathlib names and mathematical forms used in the qualified
local sources, rather than guessed natural-power substitutes. Their
applications below use only nonnegative bases and positive denominators.
The pinned Mathlib revision is `807d3836b165983210ee2ecf3cd28f239436949c`.
No local Lean probe or independent Mathlib source download was performed.

| Actual name | Form required here | Local qualified use read |
| --- | --- | --- |
| `Real.rpow_nonneg` | `0≤x → 0≤rpow x r` | `ActualPhysicalCompactCDF` and `ConditionalStandardizedPMoment` |
| `Real.rpow_pos_of_pos` | `0<x → 0<rpow x r` | `ActualPhysicalCompactCDF` |
| `Real.rpow_le_rpow` | nonnegative x, `x≤y`, `0≤r` imply `rpow x r≤rpow y r` | `OriginalCompactPMomentCost` helper and `BoundedProductEnvelopeTails` |
| `Real.mul_rpow` | nonnegative x,y: `rpow (x*y) r=rpow x r*rpow y r` | `TruncationIntegrals`; invocation there is `Real.mul_rpow (z := p) hx hy` |
| `Real.rpow_mul` | nonnegative x: `rpow x (r*s)=rpow (rpow x r) s` | `ActualPhysicalCompactCDF`, and `ConditionalStandardizedPMoment` root identities |
| `Real.rpow_one` | `rpow x 1=x` | the same scalar API normalization |
| `Real.rpow_neg_one` | `rpow x (-1)=x⁻¹` | `QuadraticFullNoiseMarkedLowRegions`, lines 224-226 |
| `Real.zero_rpow` | nonzero r: `rpow 0 r=0` | `ConditionalStandardizedPMoment` and `CanonicalProductEnvelopeTails` |

Set `m=min(1/2,cBudget)` and `d=m/2` only as prose abbreviations, not
additional public lets. `cBudget>0` gives `0<m`, `0<d`, and `d<m`. Since
`p>2`, `p>0` and `p≠0`. By `Real.rpow_pos_of_pos`, `0<c`. The root-power
identity follows by reversing `Real.rpow_mul d_nonneg (1/p) p`, the exact
arithmetic `(1/p)*p=1`, and `Real.rpow_one`. Thus `c^p=d<m`.

In the positive-beta window put `a=(p-2)/(2*p)` and `b=(p-2)/2` only in
this explanation. From the window and `p>0`, `Real.rpow_le_rpow` gives
`z^p ≤ (c*β^(-1/p)*n^a)^p`. Repeated `Real.mul_rpow` separates the three
nonnegative bases. Reverse `Real.rpow_mul` at beta and at n and use the
exact arithmetic identities

`(-1/p)*p=-1` and `((p-2)/(2*p))*p=(p-2)/2`.

Then `Real.rpow_neg_one` gives
`z^p ≤ c^p*β⁻¹*n^b`. The denominators `β` and `n^b` are strictly positive
because `β>0` and `(n:ℝ)>0`. Multiplying by beta and dividing by `n^b`
therefore proves the quantitative consequence
`β*z^p/n^b ≤ c^p`, using ordinary field cancellation. Together with the
unconditional scalar rate this proves `L≤c^p`.

Consequently `δ_i≤L≤c^p<m≤1/2`. Also `L≤c^p<m≤cBudget`, and `z≥1`
gives `1≤z²`, hence `cBudget≤cBudget*z²`. The final total-budget bound is
strict. There is no strictness loss at the upper window endpoint because
strictness comes from the explicit half-margin in c, not from a strict
window assumption.

If `β=0`, the unconditional rate yields `L≤0`, so nonnegativity yields
`L=0`. Each `δ_i≤L` then gives `δ_i=0`. This branch never cancels beta,
evaluates an inverse as if nonzero, or treats a nonintegrable integral as
zero. Since `c>0`, its pth power is positive, and the same strict margins
follow directly. If beta is nonzero, its previously proved nonnegativity
gives the positive branch; no negative beta case exists.

## Remaining work and exact limitations

No mathematical power/window obstruction was identified in Stage 1. The
route uses finite sums, a qualified scalar source-z instantiation, and
nonnegative real-power algebra. The exact Lean elaboration of this candidate,
its eventual implementation, independent complete final review, server kernel
check, and all-owned transitive-axiom audit are still required. No such check
is claimed here. A successful old producer receipt is reused as a dependency,
not represented as a kernel receipt for this new statement.

The result supplies original quantitative input for a later stability
consumer. It does not construct a coding witness, prove a weighted limit,
control any CDF, pay a zero event, instantiate an external Shao-Zhou theorem,
or close an OQ56 root. Units 228 and 229 were not read, imported, copied,
renamed, retried, or used.
