# Exact API, source and accepted-evidence bindings for author161

This is source inspection and a mathematical interface proposal, not Lean
elaboration, a server observation, an independent review or acceptance.
Only drafts/oq4/unconditional-kernel-inputs-author-v1/ is written. No
implementation .lean file is created. No shared code, imports, snapshots,
receipts, coordination/REGISTRY.json or another author's files are changed.
No toolchain/import/object probe, remote call, Lean/build/cache/Git command,
cross-chat operation or extra agent is run. The concrete parent ACK required
by the assignment was sent after full exact154/156 source reads.

## 1. Author and project boundaries

Actual author161 context: gpt-6.1-sol, xhigh, fresh context, math-theorem.
Read full skill SKILL.md and required prompt-library/openai-workflow/
lean-verification references. Project instructions override the skill's
generic local-Lean discovery and concurrency defaults: no local Lean or
server probing is authorized for this proposal author; no active heavy
lease; all eventual Lean is server-only with the existing OQ4 lease.

Read AGENTS.md, SERVER.md and current TEAM ownership/resource sections,
current streamlined-acceptance document, takeover summary, and selected
REGISTRY fields. The current OQ4 owner is01a1669c-2422-7fa2-9f3c-16bb5bd2dfc4,
activated with old-writer release; active root is01a16680-f408-7391-8c52-d1d5041bda8b.
Actual prescribed model/effort match REGISTRY gpt-6.1-sol/xhigh. No new
coordinator, schedule, goal, thread, worktree or orchestration is created.

The pinned library/lean-toolchain was read as a FILE only:
leanprover/lean4:v4.36.0-rc1. SERVER.md pins mathlib
807d3836b165983210ee2ecf3cd28f239436949c. No runtime version claim is made.
Allowed axioms remain propext, Classical.choice, Quot.sound. This proposal
has no server kernel receipt and must not be described as mechanically checked.

## 2. Source and exact consumer bindings

Original read-only b01/proof01.md:
7c51246eb02a0d694a366ce3ab5a3a9cca03723160c1291bce29dd817f68bc38.
Read source lines1–41,316–351, covering K/Kv moment/scale/event scope and
the complete terminal P0–P2 source block. Source's original common-M
sequential scope is retained; no rowwise-finiteness replacement is proposed.

Complete154 source read and hash matched:
drafts/oq4/terminal-normalized-kernel-author-v1/TerminalNormalizedKernelLimit.lean
389252ae255a995174ff4345e4b5b34967cd87e8ab69c5b62713127cfdd9be8b;
618 LF lines, formal freeze bf1a80104cb1ee7812932127d7a54c274a0db7d8a3d900cc71a092b4f781fd6d.
The two final exact heads are in namespace Shao.OQ4.TerminalNormalizedKernelLimit:
varying_row_normalized_kernel_mass_tendsto and
varying_row_closedStrip_relative_asymptotic. New public2/public3 repeat
their moment/height/time inputs and conclusions literally and delete ONLY
Cq,Cs,hCq,hCs,hAC,hS. No new desired-limit hypothesis is introduced.

Complete156 source read and hash matched:
drafts/oq4/variance-kernel-asymptotic-author-v1/VarianceKernelAsymptotic.lean
6fdd2f8053b4f5cd7aa2a3fb6cd7c001aa42bd73c0022576adabbd5e23803a33;
373 LF lines. Namespace Shao.OQ4.VarianceKernelAsymptotic, final head
varying_row_variance_closedStrip_relative_asymptotic. New public4 repeats
its original-law/variance/moment/height/time inputs and literal final
original-law probability/exponent and deletes ONLY its supplied common
constants/signs/standardized-law primitive SAC. No private156 theorem is
called or presumed exported. No156 source/import/visibility edit is needed.

Both154 and156 remain LOCAL/unqualified. 154's spectral149/P1-150
qualification remains pending; qualified152 D8 status is inherited from
the parent's current exact update, not from older154 proposal prose.
Parent-supplied152 bindings: source prefix136f8b0f/434 LF, fresh independent
review160ebd00964, original objectd1f6631a, parent acceptance
e8f291feb226211757264b11bec333e81c3a972a13663800066bb7928cd03956.
This author neither repeats that old review nor probes/rechecks its object.

## 3. Exact root BE obligation: frozen, not yet qualified

coordination/public-survival-cdf-declaration-freeze.md was read for the
root ownership, constant1024 and exact theorem3 contract. Current SHA256:
674a688c637cc88eb5d3e1f5c43486725e8f1f64510a248ca9742b423a8db2fa.
Planned import Shao.Probability.BerryEsseen is a dependency, not currently
an accepted local library module. The exact used head is:

```lean
theorem Shao.Probability.iid_unitVariance_berryEsseen
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    |(Measure.pi (fun _ : Fin k => nu)).real
        {a : Shao.Path k |
          Shao.prefixSum a k / Real.sqrt (k : ℝ) ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤
      (1024 : ℝ) * (∫ z : ℝ, |z| ^ 3 ∂nu) / Real.sqrt (k : ℝ)
```

Invoke it on actual unit-variance ν, or on its ACTUAL standardized η
after private2 proves η probability, finite third moment, mean0/second1.
Do not invoke it directly on a variance-v original law. No theorem2
characteristic-function comparison or theorem4 arbitrary-variance result is
needed here. None of root's BE/Fourier proofs is duplicated. Its eventual
complete independent review/kernel/all-owned audit remain unpaid.

## 4. Accepted actual SP and old probability machinery

library/Shao/Probability/SpitzerLaplace.lean current source matches:
2faaf41caf7b0025e7171b764b468803688802f0177f02bfa0d4645a7c4890fb.
Read the actual namespace/imports and theorem at lines304 onward:

```lean
theorem Shao.Probability.actual_maximum_spitzer_laplace (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {L s : ℝ}
    (hL : 0 < L) (hs0 : 0 < s) (hs1 : s < 1) :
    Shao.OQ4.laplaceG (Shao.OQ4.maxLaplaceMean ν L) s =
      Real.exp (Shao.OQ4.laplaceW (Shao.OQ4.endpointLaplaceMean ν L) s)
```

The acceptedv57 receipt library/verification/receipt-v57.json, SHA256
d50766cd9b6cf9b7dcfea146f9e3c4e6d2c9430975f3bc3b9bbaa512d6441d94,
has status PASS and allowed_axioms exactly the standard whitelist. Its
selected reused_canonical_objects.Shao.Probability.SpitzerLaplace records:

    source_head=2044113b88476b1d3b3c47f3da8b5388b15b6c9a
    object SHA256=86fd91edc877ed88c94de93f109bb92ee01a5b74e36f8eb946714f98766d2f9b
    original object path=/root/rivermind-data/shao-lean-20261021/workspaces/
      common-cone-derivatives-v44/.lake/build/lib/lean/Shao/Probability/SpitzerLaplace.olean
    complete qualified review=coordination/common-spitzer-laplace-review.md
    review SHA256=ca4717969ee39b7d1b9003c68f02f53adad40b3132f6f0d4aa9c517a1ae075e5

This is reuse of saved accepted original-object evidence, not a fresh server
object observation or recompile. The theorem applies twice: ν and reflectedLaw ν.

Complete library ReflectedSurvival.lean and SpitzerKernelBounds.lean were
read. Current hashes, also matched in receipt-v57 source_files_sha256:

    ReflectedSurvival b54b2300ef77375782e60a541bcffd6bed05ac4de61a776c6e0fd5e189568809
    SpitzerKernelBounds e9d956ed03c634f5214c4fd85905d86fa51f6b1e5663a43ed9d3f143fcf5e014
    IntervalConcentration 491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875

The exact SpitzerKernelBounds.spitzer_kernel_probability_inputs statement
was read completely: its namespace is Shao.OQ4. It takes ν probability,
hSq,hCube,hsecond,C_BE,hC,hCDF,hSP,hSPneg and concludes

    1≤β ∧ 0≤sqrt2*exp(6+3*C_BE) ∧ 0≤1+2*C_BE ∧
    iidOneSidedSurvival ν β (sqrt2*exp(6+3*C_BE)) ∧
    iidIntervalConcentration ν β (1+2*C_BE).

At C_BE=1024 the only rewrite is exact arithmetic1+2*1024=2049.
No numerical exponential evaluation is proposed. The reflectedLaw value
is literally ν.map(x↦−x); the existing probability instance is public.
IntervalConcentration.third_absolute_moment_ge_one actual head/proof
lines103–117 was read: integrable square/absolute cube and second1 force
β≥1 by integrating3x²≤2|x|³+1. First/square integrability is derived locally
from h3; it is not a new public premise. Actual iidIntervalConcentration
and iidOneSidedSurvival definitions and lowerBlockSurvival were read.

## 5. Accepted moment interface and actual-map APIs

Complete accepted VarianceScaling.lean was read. Current source and the
acceptedv57 source map both match
f7e0b71c4a8ab372310c28e5ab5ceadc371eb00c7dccf2dca1a44cdf4cf70d21.
Saved accepted library/verification/oq4-rademacher-lattice-shift-all/receipt.json
provenance binds its original object SHA256
62a5ab0048f6fcb7bdc1ab47c647eda477711fb35c3bb58ae6e77db0250c89ee.
The selected exact source/object entries were actually parsed, not inferred.
The prior independent CORRECT review/source-bound kernel/all-owned receipt
is also documented by156 api-evidence.md. No old proof check is repeated.

We use PUBLIC Shao.OQ4.standardized_moments, whose exact head is:

```lean
theorem standardized_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hY : Integrable Y μ)
    (hYsq : Integrable (fun ω => (Y ω) ^ 2) μ)
    (hYcube : Integrable (fun ω => |Y ω| ^ 3) μ)
    (hmean : (∫ ω, Y ω ∂μ) = 0)
    (hsecond : (∫ ω, (Y ω) ^ 2 ∂μ) = σ ^ 2) :
    let Z : Ω → ℝ := fun ω => Y ω / σ
    Integrable Z μ ∧
      Integrable (fun ω => (Z ω) ^ 2) μ ∧
      Integrable (fun ω => |Z ω| ^ 3) μ ∧
      (∫ ω, Z ω ∂μ) = 0 ∧
      (∫ ω, (Z ω) ^ 2 ∂μ) = 1 ∧
      (∫ ω, |Z ω| ^ 3 ∂μ) = (σ⁻¹) ^ 3 * (∫ ω, |Y ω| ^ 3 ∂μ)
```

Instantiate Y=id,σ=sqrt(v), with hσ from v>0 and hsecond rewritten by
Real.sq_sqrt. This is an original-measure test-function theorem. The NEW
private helper supplies the actual mapped-law transfer with the following
pinned Mathlib APIs, reusing the primary source excerpts already recorded
and used in exact156; no new remote discovery/probe is needed:

* MeasureTheory/Function/L1Space/Integrable.lean355–357,
  SHA d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759:
  integrable_map_measure (hg:AEStronglyMeasurable f (μ.map g))
  (hf:AEMeasurable g μ) gives Integrable f (μ.map g) ↔ Integrable(f∘g)μ.
* MeasureTheory/Integral/Bochner/Basic.lean1076–1078,
  SHA66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670:
  integral_map (hφ:AEMeasurable g μ)
  (hfm:AEStronglyMeasurable f (μ.map g)) gives
  ∫y,f y ∂μ.map g=∫x,f(g x)∂μ.
* MeasureTheory/Measure/Typeclasses/Probability.lean124–141,
  SHA00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b:
  Measure.isProbabilityMeasure_map_iff (hf:AEMeasurable g μ) states
  IsProbabilityMeasure(μ.map g) ↔ IsProbabilityMeasure μ.

In every use g(x)=x/sqrt(v) is measurable, all three real test functions
id,square,absolute cube are Borel, and every required composed integrability
has been established by standardized_moments. Hence the actual β' is
(sqrt(v)⁻¹)³β, with finite third moment, mean0 and second1 under η.
The public final Kv head retains the original v∈[1/2,2] and common raw M.
Its finite product/event/height/time proofs remain inside156; only its final
public theorem is consumed. No156 private interface access is assumed.

## 6. Inventory and status

Proposed path: Shao/OQ4/UnconditionalKernelAsymptotic.lean, not yet created.
Eight exact imports and six exact heads are in declarations.lean.txt:
two private helpers, four public conclusions. ZERO additional global
values/instances/aliases are proposed. Parent must freeze ALL heads,
imports and zero-new-value inventory before any authorized implementation.

Proof-local literal constants are C_BE=1024, Cq=2049 and
Cs=Real.sqrt2*Real.exp(6+3*(1024:R)); no global definitions are needed.
The existing λ value isπ²/8, never redeclared. The finite product, map,
closed strip, prefix sum, normalized mass and actual β values stay literal.

Static file/line/hash checks on this proposal are documentary only. They do
not replace substantive parent freeze, complete fresh independent final
review, or exact-source server kernel/all-owned transitive-axiom receipt.
Root BE and154/156 qualification remain pending, with accepted152 update
preserved. Source K/Kv/general OQ4 and all other original open roots stay OPEN.

Author161's assigned next step is delivery and ACTUAL_FINAL_STOP/release.
No implementation or server action is authorized by this proposal itself.
