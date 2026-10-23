# Genuine finite CDF and nonzero-drift survival declaration freeze

Root fully read all three candidate/contract/route documents and approves the exact eight public heads and ONE new literal definition cdfFourierError. The reproduced existing lindleyPrefixSurvivalBound value is comparison evidence only and MUST NOT be redeclared. All quantifiers, closed events, explicit1024/drift4/source16exp/source48exp constants and literal actual laws are frozen.

Production ownership common_survival_cdf_candidate (same fresh prescribed sol/xhigh author) ONLY new Shao/Probability/BerryEsseen.lean, FiniteSurvival.lean, SourceLindleySurvival.lean and drafts/c12-survival-cdf/. Begin genuine atomic Fourier smoothing + actual iid CDF heads1-5, then continue6-8 directly. A Taylor bound/smoothing helper alone does not close actual CDF. First five form the first substantive CDF milestone. Author/reviewer separation and fresh complete final source/types/all definition values/private/generated/recursiveAX review remain mandatory.

No hCDF/hSP/survival/atomless/symmetry/centering premise may be added. Centering is only actual intermediate pushforward and the nonzero walk drift is restored. General survival retains exp4drift and m0/r0/closed atoms. The source law has only the original finite2/mean0/normalization/truncation budget, fixed at x with conditional nonzero mean; epsilon<=1/2 stays. The original raw third moment is not imposed. No C1 circularity or qualitativeCLT rate substitution. Constant1024 is justified by the complete explicit sinc4 normalization/bandwidth, atomic CDF difference Fourier inversion, monotone absorption, quantitative Taylor/power comparison and actual Gaussian calculation in the route, each still must be formally proved.

Frozen parent2044113b88476b1d3b3c47f3da8b5388b15b6c9a in released common-cone-derivatives-v44 branchfeat/common-chord-cone-derivatives. Exact Spitzer producer now acceptedv57 and unchanged. Consume qualified old interfaces/values/scopes/objects, no oldproof/check replay or OQ4 implementation change. Any additional global definitions INCLUDING private require full literal-value addendum before implementation; proof-local values/helper theorems allowed.

All source UTF8 LF before first check. All Lean/heavy server-only CPU10-13/M8192/j4/autoImplicitfalse/root-heavy.lock, direct exit captured before any display, first whole success emits-o. No new per-command/preflight grants; repair proof/API errors directly. No sorry/admit/newaxiom/unsafe/native_decide. Root publishes/integrates after exact checks and independent review; original roots stayOPEN.

Bindings:
- drafts/c12-survival-cdf/candidate-declarations.md SHA256 2113b671d2c8cf1ecf306c031972bbefc40cff91f819c249171e99b1a83c3769
- drafts/c12-survival-cdf/source-contract.md SHA256 3dc281f7b05477a9e32665059b09e5018755de8c83ffdb23f86cbb0ed0e621dd
- drafts/c12-survival-cdf/proof-route.md SHA256 9dbdb16e0d82eedd7654260dd187d0436a14e258457bfaf51b7818d6ba60b400

## Exact frozen declarations

# Genuine finite-step CDF and nonzero-drift survival — candidate v1

Status: `CANDIDATE_NOT_FROZEN / FORMAL_IMPLEMENTATION_INCOMPLETE`.
Owner: `/root/common_survival_cdf_candidate`, actual model `gpt-6.1-sol`, effort `xhigh`.
This is a candidate contract, not Lean source, a server check, or an independent review.
Root must read and freeze exact declarations before implementation. The candidate author
must not perform the eventual independent final review.

## Proposed substantive milestones

1. `Shao.Probability.BerryEsseen`: prove the Fourier smoothing theorem and the actual
   finite iid CDF statements below. A Taylor estimate alone does **not** pay `hCDF`.
2. `Shao.Probability.FiniteSurvival`: combine that genuine CDF producer with the accepted
   actual Spitzer identity to prove nonzero-drift closed survival, with no CDF/SP inputs.
3. `Shao.Probability.SourceLindleySurvival`: pay the precise existing source predicate
   and consume the already accepted second-moment theorem without its survival premise.

These are new common modules owned by root, not edits to the OQ4 lane. The names are
proposed new declarations, not assertions that matching Mathlib APIs already exist.
No implementation or source-bound gate has been run for any of them.

## Conventions and literal values

All heads below are in `namespace Shao.Probability`, with:

```lean
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
```

`Shao.Path k`, `Shao.prefixSum`, `Shao.maxWithZero`, `lindleyRegulator`,
`lindleyPrefixSurvivalBound`, `Shao.OQ4.standardNormalCDF` and the actual product laws
retain their accepted definitions. There is exactly **one** proposed new global
definition; all other auxiliary objects may be proof-local. Any additional global
definition, including a private one, needs its literal-value addendum before production.

```lean
noncomputable def cdfFourierError
    (mu nu : Measure ℝ) (t : ℝ) : ℝ :=
  ‖MeasureTheory.charFun mu t - MeasureTheory.charFun nu t‖ / |t|
```

At `t = 0` this value is `0` by real division. Integrability near zero must be proved;
the totalized value is not a substitute for that proof.

The quantitative CDF constant is the literal real number `1024`. No choice function
selects an unspecified Berry–Esseen constant. The deliberately nonoptimal downstream
constants are `2 * Real.exp (6 + 3 * (1024 : ℝ))`, drift exponent coefficient `4`,
source survival constant `16 * Real.exp (7 + 3 * (1024 : ℝ))`, and source square-moment
constant `48 * Real.exp (7 + 3 * (1024 : ℝ))`.

The smoothing proof's exact proof-local density is
`fun u : ℝ => (3 / (2 * Real.pi)) * (Real.sinc u) ^ 4`.
Its Fourier bandwidth in the natural characteristic-function convention is `4`.
For a requested cutoff `T`, use noise `4 * U / T` and shift `16 / T`.
These choices are part of the route; there is no assumed smoothing distribution.

## Imports: candidates with inspected, existing paths

For milestone 1:

```lean
import Shao.Probability.MeasurablePath
import Shao.OQ4.IntervalConcentration
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Prod
```

Milestone 2 additionally needs the accepted `Shao.Probability.SpitzerLaplace` and
`Shao.OQ4.FiniteSurvivalLaplace`; milestone 3 additionally needs
`Shao.Probability.SourceLindleyRegulatorSecondMoment`. Existing read-only package
availability remains a root responsibility; these imports have not been compiled.

## 1. Actual Fourier-to-CDF smoothing, finite first moments and closed atoms

This is a theorem to prove from Fourier analysis. It must not become an input to the
final probability producer. Only the comparison law has a Lipschitz CDF; the first law
may have arbitrary atoms. The conjunction explicitly pays the real integral's existence.

```lean
theorem cdf_error_le_fourier_smoothing
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu1 : Integrable (fun z : ℝ => z) mu)
    (hnu1 : Integrable (fun z : ℝ => z) nu)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ,
      |nu.real (Set.Iic x) - nu.real (Set.Iic y)| ≤ L * |x - y|)
    (T : ℝ) (hT : 0 < T) :
    IntegrableOn (cdfFourierError mu nu) (Set.Icc (-T) T) ∧
      ∀ x : ℝ,
        |mu.real (Set.Iic x) - nu.real (Set.Iic x)| ≤
          2 * (∫ t : ℝ in Set.Icc (-T) T, cdfFourierError mu nu t) +
            64 * L / T
```

## 2. Actual finite iid characteristic-function producer

No assumed product identity, independence, Taylor remainder, or Gaussian comparison
appears as a premise. The target is the actual normalized finite-product pushforward.
This head is useful evidence on the way to CDF, but is not itself a CDF certificate.

```lean
theorem iid_unitVariance_charFun_error
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (hsecond : (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (ht : |t| ≤ Real.sqrt (k : ℝ) /
      (2 * (∫ z : ℝ, |z| ^ 3 ∂nu))) :
    let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂nu
    let P : Measure (Shao.Path k) :=
      Measure.pi (fun _ : Fin k => nu)
    let law : Measure ℝ :=
      P.map (fun a : Shao.Path k =>
        Shao.prefixSum a k / Real.sqrt (k : ℝ))
    ‖MeasureTheory.charFun law t -
        (Real.exp (-(t ^ 2) / 2) : ℂ)‖ ≤
      beta * |t| ^ 3 / Real.sqrt (k : ℝ) * Real.exp (-(t ^ 2) / 8)
```

## 3. The exact centered/unit-variance CDF obligation is produced

Finite third moment internally pays first and second integrability. Genuine centering
and unit second moment are explicit and must be checked before applying this head.
It directly supplies the accepted OQ4 `hCDF` with `C_BE = 1024`.

```lean
theorem iid_unitVariance_berryEsseen
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

## 4. Arbitrary mean and positive variance: actual centered sums

This is a map/moment specialization of the preceding theorem, not an application of
the unit-variance head to an uncentered law. It pays the actual coordinate map and the
finite-product pushforward internally.

```lean
theorem iid_centered_berryEsseen
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂nu
    |(Measure.pi (fun _ : Fin k => nu)).real
        {a : Shao.Path k |
          (Shao.prefixSum a k - (k : ℝ) * mu) /
            (Real.sqrt V * Real.sqrt (k : ℝ)) ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤
      (1024 : ℝ) * m3c /
        ((Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ))
```

## 5. The actual raw-sum CDF with its unavoidable drift error

The additional term depends on `sqrt k`; it cannot be hidden in a uniform centered
`hCDF`. This exact dependence is used in the Spitzer series.

```lean
theorem iid_uncentered_berryEsseen
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂nu
    |(Measure.pi (fun _ : Fin k => nu)).real
        {a : Shao.Path k |
          Shao.prefixSum a k /
            (Real.sqrt V * Real.sqrt (k : ℝ)) ≤ x} -
        Shao.OQ4.standardNormalCDF x| ≤
      (1024 : ℝ) * m3c /
          ((Real.sqrt V) ^ 3 * Real.sqrt (k : ℝ)) +
        |mu| * Real.sqrt (k : ℝ) / Real.sqrt V
```

## 6. Genuine finite survival for nonzero drift, all closed thresholds

No CDF, SP, survival, atomlessness, symmetry, or centering input. Both `m = 0` and
`r = 0` are included. The coefficient `4` explicitly retains the source's drift
exponential. The third moment in this general theorem is centered; it is converted
to the source raw third moment only in the source theorem below.

```lean
theorem iid_closed_survival_nonzero_drift
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (h3 : Integrable (fun z : ℝ => |z| ^ 3) nu)
    (hV : 0 < variance (id : ℝ → ℝ) nu)
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    let mu : ℝ := ∫ z : ℝ, z ∂nu
    let V : ℝ := variance (id : ℝ → ℝ) nu
    let m3c : ℝ := ∫ z : ℝ, |z - mu| ^ 3 ∂nu
    (Measure.pi (fun _ : Fin m => nu)).real
        {a : Shao.Path m | Shao.maxWithZero a ≤ r} ≤
      (2 * Real.exp (6 + 3 * (1024 : ℝ))) *
        min 1 ((r + m3c / V) /
          (Real.sqrt V * Real.sqrt ((m + 1 : ℕ) : ℝ))) *
        Real.exp (4 * (|mu| * Real.sqrt (m : ℝ) / Real.sqrt V))
```

## 7. Pay the literal existing source survival predicate

This is the first head that removes the accepted square-moment consumer's actual
unpaid probability premise. Original zero mean is required only for `nu`; the
conditional `rho` is permitted to have nonzero mean. The source law stays fixed at
`x`; there is no new conditioning as a threshold or future `y` changes.

```lean
theorem sourceTruncation_lindleyPrefixSurvivalBound
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (N : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (N : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu N x ≤ epsilon ^ 3 / 8) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    lindleyPrefixSurvivalBound rho N
      (16 * Real.exp (7 + 3 * (1024 : ℝ)))
```

The literal existing predicate, copied here for semantic comparison only, is:

```lean
-- Existing accepted definition, alpha-renamed nu; do not redeclare it.
def lindleyPrefixSurvivalBound
    (nu : Measure ℝ) (N : ℕ) (C : ℝ) : Prop :=
  let V : ℝ := variance (id : ℝ → ℝ) nu
  let gamma : ℝ := (∫ z : ℝ, |z| ^ 3 ∂nu) / V
  ∀ k : ℕ, 1 ≤ k → k < N → ∀ r : ℝ, 0 ≤ r →
    (Measure.pi (fun _ : Fin k => nu)).real
        {b : Shao.Path k | Shao.maxWithZero b ≤ r} ≤
      C * min 1 ((r + gamma) /
        (Real.sqrt V * Real.sqrt ((k + 1 : ℕ) : ℝ)))
```

## 8. Actual source square moment with no survival premise

This consumes the accepted `sourceTruncation_lindleyRegulator_second_moment_of_survival`
at the exact newly proved predicate. It does not repeat the accepted reversal,
disintegration, first-step, or integrability proofs.

```lean
theorem sourceTruncation_lindleyRegulator_second_moment
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (N : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) nu)
    (hnorm : (N : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1)
    (hmean : (∫ z : ℝ, z ∂nu) = 0)
    (x epsilon : ℝ) (hx : 0 ≤ x)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hR : Shao.truncationBudget nu N x ≤ epsilon ^ 3 / 8) :
    let rho : Measure ℝ :=
      ProbabilityTheory.cond nu {z | |z| ≤ epsilon / (1 + x)}
    let V : ℝ := variance (id : ℝ → ℝ) rho
    let m3 : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
    let P : Measure (Shao.Path N) :=
      Measure.pi (fun _ : Fin N => rho)
    ∀ j : Fin N,
      Integrable (fun a : Shao.Path N => (lindleyRegulator a j) ^ 2) P ∧
        (∫ a : Shao.Path N, (lindleyRegulator a j) ^ 2 ∂P) ≤
          (48 * Real.exp (7 + 3 * (1024 : ℝ))) * m3 /
            (Real.sqrt V * Real.sqrt ((j.val + 1 : ℕ) : ℝ))
```

## Boundaries and acceptance

- `k ≥ 1` is mandatory for standardized sums. Survival includes the empty path.
- The general survival theorem requires strictly positive actual variance. The source
  theorem pays this from the original normalization and accepted truncation budget.
- Closed CDFs and closed maxima keep all source atoms, including the zero-record atom.
  Strict events are bounded by closed-event inclusion. No strict/closed equality is used.
- No density, finite third moment, zero mean, or unit variance is imposed on the
  original source law beyond the displayed assumptions. Its retained law has all needed
  moments by accepted source truncation results.
- Weighted source square sums, original near-zero survival after deletion/truncation,
  complete C1/C2, and all original open roots are not closed by this candidate.
- All declarations/values above are uncompiled and unreviewed. Acceptance requires a
  qualified independent complete source-to-statement/proof review and an exact-source
  server kernel/all-owned transitive-axiom receipt, allowing only `propext`,
  `Classical.choice`, and `Quot.sound`. No local Lean invocation is authorized.
