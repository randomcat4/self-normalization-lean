# Public complex boundary amplitude declaration freeze

Root approves the exact 3 literal public definitions and 3 complete theorem bundles below. All candidate and contract mathematics was completely read once before freezing. Production ownership: common_complex_amplitude_author; only Shao/Probability/SourceComplexBoundaryAmplitude.lean and its drafts. Frozen parent 6dbd8394e336af1da55d6bf7c3d3bc3fd87f6a49 in common-short-kernel-v51.

Actual original cutoff, split window Delta=(1+lambda*y)^(-1), derivative envelope c=1/256 through order 32, genuine L1, sharp localized two Fourier norms and outside32 are required exactly. No assumed amplitude/derivative/decay/Fourier-bound premises. All C1/C2 roots, contour shifts, growing-kernel and probability dependencies stay OPEN. Additional global definitions (including private) require complete literal-value addendum before implementation; proof-local terms and helper theorems may implement these frozen statements.

Reuse the qualified SourceMarkFourierNorms private Sobolev constant by its complete name and existing object; do not edit or recompile that accepted source. Only a concrete source-level access failure justifies a frozen bridge interface. No new axioms or weakened assumptions. First complete source check emits -o; source bytes UTF-8 LF before first check. Targeted remote checks use the shared root-heavy.lock, CPU10-13, -M8192 -j4 -DautoImplicit=false, capturing direct rc before any log tail. Fresh complete independent final source/types/definition-values/axiom review remains required.

Bindings:
- drafts/c12-complex-amplitudes/candidate-declarations.md SHA256 2e4b2b4176c747c532ab02b288848e67e7beab8f4c862a256fce3d2d3ff8d3c1
- drafts/c12-complex-amplitudes/source-contract.md SHA256 7025db48dac133182d6b8875d5e2cf26a5ff8d19d6434026e60b49b134e97d6d
- drafts/c12-complex-amplitudes/accepted-sobolev-dependency.md SHA256 365ca1e056d05c2e970fe2d5860da6aac23d18dc30c633d3737090f9d39592fd

## Exact declarations

# Actual complex-boundary amplitudes: candidate declarations

State: CANDIDATE, not frozen, not implemented, not Lean checked. Author:
`/root/common_complex_amplitude_author`, fresh `gpt-6.1-sol` / `xhigh`.
Only this draft directory is owned. Root must read and freeze the exact
selected declarations before any production file or Lean command.

Proposed module: `Shao.Probability.SourceComplexBoundaryAmplitude`.
There are three actual definitions and three substantive theorem bundles.
The first two bundles form a useful standalone amplitude milestone. The
third bundle additionally needs the precise reusable Sobolev API seam
recorded in `source-contract.md`; it is not already supplied by the public
global norm theorem. No amplitude derivative, decay, or Fourier estimate is
an input to any bundle below.

## Imports, namespace, and all new definition values

```lean
import Shao.Probability.SourceFourierTestKernel
import Shao.Probability.SourceKernelAmplitudeFamily
import Shao.Probability.SourceMarkFourierNorms
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory
open scoped ContDiff FourierTransform Topology

noncomputable def sourceComplexSplitTheta (t : ℝ) : ℝ :=
  Real.smoothTransition ((t + 1) / 2)

noncomputable def sourceComplexBoundaryAmplitude
    (j : Fin 2) (y N lam r : ℝ) : ℝ :=
  if j = 0 then
    sourceKernelCutoff r *
      sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹) *
      Real.exp (-lam * y * (Real.sqrt r - Real.sqrt N))
  else
    sourceKernelCutoff r *
      (1 - sourceComplexSplitTheta ((r - N) / (1 + lam * y)⁻¹)) *
      Real.exp ((lam * y / Real.sqrt N) * r - lam * y * Real.sqrt r)

noncomputable def sourceComplexBoundaryMark
    (j : Fin 2) (y N lam u v : ℝ) : ℂ :=
  sourceMarkExponential (sourceComplexBoundaryAmplitude j y N lam) y (-u) v
```

The accepted `sourceKernelCutoff` above is used literally. It is not
redefined or shadowed. All real square roots and divisions are totalized
Mathlib operations; the conclusions cover every real `r`, including
off-support singular locations. No new global cutoff or tail window is
introduced. The `Fin 2` branch `j = 0` is the source's `a₀`; `j = 1` is
`a₁`. All other definitions and theorem names listed here are new.

## Bundle 1: the actual fixed smooth split, including its finite jet budget

```lean
theorem sourceComplexSplitTheta_data :
    ContDiff ℝ ∞ sourceComplexSplitTheta ∧
      (∀ t : ℝ,
        0 ≤ sourceComplexSplitTheta t ∧ sourceComplexSplitTheta t ≤ 1) ∧
      (∀ t : ℝ, t ≤ -1 → sourceComplexSplitTheta t = 0) ∧
      (∀ t : ℝ, 1 ≤ t → sourceComplexSplitTheta t = 1) ∧
      ∃ M : ℝ, 0 < M ∧
        ∀ (k : ℕ), k ≤ 32 → ∀ t : ℝ,
          |iteratedDeriv k sourceComplexSplitTheta t| ≤ M
```

`M` belongs to this one fixed literal theta. In particular it precedes
`k,t` and all later `y,N,lam`. The zero-order bound is included. This
theorem does not assert compact support of theta itself.

## Bundle 2: actual localized amplitudes and genuine derivative L1 payment

```lean
theorem sourceComplexBoundaryAmplitude_localized :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y N lam : ℝ),
        2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 →
        y / Real.sqrt N ≤ lam →
          let Delta : ℝ := (1 + lam * y)⁻¹
          let s : ℝ := lam * y / Real.sqrt N
          0 < Delta ∧ Delta ≤ 1 ∧
            (∀ r : ℝ,
              Real.exp (-lam * y * Real.sqrt N) *
                  sourceComplexBoundaryAmplitude 0 y N lam r +
                Real.exp (-s * r) *
                  sourceComplexBoundaryAmplitude 1 y N lam r =
                sourceKernelCutoff r * Real.exp (-lam * y * Real.sqrt r)) ∧
            ∀ j : Fin 2,
              let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
              ContDiff ℝ ∞ a ∧ HasCompactSupport a ∧
                (∀ r : ℝ, 0 ≤ a r) ∧
                tsupport a ⊆ tsupport sourceKernelCutoff ∩
                  (if j = 0 then Set.Ici (N - Delta)
                    else Set.Iic (N + Delta)) ∧
                ∀ (k : ℕ), k ≤ 32 →
                  Integrable (iteratedDeriv k a) ∧
                    (∀ r : ℝ,
                      |iteratedDeriv k a r| ≤
                        C / Delta ^ k *
                          Real.exp (-((1 / 256 : ℝ) * |r - N| / Delta))) ∧
                    (∫ r : ℝ, |iteratedDeriv k a r|) ≤
                      C * Delta / Delta ^ k
```

The one finite constant `C` precedes all growing parameters, branches,
orders through 32, and points. The fixed decay rate is explicitly
`1/256`. A finite maximum over the 33 required orders is allowed; this is
stronger than a separate `C_k` at each of these orders. `k = 0` supplies
actual amplitude integrability and its `O(Delta)` L1 norm. The displayed
recombination is only an exact real-amplitude algebra identity. It is not
a contour-shift or differentiated inversion theorem.

## Bundle 3: actual negative-phase marks, sharp localized norms and outside32

```lean
theorem sourceComplexBoundaryMark_localized_norms :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y N lam : ℝ),
        2 ≤ y → (1 / 16 : ℝ) ≤ N → N ≤ 7 →
        y / Real.sqrt N ≤ lam →
          let Delta : ℝ := (1 + lam * y)⁻¹
          ∀ (j : Fin 2) (u : ℝ),
            let a : ℝ → ℝ := sourceComplexBoundaryAmplitude j y N lam
            let B : ℝ → ℂ := sourceComplexBoundaryMark j y N lam u
            (∀ v : ℝ,
              B v = ∫ r : ℝ, (a r : ℂ) *
                Complex.exp
                  (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I))) ∧
              (∀ v : ℝ,
                Integrable (fun r : ℝ => (a r : ℂ) *
                  Complex.exp
                    (-(((u * y * Real.sqrt r + v * r : ℝ) : ℂ) * Complex.I)))) ∧
              Continuous B ∧
              Integrable (fun v : ℝ => ‖B v‖) ∧
              Integrable (fun v : ℝ => |v| * ‖B v‖) ∧
              (∫ v : ℝ, ‖B v‖) ≤
                C * (1 + Delta * Real.sqrt (y * |u|)) ∧
              (∫ v : ℝ, |v| * ‖B v‖) ≤
                C * (Delta⁻¹ + y * |u|) *
                  (1 + Delta * Real.sqrt (y * |u|)) ∧
              ∀ aStar : ℝ, 0 < aStar → aStar * y ≤ (1 / 16 : ℝ) →
                let A : Set ℝ := {v : ℝ | |u| / aStar < |v|}
                IntegrableOn (fun v : ℝ => ‖B v‖) A ∧
                  (∫ v in A, ‖B v‖) ≤
                    C / (1 + Delta * |u| / aStar) ^ 31

end Shao.Probability
```

The outside bound uses the fixed necessary source order `K₀ = 32`, hence
the exponent `1-K₀ = -31`. The smallness constant `1/16` is explicit and
the cone threshold is `|u|/aStar`, matching the existing accepted outside
normalization. The constant precedes `aStar`. No sine transform, extra
raw-moment assumption, weighted outside estimate, whole-u integration,
contour identity, complex kernel, noise factor, region probability, or
C1/C2 conclusion is claimed. Replacing `u` by `-u` gives the opposite
spatial phase without another producer.

## Freeze boundary

All theorem blocks above are complete candidate heads, without proof
placeholders. There is no Lean source file. Local or server elaboration
has not been run. Root can freeze Bundles 1-2 as the first actual amplitude
milestone while leaving Bundle 3 unimplemented until the accepted
Sobolev-head access seam is settled. Bundle 3 must not be replaced by the
coarser global bound and then reported as localized source(b).
