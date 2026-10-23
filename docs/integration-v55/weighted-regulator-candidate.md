# Actual prefix-energy weighted Lindley regulators — candidate declarations

State: `CANDIDATE_COMPLETE_NOT_FROZEN_NOT_PROVED`.
Owner: `/root/common_weighted_regulator_author`; prescribed actual model
`gpt-6.1-sol`, reasoning effort `xhigh`; fresh context, no subagents.

Proposed production module: `Shao.Probability.SourceLindleyRegulatorEnergyWeighted`.
Only root may freeze a declaration set and activate production writing.
These are complete proposed literal Lean heads, not implementations or Lean
check results. No statement is labelled `CORRECT` or accepted.

There are **zero new global definitions**, and **four substantive bundles**:
(1) actual prefix dependence, genuine L1 and the two change-of-measure
identities; (2) the actual single-time first-moment bound; (3) both fully
paid deterministic clocks; (4) actual finite sums and their original
fixed-cutoff source-law specialization. Bundle 4 contains two theorem heads,
so the proposed module has five public theorems. Root may freeze the generic
four heads separately from the final source specialization if desired.

`i : Fin N` is a zero-based coordinate; the paper's time is `i.val + 1`.
Every `Q i a` is literally `Shao.prefixSquares a (i.val + 1)` and every
`U i a` is literally `lindleyRegulator a i`. No whole-`N` energy replaces a
prefix energy, no abstract random observable replaces the true recursion,
and no centered or symmetric law is assumed. A second-moment change of
measure is only an identity, with no second-moment decay claim.

The energy-tilt producer below is a **pending acceptance dependency**:
`BoundedQuadraticTilt` is root-frozen, but not accepted merely by being
imported in these candidate heads. The prefix first-moment producer is the
exact independently reviewed source at head
`e32108dc19228e38d09f8a704a0dbaf58777181e`, not a new premise.

```lean
import Shao.Probability.BoundedQuadraticTilt
import Shao.Probability.SourceLindleyRegulatorFirstMomentSums
import Shao.Probability.SourceTruncationBridge
import Shao.OQ3.QuadraticSampleChangeOfMeasure

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Bundle 1: the actual prefix, positive weight, L1 and r=1,2 identities. -/
theorem iid_lindleyRegulator_prefix_energy_change_of_measure
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (N : ℕ) (i : Fin N) :
    let Z : ℝ := ∫ a : ℝ, Real.exp (-s * a ^ 2) ∂ν
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
    let p : Shao.Path N → Shao.Path (i.val + 1) := fun a =>
      Shao.prefixPath a (i.val + 1) (Nat.succ_le_of_lt i.is_lt)
    let U : Shao.Path N → ℝ := fun a => lindleyRegulator a i
    let Q : Shao.Path N → ℝ := fun a => Shao.prefixSquares a (i.val + 1)
    let W : Shao.Path N → ℝ := fun a => Real.exp (-s * Q a)
    Integrable (fun a : ℝ => Real.exp (-s * a ^ 2)) ν ∧
      0 < Z ∧ IsProbabilityMeasure ρ ∧
      IsProbabilityMeasure P ∧ IsProbabilityMeasure T ∧
      Measurable U ∧ Measurable Q ∧
      (∀ a : Shao.Path N,
        U a = lindleyRegulator (p a) (Fin.last i.val) ∧
        Q a = Shao.energy (p a) ∧
        0 ≤ U a ∧ 0 ≤ Q a ∧ 0 < W a ∧ W a ≤ 1) ∧
      (∀ᵐ a : Shao.Path N ∂P, U a ≤ h) ∧
      (∀ᵐ a : Shao.Path N ∂T, U a ≤ h) ∧
      Integrable W P ∧
      (∫ a : Shao.Path N, W a ∂P) = Z ^ (i.val + 1) ∧
      (∀ r : ℕ, (r = 1 ∨ r = 2) →
        Integrable (fun a : Shao.Path N => U a ^ r) P ∧
        Integrable (fun a : Shao.Path N => U a ^ r) T ∧
        Integrable (fun a : Shao.Path N => U a ^ r * W a) P ∧
        (∫ a : Shao.Path N, U a ^ r ∂T) =
          ∫ b : Shao.Path (i.val + 1),
            lindleyRegulator b (Fin.last i.val) ^ r
            ∂Measure.pi (fun _ : Fin (i.val + 1) => ρ) ∧
        (∫ a : Shao.Path N, U a ^ r * W a ∂P) =
          Z ^ (i.val + 1) * (∫ a : Shao.Path N, U a ^ r ∂T))

/-- Bundle 2: the same actual weighted first moment, with explicit constants. -/
theorem iid_lindleyRegulator_prefix_energy_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : s * h ^ 2 ≤ 1) (N : ℕ) (i : Fin N) :
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let S : ℝ := s * h ^ 2
    let B : ℝ := Real.sqrt (Real.exp S * V)
    let M : ℝ := |μ| + 2 * s * Real.exp S * m3
    let U : Shao.Path N → ℝ := fun a => lindleyRegulator a i
    let Q : Shao.Path N → ℝ := fun a => Shao.prefixSquares a (i.val + 1)
    Integrable U T ∧
      Integrable (fun a : Shao.Path N => U a * Real.exp (-s * Q a)) P ∧
      0 ≤ (∫ a : Shao.Path N, U a * Real.exp (-s * Q a) ∂P) ∧
      (∫ a : Shao.Path N, U a ∂T) ≤
        B / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + M ∧
      (∫ a : Shao.Path N, U a * Real.exp (-s * Q a) ∂P) ≤
        Real.exp (-(s * m2 / 2) * ((i.val + 1 : ℕ) : ℝ)) *
          (B / Real.sqrt ((i.val + 1 : ℕ) : ℝ) + M)

/-- Bundle 3: both finite clocks are conclusions, with no integral-comparison
or decay estimate supplied as an assumption. The empty clock is included. -/
theorem finite_energy_decay_clocks (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    let G : ℝ := ∑ i : Fin N,
      Real.exp (-(t / (N : ℝ)) * ((i.val + 1 : ℕ) : ℝ))
    let H : ℝ := ∑ i : Fin N,
      Real.exp (-(t / (N : ℝ)) * ((i.val + 1 : ℕ) : ℝ)) /
        Real.sqrt ((i.val + 1 : ℕ) : ℝ)
    0 ≤ G ∧ G ≤ (N : ℝ) ∧ t * G ≤ (N : ℝ) ∧
      G ≤ 2 * (N : ℝ) / (1 + t) ∧
      0 ≤ H ∧ H ≤ 2 * Real.sqrt G ∧
      H ≤ 2 * Real.sqrt (N : ℝ) ∧
      H ≤ 4 * Real.sqrt (N : ℝ) / (1 + Real.sqrt t)

/-- Bundle 4a: genuine finite and restricted sums under one actual long law. -/
theorem iid_lindleyRegulator_energy_weighted_sum_first_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h s : ℝ) (hh : 0 < h) (hs : 0 ≤ s)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : s * h ^ 2 ≤ 1) (N : ℕ) :
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let S : ℝ := s * h ^ 2
    let B : ℝ := Real.sqrt (Real.exp S * V)
    let M : ℝ := |μ| + 2 * s * Real.exp S * m3
    let t : ℝ := (s * m2 / 2) * (N : ℝ)
    let U : Fin N → Shao.Path N → ℝ := fun i a => lindleyRegulator a i
    let Q : Fin N → Shao.Path N → ℝ := fun i a =>
      Shao.prefixSquares a (i.val + 1)
    let F : Shao.Path N → ℝ := fun a =>
      ∑ i : Fin N, U i a * Real.exp (-s * Q i a)
    let C : ℝ := 4 * B * Real.sqrt (N : ℝ) / (1 + Real.sqrt t) +
      2 * (N : ℝ) * M / (1 + t)
    Integrable F P ∧ 0 ≤ (∫ a : Shao.Path N, F a ∂P) ∧
      (∫ a : Shao.Path N, F a ∂P) =
        ∑ i : Fin N, ∫ a : Shao.Path N, U i a * Real.exp (-s * Q i a) ∂P ∧
      (∫ a : Shao.Path N, F a ∂P) ≤ C ∧
      (∀ K : ℕ, K ≤ N →
        let FΚ : Shao.Path N → ℝ := fun a =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < K),
            U i a * Real.exp (-s * Q i a)
        Integrable FΚ P ∧ 0 ≤ (∫ a : Shao.Path N, FΚ a ∂P) ∧
          (∫ a : Shao.Path N, FΚ a ∂P) ≤ (∫ a : Shao.Path N, F a ∂P) ∧
          (∫ a : Shao.Path N, FΚ a ∂P) ≤ C)

/-- Bundle 4b: the original conditional increment law and threshold/budget
pay a concrete constant, without a survival or a Lambda-smallness input.
For fixed positive kappa the source constant is 128/sqrt(kappa). -/
theorem sourceTruncation_lindleyRegulator_energy_weighted_first_sum
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (N : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hnorm : (N : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hmean : (∫ a : ℝ, a ∂ν0) = 0)
    (x ε ε0 κ y : ℝ) (hx : 0 ≤ x) (hε : 0 < ε)
    (hε0 : 0 < ε0) (hε01 : ε0 ≤ 1) (hεsmall : ε ≤ ε0 / 2)
    (hR : Shao.truncationBudget ν0 N x ≤ ε ^ 3 / 8)
    (hκ : 0 < κ) (hκsmall : κ ≤ (1 / 16 : ℝ)) (hy : 1 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x))) :
    let ν : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ ε / (1 + x)}
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Λ : ℝ := (1 + y) * (N : ℝ) * |μ| +
      (1 + y) ^ 3 * (N : ℝ) * m3
    let U : Fin N → Shao.Path N → ℝ := fun i a => lindleyRegulator a i
    let Q : Fin N → Shao.Path N → ℝ := fun i a =>
      Shao.prefixSquares a (i.val + 1)
    let F : Shao.Path N → ℝ := fun a =>
      ∑ i : Fin N, U i a * Real.exp (-(κ * y ^ 2) * Q i a)
    IsProbabilityMeasure ν ∧
      (∀ᵐ a : ℝ ∂ν, |a| ≤ ε / (1 + x)) ∧
      (κ * y ^ 2) * (ε / (1 + x)) ^ 2 ≤ 1 ∧
      (3 / 4 : ℝ) ≤ (N : ℝ) * m2 ∧
      (N : ℝ) * V ≤ (4 / 3 : ℝ) ∧
      0 ≤ Λ ∧ Λ ≤ (1 / 2 : ℝ) ∧
      Integrable F P ∧ 0 ≤ (∫ a : Shao.Path N, F a ∂P) ∧
      (∫ a : Shao.Path N, F a ∂P) ≤
        128 / (Real.sqrt κ * (1 + y)) ∧
      (∀ K : ℕ, K ≤ N →
        let FΚ : Shao.Path N → ℝ := fun a =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < K),
            U i a * Real.exp (-(κ * y ^ 2) * Q i a)
        Integrable FΚ P ∧ 0 ≤ (∫ a : Shao.Path N, FΚ a ∂P) ∧
          (∫ a : Shao.Path N, FΚ a ∂P) ≤
            128 / (Real.sqrt κ * (1 + y)))

end Shao.Probability
```

## Constants, boundaries and acceptance

- Bundle 1 has no `s*h^2 ≤ 1` hypothesis. Bounded support gives genuine
  integrability and a positive normalizer for every `s≥0`. All-time
  weighting by `exp(-s*energy a)` would have a different normalization and
  is explicitly outside these signatures.
- Bundles 2/4a retain the actual nonzero mean through
  `M=|μ|+2*s*exp(s*h^2)*m3`; the variance envelope is
  `B=sqrt(exp(s*h^2)*V)`. There is no division by `V` or `sqrt V`.
  `V=0`, `m2=0`, `m3=0`, `s=0` are therefore included.
- Bundle 3 uses the literal constants `2` for the geometric clock and `4`
  for the inverse-square-root clock. Both are proved by finite
  telescoping, as detailed in `source-contract.md`. No improper integral,
  Gamma-function formula, clock bound or monotonicity premise is imported
  as an assumption.
- Bundle 4a includes `N=0` (zero sums and zero right side), `K=0` and
  `K=N`. In bundle 1/2, `i : Fin N` itself gives a strictly positive time;
  `i.val=0` is the paper's first time and is included.
- Bundle 4b is the actual source specialization. It exposes the original
  base-law centering and normalization, then takes the literal conditional
  law. It does not assume this conditional law is centered. Its
  `Λ≤1/2`, small energy parameter and numerical moment scales are
  conclusions paid by the original cutoff budget and threshold window.
  It permits every `0<κ≤1/16`, with constant `128/sqrt(κ)`; it does not assert a
  constant uniform as `κ→0`. Taking `K=N/2` is exactly the original
  half-time first-moment sum. Later kernel work may choose a still smaller
  fixed `κ` without invalidating this theorem.
- A full root freeze, implementation, source-hash-bound server kernel and
  actual-owned transitive-axiom receipt, and one qualified fresh complete
  independent review remain necessary. Allowed axioms are `propext`,
  `Classical.choice`, `Quot.sound`. The pending energy producer must itself
  pass that acceptance before these consumers can be finally accepted.
