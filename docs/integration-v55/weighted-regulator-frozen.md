# Actual prefix-energy weighted regulator declaration freeze

Root has read the complete candidate and source contract and approves all FIVE literal public declarations below, every parameter, hypothesis, conclusion and let binding, with ZERO new global definitions. This is an implementation authorization, not proof acceptance. No mathematical assumption may change silently.

Candidate SHA256: `8b7e0972e68c2aa53efd1cd7dd4379b72588a2ecfb74d6e397eb4e4288ab29ed`.
Contract SHA256: `ad78d4bc40e9b47933e4812b77f54c318e4f6aa834fa87fda6f82c9f7793954f`.

Owner: `/root/common_weighted_regulator_author`, only new `Shao/Probability/SourceLindleyRegulatorEnergyWeighted.lean`, its private helpers, and `drafts/c12-weighted-regulator/`. No other implementation ownership. Root verified prior writer release at `common-centered-characteristic-v44`, frozen parent `e32108dc19228e38d09f8a704a0dbaf58777181e`. Root must install exact upstream object references before first Lean check.

The bounded quadratic tilt producer is kernel/audit complete at `5e1a6a7fef2121bc0208798f7a0678975b44a0e9`, source `93c302d9de61bc4bf0cb238e82a4ed5b7f66e0ddbd2e833fec5bc6bbb25a8257`, object `cd1e326090a3fce3ecab7d8b38c14d7239c6b4fcedb600f8bb8dffb14d3dc2ec`, but its independent review is pending. Consumer development may proceed using this exact provisional object; final acceptance waits for independent CORRECT producer review. No success claim derives from import alone.

The scope is genuine prefix-only energy change of measure, first moments, both paid finite clocks, actual finite sums and the original conditional-law specialization with arbitrary `0 < κ ≤ 1/16`. The first-moment constant is explicitly `128 / (sqrt κ * (1+y))`. Second powers occur only in the exact change-of-measure identity; survival, unconditional/weighted second-moment decay, complex/growing kernels and C1/C2 remain OPEN. Prefix normalization is `Z^(i+1)`; future coordinates have probability mass one. Conditional-law centering is never assumed.

All new source is UTF8 LF before first gate. All Lean/heavy server only: root CPU10–13, root-heavy.lock, pinned versions, `-M8192 -j4 -DautoImplicit=false`. Preserve original direct Lean exits, exact source/object/log hashes and all actual-owned types/definition values/private/generated recursive axiom evidence. Standard three-axiom whitelist; no forbidden proof escapes. Fresh complete independent review is mandatory. Reuse qualified unchanged upstream evidence and objects without repeated source checks.

## Complete frozen declarations

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
