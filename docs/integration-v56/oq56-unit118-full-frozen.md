# Unit118 frozen v1: actual balanced-event mass and positive conditioning

Frozen before implementation; every public theorem type below and both imports are exact. Proof authors may not add assumptions or reinterpret actual sets. Depends on qualified117 before server execution.

The actual fixed population is ((uniform noise x signed B) x signed C). At a target, B=j with positive projection sign and C=j with one prescribed feature sign cost labelMass_j²/4. Two prescribed target signs yield labelMass_j^4/16; the two disjoint opposite orientations yield /8. Both background categories are below j, so each background observation costs q_j². Ordered target positions i<k give exactly choose(n,2), without duplicate counting. All noises are unrestricted by the event and contribute mass one.

Use actual sparseLabelMass for the general formulas, including the separate residual level zero. Substitute sparsePositiveMass ONLY when j>=1. For positive levels q_j>=3/4 and pi_j>0 already hold without alpha/core assumptions. Actual positivity of the finite pattern and infinite prefix events must be proved before normalized conditional probability is asserted. n=0,1 are covered in whole-event formulas by the empty union and zero binomial coefficient.

The entire fixed infinite prefix law supplies the actual prefix event probability. A finite proxy, formal multiplicative guess or a conditioning premise is insufficient. No conditional moments, tail estimate or root closure is claimed.

```lean
import Shao.OQ5.P53.SparseBalancedEvent
import Shao.OQ5.P53.SparseRealSample

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

theorem sparsePopulationMeasure_lowObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  sparsePopulationMeasure α x N (sparseLowObservation j) =
    ENNReal.ofReal (sparsePriorMass α x N j ^ 2)

theorem sparsePopulationMeasure_real_lowObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  (sparsePopulationMeasure α x N).real (sparseLowObservation j) =
    sparsePriorMass α x N j ^ 2

theorem sparsePopulationMeasure_targetObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool),
  sparsePopulationMeasure α x N (sparseTargetObservation j b) =
    ENNReal.ofReal (sparseLabelMass α x N j ^ 2 / 4)

theorem sparsePopulationMeasure_real_targetObservation :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool),
  (sparsePopulationMeasure α x N).real (sparseTargetObservation j b) =
    sparseLabelMass α x N j ^ 2 / 4

theorem sparseBalancedPairPattern_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool), i < k →
  (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedPairPattern j i k b) =
      sparseLabelMass α x N j ^ 4 * sparsePriorMass α x N j ^ (2 * (n - 2)) / 16

theorem sparseBalancedPairEvent_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n), i < k →
  (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedPairEvent j i k) =
      sparseLabelMass α x N j ^ 4 * sparsePriorMass α x N j ^ (2 * (n - 2)) / 8

theorem sparseBalancedEvent_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ),
  (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedEvent n j) =
      (n.choose 2 : ℝ) * sparseLabelMass α x N j ^ 4 *
        sparsePriorMass α x N j ^ (2 * (n - 2)) / 8

theorem sparseBalancedPrefixEvent_real_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ),
  (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent n j) =
    (n.choose 2 : ℝ) * sparseLabelMass α x N j ^ 4 *
      sparsePriorMass α x N j ^ (2 * (n - 2)) / 8

theorem sparseBalancedPrefixEvent_positive_level_mass :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ), 1 ≤ j →
  (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent n j) =
    (n.choose 2 : ℝ) * sparsePositiveMass α x N j ^ 4 *
      sparsePriorMass α x N j ^ (2 * (n - 2)) / 8

theorem sparseBalancedPairPattern_real_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  0 < (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N)).real
    (sparseBalancedPairPattern j i k b)

theorem sparseBalancedPrefixEvent_real_pos :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ), 2 ≤ n → 1 ≤ j →
  0 < (sparsePopulationSampleMeasure α x N).real (sparseBalancedPrefixEvent n j)

theorem sparseBalancedPairPattern_cond_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  IsProbabilityMeasure (ProbabilityTheory.cond
    (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
      (sparseBalancedPairPattern j i k b))

theorem sparseBalancedPrefixEvent_cond_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ), 2 ≤ n → 1 ≤ j →
  IsProbabilityMeasure (ProbabilityTheory.cond (sparsePopulationSampleMeasure α x N)
    (sparseBalancedPrefixEvent n j))
```

P53/OQ6/RS2 remain OPEN.
