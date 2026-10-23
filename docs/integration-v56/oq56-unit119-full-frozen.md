# Unit119 frozen v1: actual conditional product law and second moments

Frozen before proof implementation. The actual low and target conditional measures below are normalized restrictions of the full fixed population. Their positive masses come from118; no conditioning premise substitutes for that proof.

The fixed oriented event conditions independent whole observations coordinatewise. The entire conditional law must equal the product of the actual target/low conditional laws before deriving coordinate independence and marginals. The low event separates both sparse labels and leaves the independent uniform noise and signs unbiased. Actual low G/Z remain independent and centered with the original moment hypotheses; their second moments are bounded by the original moments divided by q_j². Target noise has the actual uniform law; target G/Z identities hold AE under the true conditional law. No fourth moment is used or required.

Only exact consumed old declarations/definition values/hashes/qualifications/scope are checked; qualified old proofs and checks are reused. All new proofs and actual-owned types/values/axioms require a fresh full independent review and designated-server checks.

```lean
import Shao.OQ5.P53.SparseBalancedMass
import Shao.Probability.ConditionalIID

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseLowObservationMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : Measure SparseObs :=
  ProbabilityTheory.cond (sparsePopulationMeasure α x N) (sparseLowObservation j)

def sparseTargetObservationMeasure (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool) : Measure SparseObs :=
  ProbabilityTheory.cond (sparsePopulationMeasure α x N) (sparseTargetObservation j b)

theorem sparseLowObservationMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 1 ≤ j →
  IsProbabilityMeasure (sparseLowObservationMeasure α x N j)

theorem sparseTargetObservationMeasure_probability :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  IsProbabilityMeasure (sparseTargetObservationMeasure α x N j b)

theorem sparseBalancedPairPattern_cond_eq_pi :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
    (sparseBalancedPairPattern j i k b) =
  Measure.pi (fun l : Fin n =>
    if l = i then sparseTargetObservationMeasure α x N j b
    else if l = k then sparseTargetObservationMeasure α x N j (!b)
    else sparseLowObservationMeasure α x N j)

theorem iIndepFun_sparseBalancedPairPattern_cond :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k →
  ProbabilityTheory.iIndepFun (fun l : Fin n => fun ω : Fin n → SparseObs => ω l)
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
      (sparseBalancedPairPattern j i k b))

theorem sparseBalancedPairPattern_cond_coordinate_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n j : ℕ) (i k : Fin n) (b : Bool),
  1 ≤ j → i < k → ∀ l : Fin n,
  (ProbabilityTheory.cond (Measure.pi (fun _ : Fin n => sparsePopulationMeasure α x N))
    (sparseBalancedPairPattern j i k b)).map (fun ω : Fin n → SparseObs => ω l) =
    if l = i then sparseTargetObservationMeasure α x N j b
    else if l = k then sparseTargetObservationMeasure α x N j (!b)
    else sparseLowObservationMeasure α x N j

theorem sparseLowObservationG_indep_Z :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 1 ≤ j →
  ProbabilityTheory.IndepFun (sparsePopulationG α x N) (sparsePopulationZ α x N)
    (sparseLowObservationMeasure α x N j)

theorem memLp_sparseLowObservationG_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  MemLp (sparsePopulationG α x N) 2 (sparseLowObservationMeasure α x N j)

theorem memLp_sparseLowObservationZ_two :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 0 < α → 1 ≤ j →
  MemLp (sparsePopulationZ α x N) 2 (sparseLowObservationMeasure α x N j)

theorem integral_sparseLowObservationG_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  (∫ z, sparsePopulationG α x N z ∂sparseLowObservationMeasure α x N j) = 0

theorem integral_sparseLowObservationZ_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 0 < α → 1 ≤ j →
  (∫ z, sparsePopulationZ α x N z ∂sparseLowObservationMeasure α x N j) = 0

theorem integral_sparseLowObservationG_sq_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ),
  0 < α → SparseSelectionCore α x N → 1 ≤ j →
  (∫ z, (sparsePopulationG α x N z) ^ 2 ∂sparseLowObservationMeasure α x N j) ≤
    (∫ z, (sparsePopulationG α x N z) ^ 2 ∂sparsePopulationMeasure α x N) /
      sparsePriorMass α x N j ^ 2

theorem integral_sparseLowObservationZ_sq_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 0 < α → 1 ≤ j →
  (∫ z, (sparsePopulationZ α x N z) ^ 2 ∂sparseLowObservationMeasure α x N j) ≤
    (∫ z, (sparsePopulationZ α x N z) ^ 2 ∂sparsePopulationMeasure α x N) /
      sparsePriorMass α x N j ^ 2

theorem sparseTargetObservation_noise_law :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  (sparseTargetObservationMeasure α x N j b).map (fun z : SparseObs => z.1.1) =
    Shao.OQ5.P35.noiseLaw

theorem sparseTargetObservationG_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  ∀ᵐ z : SparseObs ∂sparseTargetObservationMeasure α x N j b,
    sparsePopulationG α x N z = z.1.1 + sparseLevelShift α x N j

theorem sparseTargetObservationZ_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) (b : Bool), 1 ≤ j →
  ∀ᵐ z : SparseObs ∂sparseTargetObservationMeasure α x N j b,
    sparsePopulationZ α x N z =
      if b = true then sparseLevelAmplitude α x N j else -sparseLevelAmplitude α x N j
```

Actual conditional numerator/R² bounds, mixture estimates and original tail limits remain separate obligations. P53/OQ6/RS2 remain OPEN.
