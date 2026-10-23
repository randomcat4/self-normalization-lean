# Unit117 frozen v1: actual p53 balanced-pair event and pointwise statistics

Frozen before any proof implementation. Definitions and every public theorem type below are exact; the proof author must not alter any premise, definition, quantifier or import.

Original source p53 §4 fixes precisely two targets B=C=j, eta=+, opposite feature signs, with every remaining B,C<j. Noise is unrestricted. Ordered i<k and two explicit sign patterns permit later honest mass computation without double counting. Here only actual sets, measurability/disjointness and the original finite U/R algebra are certified. No event mass, conditional probability, tail limit or root theorem is claimed.

The actual fixed sparse coefficients and positive kernel are used. The scalar relation d_j=t_j²/(N_j-2) holds literally also at zero level by the separate zero definitions; mass statements will explicitly require positive levels. The original centered-row denominator and n>=3 hypotheses are retained. The target offsets cancel pointwise; background rows contain only the background feature sum. Existing qualified P45.BalancedBlock is the exact deterministic bridge, after verifying actual tags imply its full BalancedTarget premise.

Risk gates: actual sets rather than an abstract event; no hidden noise support requirement; no omission of B or C truncation; no sign-factor/double-count loss; no negative residual sign; no expectation substituted for pointwise equality; no silent Core/alpha/moment premises.

```lean
import Shao.OQ5.P53.SparseSampleStatistics
import Shao.OQ5.P45.BalancedBlock

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseLowObservation (j : ℕ) : Set SparseObs :=
  {z | z.1.2.1 < j ∧ z.2.1 < j}

def sparseTargetObservation (j : ℕ) (b : Bool) : Set SparseObs :=
  {z | z.1.2 = (j, true) ∧ z.2 = (j, b)}

def sparseBalancedPairPattern {n : ℕ} (j : ℕ) (i k : Fin n) (b : Bool) : Set (Fin n → SparseObs) :=
  {ω | i < k ∧ ω i ∈ sparseTargetObservation j b ∧
    ω k ∈ sparseTargetObservation j (!b) ∧
    ∀ l : Fin n, l ≠ i → l ≠ k → ω l ∈ sparseLowObservation j}

def sparseBalancedPairEvent {n : ℕ} (j : ℕ) (i k : Fin n) : Set (Fin n → SparseObs) :=
  sparseBalancedPairPattern j i k false ∪ sparseBalancedPairPattern j i k true

def sparseBalancedEvent (n j : ℕ) : Set (Fin n → SparseObs) :=
  ⋃ i : Fin n, ⋃ k : Fin n, sparseBalancedPairEvent j i k

def sparseBalancedPrefixEvent (n j : ℕ) : Set (ℕ → SparseObs) :=
  {ω | (fun i : Fin n => ω i.val) ∈ sparseBalancedEvent n j}

theorem measurableSet_sparseLowObservation :
  ∀ j : ℕ, MeasurableSet (sparseLowObservation j)

theorem measurableSet_sparseTargetObservation :
  ∀ (j : ℕ) (b : Bool), MeasurableSet (sparseTargetObservation j b)

theorem measurableSet_sparseBalancedPairPattern :
  ∀ (n j : ℕ) (i k : Fin n) (b : Bool),
  MeasurableSet (sparseBalancedPairPattern j i k b)

theorem measurableSet_sparseBalancedPairEvent :
  ∀ (n j : ℕ) (i k : Fin n), MeasurableSet (sparseBalancedPairEvent j i k)

theorem measurableSet_sparseBalancedEvent :
  ∀ n j : ℕ, MeasurableSet (sparseBalancedEvent n j)

theorem measurableSet_sparseBalancedPrefixEvent :
  ∀ n j : ℕ, MeasurableSet (sparseBalancedPrefixEvent n j)

theorem sparseBalancedPairPattern_eq_pi :
  ∀ (n j : ℕ) (i k : Fin n) (b : Bool), i < k →
  sparseBalancedPairPattern j i k b =
    Set.pi Set.univ (fun l : Fin n =>
      if l = i then sparseTargetObservation j b
      else if l = k then sparseTargetObservation j (!b)
      else sparseLowObservation j)

theorem sparseBalancedPairPattern_disjoint :
  ∀ (n j : ℕ) (i k : Fin n),
  Disjoint (sparseBalancedPairPattern j i k false)
    (sparseBalancedPairPattern j i k true)

theorem sparseBalancedPairEvent_disjoint :
  ∀ (n j : ℕ) (i k a c : Fin n), i < k → a < c → (i, k) ≠ (a, c) →
  Disjoint (sparseBalancedPairEvent j i k) (sparseBalancedPairEvent j a c)

theorem sparseBalancedPairPattern_balancedTarget :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ)
    (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  Shao.OQ5.P45.BalancedTarget (fun l => (ω l).1.1)
    (fun l => sparsePopulationG α x N (ω l))
    (fun l => sparsePopulationZ α x N (ω l))
    ({i, k} : Finset (Fin (N j)))
    (sparseLevelAmplitude α x N j) (sparseLevelShift α x N j)

theorem sparseSampleAdjustedRow_balancedPair_target :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  ∀ l : Fin (N j), l ∈ ({i, k} : Finset (Fin (N j))) →
  sparseSampleAdjustedRow α x N ω l = (ω l).1.1 +
    sparsePopulationZ α x N (ω l) *
      Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
        (fun a => sparsePopulationZ α x N (ω a)) / ((N j : ℝ) - 2)

theorem sparseSampleAdjustedRow_balancedPair_background :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  ∀ l : Fin (N j), l ∉ ({i, k} : Finset (Fin (N j))) →
  sparseSampleAdjustedRow α x N ω l = sparsePopulationG α x N (ω l) +
    sparsePopulationZ α x N (ω l) *
      (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
        (fun a => sparsePopulationZ α x N (ω a)) - sparsePopulationZ α x N (ω l)) /
          ((N j : ℝ) - 2)

theorem sparseSampleU_balancedPair_formula :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  sparseSampleU α x N ω =
    2 * sparseLevelShift α x N j / ((N j : ℝ) - 1) +
    (2 / (N j : ℝ)) * ((ω i).1.1 + (ω k).1.1) +
    (2 / (N j : ℝ)) *
      (∑ l : Fin (N j), if l ∈ ({i, k} : Finset (Fin (N j))) then 0
        else sparsePopulationG α x N (ω l)) +
    (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
        (fun l => sparsePopulationZ α x N (ω l)) ^ 2 -
      Shao.OQ5.P35.backgroundSqSum ({i, k} : Finset (Fin (N j)))
        (fun l => sparsePopulationZ α x N (ω l))) /
          ((N j : ℝ) * ((N j : ℝ) - 1))

theorem sparseSampleStudentizerSq_balancedPair_le :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ), 3 ≤ N j →
  ∀ (i k : Fin (N j)) (b : Bool) (ω : Fin (N j) → SparseObs),
  ω ∈ sparseBalancedPairPattern j i k b →
  sparseSampleStudentizerSq α x N ω ≤ (4 / ((N j : ℝ) - 1)) *
    ∑ l : Fin (N j),
      (if l ∈ ({i, k} : Finset (Fin (N j))) then
        (ω l).1.1 + sparsePopulationZ α x N (ω l) *
          Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
            (fun a => sparsePopulationZ α x N (ω a)) / ((N j : ℝ) - 2)
      else sparsePopulationG α x N (ω l) + sparsePopulationZ α x N (ω l) *
        (Shao.OQ5.P35.backgroundSum ({i, k} : Finset (Fin (N j)))
          (fun a => sparsePopulationZ α x N (ω a)) - sparsePopulationZ α x N (ω l)) /
            ((N j : ℝ) - 2)) ^ 2
```

P53/OQ6/RS2 remain OPEN. Next actual mass and conditional-law consumer must be separately frozen, proved, independently reviewed and checked on the server.
