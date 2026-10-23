import Shao.OQ5.P53.SparsePositiveStudentizer
import Shao.OQ5.P53.SparseRealModel

/-!
# Actual real p53 statistics and exact whole-sample tails

The real kernel is evaluated in the original unordered-pair U and centered-row
jackknife formulas. Its literal composition with the total decoder gives the
four statistic identities for every real finite sample. Encoder recovery uses
the closed noise support, and is not a global inverse assertion.

The complete sample decoder law transports actual denominator positivity and
actual tail events. No selection or moment hypothesis is needed for these
structural statements. Event masses, conditional estimates, tail asymptotics
and the original p53/OQ6/RS2 conclusions remain separate obligations.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Shao.OQ5.P53

local notation "SparseObs" => ((ℝ × (ℕ × Bool)) × (ℕ × Bool))

def sparseRealSampleU (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => sparseRealKernel α x N (ξ i) (ξ k))

def sparseRealSampleStudentizerSq (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => sparseRealKernel α x N (ξ i) (ξ k))

def sparseRealSampleStudentizer (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Real.sqrt (sparseRealSampleStudentizerSq α x N ξ)

def sparseRealSampleStudentized (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) {n : ℕ} (ξ : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * sparseRealSampleU α x N ξ / sparseRealSampleStudentizer α x N ξ

def sparseSampleStudentizedTailProbability (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n : ℕ) (y : ℝ) : ℝ :=
  (sparsePopulationSampleMeasure α x N).real
    {ω : ℕ → SparseObs | y ≤ sparseSampleStudentized α x N (fun i : Fin n => ω i.val)}

def sparseRealSampleStudentizedTailProbability (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (n : ℕ) (y : ℝ) : ℝ :=
  (sparseRealSampleMeasure α x N).real
    {ξ : ℕ → ℝ | y ≤ sparseRealSampleStudentized α x N
      (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)}

theorem measurable_sparseRealSampleU :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseRealSampleU α x N ξ) := by
  intro α x N n
  change Measurable (fun ξ : Fin n → ℝ =>
    sparseSampleU α x N (fun i => sparsePopulationDecode (ξ i)))
  exact (measurable_sparseSampleU α x N n).comp
    (Measurable.of_eval (fun i =>
      measurable_sparsePopulationDecode.comp (measurable_pi_apply i)))

theorem measurable_sparseRealSampleStudentizerSq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseRealSampleStudentizerSq α x N ξ) := by
  intro α x N n
  change Measurable (fun ξ : Fin n → ℝ =>
    sparseSampleStudentizerSq α x N (fun i => sparsePopulationDecode (ξ i)))
  exact (measurable_sparseSampleStudentizerSq α x N n).comp
    (Measurable.of_eval (fun i =>
      measurable_sparsePopulationDecode.comp (measurable_pi_apply i)))

theorem measurable_sparseRealSampleStudentizer :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseRealSampleStudentizer α x N ξ) := by
  intro α x N n
  exact (measurable_sparseRealSampleStudentizerSq α x N n).sqrt

theorem measurable_sparseRealSampleStudentized :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : Fin n → ℝ => sparseRealSampleStudentized α x N ξ) := by
  intro α x N n
  exact ((measurable_sparseRealSampleU α x N n).const_mul (Real.sqrt (n : ℝ))).div
    (measurable_sparseRealSampleStudentizer α x N n)

theorem measurable_sparseRealSampleStudentized_sample :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ n : ℕ,
  Measurable (fun ξ : ℕ → ℝ => sparseRealSampleStudentized α x N
    (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)) := by
  intro α x N n
  exact (measurable_sparseRealSampleStudentized α x N n).comp
    (Measurable.of_eval (fun i => measurable_sparseRealSampleCoordinate i.val))

theorem sparseRealSampleU_decode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseRealSampleU α x N ξ =
    sparseSampleU α x N (fun i => sparsePopulationDecode (ξ i)) := by
  intro α x N n ξ
  rfl

theorem sparseRealSampleU_encode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ω : Fin n → SparseObs),
  (∀ i : Fin n, (ω i).1.1 ∈ Set.Icc (-1 : ℝ) 1) →
  sparseRealSampleU α x N (fun i => sparsePopulationEncode (ω i)) =
    sparseSampleU α x N ω := by
  intro α x N n ω hω
  rw [sparseRealSampleU_decode]
  congr 1
  funext i
  exact sparsePopulationDecode_encode (ω i) (hω i)

theorem sparseRealSampleStudentizerSq_decode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseRealSampleStudentizerSq α x N ξ =
    sparseSampleStudentizerSq α x N (fun i => sparsePopulationDecode (ξ i)) := by
  intro α x N n ξ
  rfl

theorem sparseRealSampleStudentizerSq_encode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ω : Fin n → SparseObs),
  (∀ i : Fin n, (ω i).1.1 ∈ Set.Icc (-1 : ℝ) 1) →
  sparseRealSampleStudentizerSq α x N (fun i => sparsePopulationEncode (ω i)) =
    sparseSampleStudentizerSq α x N ω := by
  intro α x N n ω hω
  rw [sparseRealSampleStudentizerSq_decode]
  congr 1
  funext i
  exact sparsePopulationDecode_encode (ω i) (hω i)

theorem sparseRealSampleStudentizer_decode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseRealSampleStudentizer α x N ξ =
    sparseSampleStudentizer α x N (fun i => sparsePopulationDecode (ξ i)) := by
  intro α x N n ξ
  rfl

theorem sparseRealSampleStudentizer_encode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ω : Fin n → SparseObs),
  (∀ i : Fin n, (ω i).1.1 ∈ Set.Icc (-1 : ℝ) 1) →
  sparseRealSampleStudentizer α x N (fun i => sparsePopulationEncode (ω i)) =
    sparseSampleStudentizer α x N ω := by
  intro α x N n ω hω
  rw [sparseRealSampleStudentizer_decode]
  congr 1
  funext i
  exact sparsePopulationDecode_encode (ω i) (hω i)

theorem sparseRealSampleStudentized_decode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  sparseRealSampleStudentized α x N ξ =
    sparseSampleStudentized α x N (fun i => sparsePopulationDecode (ξ i)) := by
  intro α x N n ξ
  rfl

theorem sparseRealSampleStudentized_encode :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ω : Fin n → SparseObs),
  (∀ i : Fin n, (ω i).1.1 ∈ Set.Icc (-1 : ℝ) 1) →
  sparseRealSampleStudentized α x N (fun i => sparsePopulationEncode (ω i)) =
    sparseSampleStudentized α x N ω := by
  intro α x N n ω hω
  rw [sparseRealSampleStudentized_decode]
  congr 1
  funext i
  exact sparsePopulationDecode_encode (ω i) (hω i)

theorem sparseRealSampleStudentizerSq_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ ξ : Fin n → ℝ,
  0 ≤ sparseRealSampleStudentizerSq α x N ξ := by
  intro α x N n hn ξ
  rw [sparseRealSampleStudentizerSq_decode]
  exact sparseSampleStudentizerSq_nonneg α x N n hn _

theorem sparseRealSampleStudentizer_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (ξ : Fin n → ℝ),
  0 ≤ sparseRealSampleStudentizer α x N ξ := by
  intro α x N n ξ
  exact Real.sqrt_nonneg _

theorem sparseRealSampleStudentizer_sq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ ξ : Fin n → ℝ,
  (sparseRealSampleStudentizer α x N ξ) ^ 2 = sparseRealSampleStudentizerSq α x N ξ := by
  intro α x N n hn ξ
  exact Real.sq_sqrt (sparseRealSampleStudentizerSq_nonneg α x N n hn ξ)

private theorem real_prefix_studentizer_pos_ae (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ξ : ℕ → ℝ ∂sparseRealSampleMeasure α x N,
      0 < sparseRealSampleStudentizer α x N
        (fun i : Fin n => sparseRealSampleCoordinate i.val ξ) := by
  have hmp : MeasurePreserving
      (fun ξ : ℕ → ℝ => fun i : ℕ => sparsePopulationDecode (ξ i))
      (sparseRealSampleMeasure α x N) (sparsePopulationSampleMeasure α x N) :=
    ⟨Measurable.of_eval (fun i =>
      measurable_sparsePopulationDecode.comp (measurable_pi_apply i)),
      sparseRealSample_decode_law α x N⟩
  have h := hmp.quasiMeasurePreserving.ae
    (sparseSampleStudentizer_prefix_pos_ae α x N n hn)
  filter_upwards [h] with ξ hξ
  simpa only [sparseRealSampleCoordinate, sparseRealSampleStudentizer_decode] using hξ

theorem sparseRealSampleStudentizer_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n →
  ∀ᵐ ξ : Fin n → ℝ ∂Measure.pi (fun _ : Fin n => sparseRealMeasure α x N),
    0 < sparseRealSampleStudentizer α x N ξ := by
  intro α x N n hn
  have hm : Measurable (fun ξ : ℕ → ℝ =>
      fun i : Fin n => sparseRealSampleCoordinate i.val ξ) :=
    Measurable.of_eval (fun i => measurable_sparseRealSampleCoordinate i.val)
  have hset : MeasurableSet {ξ : Fin n → ℝ |
      0 < sparseRealSampleStudentizer α x N ξ} :=
    measurableSet_lt measurable_const (measurable_sparseRealSampleStudentizer α x N n)
  rw [← sparseRealSample_prefix_law α x N n]
  exact (ae_map_iff hm.aemeasurable hset).mpr
    (real_prefix_studentizer_pos_ae α x N n hn)

theorem sparseRealSampleStudentizer_prefix_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n →
  ∀ᵐ ξ : ℕ → ℝ ∂sparseRealSampleMeasure α x N,
    0 < sparseRealSampleStudentizer α x N
      (fun i : Fin n => sparseRealSampleCoordinate i.val ξ) := by
  intro α x N n hn
  exact real_prefix_studentizer_pos_ae α x N n hn

theorem sparseRealSampleStudentizer_cond_prefix_pos_ae :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ), 3 ≤ n → ∀ E : Set (ℕ → ℝ),
  ∀ᵐ ξ : ℕ → ℝ ∂ProbabilityTheory.cond (sparseRealSampleMeasure α x N) E,
    0 < sparseRealSampleStudentizer α x N
      (fun i : Fin n => sparseRealSampleCoordinate i.val ξ) := by
  intro α x N n hn E
  exact (ProbabilityTheory.cond_absolutelyContinuous
    (μ := sparseRealSampleMeasure α x N) (s := E)).ae_le
      (sparseRealSampleStudentizer_prefix_pos_ae α x N n hn)

theorem sparseRealSampleStudentizedTailProbability_eq :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (y : ℝ),
  sparseRealSampleStudentizedTailProbability α x N n y =
    sparseSampleStudentizedTailProbability α x N n y := by
  intro α x N n y
  let A : Set (ℕ → SparseObs) := {ω | y ≤ sparseSampleStudentized α x N
    (fun i : Fin n => ω i.val)}
  let B : Set (ℕ → ℝ) := {ξ | y ≤ sparseRealSampleStudentized α x N
    (fun i : Fin n => sparseRealSampleCoordinate i.val ξ)}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const ((measurable_sparseSampleStudentized α x N n).comp
      (Measurable.of_eval (fun i => measurable_pi_apply i.val)))
  have hdecode : Measurable
      (fun ξ : ℕ → ℝ => fun i : ℕ => sparsePopulationDecode (ξ i)) :=
    Measurable.of_eval (fun i =>
      measurable_sparsePopulationDecode.comp (measurable_pi_apply i))
  have hmass : sparseRealSampleMeasure α x N B =
      sparsePopulationSampleMeasure α x N A := by
    rw [← sparseRealSample_decode_law α x N, Measure.map_apply hdecode hA]
    congr 1
  exact congrArg ENNReal.toReal hmass

theorem sparseSampleStudentizedTailProbability_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (y : ℝ),
  0 ≤ sparseSampleStudentizedTailProbability α x N n y := by
  intro α x N n y
  exact ENNReal.toReal_nonneg

theorem sparseSampleStudentizedTailProbability_le_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (y : ℝ),
  sparseSampleStudentizedTailProbability α x N n y ≤ 1 := by
  intro α x N n y
  let : IsProbabilityMeasure (sparsePopulationSampleMeasure α x N) :=
    sparsePopulationSampleMeasure_probability α x N
  exact measureReal_le_one

theorem sparseRealSampleStudentizedTailProbability_nonneg :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (y : ℝ),
  0 ≤ sparseRealSampleStudentizedTailProbability α x N n y := by
  intro α x N n y
  exact ENNReal.toReal_nonneg

theorem sparseRealSampleStudentizedTailProbability_le_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ), ∀ (n : ℕ) (y : ℝ),
  sparseRealSampleStudentizedTailProbability α x N n y ≤ 1 := by
  intro α x N n y
  let : IsProbabilityMeasure (sparseRealSampleMeasure α x N) :=
    sparseRealSampleMeasure_probability α x N
  exact measureReal_le_one

end Shao.OQ5.P53
