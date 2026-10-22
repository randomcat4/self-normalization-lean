import Shao.OQ5.P52.FixedLayerRealSample
import Shao.OQ5.P52.FixedLayerStudentizedTail

/-!
# Original real finite statistics and exact whole-law tails

The real kernel enters the original unordered U and randomly centered
jackknife formulas directly. Whole-sample encoding preserves every finite
matrix, its true root and total ratio, and then each actual tail event.
Population centering and positive global normalization are separate.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace Shao.OQ5.P52

noncomputable section

local notation "LayerObs" => (ℝ × (ℕ → Fin 3))

def fixedRealSampleU {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.uStatistic (fun i k => fixedRealKernel (x i, x k))

def fixedRealSampleStudentizerSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Shao.OQ6.FiniteRows.jackknifeSq (fun i k => fixedRealKernel (x i, x k))

def fixedRealSampleStudentizer {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (fixedRealSampleStudentizerSq x)

def fixedRealSampleStudentized {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * fixedRealSampleU x / fixedRealSampleStudentizer x

def fixedRealSampleStudentizedTailProbability (n : ℕ) (x : ℝ) : ℝ :=
  fixedRealSampleLaw.real
    {ξ : ℕ → ℝ |
      x ≤ fixedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)}

private theorem measurable_encode_sample :
    Measurable (fun ω : ℕ → LayerObs =>
      fun i : ℕ => Shao.OQ5.P50.layerEncode (ω i)) :=
  Measurable.of_eval (fun i =>
    Shao.OQ5.P50.measurable_layerEncode.comp (measurable_pi_apply i))

theorem measurable_fixedRealSampleU (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleU x) := by
  classical
  unfold fixedRealSampleU Shao.OQ6.FiniteRows.uStatistic Shao.OQ5.P35.unorderedPairSum
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  by_cases hik : i < k
  · simpa only [ite_eq_left hik, Function.comp_def] using
      measurable_fixedRealKernel.comp
        ((measurable_pi_apply i).prodMk (measurable_pi_apply k))
  · simp only [ite_eq_right hik]
    exact measurable_const

private theorem measurable_real_row (n : ℕ) (i : Fin n) :
    Measurable (fun x : Fin n → ℝ =>
      Shao.OQ6.FiniteRows.rowMean (fun a b => fixedRealKernel (x a, x b)) i) := by
  classical
  unfold Shao.OQ6.FiniteRows.rowMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro k _
  exact measurable_fixedRealKernel.comp
    ((measurable_pi_apply i).prodMk (measurable_pi_apply k))

theorem measurable_fixedRealSampleStudentizerSq (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleStudentizerSq x) := by
  unfold fixedRealSampleStudentizerSq Shao.OQ6.FiniteRows.jackknifeSq
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_real_row n i).sub (measurable_fixedRealSampleU n)).pow_const 2

theorem measurable_fixedRealSampleStudentizer (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleStudentizer x) :=
  (measurable_fixedRealSampleStudentizerSq n).sqrt

theorem measurable_fixedRealSampleStudentized (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => fixedRealSampleStudentized x) :=
  ((measurable_fixedRealSampleU n).const_mul (Real.sqrt (n : ℝ))).div
    (measurable_fixedRealSampleStudentizer n)

theorem measurable_fixedRealSampleStudentized_sample (n : ℕ) :
    Measurable (fun ξ : ℕ → ℝ =>
      fixedRealSampleStudentized
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)) :=
  (measurable_fixedRealSampleStudentized n).comp
    (Measurable.of_eval (fun i => measurable_fixedRealSampleCoordinate i.val))

theorem fixedRealSampleU_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleU (fun i => Shao.OQ5.P50.layerEncode (x i)) = fixedSampleU x := by
  simp only [fixedRealSampleU, fixedSampleU, fixedRealKernel_encode]

theorem fixedRealSampleStudentizerSq_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleStudentizerSq (fun i => Shao.OQ5.P50.layerEncode (x i)) =
      fixedSampleStudentizerSq x := by
  simp only [fixedRealSampleStudentizerSq, fixedSampleStudentizerSq, fixedRealKernel_encode]

theorem fixedRealSampleStudentizer_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleStudentizer (fun i => Shao.OQ5.P50.layerEncode (x i)) =
      fixedSampleStudentizer x := by
  simp only [fixedRealSampleStudentizer, fixedSampleStudentizer,
    fixedRealSampleStudentizerSq_encode]

theorem fixedRealSampleStudentized_encode (n : ℕ) (x : Fin n → LayerObs) :
    fixedRealSampleStudentized (fun i => Shao.OQ5.P50.layerEncode (x i)) =
      fixedSampleStudentized x := by
  simp only [fixedRealSampleStudentized, fixedSampleStudentized,
    fixedRealSampleU_encode, fixedRealSampleStudentizer_encode]

theorem fixedRealSampleStudentizer_prefix_pos_ae (n : ℕ) (hn : 3 ≤ n) :
    ∀ᵐ ξ ∂fixedRealSampleLaw,
      0 < fixedRealSampleStudentizer
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ) := by
  have hm : MeasurableSet {ξ : ℕ → ℝ |
      0 < fixedRealSampleStudentizer
        (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)} :=
    measurableSet_lt measurable_const
      ((measurable_fixedRealSampleStudentizer n).comp
        (Measurable.of_eval (fun i => measurable_fixedRealSampleCoordinate i.val)))
  unfold fixedRealSampleLaw
  apply (ae_map_iff measurable_encode_sample.aemeasurable hm).mpr
  simpa only [fixedRealSampleCoordinate, fixedSampleCoordinate,
    fixedRealSampleStudentizer_encode] using fixedSampleStudentizer_prefix_pos_ae n hn

theorem fixedRealSampleStudentizedTailProbability_eq (n : ℕ) (x : ℝ) :
    fixedRealSampleStudentizedTailProbability n x =
      fixedSampleStudentizedTailProbability n x := by
  let A : Set (ℕ → ℝ) := {ξ | x ≤ fixedRealSampleStudentized
    (fun i : Fin n => fixedRealSampleCoordinate i.val ξ)}
  let B : Set (ℕ → LayerObs) := {ω | x ≤ fixedSampleStudentized
    (fun i : Fin n => fixedSampleCoordinate i.val ω)}
  have hA : MeasurableSet A :=
    measurableSet_le measurable_const (measurable_fixedRealSampleStudentized_sample n)
  have hmass : fixedRealSampleLaw A = fixedSampleLaw B := by
    unfold fixedRealSampleLaw
    rw [Measure.map_apply measurable_encode_sample hA]
    congr 1
    ext ω
    change (x ≤ fixedRealSampleStudentized
      (fun i : Fin n => Shao.OQ5.P50.layerEncode (ω i.val))) ↔
        x ≤ fixedSampleStudentized (fun i : Fin n => ω i.val)
    rw [fixedRealSampleStudentized_encode]
  exact congrArg ENNReal.toReal hmass

theorem fixedRealSampleStudentizedTailProbability_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ fixedRealSampleStudentizedTailProbability n x := by
  rw [fixedRealSampleStudentizedTailProbability_eq]
  exact fixedSampleStudentizedTailProbability_nonneg n x

theorem fixedRealSampleStudentizedTailProbability_le_one (n : ℕ) (x : ℝ) :
    fixedRealSampleStudentizedTailProbability n x ≤ 1 := by
  rw [fixedRealSampleStudentizedTailProbability_eq]
  exact fixedSampleStudentizedTailProbability_le_one n x

end
end Shao.OQ5.P52
