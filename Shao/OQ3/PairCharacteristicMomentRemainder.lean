import Shao.OQ3.PairProjectionAbsoluteMoments
import Shao.OQ3.ScalarCharacteristicMomentRemainder

namespace Shao.OQ3
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem pair_probability_characteristic_moment_remainder_bound
    (law : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure law] (m : ℕ)
    (hM : Integrable (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) law)
    (u v : ℝ) :
    ‖(∫ y : Fin 2 → ℝ, Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂law) -
        (∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
          ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂law : ℝ) : ℂ))‖ ≤
      (Real.exp 1 + (m : ℝ) + 1) * Real.sqrt (u ^ 2 + v ^ 2) ^ m *
        (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law) := by
  let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
  let ν : Measure ℝ := law.map L
  have hLc : Continuous L := by
    dsimp [L]
    fun_prop
  have hproj := pair_projection_absolute_moment_bound law m hM u v
  have hνM : Integrable (fun x : ℝ => |x| ^ m) ν :=
    (integrable_map_measure (continuous_abs.pow m).aestronglyMeasurable
      hLc.measurable.aemeasurable).2 hproj.1
  letI : IsProbabilityMeasure ν := inferInstance
  have hcphase : Continuous (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) := by
    fun_prop
  have hcf : (∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) ∂ν) =
      ∫ y : Fin 2 → ℝ, Complex.exp (((L y : ℝ) : ℂ) * Complex.I) ∂law :=
    integral_map hLc.measurable.aemeasurable hcphase.aestronglyMeasurable
  have hmom (j : ℕ) : (∫ x : ℝ, x ^ j ∂ν) =
      ∫ y : Fin 2 → ℝ, (L y) ^ j ∂law :=
    integral_map hLc.measurable.aemeasurable (continuous_id.pow j).aestronglyMeasurable
  have hmoment : (∫ x : ℝ, |x| ^ m ∂ν) =
      ∫ y : Fin 2 → ℝ, |L y| ^ m ∂law :=
    integral_map hLc.measurable.aemeasurable (continuous_abs.pow m).aestronglyMeasurable
  have hs := scalar_characteristic_moment_remainder_bound ν m hνM 1
  simp only [one_mul, Complex.ofReal_one, abs_one, one_pow, mul_one] at hs
  rw [hcf, hmoment] at hs
  simp_rw [hmom] at hs
  have hC : 0 ≤ Real.exp 1 + (m : ℝ) + 1 := by positivity
  calc
    _ ≤ (Real.exp 1 + (m : ℝ) + 1) * (∫ y : Fin 2 → ℝ, |L y| ^ m ∂law) := by
      simpa only [L] using hs
    _ ≤ (Real.exp 1 + (m : ℝ) + 1) *
          (Real.sqrt (u ^ 2 + v ^ 2) ^ m *
            (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law)) :=
      mul_le_mul_of_nonneg_left hproj.2.2 hC
    _ = (Real.exp 1 + (m : ℝ) + 1) * Real.sqrt (u ^ 2 + v ^ 2) ^ m *
          (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂law) := by ring

theorem uniform_pair_characteristic_moment_remainder_bound
    {ι : Type*} (law : ι → Measure (Fin 2 → ℝ))
    (hprob : ∀ i, IsProbabilityMeasure (law i)) (m : ℕ) (M : ℝ)
    (hI : ∀ i, Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) (law i))
    (hM : ∀ i, (∫ y : Fin 2 → ℝ,
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂(law i)) ≤ M) :
    ∀ (i : ι) (u v : ℝ),
      ‖(∫ y : Fin 2 → ℝ,
          Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂(law i)) -
          (∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
            ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂(law i) : ℝ) : ℂ))‖ ≤
        (Real.exp 1 + (m : ℝ) + 1) * M * Real.sqrt (u ^ 2 + v ^ 2) ^ m := by
  intro i u v
  letI : IsProbabilityMeasure (law i) := hprob i
  have hC : 0 ≤ (Real.exp 1 + (m : ℝ) + 1) * Real.sqrt (u ^ 2 + v ^ 2) ^ m := by
    positivity
  calc
    _ ≤ (Real.exp 1 + (m : ℝ) + 1) * Real.sqrt (u ^ 2 + v ^ 2) ^ m *
          (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂(law i)) :=
      pair_probability_characteristic_moment_remainder_bound (law i) m (hI i) u v
    _ ≤ (Real.exp 1 + (m : ℝ) + 1) * Real.sqrt (u ^ 2 + v ^ 2) ^ m * M :=
      mul_le_mul_of_nonneg_left (hM i) hC
    _ = (Real.exp 1 + (m : ℝ) + 1) * M * Real.sqrt (u ^ 2 + v ^ 2) ^ m := by ring

end
end Shao.OQ3

