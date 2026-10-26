import Shao.OQ6.FiniteSignExponential
import Shao.OQ6.DoubleGhostSignInvariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

namespace Shao.OQ6.PairedSelfNormalizedTail

noncomputable section

open MeasureTheory
open scoped BigOperators
open Shao.OQ6.FiniteHilbertSignMoments (signValue cubeMean)
open Shao.OQ6.DoubleGhostSignInvariance (pairedLaw swapSample)
open Shao.OQ6.FiniteSignExponential (scalarSignSum scalarEnergy)

def pairedDifference
    (n : ℕ) {Ω : Type*} (g : Ω → ℝ)
    (z : Fin n → Ω × Ω) : Fin n → ℝ :=
  fun i : Fin n => g (z i).1 - g (z i).2

def pairedTailEvent
    (n : ℕ) {Ω : Type*} (g : Ω → ℝ) (t : ℝ) :
    Set (Fin n → Ω × Ω) :=
  {z : Fin n → Ω × Ω |
    t * Real.sqrt (scalarEnergy n (pairedDifference n g z)) <
      |∑ i : Fin n, pairedDifference n g z i|}

theorem paired_swap_spec
    (n : ℕ) {Ω : Type*} (g : Ω → ℝ)
    (s : Fin n → Bool) (z : Fin n → Ω × Ω) :
    (∀ i : Fin n,
      pairedDifference n g (swapSample n s z) i =
        signValue (s i) * pairedDifference n g z i) ∧
    scalarEnergy n (pairedDifference n g (swapSample n s z)) =
      scalarEnergy n (pairedDifference n g z) ∧
    (∑ i : Fin n, pairedDifference n g (swapSample n s z) i) =
      scalarSignSum n (pairedDifference n g z) s := by
  have hdiff (i : Fin n) :
      pairedDifference n g (swapSample n s z) i =
        signValue (s i) * pairedDifference n g z i := by
    cases hsi : s i <;>
      simp [pairedDifference, Shao.OQ6.DoubleGhostSignInvariance.swapSample,
        Shao.OQ6.DoubleGhostSignInvariance.pairSwap, signValue, hsi]
  refine ⟨hdiff, ?_, ?_⟩
  · unfold scalarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiff i]
    cases hsi : s i <;> simp [signValue, hsi]
  · unfold scalarSignSum
    apply Finset.sum_congr rfl
    intro i hi
    exact hdiff i

theorem measurableSet_pairedTailEvent
    (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (g : Ω → ℝ) (hg : Measurable g) (t : ℝ) :
    MeasurableSet (pairedTailEvent n g t) := by
  have henergy : Measurable (fun z : Fin n → Ω × Ω =>
      scalarEnergy n (pairedDifference n g z)) := by
    unfold scalarEnergy pairedDifference
    fun_prop
  have hsum : Measurable (fun z : Fin n → Ω × Ω =>
      ∑ i : Fin n, pairedDifference n g z i) := by
    unfold pairedDifference
    fun_prop
  exact measurableSet_lt
    (measurable_const.mul (Real.continuous_sqrt.measurable.comp henergy))
    (continuous_abs.measurable.comp hsum)

theorem paired_tail_cube_integral
    (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (t : ℝ) :
    (pairedLaw n μ).real (pairedTailEvent n g t) =
      ∫ z : Fin n → Ω × Ω,
        cubeMean n (fun s : Fin n → Bool =>
          if t * Real.sqrt (scalarEnergy n (pairedDifference n g z)) <
              |scalarSignSum n (pairedDifference n g z) s|
          then (1 : ℝ) else (0 : ℝ)) ∂pairedLaw n μ := by
  letI instP : IsProbabilityMeasure (pairedLaw n μ) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ.prod μ)))
  let D : Set (Fin n → Ω × Ω) := pairedTailEvent n g t
  let B : (Fin n → Bool) → Set (Fin n → Ω × Ω) :=
    fun s : Fin n → Bool => {z : Fin n → Ω × Ω |
      t * Real.sqrt (scalarEnergy n (pairedDifference n g z)) <
        |scalarSignSum n (pairedDifference n g z) s|}
  let I : (Fin n → Bool) → (Fin n → Ω × Ω) → ℝ :=
    fun (s : Fin n → Bool) (z : Fin n → Ω × Ω) =>
      if t * Real.sqrt (scalarEnergy n (pairedDifference n g z)) <
          |scalarSignSum n (pairedDifference n g z) s|
      then (1 : ℝ) else (0 : ℝ)
  have hD : MeasurableSet D := measurableSet_pairedTailEvent n g hg t
  have hpre (s : Fin n → Bool) :
      B s = (swapSample n s) ⁻¹' D := by
    ext z
    change (t * Real.sqrt (scalarEnergy n (pairedDifference n g z)) <
        |scalarSignSum n (pairedDifference n g z) s|) ↔
      (t * Real.sqrt (scalarEnergy n (pairedDifference n g (swapSample n s z))) <
        |∑ i : Fin n, pairedDifference n g (swapSample n s z) i|)
    rw [(paired_swap_spec n g s z).2.1, (paired_swap_spec n g s z).2.2]
  have hB (s : Fin n → Bool) : MeasurableSet (B s) := by
    rw [hpre s]
    exact hD.preimage
      (Shao.OQ6.DoubleGhostSignInvariance.swapSample_measurePreserving n μ s).measurable
  have hI_eq (s : Fin n → Bool) :
      I s = (B s).indicator (fun _ : Fin n → Ω × Ω => (1 : ℝ)) := by
    funext z
    by_cases hz : t * Real.sqrt (scalarEnergy n (pairedDifference n g z)) <
        |scalarSignSum n (pairedDifference n g z) s| <;>
      simp [I, B, Set.indicator, hz]
  have hI_int (s : Fin n → Bool) : Integrable (I s) (pairedLaw n μ) := by
    rw [hI_eq s]
    exact (integrable_const (1 : ℝ)).indicator (hB s)
  have hmass (s : Fin n → Bool) :
      (pairedLaw n μ).real (B s) = (pairedLaw n μ).real D := by
    change ((pairedLaw n μ) (B s)).toReal = ((pairedLaw n μ) D).toReal
    rw [hpre s,
      (Shao.OQ6.DoubleGhostSignInvariance.swapSample_measurePreserving n μ s).measure_preimage
        hD.nullMeasurableSet]
  have hint (s : Fin n → Bool) :
      (∫ z : Fin n → Ω × Ω, I s z ∂pairedLaw n μ) =
        (pairedLaw n μ).real D := by
    rw [hI_eq s, integral_indicator_const (μ := pairedLaw n μ) (1 : ℝ) (hB s)]
    simpa only [smul_eq_mul, mul_one] using hmass s
  change (pairedLaw n μ).real D =
    ∫ z : Fin n → Ω × Ω,
      ((2 : ℝ) ^ n)⁻¹ * ∑ s : Fin n → Bool, I s z ∂pairedLaw n μ
  rw [integral_const_mul,
    integral_finsetSum (Finset.univ : Finset (Fin n → Bool)) (fun s _ => hI_int s)]
  simp_rw [hint]
  simp [Fintype.card_fun, nsmul_eq_mul, ← mul_assoc]

theorem paired_selfnormalized_tail
    (n : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g)
    (t : ℝ) (ht : (0 : ℝ) ≤ t) :
    (pairedLaw n μ).real (pairedTailEvent n g t) ≤
      (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by
  letI instP : IsProbabilityMeasure (pairedLaw n μ) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => μ.prod μ)))
  rw [paired_tail_cube_integral n μ g hg t]
  calc
    (∫ z : Fin n → Ω × Ω,
      cubeMean n (fun s : Fin n → Bool =>
        if t * Real.sqrt (scalarEnergy n (pairedDifference n g z)) <
            |scalarSignSum n (pairedDifference n g z) s|
        then (1 : ℝ) else (0 : ℝ)) ∂pairedLaw n μ) ≤
        ∫ _ : Fin n → Ω × Ω,
          (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) ∂pairedLaw n μ := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with z
        unfold cubeMean
        apply mul_nonneg
        · exact inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
        · apply Finset.sum_nonneg
          intro s hs
          split_ifs with hcond <;> norm_num
      · exact integrable_const _
      · filter_upwards [] with z
        exact Shao.OQ6.FiniteSignExponential.finite_sign_two_sided_tail
          n (pairedDifference n g z) t ht
    _ = (2 : ℝ) * Real.exp (-(t ^ (2 : ℕ)) / (2 : ℝ)) := by simp

end

end Shao.OQ6.PairedSelfNormalizedTail
