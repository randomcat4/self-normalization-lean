import Shao.OQ3.WeakCramerPairCompactGap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem pair_characteristic_bounded_frequency_weighted_integral_bound
    (rho : Measure (ℝ × ℝ)) [IsProbabilityMeasure rho]
    (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (K epsilon : ℝ) (hK : 0 ≤ K) (hepsilon : 0 ≤ epsilon)
    (hrad : ∀ z ∈ D, Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ K)
    (hCF : ∀ z ∈ D,
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤ epsilon)
    (k : ℕ) :
    let f : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
        ‖(∫ w : ℝ × ℝ,
          Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
    IntegrableOn f D ∧ 0 ≤ (∫ z in D, f z) ∧
      (∫ z in D, f z) ≤ 4 * K ^ (k + 2) * epsilon
 := by
  let f : (ℝ × ℝ) → ℝ := fun z =>
    (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
  change IntegrableOn f D ∧ 0 ≤ (∫ z in D, f z) ∧
    (∫ z in D, f z) ≤ 4 * K ^ (k + 2) * epsilon
  let box : Set (ℝ × ℝ) := Set.Icc (-K) K ×ˢ Set.Icc (-K) K
  have hsubset : D ⊆ box := by
    intro z hz
    have hs : (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ 2 = z.1 ^ 2 + z.2 ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have h1 : |z.1| ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := by
      nlinarith [sq_nonneg z.2, sq_abs z.1, abs_nonneg z.1,
        Real.sqrt_nonneg (z.1 ^ 2 + z.2 ^ 2)]
    have h2 : |z.2| ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) := by
      nlinarith [sq_nonneg z.1, sq_abs z.2, abs_nonneg z.2,
        Real.sqrt_nonneg (z.1 ^ 2 + z.2 ^ 2)]
    exact ⟨abs_le.mp (h1.trans (hrad z hz)), abs_le.mp (h2.trans (hrad z hz))⟩
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hrcont : Continuous (fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) := by
    fun_prop
  have hfcont : Continuous f := (hrcont.pow k).mul (continuous_pair_characteristic rho).norm
  have hfIbox : IntegrableOn f box :=
    ContinuousOn.integrableOn_compact hbox hfcont.continuousOn
  have hfID : IntegrableOn f D := hfIbox.mono_set hsubset
  have hcIbox : IntegrableOn (fun _ : ℝ × ℝ => K ^ k * epsilon) box :=
    ContinuousOn.integrableOn_compact hbox continuous_const.continuousOn
  have hcID : IntegrableOn (fun _ : ℝ × ℝ => K ^ k * epsilon) D :=
    hcIbox.mono_set hsubset
  have hbound : ∀ z ∈ D, f z ≤ K ^ k * epsilon := by
    intro z hz
    exact mul_le_mul
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) (hrad z hz) k)
      (hCF z hz) (norm_nonneg _) (pow_nonneg hK k)
  have hDle : (∫ z in D, f z) ≤ ∫ _ : ℝ × ℝ in D, K ^ k * epsilon :=
    setIntegral_mono_on hfID hcID hD hbound
  have hboxle : (∫ _ : ℝ × ℝ in D, K ^ k * epsilon) ≤
      ∫ _ : ℝ × ℝ in box, K ^ k * epsilon :=
    setIntegral_mono_set hcIbox
      (Filter.Eventually.of_forall (fun _ => mul_nonneg (pow_nonneg hK k) hepsilon))
      (Filter.Eventually.of_forall (fun z hz => hsubset hz))
  have hvol : volume.real (Set.Icc (-K) K) = 2 * K := by
    rw [Real.volume_real_Icc, max_eq_left (by linarith : 0 ≤ K - -K)]
    ring
  have harea : (∫ _ : ℝ × ℝ in box, K ^ k * epsilon) =
      4 * K ^ (k + 2) * epsilon := by
    calc
      _ = (∫ _ : ℝ in Set.Icc (-K) K, K ^ k * epsilon) *
          (∫ _ : ℝ in Set.Icc (-K) K, (1 : ℝ)) := by
        simpa only [box, mul_one, Measure.volume_eq_prod] using
          (setIntegral_prod_mul (μ := volume) (ν := volume)
            (fun _ : ℝ => K ^ k * epsilon) (fun _ : ℝ => (1 : ℝ))
            (Set.Icc (-K) K) (Set.Icc (-K) K))
      _ = 4 * K ^ (k + 2) * epsilon := by
        rw [setIntegral_const, setIntegral_const, hvol]
        simp only [smul_eq_mul, pow_add, pow_two]
        ring
  refine ⟨hfID, integral_nonneg (fun z => ?_), hDle.trans (hboxle.trans harea.le)⟩
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)

end
end Shao.OQ3
