import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Shao.OQ6.CappedSectionEnergy

noncomputable section

open MeasureTheory

theorem capped_sqrt_energy_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ) (hg : Measurable g) (hg2 : MemLp g 2 μ)
    (hgsecond : (∫ o, g o ^ 2 ∂μ) = 1)
    (R : Ω → ℝ) (hR : Measurable R)
    (hRnonneg : ∀ o, 0 ≤ R o) (hRint : Integrable R μ)
    (s : ℝ) (hs : 0 ≤ s)
    (hRsecond : (∫ o, R o ∂μ) ≤ s ^ 2)
    (a : ℝ) (ha : 0 ≤ a) :
    let cap : Ω → ℝ := fun o => min |a * g o| 1
    Integrable (fun o => cap o * Real.sqrt (R o)) μ ∧
      (∫ o, cap o * Real.sqrt (R o) ∂μ) ≤ a * s := by
  let cap : Ω → ℝ := fun o => min |a * g o| 1
  change Integrable (fun o => cap o * Real.sqrt (R o)) μ ∧
    (∫ o, cap o * Real.sqrt (R o) ∂μ) ≤ a * s
  have hag : Measurable (fun o => a * g o) := measurable_const.mul hg
  have hcapmeas : Measurable cap := by
    simpa only [cap, Real.norm_eq_abs] using hag.norm.min measurable_const
  have hcapnonneg : ∀ o, 0 ≤ cap o := fun o =>
    le_min (abs_nonneg _) (by norm_num)
  have hcaple : ∀ o, cap o ≤ a * |g o| := fun o => by
    calc
      cap o ≤ |a * g o| := min_le_left _ _
      _ = a * |g o| := by rw [abs_mul, abs_of_nonneg ha]
  have hsqrtmeas : Measurable (fun o => Real.sqrt (R o)) := hR.sqrt
  have hsqrtSq : ∀ o, Real.sqrt (R o) ^ 2 = R o :=
    fun o => Real.sq_sqrt (hRnonneg o)
  have hsqrt2 : MemLp (fun o => Real.sqrt (R o)) 2 μ := by
    apply (memLp_two_iff_integrable_sq hsqrtmeas.aestronglyMeasurable).2
    simpa only [hsqrtSq] using hRint
  have hgabs2 : MemLp (fun o => |g o|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hg2.norm
  have hmajor : Integrable (fun o => a * (|g o| * Real.sqrt (R o))) μ :=
    (hgabs2.integrable_mul hsqrt2).const_mul a
  have hpoint : ∀ o, cap o * Real.sqrt (R o) ≤
      a * (|g o| * Real.sqrt (R o)) := fun o => by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hcaple o) (Real.sqrt_nonneg (R o))
  have hcapint : Integrable (fun o => cap o * Real.sqrt (R o)) μ := by
    apply hmajor.mono' (hcapmeas.mul hsqrtmeas).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun o => by
      change |cap o * Real.sqrt (R o)| ≤ a * (|g o| * Real.sqrt (R o))
      rw [abs_of_nonneg (mul_nonneg (hcapnonneg o) (Real.sqrt_nonneg (R o)))]
      exact hpoint o
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      (2 : ℝ).HolderConjugate 2)
    (by simpa using hg2) (by simpa using hsqrt2)
  have hsqrtabs : ∀ o, |Real.sqrt (R o)| = Real.sqrt (R o) :=
    fun o => abs_of_nonneg (Real.sqrt_nonneg (R o))
  have hCS : (∫ o, |g o| * Real.sqrt (R o) ∂μ) ≤
      Real.sqrt (∫ o, g o ^ 2 ∂μ) *
        Real.sqrt (∫ o, Real.sqrt (R o) ^ 2 ∂μ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two,
      ← Real.sqrt_eq_rpow, sq_abs, hsqrtabs] using hh
  have hsqrtbound : Real.sqrt (∫ o, R o ∂μ) ≤ s := by
    calc
      _ ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hRsecond
      _ = s := Real.sqrt_sq hs
  have hbudget : (∫ o, |g o| * Real.sqrt (R o) ∂μ) ≤ s := by
    calc
      _ ≤ Real.sqrt (∫ o, g o ^ 2 ∂μ) *
          Real.sqrt (∫ o, Real.sqrt (R o) ^ 2 ∂μ) := hCS
      _ = Real.sqrt (∫ o, R o ∂μ) := by
        simp only [hsqrtSq, hgsecond, Real.sqrt_one, one_mul]
      _ ≤ s := hsqrtbound
  refine ⟨hcapint, ?_⟩
  calc
    _ ≤ ∫ o, a * (|g o| * Real.sqrt (R o)) ∂μ :=
      integral_mono hcapint hmajor hpoint
    _ = a * (∫ o, |g o| * Real.sqrt (R o) ∂μ) := by
      rw [integral_const_mul]
    _ ≤ a * s := mul_le_mul_of_nonneg_left hbudget ha

end

end Shao.OQ6.CappedSectionEnergy
