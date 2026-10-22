import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic

/-!
# Bivariate logarithmic moment generating function and Legendre rate

The logarithm is defined only on the true exponential integrability domain.
The Legendre transform takes values in `EReal`, including infinite values.
The four public statements are frozen in shared-global-rate v1.
-/

namespace Shao.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

def bivariateMGFDomain (μ : Measure Ω) (W : Ω → ℝ × ℝ) : Set (ℝ × ℝ) :=
  {θ | Integrable
    (fun ω => Real.exp (θ.1 * (W ω).1 + θ.2 * (W ω).2)) μ}

def bivariateLogMGF (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (θ : bivariateMGFDomain μ W) : ℝ :=
  Real.log (∫ ω, Real.exp
    ((θ : ℝ × ℝ).1 * (W ω).1 + (θ : ℝ × ℝ).2 * (W ω).2) ∂μ)

def bivariateLegendreRate (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (z : ℝ × ℝ) : EReal :=
  ⨆ θ : bivariateMGFDomain μ W,
    (((θ : ℝ × ℝ).1 * z.1 + (θ : ℝ × ℝ).2 * z.2 -
      bivariateLogMGF μ W θ : ℝ) : EReal)

theorem bivariateLogMGF_spec
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (θ : bivariateMGFDomain μ W) :
    (0 < (∫ ω, Real.exp
      ((θ : ℝ × ℝ).1 * (W ω).1 + (θ : ℝ × ℝ).2 * (W ω).2) ∂μ)) ∧
    Real.exp (bivariateLogMGF μ W θ) =
      (∫ ω, Real.exp
        ((θ : ℝ × ℝ).1 * (W ω).1 + (θ : ℝ × ℝ).2 * (W ω).2) ∂μ) := by
  have hpos := MeasureTheory.integral_exp_pos θ.property
  exact ⟨hpos, Real.exp_log hpos⟩

theorem bivariateLegendreRate_test_le
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (z : ℝ × ℝ) (θ : bivariateMGFDomain μ W) :
    (((θ : ℝ × ℝ).1 * z.1 + (θ : ℝ × ℝ).2 * z.2 -
      bivariateLogMGF μ W θ : ℝ) : EReal) ≤
      bivariateLegendreRate μ W z := by
  exact le_iSup (fun θ : bivariateMGFDomain μ W =>
    (((θ : ℝ × ℝ).1 * z.1 + (θ : ℝ × ℝ).2 * z.2 -
      bivariateLogMGF μ W θ : ℝ) : EReal)) θ

theorem bivariateLegendreRate_eq_of_attained_bound
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (z₀ : ℝ × ℝ) (L : ℝ)
    (hupper : ∀ θ : bivariateMGFDomain μ W,
      (θ : ℝ × ℝ).1 * z₀.1 + (θ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ ≤ L)
    (θ₀ : bivariateMGFDomain μ W)
    (hattain :
      (θ₀ : ℝ × ℝ).1 * z₀.1 + (θ₀ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ₀ = L) :
    bivariateLegendreRate μ W z₀ = (L : EReal) := by
  apply le_antisymm
  · exact iSup_le (fun θ => EReal.coe_le_coe_iff.mpr (hupper θ))
  · have htest := bivariateLegendreRate_test_le μ W z₀ θ₀
    rw [hattain] at htest
    exact htest

theorem bivariateLegendreRate_unique_minimizer_of_tests
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (z₀ : ℝ × ℝ) (L : ℝ)
    (hz₀ : z₀ ∈ D)
    (hupper : ∀ θ : bivariateMGFDomain μ W,
      (θ : ℝ × ℝ).1 * z₀.1 + (θ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ ≤ L)
    (θ₀ : bivariateMGFDomain μ W)
    (hattain :
      (θ₀ : ℝ × ℝ).1 * z₀.1 + (θ₀ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ₀ = L)
    (hsep : ∀ z ∈ D, z ≠ z₀ →
      ∃ θ : bivariateMGFDomain μ W,
        L < (θ : ℝ × ℝ).1 * z.1 + (θ : ℝ × ℝ).2 * z.2 -
          bivariateLogMGF μ W θ) :
    bivariateLegendreRate μ W z₀ = (L : EReal) ∧
      (∀ z ∈ D,
        bivariateLegendreRate μ W z₀ ≤ bivariateLegendreRate μ W z ∧
        (bivariateLegendreRate μ W z = bivariateLegendreRate μ W z₀ ↔ z = z₀)) := by
  classical
  have hvalue := bivariateLegendreRate_eq_of_attained_bound μ W z₀ L
    hupper θ₀ hattain
  refine ⟨hvalue, ?_⟩
  intro z hz
  by_cases hzz : z = z₀
  · subst z
    exact ⟨le_rfl, ⟨fun _ => rfl, fun _ => rfl⟩⟩
  · obtain ⟨θ, hstrict⟩ := hsep z hz hzz
    have hrate : bivariateLegendreRate μ W z₀ < bivariateLegendreRate μ W z := by
      rw [hvalue]
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hstrict)
        (bivariateLegendreRate_test_le μ W z θ)
    refine ⟨hrate.le, ?_⟩
    constructor
    · intro heq
      exact False.elim (hrate.ne heq.symm)
    · intro heq
      exact False.elim (hzz heq)

end

end Shao.Probability
