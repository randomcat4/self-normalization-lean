import Shao.OQ6.ActualQuadraticTiltMoments

set_option autoImplicit false
universe u
open MeasureTheory
open scoped ENNReal
namespace Shao.OQ6.OriginalEnvelopeRhoBound
noncomputable section

theorem original_residual_rho_le_envelope_second_moment
    {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [hμ : IsProbabilityMeasure μ]
    (r : Ω → Ω → ℝ)
    (hr2 : MemLp (Function.uncurry r) 2 (μ.prod μ))
    (w : Ω → ℝ)
    (hW : ∀ᵐ o : Ω ∂μ, 0 ≤ w o)
    (hSq : Integrable (fun o : Ω => (w o) ^ (2 : ℕ)) μ)
    (M : ℝ) (hM : 0 ≤ M)
    (hSqBound : (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ≤ M)
    (hEnv : ∀ᵐ o : Ω × Ω ∂μ.prod μ,
      |r o.1 o.2| ≤ w o.1 * w o.2) :
    let v : ℝ := ∫ o : Ω × Ω, (r o.1 o.2) ^ (2 : ℕ) ∂μ.prod μ
    let rho : ℝ := Real.sqrt v
    0 ≤ v ∧ v ≤ M ^ (2 : ℕ) ∧ 0 ≤ rho ∧ rho ≤ M
:= by
  dsimp only
  have hrSq : Integrable
      (fun o : Ω × Ω => (r o.1 o.2) ^ (2 : ℕ)) (μ.prod μ) := by
    simpa only [Function.uncurry] using hr2.integrable_sq
  have hProductSq : Integrable
      (fun o : Ω × Ω => (w o.1) ^ (2 : ℕ) * (w o.2) ^ (2 : ℕ))
      (μ.prod μ) := hSq.mul_prod hSq
  have hSquareEnvelope : ∀ᵐ o : Ω × Ω ∂μ.prod μ,
      (r o.1 o.2) ^ (2 : ℕ) ≤
        (w o.1) ^ (2 : ℕ) * (w o.2) ^ (2 : ℕ) := by
    filter_upwards [hEnv] with o ho
    have hSquare := pow_le_pow_left₀ (abs_nonneg (r o.1 o.2)) ho (2 : ℕ)
    simpa only [sq_abs, mul_pow] using hSquare
  have hvNonneg :
      0 ≤ ∫ o : Ω × Ω, (r o.1 o.2) ^ (2 : ℕ) ∂μ.prod μ :=
    integral_nonneg (fun o => sq_nonneg (r o.1 o.2))
  have hEnvelopeMomentNonneg :
      0 ≤ ∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ :=
    integral_nonneg (fun o => sq_nonneg (w o))
  have hvBound :
      (∫ o : Ω × Ω, (r o.1 o.2) ^ (2 : ℕ) ∂μ.prod μ) ≤ M ^ (2 : ℕ) := by
    calc
      (∫ o : Ω × Ω, (r o.1 o.2) ^ (2 : ℕ) ∂μ.prod μ) ≤
          ∫ o : Ω × Ω, (w o.1) ^ (2 : ℕ) * (w o.2) ^ (2 : ℕ) ∂μ.prod μ :=
        integral_mono_ae hrSq hProductSq hSquareEnvelope
      _ = (∫ o : Ω, (w o) ^ (2 : ℕ) ∂μ) ^ (2 : ℕ) := by
        simpa only [pow_two] using
          (integral_prod_mul (μ := μ) (ν := μ)
            (fun o : Ω => (w o) ^ (2 : ℕ))
            (fun o : Ω => (w o) ^ (2 : ℕ)))
      _ ≤ M ^ (2 : ℕ) :=
        pow_le_pow_left₀ hEnvelopeMomentNonneg hSqBound (2 : ℕ)
  refine ⟨hvNonneg, hvBound, Real.sqrt_nonneg _, ?_⟩
  calc
    Real.sqrt (∫ o : Ω × Ω, (r o.1 o.2) ^ (2 : ℕ) ∂μ.prod μ) ≤
        Real.sqrt (M ^ (2 : ℕ)) := Real.sqrt_le_sqrt hvBound
    _ = M := Real.sqrt_sq hM
end
end Shao.OQ6.OriginalEnvelopeRhoBound
