import Shao.OQ3.WeakCramerPairCompactGap
import Shao.OQ3.EuclideanGaussianPolynomialIntegrability
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Shao.OQ3
open MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem pair_characteristic_small_frequency_weighted_integral_bound
    (rho : Measure (ℝ × ℝ)) [IsProbabilityMeasure rho]
    (n : ℕ) (hn : 1 ≤ n) (delta B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ xi eta : ℝ,
      Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
        (eta / Real.sqrt (n : ℝ)) ^ 2) ≤ delta →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
          ((Real.exp (-(xi ^ 2 + eta ^ 2) / 2) : ℝ) : ℂ)‖ ≤
        B / Real.sqrt (n : ℝ) * (Real.sqrt (xi ^ 2 + eta ^ 2)) ^ 3 *
          Real.exp (-(xi ^ 2 + eta ^ 2) / 8))
    (k : ℕ) :
    let small : Set (ℝ × ℝ) := {w |
      Real.sqrt ((w.1 / Real.sqrt (n : ℝ)) ^ 2 +
        (w.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ delta}
    let error : (ℝ × ℝ) → ℝ := fun z =>
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
          ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)‖
    let weight : (ℝ × ℝ) → ℝ := fun z => (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k
    let envelope : (ℝ × ℝ) → ℝ := fun z =>
      (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ (k + 3) *
        Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
    Integrable envelope ∧ IntegrableOn (fun z => weight z * error z) small ∧
      0 ≤ (∫ z in small, weight z * error z) ∧
      (∫ z in small, weight z * error z) ≤
        B / Real.sqrt (n : ℝ) * (∫ z : ℝ × ℝ, envelope z) := by
  dsimp only
  let small : Set (ℝ × ℝ) := {w |
    Real.sqrt ((w.1 / Real.sqrt (n : ℝ)) ^ 2 +
      (w.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ delta}
  let error : (ℝ × ℝ) → ℝ := fun z =>
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
        ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)‖
  let weight : (ℝ × ℝ) → ℝ := fun z => (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k
  let envelope : (ℝ × ℝ) → ℝ := fun z =>
    (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ (k + 3) *
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
  let c : ℝ := B / Real.sqrt (n : ℝ)
  have hc : 0 ≤ c := div_nonneg hB (Real.sqrt_nonneg _)
  have hen : Integrable envelope := by
    have hp := integrable_euclidean_radius_power_gaussian (k + 3) (1 / 8) (by norm_num)
    have hexp : ∀ z : ℝ × ℝ,
        Real.exp (-(1 / 8 : ℝ) * (z.1 ^ 2 + z.2 ^ 2)) =
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8) := by
      intro z
      congr 1
      ring
    simpa only [hexp] using hp
  have hg : Integrable (fun z => c * envelope z) := hen.const_mul c
  have hF : Continuous (fun z : ℝ × ℝ =>
      ∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) :=
    continuous_pair_characteristic rho
  have hG : Continuous (fun z : ℝ × ℝ =>
      ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)) := by fun_prop
  have hecont : Continuous error := (hF.sub hG).norm
  have hwcont : Continuous weight := by dsimp [weight]; fun_prop
  have hsmall : MeasurableSet small :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hnonneg : ∀ z : ℝ × ℝ, 0 ≤ weight z * error z := by
    intro z
    exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hbound : ∀ z ∈ small, weight z * error z ≤ c * envelope z := by
    intro z hz
    have h := mul_le_mul_of_nonneg_left (herror z.1 z.2 hz)
      (pow_nonneg (Real.sqrt_nonneg (z.1 ^ 2 + z.2 ^ 2)) k)
    calc
      weight z * error z ≤
          (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
            (B / Real.sqrt (n : ℝ) * (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ 3 *
              Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)) := h
      _ = c * envelope z := by
        dsimp [c, envelope]
        rw [pow_add]
        ring
  have hei : IntegrableOn (fun z => weight z * error z) small := by
    apply hg.integrableOn.mono' (hwcont.mul hecont).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hsmall] with z hz
    change ‖weight z * error z‖ ≤ c * envelope z
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
    exact hbound z hz
  refine ⟨hen, hei, integral_nonneg hnonneg, ?_⟩
  calc
    (∫ z in small, weight z * error z) ≤ ∫ z in small, c * envelope z :=
      setIntegral_mono_on hei hg.integrableOn hsmall hbound
    _ ≤ ∫ z : ℝ × ℝ, c * envelope z :=
      setIntegral_le_integral hg (Filter.Eventually.of_forall (fun z =>
        mul_nonneg hc (by dsimp [envelope]; positivity)))
    _ = c * (∫ z : ℝ × ℝ, envelope z) := by rw [integral_const_mul]

end
end Shao.OQ3
