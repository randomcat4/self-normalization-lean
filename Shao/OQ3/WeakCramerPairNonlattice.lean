import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Trigonometric

namespace Shao.OQ3
open MeasureTheory
open scoped Topology
noncomputable section

theorem pair_characteristic_modulus_one_ae_constant
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (u v : ℝ)
    (hmod : ‖(∫ w : ℝ × ℝ,
      Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ = 1) :
    Integrable (fun w : ℝ × ℝ =>
      Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I)) law ∧
      ∀ᵐ w ∂law,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) =
          ∫ z : ℝ × ℝ,
            Complex.exp (((u * z.1 + v * z.2 : ℝ) : ℂ) * Complex.I) ∂law := by
  let K : (ℝ × ℝ) → ℂ := fun w =>
    Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I)
  have hcont : Continuous K := by fun_prop
  have hnorm : ∀ w : ℝ × ℝ, ‖K w‖ = 1 := fun w =>
    Complex.norm_exp_ofReal_mul_I _
  have hint : Integrable K law := (integrable_const (1 : ℝ)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun w => (hnorm w).le))
  letI : StrictConvexSpace ℝ ℂ := by
    apply StrictConvexSpace.of_norm_add_ne_two
    intro x y hx hy hne hsum
    have hpar := parallelogram_law_with_norm ℝ x y
    rw [hx, hy, hsum] at hpar
    have hzero : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp hzero))
  have hdich := ae_eq_const_or_norm_integral_lt_of_norm_le_const
    (μ := law) (f := K) (C := (1 : ℝ))
    (Filter.Eventually.of_forall (fun w => (hnorm w).le))
  refine ⟨hint, ?_⟩
  rcases hdich with heq | hlt
  · change ∀ᵐ w ∂law, K w = ∫ z, K z ∂law
    change ∀ᵐ w ∂law, K w = ⨍ z, K z ∂law at heq
    simpa [average_eq] using heq
  · have hlt' : ‖(∫ w, K w ∂law)‖ < 1 := by simpa using hlt
    exact ((ne_of_lt hlt') hmod).elim

theorem weak_cramer_pair_characteristic_norm_lt_one
    (law : Measure (ℝ × ℝ)) [IsProbabilityMeasure law]
    (beta c R : ℝ) (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ u v : ℝ, R < Real.sqrt (u ^ 2 + v ^ 2) →
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ ≤
          1 - c * Real.rpow (Real.sqrt (u ^ 2 + v ^ 2)) (-beta))
    (u v : ℝ) (hne : u ≠ 0 ∨ v ≠ 0) :
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂law)‖ < 1 := by
  let K : (ℝ × ℝ) → ℂ := fun w =>
    Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I)
  have hnorm : ∀ w : ℝ × ℝ, ‖K w‖ = 1 := fun w =>
    Complex.norm_exp_ofReal_mul_I _
  have hcont : Continuous K := by fun_prop
  have hint : Integrable K law := (integrable_const (1 : ℝ)).mono'
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun w => (hnorm w).le))
  have hle : ‖(∫ w, K w ∂law)‖ ≤ 1 := by
    calc
      ‖(∫ w, K w ∂law)‖ ≤ ∫ w, ‖K w‖ ∂law := norm_integral_le_integral_norm K
      _ = 1 := by simp [hnorm]
  by_contra hnot
  have hmod : ‖(∫ w, K w ∂law)‖ = 1 :=
    le_antisymm hle (le_of_not_gt hnot)
  have hae := (pair_characteristic_modulus_one_ae_constant law u v hmod).2
  let zeta : ℂ := ∫ w, K w ∂law
  have hr : 0 < Real.sqrt (u ^ 2 + v ^ 2) := by
    apply Real.sqrt_pos.mpr
    rcases hne with hu | hv
    · nlinarith [sq_pos_of_ne_zero hu, sq_nonneg v]
    · nlinarith [sq_pos_of_ne_zero hv, sq_nonneg u]
  obtain ⟨m, hm⟩ := exists_nat_gt (R / Real.sqrt (u ^ 2 + v ^ 2))
  have hrad : Real.sqrt (((m : ℝ) * u) ^ 2 + ((m : ℝ) * v) ^ 2) =
      (m : ℝ) * Real.sqrt (u ^ 2 + v ^ 2) := by
    rw [show ((m : ℝ) * u) ^ 2 + ((m : ℝ) * v) ^ 2 =
      (m : ℝ) ^ 2 * (u ^ 2 + v ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg (m : ℝ)), Real.sqrt_sq (Nat.cast_nonneg m)]
  have hfreq : R < Real.sqrt (((m : ℝ) * u) ^ 2 + ((m : ℝ) * v) ^ 2) := by
    rw [hrad]
    exact (div_lt_iff₀ hr).mp hm
  have haepower : (fun w : ℝ × ℝ =>
      Complex.exp (((((m : ℝ) * u) * w.1 + ((m : ℝ) * v) * w.2 : ℝ) : ℂ) *
        Complex.I)) =ᵐ[law] (fun _ => zeta ^ m) := by
    filter_upwards [hae] with w hw
    have hexp : Complex.exp
        (((((m : ℝ) * u) * w.1 + ((m : ℝ) * v) * w.2 : ℝ) : ℂ) * Complex.I) =
        (K w) ^ m := by
      dsimp only [K]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp]
    exact congrArg (fun z : ℂ => z ^ m) hw
  have hpower : (∫ w : ℝ × ℝ,
      Complex.exp (((((m : ℝ) * u) * w.1 + ((m : ℝ) * v) * w.2 : ℝ) : ℂ) *
        Complex.I) ∂law) = zeta ^ m := by
    rw [integral_congr_ae haepower]
    simp
  have hmodpower : ‖(∫ w : ℝ × ℝ,
      Complex.exp (((((m : ℝ) * u) * w.1 + ((m : ℝ) * v) * w.2 : ℝ) : ℂ) *
        Complex.I) ∂law)‖ = 1 := by
    rw [hpower, norm_pow, hmod, one_pow]
  have hwc := hWC ((m : ℝ) * u) ((m : ℝ) * v) hfreq
  rw [hmodpower] at hwc
  have hpos := mul_pos hc (Real.rpow_pos_of_pos (lt_of_le_of_lt hR hfreq) (-beta))
  simp only [Real.rpow_eq_pow] at hwc hpos
  linarith

end
end Shao.OQ3
