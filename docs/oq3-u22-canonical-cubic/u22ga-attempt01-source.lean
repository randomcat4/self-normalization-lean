import Shao.OQ3.DirectionalMomentPolynomialContinuity
import Shao.OQ3.GaussianFiniteHermiteIntegral
import Shao.OQ3.CompactOpenDomainSixOrderGaussianPolynomialTail
import Shao.OQ3.ActualCGFFirstWeightGaussianZero
import Shao.OQ3.ActualMixedThirdMomentHermiteBound

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000

theorem pair_third_moment_gaussian_hermite_integral
    (mu : Measure (Fin 2 → ℝ))
    (hM : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) mu) :
    let M : (ℝ × ℝ) → ℝ := fun z =>
      ∫ y : Fin 2 → ℝ, (z.1 * y 0 + z.2 * y 1) ^ 3 ∂mu
    let b : Fin 4 → ℝ := fun j =>
      ∫ y : Fin 2 → ℝ, y 0 ^ j.val * y 1 ^ (3 - j.val) ∂mu
    let P1 : (ℝ × ℝ) → ℝ := fun x => (1 / 6 : ℝ) *
      ∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * b j *
        (gaussianHermitePolynomial j.val).eval x.1 *
          (gaussianHermitePolynomial (3 - j.val)).eval x.2
    ∀ x : ℝ × ℝ,
      Integrable (fun z : ℝ × ℝ =>
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          (Complex.I ^ 3 / 6) * (M z : ℂ) *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
      (∫ z : ℝ × ℝ,
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          (Complex.I ^ 3 / 6) * (M z : ℂ) *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
        ((2 * Real.pi * P1 x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
  classical
  intro M b P1 x
  let s : Finset (ℕ × ℕ) := {(0, 3), (1, 2), (2, 1), (3, 0)}
  let a : (ℕ × ℕ) → ℝ := fun k => (Nat.choose 3 k.1 : ℝ) *
    (∫ y : Fin 2 → ℝ, y 0 ^ k.1 * y 1 ^ (3 - k.1) ∂mu) / 6
  have hMformula (z : ℝ × ℝ) : M z =
      ∑ j ∈ Finset.range 4, z.1 ^ j * z.2 ^ (3 - j) * (Nat.choose 3 j : ℝ) *
        (∫ y : Fin 2 → ℝ, y 0 ^ j * y 1 ^ (3 - j) ∂mu) :=
    (pair_directional_moment_binomial_continuous mu 3 hM).2.1 z
  have hpoly (z : ℝ × ℝ) :
      (∑ k ∈ s, (a k : ℂ) *
        (Complex.I * (z.1 : ℂ)) ^ k.1 * (Complex.I * (z.2 : ℂ)) ^ k.2) =
      (Complex.I ^ 3 / 6) * (M z : ℂ) := by
    rw [hMformula]
    norm_num [s, a, Finset.sum_range_succ]
    push_cast
    ring
  have hHermite :
      (∑ k ∈ s, a k * (gaussianHermitePolynomial k.1).eval x.1 *
        (gaussianHermitePolynomial k.2).eval x.2) = P1 x := by
    norm_num [s, a, b, P1, Fin.sum_univ_succ]
    ring
  have h := pair_standard_gaussian_finite_hermite_integral s a x
  simpa only [hpoly, hHermite, mul_assoc] using h

theorem compact_open_domain_first_hermite_correction_uniform
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hdet : ∀ p ∈ Theta, 0 < (parabolaCovariance
      (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det)
    (hWC : ∀ p ∈ Theta, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
      ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - means p)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
    let Phi : (ℝ × ℝ) → ℝ → ℝ → ℂ := fun p xi eta =>
      ∫ y : Fin 2 → ℝ,
        Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂laws p
    let b : Theta → Fin 4 → ℝ := fun p j =>
      ∫ y : Fin 2 → ℝ, y 0 ^ j.val * y 1 ^ (3 - j.val) ∂laws p
    let P1 : Theta → (ℝ × ℝ) → ℝ := fun p x => (1 / 6 : ℝ) *
      ∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * b p j *
        (gaussianHermitePolynomial j.val).eval x.1 *
          (gaussianHermitePolynomial (3 - j.val)).eval x.2
    ∃ C : ℝ, 0 < C ∧ ∀ p : Theta,
      P1 p (0, 0) = 0 ∧
      (∀ x : ℝ × ℝ, Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ 1 →
        |P1 p x| ≤ C * Real.sqrt (x.1 ^ 2 + x.2 ^ 2)) ∧
      ∀ n : ℕ, 1 ≤ n →
        let kappa : (ℝ × ℝ) → ℕ → ℝ := fun z j =>
          iteratedDeriv j (ProbabilityTheory.cgf
            (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) (laws p)) 0
        let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
          (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
            (kappa z (j.val + 3) : ℂ) /
              (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
        let S1 : (ℝ × ℝ) → ℂ := fun z =>
          ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
            ∑ sigma : Fin q.val → Fin 6,
              if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a z (sigma i) else 0
        ∀ x : ℝ × ℝ,
          Integrable (fun z : ℝ × ℝ =>
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
              S1 z * Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
          (∫ z : ℝ × ℝ,
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
              S1 z * Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
            ((2 * Real.pi * P1 p x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) /
              Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
  classical
  intro tilt D s t A means Y laws Phi b P1
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized, hocticExp, horderSix, hweighted, htail⟩ :=
    compact_open_domain_six_order_gaussian_polynomial_tail mu Theta hcompact hTheta
      beta c R hbeta hc hR hdet hWC
  obtain ⟨B, hBpos, hBound⟩ := hmom 3
  have hM (p : Theta) : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (laws p) := (hBound p p.property).1
  have hBM (p : Theta) :
      (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂laws p) ≤ B :=
    (hBound p p.property).2.2
  have hUniform := uniform_actual_moment_cubic_hermite_local_bound
    (fun p : Theta => laws p) B hBpos.le hM hBM
  refine ⟨(16 / 3 : ℝ) * B, by positivity, ?_⟩
  intro p
  refine ⟨(hUniform p).1, (hUniform p).2, ?_⟩
  intro n hn kappa a S1 x
  have hk (z : ℝ × ℝ) :
      iteratedDeriv 3 (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) (laws p)) 0 =
      (∫ y : Fin 2 → ℝ, (z.1 * y 0 + z.2 * y 1) ^ 3 ∂laws p) :=
    (hcgf p p.property z.1 z.2).2.2.1
  have hS (z : ℝ × ℝ) : S1 z =
      (1 / (Real.sqrt (n : ℝ) : ℂ)) * (Complex.I ^ 3 / 6) *
        ((∫ y : Fin 2 → ℝ, (z.1 * y 0 + z.2 * y 1) ^ 3 ∂laws p : ℝ) : ℂ) := by
    have hword : S1 z = a z 0 := six_order_word_weight_one (a z)
    rw [hword]
    change (Complex.I ^ 3 / 6) *
      ((iteratedDeriv 3 (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) (laws p)) 0 : ℝ) : ℂ) /
        (Real.sqrt (n : ℝ) : ℂ) ^ 1 = _
    rw [hk]
    simp only [div_eq_mul_inv, pow_one]
    ring
  have hf :
      (fun z : ℝ × ℝ =>
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          S1 z * Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
      fun z : ℝ × ℝ => (1 / (Real.sqrt (n : ℝ) : ℂ)) *
        (Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
          (Complex.I ^ 3 / 6) *
            ((∫ y : Fin 2 → ℝ, (z.1 * y 0 + z.2 * y 1) ^ 3 ∂laws p : ℝ) : ℂ) *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) := by
    funext z
    rw [hS]
    ring
  have hGen := pair_third_moment_gaussian_hermite_integral (laws p) (hM p) x
  rw [hf]
  constructor
  · exact hGen.1.const_mul _
  · rw [integral_const_mul, hGen.2]
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hsn : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hnpos).ne'
    push_cast
    field_simp [hsn] <;> ring

theorem sqrt_sample_scaled_local_correction_bound
    {iota : Type*} (P : iota → (ℝ × ℝ) → ℝ) (C K : ℝ) (hC : 0 ≤ C)
    (hP : ∀ p : iota, ∀ x : ℝ × ℝ,
      Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ 1 →
        |P p x| ≤ C * Real.sqrt (x.1 ^ 2 + x.2 ^ 2))
    (n : ℕ) (hn : 1 ≤ n) (hKn : K ≤ Real.sqrt (n : ℝ))
    (p : iota) (x : ℝ × ℝ)
    (hx : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ K / Real.sqrt (n : ℝ)) :
    |P p x| / Real.sqrt (n : ℝ) ≤ C * K / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  have hr1 : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ 1 :=
    hx.trans ((div_le_one hs).2 hKn)
  calc
    _ ≤ (C * (K / Real.sqrt (n : ℝ))) / Real.sqrt (n : ℝ) :=
      div_le_div_of_nonneg_right
        ((hP p x hr1).trans (mul_le_mul_of_nonneg_left hx hC)) hs.le
    _ = C * K / (Real.sqrt (n : ℝ) ^ 2) := by field_simp [hs.ne'] <;> ring
    _ = C * K / (n : ℝ) := by rw [hs2]

end
end Shao.OQ3
