import Shao.OQ3.CompactOpenDomainUniformCGFCumulantBounds
import Shao.OQ3.ActualCubicHermiteCorrection
import Shao.OQ3.ActualCGFHigherWeightGaussianIntegral
import Shao.OQ3.SixOrderWordHigherDecomposition
import Shao.OQ3.GaussianMvPolynomialHermiteIntegral

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_hermite_first_correction_remainder_bound
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
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
      let X : (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ := fun z y => z.1 * y 0 + z.2 * y 1
      let kappa : ℕ → (ℝ × ℝ) → ℝ := fun j z =>
        iteratedDeriv j (ProbabilityTheory.cgf (X z) (laws p)) 0
      let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
        (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
          (kappa (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
      let Sn : (ℝ × ℝ) → ℂ := fun z =>
        ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a z (sigma l) else 0
      let G : (ℝ × ℝ) → ℂ := fun z => Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)
      let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
        Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
      let phi : (ℝ × ℝ) → ℝ := fun x =>
        (1 / (2 * Real.pi)) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
      ∀ H : MvPolynomial (Fin 2) ℝ,
        (∀ z : ℝ × ℝ, MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] H = Sn z) →
        let reference : (ℝ × ℝ) → ℝ := fun x => (1 / (2 * Real.pi)) *
          (∑ d ∈ H.support, H.coeff d *
            (gaussianHermitePolynomial (d 0)).eval x.1 *
              (gaussianHermitePolynomial (d 1)).eval x.2) *
                Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
        ∀ x : ℝ × ℝ,
          Integrable (fun z : ℝ × ℝ => kernel x z * Sn z * G z) ∧
            |reference x - phi x * (1 + P1 p x / Real.sqrt (n : ℝ))| ≤ C / (n : ℝ) := by
  classical
  intro tilt D s t A means Y laws Phi b P1
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly, hcgf, hcum⟩ :=
    compact_open_domain_uniform_cgf_cumulant_bounds mu Theta hcompact hTheta
      beta c R hbeta hc hR hdet hWC
  have hprob (p : Theta) : IsProbabilityMeasure (laws p) :=
    (hpoint p p.property).2.2.2.2.2.1
  have h0 (p : Theta) (u v : ℝ) : 0 ∈ interior (ProbabilityTheory.integrableExpSet
      (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (laws p)) :=
    (hcgf p p.property u v).1
  have hM (p : Theta) (j : ℕ) : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ j) (laws p) := by
    obtain ⟨Cj, hCj, hBj⟩ := hmom j
    exact (hBj p p.property).1
  choose Ck hCk hCbound using hcum
  let B : Fin 6 → ℝ := fun j => Ck (j.val + 3)
  have hB (j : Fin 6) : 0 ≤ B j := (hCk (j.val + 3)).le
  have hBound (j : Fin 6) (p : Theta) (u v : ℝ) :
      |iteratedDeriv (j.val + 3) (ProbabilityTheory.cgf
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (laws p)) 0| ≤
          B j * Real.sqrt (u ^ 2 + v ^ 2) ^ (j.val + 3) :=
    hCbound (j.val + 3) p p.property u v
  obtain ⟨C, hC, hHigher⟩ := uniform_actual_cgf_higher_weight_gaussian_integral_bound
    (fun p : Theta => laws p) hprob h0 hM B hB hBound
  obtain ⟨C1, hC1, hFirst⟩ := compact_open_domain_first_hermite_correction_uniform
    mu Theta hcompact hTheta beta c R hbeta hc hR hdet hWC
  let c0 : ℝ := 1 / (2 * Real.pi) ^ 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  refine ⟨c0 * C, by positivity, ?_⟩
  intro n hn p X kappa a Sn G kernel phi H hEval reference x
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  let S1 : (ℝ × ℝ) → ℂ := fun z =>
    ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if (∑ l, ((sigma l).val + 1)) = 1 then ∏ l, a z (sigma l) else 0
  let W : (ℝ × ℝ) → ℂ := fun z =>
    ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if 2 ≤ (∑ l, ((sigma l).val + 1)) ∧
          (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a z (sigma l) else 0
  have hFull : Integrable (fun z : ℝ × ℝ => kernel x z * Sn z * G z) ∧
      (∫ z : ℝ × ℝ, kernel x z * Sn z * G z) =
        ((2 * Real.pi * (∑ d ∈ H.support, H.coeff d *
          (gaussianHermitePolynomial (d 0)).eval x.1 *
            (gaussianHermitePolynomial (d 1)).eval x.2) *
              Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
    simpa only [kernel, G, hEval] using pair_mv_polynomial_gaussian_hermite_integral H x
  have hZero : Integrable (fun z : ℝ × ℝ => kernel x z * G z) ∧
      (∫ z : ℝ × ℝ, kernel x z * G z) =
        ((2 * Real.pi * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
    simpa [kernel, G, gaussianHermitePolynomial] using
      pair_mv_polynomial_gaussian_hermite_integral (1 : MvPolynomial (Fin 2) ℝ) x
  have hOne : Integrable (fun z : ℝ × ℝ => kernel x z * S1 z * G z) ∧
      (∫ z : ℝ × ℝ, kernel x z * S1 z * G z) =
        ((2 * Real.pi * P1 p x * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) /
          Real.sqrt (n : ℝ) : ℝ) : ℂ) := (hFirst p).2.2 n hn x
  have hHigh : Integrable (fun z : ℝ × ℝ => kernel x z * (G z * W z)) ∧
      ‖∫ z : ℝ × ℝ, kernel x z * (G z * W z)‖ ≤ C / (n : ℝ) :=
    (hHigher n hn p).2.2.2.2 x
  have hsplit (z : ℝ × ℝ) : kernel x z * Sn z * G z =
      (kernel x z * G z + kernel x z * S1 z * G z) + kernel x z * (G z * W z) := by
    have hSn : Sn z = 1 + a z 0 + W z := six_order_word_higher_weight_decomposition (a z)
    have hS1 : S1 z = a z 0 := six_order_word_weight_one (a z)
    rw [hSn, ← hS1]
    ring
  have hIntegralSplit : (∫ z : ℝ × ℝ, kernel x z * Sn z * G z) =
      ((∫ z : ℝ × ℝ, kernel x z * G z) +
        (∫ z : ℝ × ℝ, kernel x z * S1 z * G z)) +
          (∫ z : ℝ × ℝ, kernel x z * (G z * W z)) := by
    calc
      _ = ∫ z : ℝ × ℝ, (kernel x z * G z + kernel x z * S1 z * G z) +
          kernel x z * (G z * W z) := integral_congr_ae (Filter.Eventually.of_forall hsplit)
      _ = _ := by
        exact (integral_add (hZero.1.add hOne.1) hHigh.1).trans
          (congrArg (fun z : ℂ => z + (∫ z : ℝ × ℝ, kernel x z * (G z * W z)))
            (integral_add hZero.1 hOne.1))
  have hInvFull : ((c0 : ℝ) : ℂ) * (∫ z : ℝ × ℝ, kernel x z * Sn z * G z) =
      ((reference x : ℝ) : ℂ) := by
    rw [hFull.2]
    dsimp only [reference, c0]
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring
  have hInvZero : ((c0 : ℝ) : ℂ) * (∫ z : ℝ × ℝ, kernel x z * G z) =
      ((phi x : ℝ) : ℂ) := by
    rw [hZero.2]
    dsimp only [phi, c0]
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring
  have hInvOne : ((c0 : ℝ) : ℂ) * (∫ z : ℝ × ℝ, kernel x z * S1 z * G z) =
      ((phi x * P1 p x / Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
    rw [hOne.2]
    dsimp only [phi, c0]
    push_cast
    field_simp [Real.pi_ne_zero, hs.ne'] <;> ring
  have hError : ((reference x - phi x * (1 + P1 p x / Real.sqrt (n : ℝ)) : ℝ) : ℂ) =
      ((c0 : ℝ) : ℂ) * (∫ z : ℝ × ℝ, kernel x z * (G z * W z)) := by
    have hreal : ((phi x * (1 + P1 p x / Real.sqrt (n : ℝ)) : ℝ) : ℂ) =
        ((phi x : ℝ) : ℂ) + ((phi x * P1 p x / Real.sqrt (n : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [Complex.ofReal_sub, hreal, ← hInvFull, ← hInvZero, ← hInvOne, hIntegralSplit]
    ring
  refine ⟨hFull.1, ?_⟩
  calc
    _ = ‖((reference x - phi x * (1 + P1 p x / Real.sqrt (n : ℝ)) : ℝ) : ℂ)‖ := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖((c0 : ℝ) : ℂ) * (∫ z : ℝ × ℝ, kernel x z * (G z * W z))‖ := by rw [hError]
    _ = c0 * ‖∫ z : ℝ × ℝ, kernel x z * (G z * W z)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0.le]
    _ ≤ c0 * (C / (n : ℝ)) := mul_le_mul_of_nonneg_left hHigh.2 hc0.le
    _ = (c0 * C) / (n : ℝ) := by ring

end
end Shao.OQ3
