import Shao.OQ3.CompactOpenDomainSixOrderLogCubicOscillatoryWindow
import Shao.OQ3.GaussianDampedWeightedErrorIntegral

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_six_order_log_cubic_damped_window
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
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
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      (∀ p ∈ Theta, ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
        xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2)) ∧
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
      (∀ p : Theta,
        (∀ w : ℝ × ℝ, E p w =
          (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
        ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
        ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo) ∧
        ∀ x : ℝ, E p ((x, x ^ 2) - (means p 0, means p 1)) =
          (Y p x 0, Y p x 1)) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
        (∀ n : ℕ, N ≤ n → ∀ p : Theta, ∀ b : ℝ, 0 ≤ b →
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          let X : (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ :=
            fun z y => z.1 * y 0 + z.2 * y 1
          let kappa : ℕ → (ℝ × ℝ) → ℝ :=
            fun j z => iteratedDeriv j (ProbabilityTheory.cgf (X z) (laws p)) 0
          let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
            (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
              (kappa (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
          let Pn : (ℝ × ℝ) → ℂ := fun z =>
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
              ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
                ∑ sigma : Fin q.val → Fin 6,
                  if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
          let window : Set (ℝ × ℝ) := {z |
            Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ)}
          let weight : (ℝ × ℝ) → ℝ := fun z => Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k
          let error : (ℝ × ℝ) → ℂ := fun z =>
            (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) *
              Complex.I) ∂rho) - Pn z
          let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
          let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
          IsProbabilityMeasure rho ∧ Continuous Pn ∧ Continuous error ∧
            IntegrableOn (fun z => weight z * ‖error z‖) window ∧
              0 ≤ (∫ z in window, weight z * ‖error z‖) ∧
              (∫ z in window, weight z * ‖error z‖) ≤
                C / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) ∧
              IntegrableOn (fun z => weight z * ‖(damping z : ℂ) * error z‖) window ∧
              (∫ z in window, weight z * ‖(damping z : ℂ) * error z‖) ≤
                C / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) ∧
              ∀ x : ℝ × ℝ,
                IntegrableOn (fun z => kernel x z * (weight z : ℂ) *
                  ((damping z : ℂ) * error z)) window ∧
                  ‖∫ z in window, kernel x z * (weight z : ℂ) *
                    ((damping z : ℂ) * error z)‖ ≤
                      C / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) ∧
        ∀ epsilon : ℝ, 0 < epsilon →
          ∃ Ne : ℕ, N ≤ Ne ∧ ∀ n : ℕ, Ne ≤ n → ∀ p : Theta, ∀ b : ℝ, 0 ≤ b →
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          let X : (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ := fun z y => z.1 * y 0 + z.2 * y 1
          let kappa : ℕ → (ℝ × ℝ) → ℝ :=
            fun j z => iteratedDeriv j (ProbabilityTheory.cgf (X z) (laws p)) 0
          let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
            (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
              (kappa (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
          let Pn : (ℝ × ℝ) → ℂ := fun z =>
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
              ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
                ∑ sigma : Fin q.val → Fin 6,
                  if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
          let window : Set (ℝ × ℝ) := {z |
            Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ)}
          let weight : (ℝ × ℝ) → ℝ := fun z => Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k
          let error : (ℝ × ℝ) → ℂ := fun z =>
            (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) *
              Complex.I) ∂rho) - Pn z
          let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
          let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
          (n : ℝ) ^ 3 * (∫ z in window, weight z * ‖(damping z : ℂ) * error z‖) < epsilon ∧
            ∀ x : ℝ × ℝ,
              (n : ℝ) ^ 3 *
                ‖∫ z in window, kernel x z * (weight z : ℂ) *
                  ((damping z : ℂ) * error z)‖ < epsilon := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized, hocticExp, horderSix, hweighted,
      hgaussian, hfarPoint, hfarInt, hmiddle, hwindow⟩ :=
    compact_open_domain_six_order_log_cubic_oscillatory_window mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, ?_⟩
  intro k
  obtain ⟨C, hC, N, hN, hwin, hsmall⟩ := hwindow k
  refine ⟨C, hC, N, hN, ?_, ?_⟩
  · intro n hn p b hb Qsample M T rho X kappa a Pn window weight error damping kernel
    have h := hwin n hn p
    have hd := pair_gaussian_damped_weighted_error_integral_bound
      error h.2.2.1 window k b hb h.2.2.2.1
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, hd.1, hd.2.1.trans h.2.2.2.2.2.1, ?_⟩
    intro x
    exact ⟨(hd.2.2 x).1, (hd.2.2 x).2.trans h.2.2.2.2.2.1⟩
  · intro epsilon hepsilon
    obtain ⟨Ne, hNe, hs⟩ := hsmall epsilon hepsilon
    refine ⟨Ne, hNe, ?_⟩
    intro n hn p b hb Qsample M T rho X kappa a Pn window weight error damping kernel
    have hnN : N ≤ n := hNe.trans hn
    have h := hwin n hnN p
    have hsmalln := hs n hn p
    have hd := pair_gaussian_damped_weighted_error_integral_bound
      error h.2.2.1 window k b hb h.2.2.2.1
    have hmul : 0 ≤ (n : ℝ) ^ 3 := by positivity
    refine ⟨lt_of_le_of_lt (mul_le_mul_of_nonneg_left hd.2.1 hmul) hsmalln.1, ?_⟩
    intro x
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hd.2.2 x).2 hmul) hsmalln.1

end
end Shao.OQ3
