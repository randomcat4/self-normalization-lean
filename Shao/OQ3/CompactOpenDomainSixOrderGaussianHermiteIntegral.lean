import Shao.OQ3.CompactOpenDomainSixOrderGaussianPolynomialTail
import Shao.OQ3.GaussianSixOrderActualCGFHermiteIntegral
import Shao.OQ3.ActualCGFFirstWeightGaussianZero

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_six_order_gaussian_hermite_integral
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
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
      (∀ p : Theta, ∀ w : ℝ × ℝ, E p w =
        (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
        let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
        let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
          ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
        let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
          Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
        let rho : Measure (ℝ × ℝ) := Qsample.map T
        IsProbabilityMeasure rho ∧
        let kappa : (ℝ × ℝ) → ℕ → ℝ := fun z j =>
          iteratedDeriv j (ProbabilityTheory.cgf
            (fun y : Fin 2 → ℝ => z.1 * y 0 + z.2 * y 1) (laws p)) 0
        let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
          (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
            (kappa z (j.val + 3) : ℂ) /
              (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
        let S : (ℝ × ℝ) → ℂ := fun z =>
          ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
            ∑ sigma : Fin q.val → Fin 6,
              if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
        let S1 : (ℝ × ℝ) → ℂ := fun z =>
          ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
            ∑ sigma : Fin q.val → Fin 6,
              if (∑ i, ((sigma i).val + 1)) = 1 then ∏ i, a z (sigma i) else 0
        ∃ P : MvPolynomial (Fin 2) ℝ,
          (∀ z : ℝ × ℝ, MvPolynomial.eval₂ Complex.ofRealHom
            ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] P = S z) ∧
          (∀ x : ℝ × ℝ,
            Integrable (fun z : ℝ × ℝ =>
              Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
                S z * Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
            (∫ z : ℝ × ℝ,
              Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ)) *
                S z * Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) =
              ((2 * Real.pi *
                (∑ d ∈ P.support, P.coeff d *
                  (gaussianHermitePolynomial (d 0)).eval x.1 *
                    (gaussianHermitePolynomial (d 1)).eval x.2) *
                      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ)) ∧
          Integrable (fun z : ℝ × ℝ => S1 z *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) ∧
          (∫ z : ℝ × ℝ, S1 z *
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2)) = 0 := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized, hocticExp, horderSix, hweighted, htail⟩ :=
    compact_open_domain_six_order_gaussian_polynomial_tail mu Theta hcompact hTheta
      beta c R hbeta hc hR hdet hWC
  obtain ⟨Ca, da, hCa, hda, hda1, hIID⟩ := hactual
  refine ⟨E, (fun p => (hE p).1), ?_⟩
  intro n hn p Qsample M T rho
  refine ⟨(hIID n hn p).1, ?_⟩
  intro kappa a S S1
  letI : IsProbabilityMeasure (laws p) := (hpoint p p.property).2.2.2.2.2.1
  have h0 (u v : ℝ) :
      0 ∈ interior (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (laws p)) :=
    (hcgf p p.property u v).1
  have hM (j : ℕ) : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ j) (laws p) := by
    obtain ⟨C, hC, hBound⟩ := hmom j
    exact (hBound p p.property).1
  obtain ⟨P, heval, hIntegral⟩ :=
    pair_directional_cgf_six_order_gaussian_hermite_integral (laws p) h0 hM n hn
  have hOne := actual_cgf_six_order_weight_one_gaussian_integral_zero (laws p) h0 hM n
  exact ⟨P, heval, hIntegral, hOne⟩

end
end Shao.OQ3
