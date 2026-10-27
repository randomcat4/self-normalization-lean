import Shao.OQ3.CompactOpenDomainOcticExponentialError
import Shao.OQ3.ActualCGFNormalizedOcticPolynomial
import Shao.OQ3.ComplexGaussianSixOrderPolynomialError
import Shao.OQ3.PairCharacteristicLowMomentPolynomial

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_six_order_edgeworth_polynomial_error
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
      (∀ delta : ℝ, 0 < delta → ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ =>
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta)) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ∧
        (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ≤ C) ∧
    let L : ℝ := 1 / Real.sqrt hi
    let U : ℝ := 1 / Real.sqrt lo
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < L ∧ 0 < U ∧ 0 < cA ∧ 0 ≤ RA ∧
      (∀ p ∈ Theta,
        0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
          0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
        IsProbabilityMeasure (laws p) ∧
        (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (laws p) ∧
          (∫ y : Fin 2 → ℝ, y i ∂laws p) = 0) ∧
        (∀ i j : Fin 2, ProbabilityTheory.covariance
          (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
            if i = j then 1 else 0) ∧
        (∀ xi eta : ℝ,
          L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
            Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
              (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
          Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
              (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
            U * Real.sqrt (xi ^ 2 + eta ^ 2)) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤ 1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) ∧
      (∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ∧
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ≤ C) ∧
      (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta, ∀ u v : ℝ,
        ‖Phi p u v - (∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
          ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂laws p : ℝ) : ℂ))‖ ≤
          C * Real.sqrt (u ^ 2 + v ^ 2) ^ m) ∧
      (∀ m : ℕ, 1 ≤ m → ∃ K2 Km delta : ℝ,
        0 < K2 ∧ 0 < Km ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ p ∈ Theta, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
          let P : ℂ := ∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
            ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂laws p : ℝ) : ℂ)
          ‖Phi p u v - 1‖ ≤ 1 / 2 ∧ ‖P - 1‖ ≤ 1 ∧ ∀ q : ℕ,
            ‖Complex.log (Phi p u v) - Complex.logTaylor (q + 1) (P - 1)‖ ≤
              2 * (K2 * (u ^ 2 + v ^ 2)) ^ (q + 1) / ((q + 1 : ℕ) : ℝ) +
                ((q + 1 : ℕ) : ℝ) * Km * Real.sqrt (u ^ 2 + v ^ 2) ^ m) ∧
      (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ p ∈ Theta, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
          let Q : ℂ := -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
            Complex.I * ((∫ y : Fin 2 → ℝ,
              (u * y 0 + v * y 1) ^ 3 ∂laws p : ℝ) : ℂ) / 6 +
            (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂laws p : ℝ) -
              3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / 24
          ‖Complex.log (Phi p u v) - Q‖ ≤
            C * Real.sqrt (u ^ 2 + v ^ 2) ^ 5) ∧
      (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure rho ∧
            ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
              let Qn : ℂ := -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
                Complex.I * ((∫ y : Fin 2 → ℝ,
                  (u * y 0 + v * y 1) ^ 3 ∂laws p : ℝ) : ℂ) /
                    (6 * (Real.sqrt (n : ℝ) : ℂ)) +
                (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂laws p : ℝ) -
                  3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / (24 * (n : ℂ))
              Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ≠ 0 ∧
                ‖(n : ℂ) * Complex.log
                    (Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) - Qn‖ ≤
                  C * Real.sqrt (u ^ 2 + v ^ 2) ^ 5 /
                    ((n : ℝ) * Real.sqrt (n : ℝ)) ∧
                (∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho) =
                    Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ n ∧
                (∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho) =
                    Complex.exp ((n : ℂ) * Complex.log
                      (Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))))) ∧
      (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure rho ∧
            ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
              let Qn : ℂ := -((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2 -
                Complex.I * ((∫ y : Fin 2 → ℝ,
                  (u * y 0 + v * y 1) ^ 3 ∂laws p : ℝ) : ℂ) /
                    (6 * (Real.sqrt (n : ℝ) : ℂ)) +
                (((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂laws p : ℝ) -
                  3 * (u ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) / (24 * (n : ℂ))
              ‖∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho‖ ≤ Real.exp (-(u ^ 2 + v ^ 2) / 4) ∧
                ‖(∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                    Complex.I) ∂rho) - Complex.exp Qn‖ ≤
                  C * Real.sqrt (u ^ 2 + v ^ 2) ^ 5 /
                    ((n : ℝ) * Real.sqrt (n : ℝ)) *
                      Real.exp (-(u ^ 2 + v ^ 2) / 8)) ∧
      (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure rho ∧
            ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
              let Pn : ℂ := Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) *
                (1 - Complex.I * ((∫ y : Fin 2 → ℝ,
                  (u * y 0 + v * y 1) ^ 3 ∂laws p : ℝ) : ℂ) /
                    (6 * (Real.sqrt (n : ℝ) : ℂ)) +
                  (((((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂laws p : ℝ) -
                    3 * (u ^ 2 + v ^ 2) ^ 2) / 24 -
                    (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 3 ∂laws p) ^ 2 / 72 : ℝ) : ℂ) /
                      (n : ℂ)))
              ‖∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho‖ ≤ Real.exp (-(u ^ 2 + v ^ 2) / 4) ∧
                ‖(∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                    Complex.I) ∂rho) - Pn‖ ≤
                  C * (Real.sqrt (u ^ 2 + v ^ 2) ^ 5 + Real.sqrt (u ^ 2 + v ^ 2) ^ 7 +
                    Real.sqrt (u ^ 2 + v ^ 2) ^ 8 + Real.sqrt (u ^ 2 + v ^ 2) ^ 9) /
                    ((n : ℝ) * Real.sqrt (n : ℝ)) *
                      Real.exp (-(u ^ 2 + v ^ 2) / 8)) ∧
      (∀ p ∈ Theta, ∀ u v : ℝ,
        let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
        0 ∈ interior (ProbabilityTheory.integrableExpSet X (laws p)) ∧
          (∫ y : Fin 2 → ℝ, X y ∂laws p) = 0 ∧
          iteratedDeriv 3 (ProbabilityTheory.cgf X (laws p)) 0 =
            (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 3 ∂laws p) ∧
          iteratedDeriv 4 (ProbabilityTheory.cgf X (laws p)) 0 =
            (∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ 4 ∂laws p) -
              3 * (u ^ 2 + v ^ 2) ^ 2) ∧
      (∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta, ∀ u v : ℝ,
        let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
        |iteratedDeriv k (ProbabilityTheory.cgf X (laws p)) 0| ≤
          C * Real.sqrt (u ^ 2 + v ^ 2) ^ k) ∧
      (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ p ∈ Theta, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
          let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
          let kappa : ℕ → ℝ := fun j => iteratedDeriv j (ProbabilityTheory.cgf X (laws p)) 0
          let Q8 : ℂ := ∑ j ∈ Finset.range 9,
            (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ)
          ‖Complex.log (Phi p u v) - Q8‖ ≤ C * Real.sqrt (u ^ 2 + v ^ 2) ^ 9) ∧
      (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure rho ∧
            ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
              let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
              let kappa : ℕ → ℝ := fun j =>
                iteratedDeriv j (ProbabilityTheory.cgf X (laws p)) 0
              let Qn8 : ℂ := ∑ j ∈ Finset.range 9,
                (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ) *
                  (n : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ j
              Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ≠ 0 ∧
                ‖(n : ℂ) * Complex.log
                    (Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))) - Qn8‖ ≤
                  C * Real.sqrt (u ^ 2 + v ^ 2) ^ 9 /
                    ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) ∧
                (∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho) =
                    Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ)) ^ n ∧
                (∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho) =
                    Complex.exp ((n : ℂ) * Complex.log
                      (Phi p (u / Real.sqrt (n : ℝ)) (v / Real.sqrt (n : ℝ))))) ∧
      (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure rho ∧
            ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
              let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
              let kappa : ℕ → ℝ := fun j =>
                iteratedDeriv j (ProbabilityTheory.cgf X (laws p)) 0
              let Qn8 : ℂ := ∑ j ∈ Finset.range 9,
                (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ) *
                  (n : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ j
              ‖∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho‖ ≤ Real.exp (-(u ^ 2 + v ^ 2) / 4) ∧
                ‖(∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho) - Complex.exp Qn8‖ ≤
                    C * Real.sqrt (u ^ 2 + v ^ 2) ^ 9 /
                      ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) *
                        Real.exp (-(u ^ 2 + v ^ 2) / 8)) ∧
      ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure rho ∧
            ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta * Real.sqrt (n : ℝ) →
              let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
              let kappa : ℕ → ℝ := fun j =>
                iteratedDeriv j (ProbabilityTheory.cgf X (laws p)) 0
              let a : Fin 6 → ℂ := fun j =>
                (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
                  (kappa (j.val + 3) : ℂ) /
                    (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
              let Pn : ℂ := Complex.exp (-((u ^ 2 + v ^ 2 : ℝ) : ℂ) / 2) *
                ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
                  ∑ sigma : Fin q.val → Fin 6,
                    if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a (sigma i) else 0
              ‖∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho‖ ≤ Real.exp (-(u ^ 2 + v ^ 2) / 4) ∧
                ‖(∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho) - Pn‖ ≤
                    C * (Real.sqrt (u ^ 2 + v ^ 2) ^ 9 +
                      Real.sqrt (u ^ 2 + v ^ 2) ^ 56) /
                        ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) *
                          Real.exp (-(u ^ 2 + v ^ 2) / 8) := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized, hocticExp⟩ :=
    compact_open_domain_octic_exponential_error mu Theta hcompact hTheta
      beta c R hbeta hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
    hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
    hcgf, hcum, hoctic, hnormalized, hocticExp, ?_⟩
  choose K hKpos hK using hcum
  let Bnd : Fin 6 → ℝ := fun j => K (j.val + 3)
  have hBnd (j : Fin 6) : 0 ≤ Bnd j := (hKpos _).le
  let B : ℝ := ∑ j, Bnd j
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => hBnd j)
  obtain ⟨Cp, hCp, hP⟩ := complex_gaussian_six_order_exponential_polynomial_error Bnd hBnd
  obtain ⟨Ce, de, hCe, hde, hde1, hOct⟩ := hocticExp
  let dsmall : ℝ := 1 / (4 * (B + 1))
  have hdsmall : 0 < dsmall := by dsimp only [dsmall]; positivity
  have hBd : B * dsmall ≤ 1 / 4 := by
    have hratio : B / (B + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < B + 1)).mpr
      linarith
    calc
      _ = (B / (B + 1)) / 4 := by
        dsimp only [dsmall]
        field_simp [show B + 1 ≠ 0 by positivity] <;> ring
      _ ≤ 1 / 4 := div_le_div_of_nonneg_right hratio (by norm_num)
  refine ⟨Ce + Cp, min de dsmall, by positivity, lt_min hde hdsmall,
    (min_le_left _ _).trans hde1, ?_⟩
  intro n hn p Qsample M T rho
  refine ⟨(hOct n hn p).1, ?_⟩
  intro u v huv X kappa a Pn
  let sn : ℝ := Real.sqrt (n : ℝ)
  let tau : ℝ := 1 / sn
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  let S : ℝ := u ^ 2 + v ^ 2
  let den : ℝ := (n : ℝ) ^ 3 * sn
  let cf : ℂ := ∫ w : ℝ × ℝ,
    Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂rho
  let Qn8 : ℂ := ∑ j ∈ Finset.range 9,
    (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ) *
      (n : ℂ) / (sn : ℂ) ^ j
  let P0 : ℂ := ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
    ∑ sigma : Fin q.val → Fin 6,
      if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a (sigma i) else 0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < sn := Real.sqrt_pos.mpr hnR
  have hsn1 : 1 ≤ sn := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnR1
  have hsq : sn ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have htau0 : 0 ≤ tau := one_div_nonneg.mpr hsn.le
  have htau1 : tau ≤ 1 := (div_le_one hsn).mpr hsn1
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hr2 : r ^ 2 = S := Real.sq_sqrt hS
  have hden : 0 < den := by dsimp only [den]; positivity
  have hrde : r ≤ de * sn :=
    huv.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsn.le)
  have hO := (hOct n hn p).2 u v hrde
  refine ⟨hO.1, ?_⟩
  letI : IsProbabilityMeasure (laws p) := (hpoint p p.property).2.2.2.2.2.1
  have hcoords := (hpoint p p.property).2.2.2.2.2.2.1
  have hcov := (hpoint p p.property).2.2.2.2.2.2.2.1
  have hm2 : (∫ y : Fin 2 → ℝ, X y ^ 2 ∂laws p) = S :=
    (pair_probability_directional_first_two_moments (laws p)
      (fun j => (hcoords j).1) (fun j => (hcoords j).2) hcov u v).2.2.2.2
  have hQ : Qn8 = -((S : ℝ) : ℂ) / 2 + ∑ j, a j := by
    have hER := centered_actual_cgf_normalized_octic_polynomial (laws p) X
      (hcgf p p.property u v).1 (hcgf p p.property u v).2.1 n hn
    change Qn8 = -((∫ y : Fin 2 → ℝ, X y ^ 2 ∂laws p : ℝ) : ℂ) / 2 +
      ∑ j, a j at hER
    rw [hm2] at hER
    exact hER
  have hcoeff (j : Fin 6) :
      ‖(Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
        (kappa (j.val + 3) : ℂ)‖ ≤ Bnd j * r ^ (j.val + 3) := by
    have hfac : (1 : ℝ) ≤ ((j.val + 3).factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (j.val + 3))
    calc
      _ = |kappa (j.val + 3)| / ((j.val + 3).factorial : ℝ) := by
        norm_num [norm_mul, norm_div, norm_pow] <;> ring
      _ ≤ |kappa (j.val + 3)| := div_le_self (abs_nonneg _) hfac
      _ ≤ _ := hK (j.val + 3) p p.property u v
  have ha (j : Fin 6) :
      ‖a j‖ ≤ Bnd j * tau ^ (j.val + 1) * r ^ (j.val + 3) := by
    calc
      _ = ‖(Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
          (kappa (j.val + 3) : ℂ)‖ / sn ^ (j.val + 1) := by
        dsimp only [a]
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ (Bnd j * r ^ (j.val + 3)) / sn ^ (j.val + 1) :=
        div_le_div_of_nonneg_right (hcoeff j) (pow_nonneg hsn.le _)
      _ = _ := by dsimp only [tau]; rw [_root_.one_div_pow]; ring
  have hx : r / sn ≤ min de dsmall := (div_le_iff₀ hsn).mpr huv
  have hx0 : 0 ≤ r / sn := div_nonneg hr0 hsn.le
  have hx1 : r / sn ≤ 1 := hx.trans ((min_le_left _ _).trans hde1)
  have hxsmall : r / sn ≤ dsmall := hx.trans (min_le_right _ _)
  have hNormZ : ‖∑ j, a j‖ ≤ r ^ 2 / 4 := by
    have hterm (j : Fin 6) : ‖a j‖ ≤ Bnd j * r ^ 2 * dsmall := by
      have hpow : (r / sn) ^ (j.val + 1) ≤ dsmall :=
        (show (r / sn) ^ (j.val + 1) ≤ r / sn by
          simpa only [pow_one] using pow_le_pow_of_le_one hx0 hx1 (by omega : 1 ≤ j.val + 1)).trans hxsmall
      calc
        _ ≤ Bnd j * tau ^ (j.val + 1) * r ^ (j.val + 3) := ha j
        _ = Bnd j * r ^ 2 * (r / sn) ^ (j.val + 1) := by
          dsimp only [tau]
          rw [show j.val + 3 = (j.val + 1) + 2 by omega, pow_add, div_pow, _root_.one_div_pow]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg (hBnd j) (sq_nonneg r))
    calc
      _ ≤ ∑ j, ‖a j‖ := norm_sum_le _ _
      _ ≤ ∑ j, Bnd j * r ^ 2 * dsmall := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (B * dsmall) * r ^ 2 := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
      _ ≤ (1 / 4) * r ^ 2 := mul_le_mul_of_nonneg_right hBd (sq_nonneg r)
      _ = _ := by ring
  have hPoly := hP tau r htau0 htau1 hr0 a ha hNormZ
  have hExpr : Complex.exp Qn8 - Pn =
      Complex.exp (-((r ^ 2 : ℝ) : ℂ) / 2) * (Complex.exp (∑ j, a j) - P0) := by
    rw [hQ, Complex.exp_add, hr2]
    dsimp only [Pn, P0, S]
    ring
  have hTau7 : tau ^ 7 = 1 / den := by
    dsimp only [tau, den]
    rw [← hsq]
    field_simp [hsn.ne'] <;> ring
  have hGauss : Real.exp (-S / 4) ≤ Real.exp (-S / 8) :=
    Real.exp_le_exp.mpr (by linarith)
  have hPolyFinal : ‖Complex.exp Qn8 - Pn‖ ≤
      Cp * (r ^ 9 + r ^ 56) / den * Real.exp (-S / 8) := by
    calc
      _ = ‖Complex.exp (-((r ^ 2 : ℝ) : ℂ) / 2) *
          (Complex.exp (∑ j, a j) - P0)‖ := congrArg norm hExpr
      _ ≤ Cp * tau ^ 7 * (r ^ 9 + r ^ 56) * Real.exp (-(r ^ 2) / 4) := hPoly
      _ = Cp * (r ^ 9 + r ^ 56) / den * Real.exp (-S / 4) := by
        rw [hTau7, hr2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hGauss (by positivity)
  have hOctFinal : ‖cf - Complex.exp Qn8‖ ≤
      Ce * (r ^ 9 + r ^ 56) / den * Real.exp (-S / 8) := by
    calc
      _ ≤ Ce * r ^ 9 / den * Real.exp (-S / 8) := hO.2
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (pow_nonneg hr0 _)) hCe.le) hden.le)
        (Real.exp_pos _).le
  calc
    _ = ‖(cf - Complex.exp Qn8) + (Complex.exp Qn8 - Pn)‖ := by congr 1; ring
    _ ≤ ‖cf - Complex.exp Qn8‖ + ‖Complex.exp Qn8 - Pn‖ := norm_add_le _ _
    _ ≤ Ce * (r ^ 9 + r ^ 56) / den * Real.exp (-S / 8) +
        Cp * (r ^ 9 + r ^ 56) / den * Real.exp (-S / 8) :=
      add_le_add hOctFinal hPolyFinal
    _ = _ := by ring

end
end Shao.OQ3
