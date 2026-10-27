import Shao.OQ3.CompactOpenDomainSixOrderLogCubicFarFrequency
import Shao.OQ3.CompactOpenDomainWeightedGaussianWindow

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_six_order_log_cubic_weighted_window
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
                          Real.exp (-(u ^ 2 + v ^ 2) / 8)) ∧
      (∃ deltaInt : ℝ, 0 < deltaInt ∧ deltaInt ≤ 1 ∧ ∀ k : ℕ,
        let envelope : (ℝ × ℝ) → ℝ := fun z =>
          (Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ (k + 9) +
            Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ (k + 56)) *
              Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
        Integrable envelope ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : Theta,
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
          let small : Set (ℝ × ℝ) := {z |
            Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ deltaInt * Real.sqrt (n : ℝ)}
          let weight : (ℝ × ℝ) → ℝ := fun z => Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k
          let error : (ℝ × ℝ) → ℂ := fun z =>
            (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) *
              Complex.I) ∂rho) - Pn z
          IsProbabilityMeasure rho ∧ Continuous Pn ∧ Continuous error ∧
            IntegrableOn (fun z => weight z * ‖error z‖) small ∧
              0 ≤ (∫ z in small, weight z * ‖error z‖) ∧
              (∫ z in small, weight z * ‖error z‖) ≤
                C / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) ∧
      (let X : Theta → (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ :=
        fun p z y => z.1 * y 0 + z.2 * y 1
      let kappa : Theta → ℕ → (ℝ × ℝ) → ℝ :=
        fun p j z => iteratedDeriv j (ProbabilityTheory.cgf (X p z) (laws p)) 0
      let a : Theta → ℕ → (ℝ × ℝ) → Fin 6 → ℂ := fun p n z j =>
        (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
          (kappa p (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
      let Pn : Theta → ℕ → (ℝ × ℝ) → ℂ := fun p n z =>
        Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
          ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
            ∑ sigma : Fin q.val → Fin 6,
              if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a p n z (sigma l) else 0
      ∃ C : ℝ, 0 < C ∧
        (∀ n : ℕ, 1 ≤ n → ∀ p : Theta, ∀ u v : ℝ,
          ‖Pn p n (u, v)‖ ≤ C * (1 + Real.sqrt (u ^ 2 + v ^ 2) ^ 18) *
            Real.exp (-(u ^ 2 + v ^ 2) / 2)) ∧
        ∀ delta : ℝ, 0 < delta → ∀ k : ℕ, ∀ q epsilon : ℝ, 0 < epsilon →
          ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : Theta,
            let tail : Set (ℝ × ℝ) := {z |
              delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
            let f : (ℝ × ℝ) → ℝ := fun z =>
              Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k * ‖Pn p n z‖
            IntegrableOn f tail ∧ 0 ≤ (∫ z in tail, f z) ∧
              Real.rpow (n : ℝ) q * (∫ z in tail, f z) < epsilon) ∧
      (∀ q epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : Theta, ∀ xi eta : ℝ,
          Real.sqrt (n : ℝ) * RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          Real.sqrt (xi ^ 2 + eta ^ 2) ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ) →
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure rho ∧ Real.rpow (n : ℝ) q *
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ < epsilon) ∧
      (∀ k : ℕ, ∀ q epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Qsample.map T
          let far : Set (ℝ × ℝ) := {z |
            Real.sqrt (n : ℝ) * RA < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ∧
            Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ)}
          let f : (ℝ × ℝ) → ℝ := fun z =>
            Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ k *
              ‖(∫ w : ℝ × ℝ,
                Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
          IsProbabilityMeasure rho ∧ IntegrableOn f far ∧
            0 ≤ (∫ z in far, f z) ∧
              Real.rpow (n : ℝ) q * (∫ z in far, f z) < epsilon) ∧
      (∀ delta H : ℝ, 0 < delta → ∀ k : ℕ, ∀ q epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : Theta,
          let nu : Measure ℝ := tilt p
          let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let M : Shao.Path n → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : Shao.Path n → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Q.map T
          let middle : Set (ℝ × ℝ) := {z |
            delta ≤ Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
              (z.2 / Real.sqrt (n : ℝ)) ^ 2) ∧
            Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
              (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ H}
          let f : (ℝ × ℝ) → ℝ := fun z =>
            (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
              ‖(∫ w : ℝ × ℝ,
                Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
          IsProbabilityMeasure rho ∧ IntegrableOn f middle ∧
            0 ≤ (∫ z in middle, f z) ∧
            Real.rpow (n : ℝ) q * (∫ z in middle, f z) < epsilon) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ p : Theta,
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
          IsProbabilityMeasure rho ∧ Continuous Pn ∧ Continuous error ∧
            IntegrableOn (fun z => weight z * ‖error z‖) window ∧
              0 ≤ (∫ z in window, weight z * ‖error z‖) ∧
              (∫ z in window, weight z * ‖error z‖) ≤
                C / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized, hocticExp, horderSix, hweighted,
      hgaussian, hfarPoint, hfarInt⟩ :=
    compact_open_domain_six_order_log_cubic_far_frequency mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR hdet hWC
  obtain ⟨loD, hiD, hloD, hhiD, hspecD, ED, hED, hmomentD, hLD, hUD, hcAD, hRAD,
      hbaseD, hnatD, hmiddleD, hlocalD, hpointD, hlocalIntD, hfarIntD, hmidD, hwindowD⟩ :=
    compact_open_domain_standardized_weighted_gaussian_window_family
      mu Theta hcompact hTheta beta c R hbeta hbetaUpper hc hR hdet hWC
  have hEE : ED = E := by
    funext p
    apply ContinuousLinearEquiv.ext
    funext w
    exact ((hED p).1 w).trans ((hE p).1 w).symm
  rw [hEE] at hmidD
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
    hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
    hcgf, hcum, hoctic, hnormalized, hocticExp, horderSix, hweighted,
    hgaussian, hfarPoint, hfarInt, hmidD, ?_⟩
  obtain ⟨delta, hdelta, hdelta1, hsmallInt⟩ := hweighted
  let H : ℝ := R / (1 / Real.sqrt hi)
  obtain ⟨CP, hCP, hglobalP, htailP⟩ := hgaussian
  intro k
  obtain ⟨henvelope, C, hC, hsmallFn⟩ := hsmallInt k
  obtain ⟨NM, hNM, hmiddleFn⟩ := hmidD delta H hdelta k 4 1 (by norm_num)
  obtain ⟨NF, hNF, hfar⟩ := hfarInt k 4 1 (by norm_num)
  obtain ⟨NG, hNG, hgaussFn⟩ := htailP delta hdelta k 4 1 (by norm_num)
  let N : ℕ := max 2 (max NM (max NF NG))
  refine ⟨C + 3, by linarith, N, le_max_left _ _, ?_⟩
  intro n hn p Qsample M T rho X kappa a Pn window weight error
  have hn2 : 2 ≤ n := (le_max_left 2 _).trans hn
  have hn1 : 1 ≤ n := (by omega : 1 ≤ 2).trans hn2
  have hnM : NM ≤ n := (le_max_left NM _).trans ((le_max_right 2 _).trans hn)
  have hnF : NF ≤ n :=
    (le_max_left NF NG).trans ((le_max_right NM _).trans ((le_max_right 2 _).trans hn))
  have hnG : NG ≤ n :=
    (le_max_right NF NG).trans ((le_max_right NM _).trans ((le_max_right 2 _).trans hn))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsle : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt hnR.le, sq_nonneg (Real.sqrt (n : ℝ) - 1)]
  let fs : (ℝ × ℝ) → ℝ := fun z => weight z * ‖error z‖
  let fc : (ℝ × ℝ) → ℝ := fun z =>
    weight z * ‖(∫ w : ℝ × ℝ,
      Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
  let fg : (ℝ × ℝ) → ℝ := fun z => weight z * ‖Pn z‖
  let small : Set (ℝ × ℝ) := {z |
    Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ delta * Real.sqrt (n : ℝ)}
  let mid : Set (ℝ × ℝ) := {z |
    delta ≤ Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
      (z.2 / Real.sqrt (n : ℝ)) ^ 2) ∧
    Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
      (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ H}
  let far : Set (ℝ × ℝ) := {z |
    Real.sqrt (n : ℝ) * H < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ∧
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3 * Real.log (n : ℝ)}
  let gtail : Set (ℝ × ℝ) := {z |
    delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
  have hsmall := hsmallFn n hn1 p
  have hmid := hmiddleFn n hnM p
  have hfarBound := hfar n hnF p
  have hgauss := hgaussFn n hnG p
  dsimp only at hsmall hmid hfarBound hgauss
  have hrho : IsProbabilityMeasure rho := hsmall.1
  letI : IsProbabilityMeasure rho := hrho
  have hrcont : Continuous (fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) := by
    fun_prop
  have hscaledcont : Continuous (fun z : ℝ × ℝ =>
      Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
        (z.2 / Real.sqrt (n : ℝ)) ^ 2)) := by fun_prop
  have hWin : MeasurableSet window := (isClosed_le hrcont continuous_const).measurableSet
  have hS : MeasurableSet small := (isClosed_le hrcont continuous_const).measurableSet
  have hM : MeasurableSet mid :=
    (isClosed_le continuous_const hscaledcont).measurableSet.inter
      (isClosed_le hscaledcont continuous_const).measurableSet
  have hF : MeasurableSet far :=
    (isOpen_lt continuous_const hrcont).measurableSet.inter hWin
  have hG : MeasurableSet gtail := (isClosed_le continuous_const hrcont).measurableSet
  have hfs0 : ∀ z, 0 ≤ fs z := fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hfc0 : ∀ z, 0 ≤ fc z := fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hfg0 : ∀ z, 0 ≤ fg z := fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hInd0 (A : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ)
      (hf : ∀ z, 0 ≤ f z) (z : ℝ × ℝ) : 0 ≤ A.indicator f z := by
    by_cases hz : z ∈ A
    · simpa only [Set.indicator_of_mem hz] using hf z
    · simp only [Set.indicator_of_notMem hz, le_refl]
  have hIS : Integrable (small.indicator fs) := (integrable_indicator_iff hS).2 hsmall.2.2.2.1
  have hIM : Integrable (mid.indicator fc) := (integrable_indicator_iff hM).2 hmid.2.1
  have hIF : Integrable (far.indicator fc) := (integrable_indicator_iff hF).2 hfarBound.2.1
  have hIG : Integrable (gtail.indicator fg) := (integrable_indicator_iff hG).2 hgauss.1
  let g : (ℝ × ℝ) → ℝ :=
    small.indicator fs + mid.indicator fc + far.indicator fc + gtail.indicator fg
  have hg : Integrable g := ((hIS.add hIM).add hIF).add hIG
  have hscaled (z : ℝ × ℝ) :
      Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
        (z.2 / Real.sqrt (n : ℝ)) ^ 2) =
        Real.sqrt (z.1 ^ 2 + z.2 ^ 2) / Real.sqrt (n : ℝ) := by
    rw [div_pow, div_pow, ← add_div, Real.sq_sqrt hnR.le]
    exact Real.sqrt_div (add_nonneg (sq_nonneg _) (sq_nonneg _)) _
  have htriangle (z : ℝ × ℝ) : fs z ≤ fc z + fg z := by
    have he : ‖error z‖ ≤
        ‖(∫ w : ℝ × ℝ,
          Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ +
          ‖Pn z‖ := norm_sub_le _ _
    have hm := mul_le_mul_of_nonneg_left he
      (pow_nonneg (Real.sqrt_nonneg (z.1 ^ 2 + z.2 ^ 2)) k)
    simpa only [mul_add] using hm
  have hdom : ∀ z, window.indicator fs z ≤ g z := by
    intro z
    have h0S := hInd0 small fs hfs0 z
    have h0M := hInd0 mid fc hfc0 z
    have h0F := hInd0 far fc hfc0 z
    have h0G := hInd0 gtail fg hfg0 z
    by_cases hw : z ∈ window
    · by_cases hzS : z ∈ small
      · dsimp [g]
        rw [Set.indicator_of_mem hw, Set.indicator_of_mem hzS]
        linarith
      · have hgt : z ∈ gtail := by
          change delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)
          have hnsmall : ¬ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤
              delta * Real.sqrt (n : ℝ) := hzS
          exact (lt_of_not_ge hnsmall).le
        have hcover : fc z ≤ mid.indicator fc z + far.indicator fc z := by
          by_cases hu : Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
              (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ H
          · have hd : delta ≤ Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
                (z.2 / Real.sqrt (n : ℝ)) ^ 2) := by
              rw [hscaled z]
              exact (le_div_iff₀ hs).2 hgt
            have hm : z ∈ mid := ⟨hd, hu⟩
            rw [Set.indicator_of_mem hm]
            exact le_add_of_nonneg_right h0F
          · have hfm : z ∈ far := by
              refine ⟨?_, hw⟩
              have hu' : H < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) / Real.sqrt (n : ℝ) := by
                rw [← hscaled z]
                exact lt_of_not_ge hu
              have hp := (lt_div_iff₀ hs).1 hu'
              nlinarith
            rw [Set.indicator_of_mem hfm]
            exact le_add_of_nonneg_left h0M
        dsimp [g]
        rw [Set.indicator_of_mem hw, Set.indicator_of_notMem hzS,
          Set.indicator_of_mem hgt]
        linarith [htriangle z]
    · dsimp [g]
      rw [Set.indicator_of_notMem hw]
      linarith
  have hfscont : Continuous fs := by
    have hw : Continuous weight := by fun_prop
    exact hw.mul hsmall.2.2.1.norm
  have hWI : Integrable (window.indicator fs) :=
    hg.mono' (hfscont.aestronglyMeasurable.indicator hWin)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hInd0 window fs hfs0 z)]
        exact hdom z))
  have hwindowI : IntegrableOn fs window := (integrable_indicator_iff hWin).1 hWI
  have hrpow : Real.rpow (n : ℝ) (4 : ℝ) = (n : ℝ) ^ 4 :=
    Real.rpow_natCast (n : ℝ) 4
  have hden : (n : ℝ) ^ 3 * Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ 4 := by
    calc
      _ ≤ (n : ℝ) ^ 3 * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsle (pow_nonneg hnR.le 3)
      _ = _ := by ring
  have hunit (J : ℝ) (hJ0 : 0 ≤ J) (hJ : (n : ℝ) ^ 4 * J < 1) :
      J ≤ 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hnR 3) hs)).2
    calc
      J * ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) ≤ J * (n : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left hden hJ0
      _ ≤ 1 := by nlinarith
  have hmidRate : (∫ z in mid, fc z) ≤ 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) :=
    hunit _ hmid.2.2.1 (by simpa only [hrpow] using hmid.2.2.2)
  have hfarRate : (∫ z in far, fc z) ≤ 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) :=
    hunit _ hfarBound.2.2.1 (by simpa only [hrpow] using hfarBound.2.2.2)
  have hgaussRate : (∫ z in gtail, fg z) ≤ 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) :=
    hunit _ hgauss.2.1 (by simpa only [hrpow] using hgauss.2.2)
  have hgint : (∫ z : ℝ × ℝ, g z) =
      (∫ z in small, fs z) + (∫ z in mid, fc z) +
        (∫ z in far, fc z) + (∫ z in gtail, fg z) := by
    dsimp [g]
    have h1 := integral_add ((hIS.add hIM).add hIF) hIG
    have h2 := integral_add (hIS.add hIM) hIF
    have h3 := integral_add hIS hIM
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3,
      integral_indicator hS, integral_indicator hM, integral_indicator hF,
      integral_indicator hG]
  refine ⟨hrho, hsmall.2.1, hsmall.2.2.1, hwindowI, integral_nonneg hfs0, ?_⟩
  calc
    (∫ z in window, fs z) = ∫ z : ℝ × ℝ, window.indicator fs z :=
      (integral_indicator hWin).symm
    _ ≤ ∫ z : ℝ × ℝ, g z := integral_mono hWI hg hdom
    _ = (∫ z in small, fs z) + (∫ z in mid, fc z) +
        (∫ z in far, fc z) + (∫ z in gtail, fg z) := hgint
    _ ≤ C / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) + 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) +
        1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) + 1 / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) :=
      add_le_add (add_le_add (add_le_add hsmall.2.2.2.2.2 hmidRate) hfarRate) hgaussRate
    _ = (C + 3) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by ring

end
end Shao.OQ3
