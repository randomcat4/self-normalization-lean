import Shao.OQ3.CompactOpenDomainNormalizedOcticCGFLogExponent
import Shao.OQ3.ComplexExpAddError

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 1000000 in
theorem compact_open_domain_octic_exponential_error
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
              let Qn8 : ℂ := ∑ j ∈ Finset.range 9,
                (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ) *
                  (n : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ j
              ‖∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho‖ ≤ Real.exp (-(u ^ 2 + v ^ 2) / 4) ∧
                ‖(∫ w : ℝ × ℝ, Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) *
                  Complex.I) ∂rho) - Complex.exp Qn8‖ ≤
                    C * Real.sqrt (u ^ 2 + v ^ 2) ^ 9 /
                      ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) *
                        Real.exp (-(u ^ 2 + v ^ 2) / 8) := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized⟩ :=
    compact_open_domain_normalized_octic_cgf_log_exponent mu Theta hcompact hTheta
      beta c R hbeta hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
    hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
    hcgf, hcum, hoctic, hnormalized, ?_⟩
  obtain ⟨C8, d8, hC8, hd8, hd81, h8⟩ := hnormalized
  obtain ⟨C0, d0, hC0, hd0, hd01, hG⟩ := hquart
  let dsmall : ℝ := 1 / (8 * (C8 + 1))
  have hdsmall : 0 < dsmall := by dsimp [dsmall]; positivity
  refine ⟨C8, min d8 (min d0 dsmall), hC8, lt_min hd8 (lt_min hd0 hdsmall),
    (min_le_left _ _).trans hd81, ?_⟩
  intro n hn p Qsample M T rho
  refine ⟨(h8 n hn p).1, ?_⟩
  intro u v huv X kappa Qn8
  let sn : ℝ := Real.sqrt (n : ℝ)
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  let S : ℝ := u ^ 2 + v ^ 2
  let z : ℂ := (n : ℂ) * Complex.log (Phi p (u / sn) (v / sn))
  let e : ℂ := Qn8 - z
  let b : ℝ := C8 * r ^ 9 / ((n : ℝ) ^ 3 * sn)
  let cf : ℂ := ∫ w : ℝ × ℝ,
    Complex.exp (((u * w.1 + v * w.2 : ℝ) : ℂ) * Complex.I) ∂rho
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsn : 0 < sn := Real.sqrt_pos.mpr hnR
  have hsq : sn ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = S := Real.sq_sqrt (by positivity)
  have hr8 : r ≤ d8 * sn :=
    huv.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsn.le)
  have hrG : r ≤ d0 * sn :=
    huv.trans (mul_le_mul_of_nonneg_right
      ((min_le_right d8 (min d0 dsmall)).trans (min_le_left d0 dsmall)) hsn.le)
  have hNorm := (h8 n hn p).2 u v hr8
  have hGauss := (hG n hn p).2 u v hrG
  refine ⟨hGauss.1, ?_⟩
  have hCF : cf = Complex.exp z := hNorm.2.2.2
  have herror : ‖z - Qn8‖ ≤ b := hNorm.2.1
  have he : ‖e‖ ≤ b := by rw [e, norm_sub_rev]; exact herror
  have hz : z.re ≤ -S / 4 := Real.exp_le_exp.mp (by
    calc
      Real.exp z.re = ‖Complex.exp z‖ := (Complex.norm_exp z).symm
      _ = ‖cf‖ := congrArg norm hCF.symm
      _ ≤ Real.exp (-S / 4) := hGauss.1)
  have hx : r / sn ≤ min d8 (min d0 dsmall) := (div_le_iff₀ hsn).mpr huv
  have hx0 : 0 ≤ r / sn := div_nonneg hr0 hsn.le
  have hx1 : r / sn ≤ 1 := hx.trans ((min_le_left _ _).trans hd81)
  have hxsmall : r / sn ≤ dsmall :=
    hx.trans ((min_le_right d8 (min d0 dsmall)).trans (min_le_right d0 dsmall))
  have hpow : (r / sn) ^ 7 ≤ r / sn := by
    simpa only [pow_one] using pow_le_pow_of_le_one hx0 hx1 (by norm_num : 1 ≤ 7)
  have hratio : C8 / (C8 + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < C8 + 1)).mpr
    linarith
  have hCd : C8 * dsmall ≤ 1 / 8 := by
    calc
      _ = (C8 / (C8 + 1)) / 8 := by dsimp [dsmall]; ring
      _ ≤ 1 / 8 := div_le_div_of_nonneg_right hratio (by norm_num)
  have hb : b ≤ (S / 4) / 2 := by
    calc
      b = C8 * r ^ 2 * (r / sn) ^ 7 := by
        dsimp only [b]
        rw [← hsq]
        field_simp [hsn.ne'] <;> ring
      _ ≤ C8 * r ^ 2 * dsmall :=
        mul_le_mul_of_nonneg_left (hpow.trans hxsmall) (by positivity)
      _ = (C8 * dsmall) * r ^ 2 := by ring
      _ ≤ (1 / 8) * r ^ 2 := mul_le_mul_of_nonneg_right hCd (sq_nonneg r)
      _ = (S / 4) / 2 := by rw [hr2]; ring
  have hExp := norm_complex_exp_add_error_of_re_le z e (S / 4) b (by linarith) he hb
  have hsum : z + e = Qn8 := by dsimp only [e]; ring
  rw [hsum] at hExp
  calc
    ‖cf - Complex.exp Qn8‖ = ‖Complex.exp Qn8 - Complex.exp z‖ := by
      rw [hCF, norm_sub_rev]
    _ ≤ ‖e‖ * Real.exp (-(S / 4) / 2) := hExp
    _ ≤ b * Real.exp (-(S / 4) / 2) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = C8 * r ^ 9 / ((n : ℝ) ^ 3 * sn) * Real.exp (-S / 8) := by
      dsimp only [b]
      congr 2
      ring

end
end Shao.OQ3
