import Shao.OQ3.CompactOpenDomainUniformCGFCumulantBounds
import Shao.OQ3.ComplexLogTaylorOcticCorrection
import Shao.OQ3.ActualCGFOcticLogPolynomial
import Shao.OQ3.PairMomentEdgeworthExponentialError

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

theorem compact_open_domain_octic_cgf_log_remainder
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
      ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ p ∈ Theta, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
          let X : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
          let kappa : ℕ → ℝ := fun j => iteratedDeriv j (ProbabilityTheory.cgf X (laws p)) 0
          let Q8 : ℂ := ∑ j ∈ Finset.range 9,
            (Complex.I ^ j / (j.factorial : ℂ)) * (kappa j : ℂ)
          ‖Complex.log (Phi p u v) - Q8‖ ≤ C * Real.sqrt (u ^ 2 + v ^ 2) ^ 9 := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly, hcgf, hcum⟩ :=
    compact_open_domain_uniform_cgf_cumulant_bounds mu Theta hcompact hTheta
      beta c R hbeta hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
    hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly, hcgf, hcum, ?_⟩
  choose M hMpos hM using hmom
  obtain ⟨K2, K9, delta, hK2, hK9, hdelta, hdelta1, hTL⟩ := hlogTaylor 9 (by norm_num)
  obtain ⟨CE, hCE, hEL⟩ := complex_log_taylor_octic_correction_bound
    (M 2) (M 3) (M 4) (M 5) (M 6) (M 7) (M 8)
    (hMpos 2).le (hMpos 3).le (hMpos 4).le (hMpos 5).le
    (hMpos 6).le (hMpos 7).le (hMpos 8).le
  refine ⟨2 * K2 ^ 5 + 5 * K9 + CE, delta, by positivity, hdelta, hdelta1, ?_⟩
  intro p hp u v huv X kappa Q8
  letI : IsProbabilityMeasure (laws p) := (hpoint p hp).2.2.2.2.2.1
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := huv.trans hdelta1
  have hr2 : r ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  let m : ℕ → ℝ := fun j => ∫ y : Fin 2 → ℝ, X y ^ j ∂laws p
  let a : ℂ := -(m 2 : ℂ) / 2
  let b : ℂ := -Complex.I * (m 3 : ℂ) / 6
  let c : ℂ := (m 4 : ℂ) / 24
  let d : ℂ := Complex.I * (m 5 : ℂ) / 120
  let e : ℂ := -(m 6 : ℂ) / 720
  let f : ℂ := -Complex.I * (m 7 : ℂ) / 5040
  let g : ℂ := (m 8 : ℂ) / 40320
  let Q : ℂ := a + b + c + d + e + f + g -
    (a ^ 2 + 2 * a * b + 2 * a * c + b ^ 2 + 2 * a * d +
      2 * b * c + 2 * a * e + 2 * b * d + c ^ 2) / 2 +
    (a ^ 3 + 3 * a ^ 2 * b + 3 * a ^ 2 * c + 3 * a * b ^ 2) / 3 - a ^ 4 / 4
  let P : ℂ := ∑ j ∈ Finset.range 9, (Complex.I ^ j / (j.factorial : ℂ)) * (m j : ℂ)
  have h0 : 0 ∈ interior (ProbabilityTheory.integrableExpSet X (laws p)) :=
    (hcgf p hp u v).1
  have hmean : (∫ y : Fin 2 → ℝ, X y ∂laws p) = 0 := (hcgf p hp u v).2.1
  have hm0 : m 0 = 1 := by simp [m]
  have hm1 : m 1 = 0 := by simpa [m] using hmean
  have hm (j : ℕ) : |m j| ≤ M j * r ^ j := by
    calc
      _ ≤ r ^ j * (∫ y : Fin 2 → ℝ,
          Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) ^ j ∂laws p) :=
        (pair_projection_signed_moment_bound (laws p) j (hM j p hp).1 u v).2
      _ ≤ r ^ j * M j := mul_le_mul_of_nonneg_left (hM j p hp).2.2 (pow_nonneg hr0 _)
      _ = _ := mul_comm _ _
  have ha : ‖a‖ ≤ M 2 * r ^ 2 := by
    norm_num [a, norm_div, norm_mul]
    exact (div_le_self (abs_nonneg (m 2)) (by norm_num : (1 : ℝ) ≤ 2)).trans (hm 2)
  have hb : ‖b‖ ≤ M 3 * r ^ 3 := by
    norm_num [b, norm_div, norm_mul]
    exact (div_le_self (abs_nonneg (m 3)) (by norm_num : (1 : ℝ) ≤ 6)).trans (hm 3)
  have hc : ‖c‖ ≤ M 4 * r ^ 4 := by
    norm_num [c, norm_div, norm_mul]
    exact (div_le_self (abs_nonneg (m 4)) (by norm_num : (1 : ℝ) ≤ 24)).trans (hm 4)
  have hd : ‖d‖ ≤ M 5 * r ^ 5 := by
    norm_num [d, norm_div, norm_mul]
    exact (div_le_self (abs_nonneg (m 5)) (by norm_num : (1 : ℝ) ≤ 120)).trans (hm 5)
  have he : ‖e‖ ≤ M 6 * r ^ 6 := by
    norm_num [e, norm_div, norm_mul]
    exact (div_le_self (abs_nonneg (m 6)) (by norm_num : (1 : ℝ) ≤ 720)).trans (hm 6)
  have hf : ‖f‖ ≤ M 7 * r ^ 7 := by
    norm_num [f, norm_div, norm_mul]
    exact (div_le_self (abs_nonneg (m 7)) (by norm_num : (1 : ℝ) ≤ 5040)).trans (hm 7)
  have hg : ‖g‖ ≤ M 8 * r ^ 8 := by
    norm_num [g, norm_div, norm_mul]
    exact (div_le_self (abs_nonneg (m 8)) (by norm_num : (1 : ℝ) ≤ 40320)).trans (hm 8)
  have hP : P - 1 = a + b + c + d + e + f + g := by
    norm_num [P, Finset.sum_range_succ, hm0, hm1, a, b, c, d, e, f, g,
      pow_succ, Complex.I_sq]
    ring_nf
  have hQ : Q = Q8 := centered_actual_cgf_octic_log_polynomial (laws p) X h0 hmean
  have hCorr : ‖Complex.logTaylor 5 (P - 1) - Q8‖ ≤ CE * r ^ 9 := by
    rw [hP, ← hQ]
    exact hEL r hr0 hr1 a b c d e f g ha hb hc hd he hf hg
  have hApprox : ‖Complex.log (Phi p u v) - Complex.logTaylor 5 (P - 1)‖ ≤
      2 * (K2 * (u ^ 2 + v ^ 2)) ^ 5 / 5 + 5 * K9 * r ^ 9 := by
    exact (hTL p hp u v huv).2.2 4
  have hr10 : r ^ 10 ≤ r ^ 9 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hSmall : 2 * (K2 * (u ^ 2 + v ^ 2)) ^ 5 / 5 ≤ 2 * K2 ^ 5 * r ^ 9 := by
    calc
      _ = ((2 / 5 : ℝ) * K2 ^ 5) * r ^ 10 := by rw [← hr2]; ring
      _ ≤ (2 * K2 ^ 5) * r ^ 10 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (2 / 5 : ℝ) ≤ 2)
          (pow_nonneg hK2.le _)) (pow_nonneg hr0 _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hr10 (by positivity)
  have hLog : ‖Complex.log (Phi p u v) - Complex.logTaylor 5 (P - 1)‖ ≤
      (2 * K2 ^ 5 + 5 * K9) * r ^ 9 := hApprox.trans (by
    calc
      _ ≤ 2 * K2 ^ 5 * r ^ 9 + 5 * K9 * r ^ 9 := add_le_add hSmall (le_refl _)
      _ = _ := by ring)
  calc
    _ = ‖(Complex.log (Phi p u v) - Complex.logTaylor 5 (P - 1)) +
        (Complex.logTaylor 5 (P - 1) - Q8)‖ := by congr 1; ring
    _ ≤ ‖Complex.log (Phi p u v) - Complex.logTaylor 5 (P - 1)‖ +
        ‖Complex.logTaylor 5 (P - 1) - Q8‖ := norm_add_le _ _
    _ ≤ (2 * K2 ^ 5 + 5 * K9) * r ^ 9 + CE * r ^ 9 := add_le_add hLog hCorr
    _ = _ := by ring

end
end Shao.OQ3
