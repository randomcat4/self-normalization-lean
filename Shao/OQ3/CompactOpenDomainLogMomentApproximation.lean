import Shao.OQ3.CompactOpenDomainCharacteristicMoments
import Shao.OQ3.StandardizedPairLogMomentApproximation

namespace Shao.OQ3

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

theorem compact_open_domain_pair_log_moment_approximation
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
      ∀ m : ℕ, 1 ≤ m → ∃ K2 Km delta : ℝ,
        0 < K2 ∧ 0 < Km ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ p ∈ Theta, ∀ u v : ℝ, Real.sqrt (u ^ 2 + v ^ 2) ≤ delta →
          let P : ℂ := ∑ j ∈ Finset.range m, (Complex.I ^ j / (j.factorial : ℂ)) *
            ((∫ y : Fin 2 → ℝ, (u * y 0 + v * y 1) ^ j ∂laws p : ℝ) : ℂ)
          ‖Phi p u v - 1‖ ≤ 1 / 2 ∧ ‖P - 1‖ ≤ 1 ∧ ∀ q : ℕ,
            ‖Complex.log (Phi p u v) - Complex.logTaylor (q + 1) (P - 1)‖ ≤
              2 * (K2 * (u ^ 2 + v ^ 2)) ^ (q + 1) / ((q + 1 : ℕ) : ℝ) +
                ((q + 1 : ℕ) : ℝ) * Km * Real.sqrt (u ^ 2 + v ^ 2) ^ m := by
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hspec, E, hE, hreal, hrest⟩ :=
    compact_open_domain_pair_characteristic_moment_expansion
      mu Theta hcompact hTheta beta c R hbeta hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hspec, E, hE, hreal, ?_⟩
  intro L U cA RA
  rcases hrest with ⟨hL, hU, hcA, hRA, hpoint, hmom, hchar⟩
  refine ⟨hL, hU, hcA, hRA, hpoint, hmom, hchar, ?_⟩
  intro m hm
  obtain ⟨M3, hM3pos, hM3⟩ := hmom 3
  obtain ⟨Mm, hMmpos, hMm⟩ := hmom m
  have hprob : ∀ p : Theta, IsProbabilityMeasure (laws p) := by
    intro p
    exact (hpoint p p.property).2.2.2.2.2.1
  have hL2 : ∀ p : Theta, ∀ j : Fin 2,
      MemLp (fun y : Fin 2 → ℝ => y j) 2 (laws p) := by
    intro p j
    exact ((hpoint p p.property).2.2.2.2.2.2.1 j).1
  have hmean : ∀ p : Theta, ∀ j : Fin 2,
      (∫ y : Fin 2 → ℝ, y j ∂laws p) = 0 := by
    intro p j
    exact ((hpoint p p.property).2.2.2.2.2.2.1 j).2
  have hcov : ∀ p : Theta, ∀ j k : Fin 2,
      ProbabilityTheory.covariance
        (fun y : Fin 2 → ℝ => y j) (fun y : Fin 2 → ℝ => y k) (laws p) =
          if j = k then 1 else 0 := by
    intro p j k
    exact (hpoint p p.property).2.2.2.2.2.2.2.1 j k
  have hI3 : ∀ p : Theta, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3) (laws p) := by
    intro p
    exact (hM3 p p.property).1
  have hbound3 : ∀ p : Theta,
      (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ 3 ∂laws p) ≤ M3 := by
    intro p
    exact (hM3 p p.property).2.2
  have hIm : ∀ p : Theta, Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) (laws p) := by
    intro p
    exact (hMm p p.property).1
  have hboundm : ∀ p : Theta,
      (∫ y : Fin 2 → ℝ, Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m ∂laws p) ≤ Mm := by
    intro p
    exact (hMm p p.property).2.2
  obtain ⟨hK2, hKm, delta, hdpos, hdle, hlog⟩ :=
    uniform_standardized_pair_log_moment_approximation
      (fun p : Theta => laws p) hprob hL2 hmean hcov m hm M3 Mm
        hI3 hbound3 hIm hboundm
  refine ⟨2 + (Real.exp 1 + 4) * |M3|,
    1 + (Real.exp 1 + (m : ℝ) + 1) * |Mm|,
    delta, hK2, hKm, hdpos, hdle, ?_⟩
  intro p hp u v hrad
  exact hlog ⟨p, hp⟩ u v hrad

end
end Shao.OQ3
