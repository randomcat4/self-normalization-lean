import Shao.OQ3.CovarianceWhitening
import Shao.OQ3.CompactTiltCovarianceSpectrum

/-!
Full bounded compact-tilt standardization from exact accepted public producers.
Source R2:38-60,74-76,83-92,343-373; scope81 frozen dbd4392151790ce2a9e86cc84f8fe26fe6e116c84444d79fa31847fb53fd9d99.
-/

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix ENNReal NNReal
noncomputable section

theorem exists_compact_tilted_whitened_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (u0 v0 beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hWC : ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => u0 * x + v0 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) :
    let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
    let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      let lo : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
      let hi : ℝ := 2 * (M ^ 2 + M ^ 4) + 1 + lo
      let c0 : ℝ := m ^ 2 * c / 2
      let mup : (ℝ × ℝ) → Measure ℝ := fun p =>
        mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
      let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (mup p)
      let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
      let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
      let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
        ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
          ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
      let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
        ![∫ x, x ∂mup p, ∫ x, x ^ 2 ∂mup p]
      let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x =>
        A p *ᵥ (![x, x ^ 2] - means p)
      let nu : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (mup p).map (Y p)
      let Phi : (ℝ × ℝ) → ℝ → ℝ → ℂ := fun p xi eta =>
        ∫ y : Fin 2 → ℝ,
          Complex.exp (((xi * y 0 + eta * y 1 : ℝ) : ℂ) * Complex.I) ∂nu p
      let L : ℝ := 1 / Real.sqrt hi
      let U : ℝ := 1 / Real.sqrt lo
      let Q : ℝ := 4 * U * (M + M ^ 2)
      let cA : ℝ := c0 * Real.rpow U (-beta)
      let RA : ℝ := R / L
      0 < lo ∧ lo < hi ∧ 0 < c0 ∧
        0 < L ∧ 0 < U ∧ 0 ≤ Q ∧ 0 < cA ∧ 0 ≤ RA ∧
        ∀ p ∈ K,
          IsProbabilityMeasure (mup p) ∧ (∀ᵐ x ∂mup p, |x| ≤ M) ∧
          MemLp (fun x : ℝ => x) 2 (mup p) ∧
          MemLp (fun x : ℝ => x ^ 2) 2 (mup p) ∧
          (ENNReal.ofReal m • mu0 ≤ mup p) ∧
          (∀ xi eta : ℝ,
            lo * (xi ^ 2 + eta ^ 2) ≤
                xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
              xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
                hi * (xi ^ 2 + eta ^ 2)) ∧
          (∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
            ‖jointCharacteristic (mup p) xi eta‖ ≤
              1 - c0 * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) ∧
          0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
          (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
            0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
          IsProbabilityMeasure (nu p) ∧
          (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (nu p) ∧
            (∫ y : Fin 2 → ℝ, y i ∂nu p) = 0) ∧
          (∀ i j : Fin 2,
            ProbabilityTheory.covariance (fun y : Fin 2 → ℝ => y i)
              (fun y : Fin 2 → ℝ => y j) (nu p) = if i = j then 1 else 0) ∧
          (∀ᵐ y : Fin 2 → ℝ ∂nu p, Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2) ≤ Q) ∧
          (∀ k : ℕ,
            Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k)
              (nu p) ∧
            (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂nu p) ≤ Q ^ k) ∧
          ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
            ‖Phi p xi eta‖ ≤
              1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta) := by
  let mu0 : Measure ℝ := mu.tilted (fun x => u0 * x + v0 * x ^ 2)
  let D0 : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance mu0
  obtain ⟨m, hm, hm1, hlo, hlohi, hc0, hfamily⟩ :=
    exists_compact_tilted_covariance_spectral_bounds
      mu M hM hb K hK u0 v0 beta c R hc hWC
  let lo : ℝ := m * D0.det / (D0 0 0 + D0 1 1)
  let hi : ℝ := 2 * (M ^ 2 + M ^ 4) + 1 + lo
  let c0 : ℝ := m ^ 2 * c / 2
  let mup : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  have hprob (p : ℝ × ℝ) (hp : p ∈ K) : IsProbabilityMeasure (mup p) :=
    (hfamily p hp).1
  have hbound (p : ℝ × ℝ) (hp : p ∈ K) : ∀ᵐ x ∂mup p, |x| ≤ M :=
    (hfamily p hp).2.1
  have hspec (p : ℝ × ℝ) (hp : p ∈ K) :=
    (hfamily p hp).2.2.2.2.2.1
  have hraw (p : ℝ × ℝ) (hp : p ∈ K) :=
    (hfamily p hp).2.2.2.2.2.2
  obtain ⟨hL, hU, hQ, hcA, hRA, hwhite⟩ :=
    uniform_covariance_whitened_moments_weakCramer K mup hprob M lo hi beta c0 R
      hM hlo (lt_trans hlo hlohi) hbeta hc0 hR hbound hspec hraw
  refine ⟨m, hm, hm1, hlo, hlohi, hc0, hL, hU, hQ, hcA, hRA, ?_⟩
  intro p hp
  obtain ⟨hpProb, hpBound, hp1, hp2, hpDom, hpSpec, hpRaw⟩ := hfamily p hp
  exact ⟨hpProb, hpBound, hp1, hp2, hpDom, hpSpec, hpRaw, hwhite p hp⟩

end
end Shao.OQ3
