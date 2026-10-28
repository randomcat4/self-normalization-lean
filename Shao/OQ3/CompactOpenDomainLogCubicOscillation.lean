import Shao.OQ3.CompactOpenDomainCovarianceSpectrum
import Shao.OQ3.CompactParabolaLogCubicOscillation

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Matrix Topology
noncomputable section

theorem compact_open_domain_parabola_log_cubic_gaussian_oscillation
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (hdet : ∀ p ∈ Theta, 0 < (parabolaCovariance
      (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det)
    (level a0 rho : ℝ) (hrho : 0 ≤ rho) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
    let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
    let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
    let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
      ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
        ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      (∀ p ∈ Theta, ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
        xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2)) ∧
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
      (∀ p : Theta, A p * D p * A p = 1 ∧
        (∀ w : ℝ × ℝ, E p w =
          (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
        ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
        ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo)) ∧
      ∃ M : ℝ, 0 < M ∧ (∀ p : Theta, ‖(p : ℝ × ℝ)‖ ≤ M) ∧
        let U : ℝ := 1 / Real.sqrt lo
        let R0 : ℝ := 2 * U
        let kappa0 : ℝ := (2 * M) * (4 * hi * U)
        let G0 : ℝ := R0 * (1 + 2 * (|a0| + rho) / level ^ 2)
        let Cstar : ℝ := Real.exp (kappa0 * R0) *
          (8 * kappa0 * (R0 + 1) ^ 2 + 768 * (G0 + 1))
        0 < Cstar ∧
        ∀ (p : Theta) (n : ℕ), 2 ≤ n → ∀ (y : ℝ × ℝ) (aL aR qL qR : ℝ),
          y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR →
          aR - aL ≤ 1 / (n : ℝ) → qR - qL ≤ 1 / (n : ℝ) →
          let h : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
          let cellA : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
            {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
              0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
          let stdCell : Set (ℝ × ℝ) :=
            (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E p (w - y)) '' cellA
          let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
            ((p : ℝ × ℝ).1 * ((E p).symm v).1 +
              (p : ℝ × ℝ).2 * ((E p).symm v).2))
          let Φ : Measure (ℝ × ℝ) :=
            (gaussianReal 0 1).prod (gaussianReal 0 1)
          Integrable (openBallOscillation (stdCell.indicator g) h) Φ ∧
            (∫ z, openBallOscillation (stdCell.indicator g) h z ∂Φ) ≤
              Cstar * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := by
  dsimp only
  let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
  obtain ⟨lo, hi, hlo, hhi, hs⟩ :=
    compact_open_domain_covariance_spectral_bounds mu Theta hcompact hTheta hdet
  have hspec : ∀ p ∈ Theta, ∀ xi eta : ℝ,
      lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ∧
        xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2) := by
    intro p hp xi eta
    have h := hs p hp xi eta
    constructor
    · calc
        lo * (xi ^ 2 + eta ^ 2) ≤
            D p 0 0 * xi ^ 2 + 2 * D p 0 1 * xi * eta + D p 1 1 * eta ^ 2 := h.1
        _ = xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 := by ring
    · calc
        xi ^ 2 * D p 0 0 + 2 * xi * eta * D p 0 1 + eta ^ 2 * D p 1 1 =
            D p 0 0 * xi ^ 2 + 2 * D p 0 1 * xi * eta + D p 1 1 * eta ^ 2 := by ring
        _ ≤ hi * (xi ^ 2 + eta ^ 2) := h.2
  refine ⟨lo, hi, hlo, hhi, hspec, ?_⟩
  exact compact_parabola_pair_log_cubic_gaussian_oscillation mu Theta hcompact
    lo hi hlo hhi hspec level a0 rho hrho

end
end Shao.OQ3
