import Shao.OQ3.OpenDomainAffineMoments
import Shao.OQ3.QuadraticWhiteningSpectralData

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

theorem compact_open_domain_covariance_whitened_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (lo hi beta c R : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hspec : ∀ p ∈ Theta,
      let D : Matrix (Fin 2) (Fin 2) ℝ :=
        parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      ∀ xi eta : ℝ,
        lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2))
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
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ∧
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ≤ C := by
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
  let L : ℝ := 1 / Real.sqrt hi
  let U : ℝ := 1 / Real.sqrt lo
  have hL : 0 < L := one_div_pos.mpr (Real.sqrt_pos.mpr hhi)
  have hU : 0 < U := one_div_pos.mpr (Real.sqrt_pos.mpr hlo)
  have hprob (p : ℝ × ℝ) (hp : p ∈ Theta) : IsProbabilityMeasure (tilt p) :=
    (open_domain_quadratic_tilt_directional_cumulants mu p (hTheta hp)).1
  have hdata (p : ℝ × ℝ) (hp : p ∈ Theta) :=
    quadratic_whitening_spectral_data (D p) (by rfl) lo hi hlo hhi (hspec p hp)
  have hfreq : ∀ p ∈ Theta, ∀ xi eta : ℝ,
      L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
        Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 + (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
      Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 + (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
        U * Real.sqrt (xi ^ 2 + eta ^ 2) := by
    intro p hp
    exact (hdata p hp).2.2.2.2.2.1
  have hentry : ∀ p ∈ Theta, ∀ i j : Fin 2, |A p i j| ≤ U := by
    intro p hp
    exact (hdata p hp).2.2.2.2.2.2
  have hmom := compact_open_domain_affine_parabola_moments mu Theta hcompact hTheta A U hU.le hentry
  obtain ⟨hcA, hRA, htrans⟩ := uniform_weakCramer_of_affine_frequency_bounds
    Theta tilt hprob A means L U beta c R hL hU hbeta hc hR hfreq hWC
  refine ⟨hL, hU, hcA, hRA, ?_, hmom.2⟩
  intro p hp
  letI : IsProbabilityMeasure (tilt p) := hprob p hp
  obtain ⟨hs, ht, hAsym, hwhite, hpositive, hfrequency, _hentries⟩ := hdata p hp
  have hfull := open_domain_quadratic_tilt_directional_cumulants mu p (hTheta hp)
  have hx : MemLp (fun x : ℝ => x) 2 (tilt p) := hfull.2.1
  have hx2 : MemLp (fun x : ℝ => x ^ 2) 2 (tilt p) := hfull.2.2.1
  obtain ⟨hlaw, hmean, hcov⟩ := centered_affine_parabola_mean_covariance (tilt p) hx hx2 (A p)
  letI : IsProbabilityMeasure (laws p) := hlaw
  have hunit (i j : Fin 2) : ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
        if i = j then 1 else 0 := by
    rw [hcov, hAsym, hwhite]
    exact Matrix.one_apply
  exact ⟨hs, ht, hAsym, hwhite, hpositive, hlaw, hmean, hunit, hfrequency, (htrans p hp).2⟩

end
end Shao.OQ3
