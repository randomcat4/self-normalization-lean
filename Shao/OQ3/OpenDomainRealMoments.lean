import Shao.OQ3.OpenDomainAffineMoments
import Shao.OQ3.QuadraticWhiteningSpectralData

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology ContDiff
noncomputable section

private theorem nonnegative_rpow_le_one_add_nat_power
    (x r : ℝ) (n : ℕ) (hx : 0 ≤ x) (hr : 0 ≤ r) (hrn : r ≤ (n : ℝ)) :
    Real.rpow x r ≤ 1 + x ^ n := by
  by_cases hx1 : x ≤ 1
  · have hle : Real.rpow x r ≤ 1 := Real.rpow_le_one hx hx1 hr
    exact hle.trans (by linarith [pow_nonneg hx n])
  · calc
      Real.rpow x r ≤ Real.rpow x (n : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hx1)) hrn
      _ = x ^ n := Real.rpow_natCast x n
      _ ≤ 1 + x ^ n := by linarith

theorem compact_open_domain_affine_parabola_real_moments
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hA : ∀ theta ∈ Theta, ∀ i j : Fin 2, |A theta i j| ≤ U) :
    let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
      mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
    let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
      ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
    let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x =>
      A p *ᵥ (![x, x ^ 2] - means p)
    let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
    (∀ theta ∈ Theta, IsProbabilityMeasure (laws theta)) ∧
      ∀ r : ℝ, 0 ≤ r → ∃ C : ℝ, 0 < C ∧ ∀ theta ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) r)
          (laws theta) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) r ∂laws theta) ∧
        (∫ y : Fin 2 → ℝ, Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) r ∂laws theta) ≤ C := by
  let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let means : (ℝ × ℝ) → (Fin 2 → ℝ) := fun p =>
    ![∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p]
  let Y : (ℝ × ℝ) → ℝ → (Fin 2 → ℝ) := fun p x => A p *ᵥ (![x, x ^ 2] - means p)
  let laws : (ℝ × ℝ) → Measure (Fin 2 → ℝ) := fun p => (tilt p).map (Y p)
  let radius : (Fin 2 → ℝ) → ℝ := fun y => Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)
  have hradius : Continuous radius := by dsimp [radius]; fun_prop
  have hnatural := compact_open_domain_affine_parabola_moments mu Theta hcompact hTheta A U hU hA
  refine ⟨hnatural.1, ?_⟩
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_gt r
  obtain ⟨Cn, hCn, hnMom⟩ := hnatural.2 n
  refine ⟨1 + Cn, by linarith, ?_⟩
  intro p hp
  letI : IsProbabilityMeasure (laws p) := hnatural.1 p hp
  have hcont : Continuous (fun y : Fin 2 → ℝ => Real.rpow (radius y) r) :=
    (Real.continuous_rpow_const hr).comp hradius
  have hdom : Integrable (fun y : Fin 2 → ℝ => 1 + radius y ^ n) (laws p) :=
    (integrable_const (1 : ℝ)).add (hnMom p hp).1
  have hpoint (y : Fin 2 → ℝ) : Real.rpow (radius y) r ≤ 1 + radius y ^ n :=
    nonnegative_rpow_le_one_add_nat_power (radius y) r n (Real.sqrt_nonneg _) hr hn.le
  have hi : Integrable (fun y : Fin 2 → ℝ => Real.rpow (radius y) r) (laws p) := by
    apply hdom.mono' hcont.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.rpow (radius y) r from
        Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
      exact hpoint y
  refine ⟨hi, integral_nonneg (fun y => Real.rpow_nonneg (Real.sqrt_nonneg _) _), ?_⟩
  calc
    (∫ y : Fin 2 → ℝ, Real.rpow (radius y) r ∂laws p) ≤
        ∫ y : Fin 2 → ℝ, 1 + radius y ^ n ∂laws p := integral_mono hi hdom hpoint
    _ = 1 + ∫ y : Fin 2 → ℝ, radius y ^ n ∂laws p := by
      rw [integral_add (integrable_const 1) (hnMom p hp).1]
      have hone : (∫ _y : Fin 2 → ℝ, (1 : ℝ) ∂laws p) = 1 := by
        rw [integral_const]
        simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
      rw [hone]
    _ ≤ 1 + Cn := by linarith [(hnMom p hp).2.2]

theorem compact_open_domain_whitened_eight_add_delta_moment
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (lo hi delta : ℝ) (hlo : 0 < lo) (hhi : 0 < hi) (hdelta : 0 < delta)
    (hspec : ∀ p ∈ Theta,
      let D : Matrix (Fin 2) (Fin 2) ℝ :=
        parabolaCovariance (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
      ∀ xi eta : ℝ,
        lo * (xi ^ 2 + eta ^ 2) ≤
          xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ∧
        xi ^ 2 * D 0 0 + 2 * xi * eta * D 0 1 + eta ^ 2 * D 1 1 ≤
          hi * (xi ^ 2 + eta ^ 2)) :
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
    (∀ p ∈ Theta, (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
      IsProbabilityMeasure (laws p)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ =>
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta)) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ∧
        (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ≤ C := by
  let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
  let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
  let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
  let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
    ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
      ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
  let U : ℝ := 1 / Real.sqrt lo
  have hU : 0 < U := one_div_pos.mpr (Real.sqrt_pos.mpr hlo)
  have hdata (p : ℝ × ℝ) (hp : p ∈ Theta) :=
    quadratic_whitening_spectral_data (D p) (by rfl) lo hi hlo hhi (hspec p hp)
  have hentry : ∀ p ∈ Theta, ∀ i j : Fin 2, |A p i j| ≤ U := by
    intro p hp
    exact (hdata p hp).2.2.2.2.2.2
  have hmom := compact_open_domain_affine_parabola_real_moments
    mu Theta hcompact hTheta A U hU.le hentry
  refine ⟨?_, hmom.2 (8 + delta) (by linarith)⟩
  intro p hp
  exact ⟨(hdata p hp).2.2.1, (hdata p hp).2.2.2.1, hmom.1 p hp⟩

end
end Shao.OQ3
