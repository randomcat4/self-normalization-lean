import Shao.OQ3.QuadraticWhiteningPairEquiv

namespace Shao.OQ3
open MeasureTheory
open scoped Matrix Topology
noncomputable section

theorem parabola_covariance_pair_whitening_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
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
    let B : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => D p * A p
    let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
      (∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p)
    ∃ E : Theta → ((ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)), ∀ p : Theta,
      A p * D p * A p = 1 ∧
      (∀ w : ℝ × ℝ, E p w =
        (A p 0 0 * w.1 + A p 0 1 * w.2, A p 1 0 * w.1 + A p 1 1 * w.2)) ∧
      (∀ w : ℝ × ℝ, (E p).symm w =
        (B p 0 0 * w.1 + B p 0 1 * w.2, B p 1 0 * w.1 + B p 1 1 * w.2)) ∧
      ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 2 * (1 / Real.sqrt lo) ∧
      ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ 4 * hi * (1 / Real.sqrt lo) ∧
      ∀ x : ℝ, E p ((x, x ^ 2) - means p) =
        ((A p *ᵥ (![x, x ^ 2] - ![(means p).1, (means p).2])) 0,
          (A p *ᵥ (![x, x ^ 2] - ![(means p).1, (means p).2])) 1) := by
  classical
  dsimp only
  let tilt : (ℝ × ℝ) → Measure ℝ := fun p =>
    mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)
  let D : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => parabolaCovariance (tilt p)
  let s : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 * D p 1 1 - (D p 0 1) ^ 2)
  let t : (ℝ × ℝ) → ℝ := fun p => Real.sqrt (D p 0 0 + D p 1 1 + 2 * s p)
  let A : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p =>
    ![![(D p 1 1 + s p) / (s p * t p), -(D p 0 1) / (s p * t p)],
      ![-(D p 0 1) / (s p * t p), (D p 0 0 + s p) / (s p * t p)]]
  let B : (ℝ × ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun p => D p * A p
  let means : (ℝ × ℝ) → (ℝ × ℝ) := fun p =>
    (∫ x : ℝ, x ∂tilt p, ∫ x : ℝ, x ^ 2 ∂tilt p)
  have hpoint (p : Theta) := quadratic_whitening_pair_equiv
    (D p) (by rfl) lo hi hlo hhi (hspec p p.property)
  choose E hE using (fun p : Theta => (hpoint p).2)
  refine ⟨E, ?_⟩
  intro p
  refine ⟨(hpoint p).1, (hE p).1, (hE p).2.1,
    (hE p).2.2.1, (hE p).2.2.2, ?_⟩
  intro x
  rw [(hE p).1 ((x, x ^ 2) - means p)]
  apply Prod.ext <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, D, tilt, means]

end
end Shao.OQ3
