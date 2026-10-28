import Shao.OQ3.CompactOpenDomainActualCellHermite
import Shao.OQ3.StandardizedCellChangeOfMeasure

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_actual_cell_physical_hermite_approximation
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
    (level a0 stripRadius : ℝ) (hstripRadius : 0 ≤ stripRadius)
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
    let Klog : (ℝ × ℝ) → ℝ := fun p => Real.log
      (∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu)
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
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let nu : Measure (ℝ × ℝ) := Qsample.map T
          let X : (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ := fun z y => z.1 * y 0 + z.2 * y 1
          let kappa : ℕ → (ℝ × ℝ) → ℝ :=
            fun j z => iteratedDeriv j (ProbabilityTheory.cgf (X z) (laws p)) 0
          let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
            (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
              (kappa (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
          let Sn : (ℝ × ℝ) → ℂ := fun z =>
            ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
              ∑ sigma : Fin q.val → Fin 6,
                if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
          let P : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => mu)
          let rateAtMean : ℝ := (p : ℝ × ℝ).1 * means p 0 +
            (p : ℝ × ℝ).2 * means p 1 - Klog p
          IsProbabilityMeasure nu ∧
            ∃ H : MvPolynomial (Fin 2) ℝ,
              (∀ z : ℝ × ℝ, MvPolynomial.eval₂ Complex.ofRealHom
                ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] H = Sn z) ∧
              let reference : (ℝ × ℝ) → ℝ := fun x => (1 / (2 * Real.pi)) *
                (∑ d ∈ H.support, H.coeff d *
                  (gaussianHermitePolynomial (d 0)).eval x.1 *
                    (gaussianHermitePolynomial (d 1)).eval x.2) *
                      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
              ∀ aL aR qL qR : ℝ,
                (means p 0, means p 1) ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR →
                aR - aL ≤ 1 / (n : ℝ) → qR - qL ≤ 1 / (n : ℝ) →
                let cellA : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
                  {w : ℝ × ℝ | |w.1 - a0| ≤ stripRadius ∧
                    0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧
                      w.1 ^ 2 / level ^ 2 - w.2 ≤ stripRadius}
                let stdCell : Set (ℝ × ℝ) :=
                  (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) •
                    E p (w - (means p 0, means p 1))) '' cellA
                let g : (ℝ × ℝ) → ℝ := fun z => Real.exp (-Real.sqrt (n : ℝ) *
                  ((p : ℝ × ℝ).1 * ((E p).symm z).1 +
                    (p : ℝ × ℝ).2 * ((E p).symm z).2))
                let f : (ℝ × ℝ) → ℝ := stdCell.indicator g
                Measurable f ∧ Integrable f ∧ Integrable f nu ∧
                  Integrable (fun z : ℝ × ℝ => f z * reference z) ∧
                    P.real (M ⁻¹' cellA) = Real.exp (-(n : ℝ) * rateAtMean) *
                      (∫ z : ℝ × ℝ, f z ∂nu) ∧
                    (n : ℝ) ^ 3 * |Real.exp ((n : ℝ) * rateAtMean) * P.real (M ⁻¹' cellA) -
                      (∫ z : ℝ × ℝ, f z * reference z)| < epsilon := by
  classical
  intro tilt D s t A means Y laws Phi Klog
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hApprox⟩ :=
    compact_open_domain_actual_cell_weighted_hermite_approximation mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR level a0 stripRadius hstripRadius hdet hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, ?_⟩
  intro epsilon hepsilon
  obtain ⟨N, hN, hSmall⟩ := hApprox epsilon hepsilon
  refine ⟨N, hN, ?_⟩
  intro n hn p Qsample M T nu X kappa a Sn P rateAtMean
  have hn1 : 1 ≤ n := by have := hN.trans hn; omega
  have ha := hSmall n hn p
  obtain ⟨H, hEval, hCell⟩ := ha.2
  refine ⟨ha.1, H, hEval, ?_⟩
  intro reference aL aR qL qR hy hawidth hqwidth cellA stdCell g f
  have hf := hCell aL aR qL qR hy hawidth hqwidth
  have hCellMeas : MeasurableSet cellA := by
    have ht : Continuous (fun w : ℝ × ℝ => w.1 ^ 2 / level ^ 2 - w.2) := by fun_prop
    exact (measurableSet_Ioc.prod measurableSet_Ioc).inter
      (((isClosed_le (continuous_fst.sub continuous_const).abs continuous_const).inter
        ((isClosed_le continuous_const ht).inter (isClosed_le ht continuous_const))).measurableSet)
  have hdom : (p : ℝ × ℝ) ∈
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)) :=
    interior_subset (hTheta p.property)
  have hchange := iid_quadratic_standardized_cell_change_of_measure mu (p : ℝ × ℝ) hdom
    n hn1 (means p 0, means p 1) (E p) cellA hCellMeas
  have hBeq : {z : ℝ × ℝ | (means p 0, means p 1) +
      (Real.sqrt (n : ℝ))⁻¹ • (E p).symm z ∈ cellA} = stdCell := hchange.2.1
  have hStdMeas : MeasurableSet stdCell := hBeq ▸ hchange.1
  have hSetIdentity := hchange.2.2.2
  rw [hBeq] at hSetIdentity
  have hIdentity : P.real (M ⁻¹' cellA) = Real.exp (-(n : ℝ) * rateAtMean) *
      (∫ z : ℝ × ℝ, f z ∂nu) := by
    change P.real (M ⁻¹' cellA) = Real.exp (-(n : ℝ) * rateAtMean) *
      (∫ z : ℝ × ℝ, stdCell.indicator g z ∂nu)
    rw [integral_indicator hStdMeas]
    exact hSetIdentity
  have hCancel : Real.exp ((n : ℝ) * rateAtMean) * P.real (M ⁻¹' cellA) =
      ∫ z : ℝ × ℝ, f z ∂nu := by
    rw [hIdentity, ← mul_assoc, ← Real.exp_add]
    rw [show (n : ℝ) * rateAtMean + -(n : ℝ) * rateAtMean = 0 by ring,
      Real.exp_zero, one_mul]
  refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hIdentity, ?_⟩
  rw [hCancel]
  exact hf.2.2.2.2

end
end Shao.OQ3
