import Shao.OQ3.CompactOpenDomainActualCellDesmoothing

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_actual_cell_weighted_desmoothing_small
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
          let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
          let v : ℝ≥0 := Real.toNNReal (2 * b)
          let gamma : Measure (ℝ × ℝ) :=
            (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
          let smoothed : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
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
            IsProbabilityMeasure nu ∧ IsProbabilityMeasure smoothed ∧
              Integrable f nu ∧ Integrable f smoothed ∧
                (n : ℝ) ^ 3 *
                  |(∫ z : ℝ × ℝ, f z ∂smoothed) - (∫ z : ℝ × ℝ, f z ∂nu)| < epsilon := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, C, D0, hC, hD0, N0, hN0, hBound⟩ :=
    compact_open_domain_actual_cell_weighted_desmoothing_bound mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR level a0 stripRadius hstripRadius hdet hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, ?_⟩
  intro epsilon hepsilon
  have ht : Tendsto (fun n : ℕ => D0 * ((n : ℝ) ^ 3 *
      (Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)))))
      atTop (nhds 0) := by
    simpa only [mul_zero] using log_cubic_gaussian_oscillation_normalized_tendsto_zero.const_mul D0
  have hs : ∀ᶠ n : ℕ in atTop, D0 * ((n : ℝ) ^ 3 *
      (Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)))) < epsilon / 2 :=
    ht.eventually (gt_mem_nhds (half_pos hepsilon))
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.1 hs
  obtain ⟨J, hJ⟩ := exists_nat_gt (C / (epsilon / 2))
  refine ⟨max N0 (max Nlog (J + 1)), hN0.trans (le_max_left _ _), ?_⟩
  intro n hn p Qsample M T nu b v gamma smoothed aL aR qL qR hy hawidth hqwidth
    cellA stdCell g f
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hnlog : Nlog ≤ n := (le_max_left Nlog (J + 1)).trans ((le_max_right _ _).trans hn)
  have hJn : J < n := by
    have hh := (le_max_right Nlog (J + 1)).trans ((le_max_right N0 _).trans hn)
    omega
  have hJnR : (J : ℝ) < (n : ℝ) := by exact_mod_cast hJn
  have hn2 : 2 ≤ n := hN0.trans hn0
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hCsmall : C / (n : ℝ) < epsilon / 2 := by
    apply (div_lt_iff₀ hnp).2
    have h := (div_lt_iff₀ (half_pos hepsilon)).1 (hJ.trans hJnR)
    nlinarith
  have hLogsmall := hNlog n hnlog
  have hb := hBound n hn0 p aL aR qL qR hy hawidth hqwidth
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, ?_⟩
  have hscale := mul_le_mul_of_nonneg_left hb.2.2.2.2 (pow_nonneg hnp.le 3)
  have hidentity : (n : ℝ) ^ 3 *
      (D0 * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) + C / (n : ℝ) ^ 4) =
      D0 * ((n : ℝ) ^ 3 *
        (Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)))) + C / (n : ℝ) := by
    field_simp [hnp.ne', (Real.sqrt_pos.mpr hnp).ne'] <;> ring
  rw [hidentity] at hscale
  exact hscale.trans_lt (by linarith)

end
end Shao.OQ3
