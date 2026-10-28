import Shao.OQ3.CompactOpenDomainActualCellHermite
import Shao.OQ3.CompactOpenDomainHermiteLocalGaussian
import Shao.OQ3.WeightedRelativeReferenceIntegral

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_actual_cell_weighted_gaussian_approximation
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
    let phi : (ℝ × ℝ) → ℝ := fun x =>
      (1 / (2 * Real.pi)) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
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
      ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ p : Theta,
          let Qsample : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => tilt p)
          let M : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : (Fin n → ℝ) → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let nu : Measure (ℝ × ℝ) := Qsample.map T
          IsProbabilityMeasure nu ∧
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
            let J0 : ℝ := ∫ z : ℝ × ℝ, f z * phi z
            Measurable f ∧ Integrable f ∧ Integrable f nu ∧
              Integrable (fun z : ℝ × ℝ => f z * phi z) ∧ 0 ≤ J0 ∧
                |(∫ z : ℝ × ℝ, f z ∂nu) - J0| <
                  (C / (n : ℝ)) * J0 + epsilon / (n : ℝ) ^ 3 := by
  classical
  intro tilt D s t A means Y laws Phi phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hApprox⟩ :=
    compact_open_domain_actual_cell_weighted_hermite_approximation mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR level a0 stripRadius hstripRadius hdet hWC
  let R0 : ℝ := 2 * (1 / Real.sqrt lo)
  let K : ℝ := 2 * R0
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨C, hC, Ng, hNg, hGaussian⟩ :=
    compact_open_domain_hermite_local_gaussian_relative_bound
      mu Theta hcompact hTheta beta c R hbeta hc hR hdet hWC K hK
  have hphiMeas : Measurable phi := by
    have hcont : Continuous phi := by dsimp [phi]; fun_prop
    exact hcont.measurable
  have hphi0 (z : ℝ × ℝ) : 0 ≤ phi z := by dsimp [phi]; positivity
  have hphiBound (z : ℝ × ℝ) : phi z ≤ 1 / (2 * Real.pi) := by
    dsimp only [phi]
    calc
      _ ≤ (1 / (2 * Real.pi)) * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z.1, sq_nonneg z.2]))
          (by positivity)
      _ = _ := mul_one _
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, C, hC, ?_⟩
  intro epsilon hepsilon
  obtain ⟨Nh, hNh, hHermite⟩ := hApprox epsilon hepsilon
  refine ⟨max Nh Ng, hNh.trans (le_max_left _ _), ?_⟩
  intro n hn p Qsample M T nu
  have hnh : Nh ≤ n := (le_max_left _ _).trans hn
  have hng : Ng ≤ n := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ n := hNg.trans hng
  have hnp : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  obtain ⟨hnu, H, hEval, hCells⟩ := hHermite n hnh p
  let reference : (ℝ × ℝ) → ℝ := fun x => (1 / (2 * Real.pi)) *
    (∑ d ∈ H.support, H.coeff d *
      (gaussianHermitePolynomial (d 0)).eval x.1 *
        (gaussianHermitePolynomial (d 1)).eval x.2) *
          Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
  have href : Measurable reference := by
    have hcont : Continuous reference := by dsimp [reference]; fun_prop
    exact hcont.measurable
  refine ⟨hnu, ?_⟩
  intro aL aR qL qR hy hawidth hqwidth cellA stdCell g f J0
  have hCellData : Measurable f ∧ Integrable f ∧ Integrable f nu ∧
      Integrable (fun z : ℝ × ℝ => f z * reference z) ∧
        (n : ℝ) ^ 3 * |(∫ z : ℝ × ℝ, f z ∂nu) -
          (∫ z : ℝ × ℝ, f z * reference z)| < epsilon :=
    hCells aL aR qL qR hy hawidth hqwidth
  obtain ⟨hf, hfi, hfinu, hfiRef, hHermiteError⟩ := hCellData
  have hcell : ∀ w ∈ cellA, ‖w - (means p 0, means p 1)‖ ≤ 1 / (n : ℝ) := by
    intro w hw
    have ha : w.1 ∈ Set.Ioc aL aR := hw.1.1
    have hq : w.2 ∈ Set.Ioc qL qR := hw.1.2
    have hx : |w.1 - means p 0| ≤ 1 / (n : ℝ) :=
      abs_le.mpr ⟨by linarith [ha.1, hy.1.2], by linarith [ha.2, hy.1.1]⟩
    have hz : |w.2 - means p 1| ≤ 1 / (n : ℝ) :=
      abs_le.mpr ⟨by linarith [hq.1, hy.2.2], by linarith [hq.2, hy.2.1]⟩
    simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs] using max_le hx hz
  have hsupp : ∀ z ∈ stdCell, ‖z‖ ≤ R0 / Real.sqrt (n : ℝ) := by
    have ha := standardized_cell_support_bound n hn1 (E p) (means p 0, means p 1)
      1 (by norm_num) cellA hcell
    intro z hz
    have hb := ha z hz
    have hnorm : ‖(E p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖ ≤ R0 := (hE p).2.1
    exact hb.trans (div_le_div_of_nonneg_right (by simpa only [one_mul] using hnorm) hs.le)
  have hEuclidean : ∀ z ∈ stdCell,
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ K / Real.sqrt (n : ℝ) := by
    intro z hz
    have hb : 0 ≤ R0 / Real.sqrt (n : ℝ) := div_nonneg hR0 hs.le
    have hmax : max |z.1| |z.2| ≤ R0 / Real.sqrt (n : ℝ) := by
      simpa only [Prod.norm_def, Real.norm_eq_abs] using hsupp z hz
    have h1 : z.1 ^ 2 ≤ (R0 / Real.sqrt (n : ℝ)) ^ 2 := by
      simpa only [← pow_two, sq_abs] using
        mul_self_le_mul_self (abs_nonneg z.1) ((le_max_left _ _).trans hmax)
    have h2 : z.2 ^ 2 ≤ (R0 / Real.sqrt (n : ℝ)) ^ 2 := by
      simpa only [← pow_two, sq_abs] using
        mul_self_le_mul_self (abs_nonneg z.2) ((le_max_right _ _).trans hmax)
    calc
      _ ≤ Real.sqrt ((2 * (R0 / Real.sqrt (n : ℝ))) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (R0 / Real.sqrt (n : ℝ))])
      _ = 2 * (R0 / Real.sqrt (n : ℝ)) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hb)]
      _ = K / Real.sqrt (n : ℝ) := by dsimp [K]; ring
  have hf0 (z : ℝ × ℝ) : 0 ≤ f z := by
    by_cases hz : z ∈ stdCell
    · have hg0 : 0 ≤ g z := by dsimp [g]; positivity
      simpa only [f, Set.indicator_of_mem hz] using hg0
    · simp only [f, Set.indicator_of_notMem hz, le_refl]
  have hRelative (z : ℝ × ℝ) (hfz : f z ≠ 0) :
      |reference z - phi z| ≤ (C / (n : ℝ)) * phi z := by
    have hz : z ∈ stdCell := by
      by_contra hnz
      simp only [f, Set.indicator_of_notMem hnz, ne_eq, not_true_eq_false] at hfz
    exact hGaussian n hng p H hEval z (hEuclidean z hz)
  have hWeighted := nonnegative_weighted_relative_reference_error phi reference f
    hphiMeas href hf hfi hf0 hphi0 (1 / (2 * Real.pi)) (C / (n : ℝ))
      (by positivity) (div_nonneg hC.le hnp.le) hphiBound hRelative
  have hSmall : |(∫ z : ℝ × ℝ, f z ∂nu) -
      (∫ z : ℝ × ℝ, f z * reference z)| < epsilon / (n : ℝ) ^ 3 := by
    apply (lt_div_iff₀ (pow_pos hnp 3)).mpr
    calc
      _ = (n : ℝ) ^ 3 * |(∫ z : ℝ × ℝ, f z ∂nu) -
          (∫ z : ℝ × ℝ, f z * reference z)| := mul_comm _ _
      _ < _ := hHermiteError
  refine ⟨hf, hfi, hfinu, hWeighted.1, hWeighted.2.2.1, ?_⟩
  calc
    _ = |((∫ z : ℝ × ℝ, f z ∂nu) - (∫ z : ℝ × ℝ, f z * reference z)) +
        ((∫ z : ℝ × ℝ, f z * reference z) - J0)| := by congr 1 <;> ring
    _ ≤ |(∫ z : ℝ × ℝ, f z ∂nu) - (∫ z : ℝ × ℝ, f z * reference z)| +
        |(∫ z : ℝ × ℝ, f z * reference z) - J0| := abs_add_le _ _
    _ < epsilon / (n : ℝ) ^ 3 + (C / (n : ℝ)) * J0 :=
      add_lt_add_of_lt_of_le hSmall hWeighted.2.2.2
    _ = (C / (n : ℝ)) * J0 + epsilon / (n : ℝ) ^ 3 := add_comm _ _

end
end Shao.OQ3
