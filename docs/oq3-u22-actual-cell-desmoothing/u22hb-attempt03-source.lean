import Shao.OQ3.CompactOpenDomainSmoothedDensityBound
import Shao.OQ3.CompactParabolaLogCubicOscillation
import Shao.OQ3.GaussianHalfOscillationNoise
import Shao.OQ3.BoundedIndicatorDesmoothing

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_actual_cell_weighted_desmoothing_bound
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
      ∃ C D0 : ℝ, 0 < C ∧ 0 < D0 ∧ ∃ N : ℕ, 2 ≤ N ∧
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
                |(∫ z : ℝ × ℝ, f z ∂smoothed) - (∫ z : ℝ × ℝ, f z ∂nu)| ≤
                  D0 * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) +
                    C / (n : ℝ) ^ 4 := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, K, hK, N0, hN0, hDensity⟩ :=
    compact_open_domain_cubic_smoothed_density_uniform_bound mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR hdet hWC
  obtain ⟨Eg, hEg, M0, hM0, hMbound, hCs, hOsc⟩ :=
    compact_parabola_pair_log_cubic_gaussian_oscillation mu Theta hcompact
      lo hi hlo hhi hbounds level a0 stripRadius hstripRadius
  have hEE : Eg = E := by
    funext p
    apply ContinuousLinearEquiv.ext
    funext w
    exact ((hEg p).2.1 w).trans ((hE p).1 w).symm
  subst Eg
  let U : ℝ := 1 / Real.sqrt lo
  let R0 : ℝ := 2 * U
  let kappa0 : ℝ := (2 * M0) * (4 * hi * U)
  let G0 : ℝ := R0 * (1 + 2 * (|a0| + stripRadius) / level ^ 2)
  let Cg : ℝ := Real.exp (kappa0 * R0)
  let Cstar : ℝ := Cg * (8 * kappa0 * (R0 + 1) ^ 2 + 768 * (G0 + 1))
  let J : ℝ := (2 * Real.pi) * K * Real.exp ((R0 + 1) ^ 2)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  have hkappa0 : 0 ≤ kappa0 := by dsimp [kappa0]; positivity
  have hCg : 0 < Cg := Real.exp_pos _
  have hCstar : 0 < Cstar := hCs
  have hJ : 0 < J := by dsimp [J]; positivity
  obtain ⟨Nt, hNt, hTail⟩ := cubic_gaussian_half_oscillation_noise_superpolynomial 4 (by norm_num)
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, 2 * Cg, J * Cstar,
    by positivity, by positivity, max N0 Nt, hN0.trans (le_max_left _ _), ?_⟩
  intro n hn p Qsample M T nu b v gamma smoothed aL aR qL qR hy hawidth hqwidth
    cellA stdCell g f
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hnt : Nt ≤ n := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := hN0.trans hn0
  have hn1 : 1 ≤ n := by omega
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    nlinarith [Real.sq_sqrt hnp.le, Real.sqrt_nonneg (n : ℝ)]
  let h : ℝ := Real.log (n : ℝ) / (n : ℝ) ^ 3
  obtain ⟨hh, hsmall⟩ := log_cubic_gaussian_radius_admissible n hn2
  have hhpos : 0 < h := hh
  have hsmall1 : h ≤ 1 := hsmall.trans ((div_le_iff₀ hs).2 (by simpa using hs1))
  let k : (ℝ × ℝ) → ℝ := fun x => (1 / (4 * Real.pi * b)) *
    ∫ w : ℝ × ℝ, Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu
  have hd := hDensity n hn0 p
  have hk : Measurable k := hd.2.2.2.1
  have hkbound : ∀ z : ℝ × ℝ, 0 ≤ k z ∧ k z ≤ K := hd.2.2.2.2.2.2
  have hsmoothed : smoothed = volume.withDensity (fun z => ENNReal.ofReal (k z)) := hd.2.2.1
  letI : IsProbabilityMeasure nu := hd.1
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
  have hsuppR : ∀ z ∈ stdCell, ‖z‖ ≤ R0 := by
    intro z hz
    apply (hsupp z hz).trans
    apply (div_le_iff₀ hs).2
    nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hs1)]
  let kappa : ℝ := (|(p : ℝ × ℝ).1| + |(p : ℝ × ℝ).2|) *
    ‖((E p).symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
  have hpcoords : |(p : ℝ × ℝ).1| ≤ M0 ∧ |(p : ℝ × ℝ).2| ≤ M0 := by
    have hp := hMbound p
    change max |(p : ℝ × ℝ).1| |(p : ℝ × ℝ).2| ≤ M0 at hp
    exact ⟨(le_max_left _ _).trans hp, (le_max_right _ _).trans hp⟩
  have hkappa : kappa ≤ kappa0 := by
    apply mul_le_mul (show |(p : ℝ × ℝ).1| + |(p : ℝ × ℝ).2| ≤ 2 * M0 by
      linarith [hpcoords.1, hpcoords.2]) (hE p).2.2.1 (norm_nonneg _) (by positivity)
  have hgBound : ∀ z ∈ stdCell, |g z| ≤ Cg := by
    have hw := (standardized_cell_exponential_bounds n hn1 (p : ℝ × ℝ) (E p) R0 hR0).1
    intro z hz
    exact (hw z (hsupp z hz)).2.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hkappa hR0))
  have hCellMeas : MeasurableSet cellA := by
    have ht : Continuous (fun w : ℝ × ℝ => w.1 ^ 2 / level ^ 2 - w.2) := by fun_prop
    exact (measurableSet_Ioc.prod measurableSet_Ioc).inter
      (((isClosed_le (continuous_fst.sub continuous_const).abs continuous_const).inter
        ((isClosed_le continuous_const ht).inter (isClosed_le ht continuous_const))).measurableSet)
  have hEmb : MeasurableEmbedding (fun w : ℝ × ℝ =>
      Real.sqrt (n : ℝ) • E p (w - (means p 0, means p 1))) := by
    let e1 : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.addRight (-(means p 0, means p 1))
    let e3 : ℝ ≃ₜ ℝ := Homeomorph.mulLeft₀ (Real.sqrt (n : ℝ)) hs.ne'
    have he := (e3.prodCongr e3).isClosedEmbedding.measurableEmbedding.comp
      ((E p).toHomeomorph.isClosedEmbedding.measurableEmbedding.comp
        e1.isClosedEmbedding.measurableEmbedding)
    change MeasurableEmbedding (fun w : ℝ × ℝ =>
      (Real.sqrt (n : ℝ) * (E p (w - (means p 0, means p 1))).1,
        Real.sqrt (n : ℝ) * (E p (w - (means p 0, means p 1))).2)) at he
    exact he
  have hStdMeas : MeasurableSet stdCell := hEmb.measurableSet_image.mpr hCellMeas
  have hgMeas : Measurable g := by
    have hc : Continuous g := by dsimp [g]; fun_prop
    exact hc.measurable
  have hcpl := bounded_density_indicator_desmoothing_bound nu gamma stdCell hStdMeas
    g hgMeas Cg R0 h K hCg.le hR0 hhpos hK.le hgBound hsuppR k hk hkbound hsmoothed
  have ho := hOsc p n hn2 (means p 0, means p 1) aL aR qL qR hy hawidth hqwidth
  let Phi0 : Measure (ℝ × ℝ) :=
    (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hOscBound : (∫ z : ℝ × ℝ, openBallOscillation f h z ∂Phi0) ≤
      Cstar * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ)) := ho.2
  have hfBound (z : ℝ × ℝ) : |f z| ≤ Cg := by
    by_cases hz : z ∈ stdCell
    · simpa only [f, Set.indicator_of_mem hz] using hgBound z hz
    · simp only [f, Set.indicator_of_notMem hz, abs_zero]
      exact hCg.le
  have hsize := (open_ball_oscillation_properties f Cg h hCg.le hfBound).1
  have hOsc0 : 0 ≤ (∫ z : ℝ × ℝ, openBallOscillation f h z ∂Phi0) :=
    MeasureTheory.integral_nonneg (fun z => (hsize z).1)
  have hsq : (R0 + h) ^ 2 ≤ (R0 + 1) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (add_nonneg hR0 hhpos.le), abs_of_nonneg (by linarith : 0 ≤ R0 + 1)]
    linarith
  have hcoef : (2 * Real.pi) * K * Real.exp ((R0 + h) ^ 2) ≤ J :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq) (by positivity)
  have hOscTerm :
      ((2 * Real.pi) * K * Real.exp ((R0 + h) ^ 2)) *
        (∫ z : ℝ × ℝ, openBallOscillation f h z ∂Phi0) ≤
          J * (Cstar * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) :=
    (mul_le_mul_of_nonneg_right hcoef hOsc0).trans
      (mul_le_mul_of_nonneg_left hOscBound hJ.le)
  have ht : gamma.real {d : ℝ × ℝ | h / 2 < ‖d‖} ≤ Real.rpow (n : ℝ) (-(4 : ℝ)) :=
    (hTail n hnt).2.2.2
  have hrpow : Real.rpow (n : ℝ) (-(4 : ℝ)) = 1 / (n : ℝ) ^ 4 := by
    change (n : ℝ) ^ (-(4 : ℝ)) = 1 / (n : ℝ) ^ 4
    rw [Real.rpow_neg hnp.le]
    rfl
  rw [hrpow] at ht
  have hTailTerm : 2 * Cg * gamma.real {d : ℝ × ℝ | h / 2 < ‖d‖} ≤
      (2 * Cg) / (n : ℝ) ^ 4 := by
    calc
      _ ≤ (2 * Cg) * (1 / (n : ℝ) ^ 4) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  refine ⟨hd.1, hcpl.1, hcpl.2.1, hcpl.2.2.1, ?_⟩
  calc
    _ ≤ ((2 * Real.pi) * K * Real.exp ((R0 + h) ^ 2)) *
        (∫ z : ℝ × ℝ, openBallOscillation f h z ∂Phi0) +
          2 * Cg * gamma.real {d : ℝ × ℝ | h / 2 < ‖d‖} := hcpl.2.2.2.2.2
    _ ≤ J * (Cstar * Real.log (n : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))) +
        (2 * Cg) / (n : ℝ) ^ 4 := add_le_add hOscTerm hTailTerm
    _ = _ := by ring

end
end Shao.OQ3
