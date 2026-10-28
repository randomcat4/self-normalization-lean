import Shao.OQ3.CompactOpenDomainActualCellDesmoothingSmall
import Shao.OQ3.CompactOpenDomainSmoothedHermiteDensity
import Shao.OQ3.DensityWeightedTestError
import Shao.OQ3.BoundedSupportTestIntegrability

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_actual_cell_weighted_hermite_approximation
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
                    (n : ℝ) ^ 3 * |(∫ z : ℝ × ℝ, f z ∂nu) -
                      (∫ z : ℝ × ℝ, f z * reference z)| < epsilon := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hDes⟩ :=
    compact_open_domain_actual_cell_weighted_desmoothing_small mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR level a0 stripRadius hstripRadius hdet hWC
  obtain ⟨Eg, hEg, M0, hM0, hMbound, _hCs, _hOsc⟩ :=
    compact_parabola_pair_log_cubic_gaussian_oscillation mu Theta hcompact
      lo hi hlo hhi hbounds level a0 stripRadius hstripRadius
  have hEgE : Eg = E := by
    funext p
    apply ContinuousLinearEquiv.ext
    funext w
    exact ((hEg p).2.1 w).trans ((hE p).1 w).symm
  subst Eg
  obtain ⟨lo2, hi2, hlo2, hhi2, hbounds2, E2, hE2, hApprox⟩ :=
    compact_open_domain_cubic_smoothed_hermite_density_approximation mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR hdet hWC
  have hE2E : E2 = E := by
    funext p
    apply ContinuousLinearEquiv.ext
    funext w
    exact ((hE2 p).1 w).trans ((hE p).1 w).symm
  subst E2
  let U : ℝ := 1 / Real.sqrt lo
  let R0 : ℝ := 2 * U
  let kappa0 : ℝ := (2 * M0) * (4 * hi * U)
  let Cg : ℝ := Real.exp (kappa0 * R0)
  let B : ℝ := 4 * Cg * R0 ^ 2 + 1
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hR0 : 0 ≤ R0 := by dsimp [R0]; positivity
  have hkappa0 : 0 ≤ kappa0 := by dsimp [kappa0]; positivity
  have hCg : 0 < Cg := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, ?_⟩
  intro epsilon hepsilon
  obtain ⟨Nd, hNd, hDesSmall⟩ := hDes (epsilon / 2) (half_pos hepsilon)
  obtain ⟨Na, hNa, hApproxSmall⟩ := hApprox (epsilon / (2 * B)) (by positivity)
  refine ⟨max Nd Na, hNd.trans (le_max_left _ _), ?_⟩
  intro n hn p Qsample M T nu X kappa a Sn
  have hnd : Nd ≤ n := (le_max_left _ _).trans hn
  have hna : Na ≤ n := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := hNd.trans hnd
  have hn1 : 1 ≤ n := by omega
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := by
    nlinarith [Real.sq_sqrt hnp.le, Real.sqrt_nonneg (n : ℝ)]
  let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
  let v : ℝ≥0 := Real.toNNReal (2 * b)
  let gamma : Measure (ℝ × ℝ) :=
    (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
  let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
  let k : (ℝ × ℝ) → ℝ := fun x => (1 / (4 * Real.pi * b)) *
    ∫ w : ℝ × ℝ, Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu
  have ha := hApproxSmall n hna p
  letI : IsProbabilityMeasure nu := ha.1
  letI : IsProbabilityMeasure rho := ha.2.2.2.1
  have hrho : rho = volume.withDensity (fun x => ENNReal.ofReal (k x)) := ha.2.2.2.2.1
  obtain ⟨H, hEval, hRefSmall⟩ := ha.2.2.2.2.2.2.2
  refine ⟨ha.1, H, hEval, ?_⟩
  intro reference
  have href : Measurable reference := by
    have hcont : Continuous reference := by dsimp only [reference]; fun_prop
    exact hcont.measurable
  have hDensity := gaussian_smoothed_pair_real_density nu b (by dsimp [b]; positivity)
  have hk : Measurable k := hDensity.2.2.1
  have hk0 : ∀ z : ℝ × ℝ, 0 ≤ k z := fun z => (hDensity.2.2.2.1 z).1
  let delta : ℝ := (epsilon / (2 * B)) / (n : ℝ) ^ 3
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have herror : ∀ z : ℝ × ℝ, |k z - reference z| ≤ delta := by
    intro z
    apply (le_div_iff₀ (pow_pos hnp 3)).2
    have hz : (n : ℝ) ^ 3 * |k z - reference z| ≤ epsilon / (2 * B) := (hRefSmall z).2.le
    calc
      _ = (n : ℝ) ^ 3 * |k z - reference z| := mul_comm _ _
      _ ≤ _ := hz
  intro aL aR qL qR hy hawidth hqwidth cellA stdCell g f
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
  have hf : Measurable f := hgMeas.indicator hStdMeas
  have hfBound : ∀ z : ℝ × ℝ, |f z| ≤ Cg := by
    intro z
    by_cases hz : z ∈ stdCell
    · simpa only [f, Set.indicator_of_mem hz] using hgBound z hz
    · simp only [f, Set.indicator_of_notMem hz, abs_zero]
      exact hCg.le
  have hfZero : ∀ z : ℝ × ℝ, R0 < ‖z‖ → f z = 0 := by
    intro z hz
    have hnmem : z ∉ stdCell := fun hm => (not_lt_of_ge (hsuppR z hm)) hz
    exact Set.indicator_of_notMem hnmem g
  have hLeb := bounded_support_test_integrable_l1_bound f hf Cg R0 hCg.le hR0 hfBound hfZero
  have hMass : (∫ z : ℝ × ℝ, |f z|) ≤ B := hLeb.2.trans (by dsimp only [B]; linarith)
  have hWeighted := density_weighted_test_error_bound rho k reference f hk hk0 hrho href hf
    hLeb.1 Cg delta hCg.le hdelta hfBound herror
  have hDesCell := hDesSmall n hnd p aL aR qL qR hy hawidth hqwidth
  refine ⟨hf, hLeb.1, hDesCell.2.2.1, hWeighted.2.2.1, ?_⟩
  have hWeightedScale : (n : ℝ) ^ 3 *
      |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z * reference z)| ≤ epsilon / 2 := by
    calc
      _ ≤ (n : ℝ) ^ 3 * (delta * (∫ z : ℝ × ℝ, |f z|)) :=
        mul_le_mul_of_nonneg_left hWeighted.2.2.2 (pow_nonneg hnp.le 3)
      _ ≤ (n : ℝ) ^ 3 * (delta * B) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hMass hdelta) (pow_nonneg hnp.le 3)
      _ = epsilon / 2 := by
        dsimp only [delta]
        field_simp [hnp.ne', hB.ne'] <;> ring
  have htri : |(∫ z : ℝ × ℝ, f z ∂nu) - (∫ z : ℝ × ℝ, f z * reference z)| ≤
      |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z ∂nu)| +
        |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z * reference z)| := by
    calc
      _ = |((∫ z : ℝ × ℝ, f z ∂nu) - (∫ z : ℝ × ℝ, f z ∂rho)) +
          ((∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z * reference z))| := by
            congr 1
            ring
      _ ≤ |(∫ z : ℝ × ℝ, f z ∂nu) - (∫ z : ℝ × ℝ, f z ∂rho)| +
          |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z * reference z)| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (∫ z : ℝ × ℝ, f z ∂nu) (∫ z : ℝ × ℝ, f z ∂rho)]
  have hscale := mul_le_mul_of_nonneg_left htri (pow_nonneg hnp.le 3)
  have hdsmall : (n : ℝ) ^ 3 *
      |(∫ z : ℝ × ℝ, f z ∂rho) - (∫ z : ℝ × ℝ, f z ∂nu)| < epsilon / 2 :=
    hDesCell.2.2.2.2
  nlinarith

end
end Shao.OQ3
