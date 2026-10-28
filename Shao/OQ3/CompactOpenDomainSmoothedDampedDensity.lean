import Shao.OQ3.CompactOpenDomainSixOrderLogCubicOscillatoryWindow
import Shao.OQ3.GaussianDampedWeightedErrorIntegral
import Shao.OQ3.GaussianSmoothedDensityErrorGlue
import Shao.OQ3.GaussianSmoothedLogCubicWindowTail

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_cubic_smoothed_damped_density_approximation
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hbetaUpper : beta < (2 : ℝ) / 5)
    (hc : 0 < c) (hR : 0 ≤ R)
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
          let Pn : (ℝ × ℝ) → ℂ := fun z =>
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) *
              ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
                ∑ sigma : Fin q.val → Fin 6,
                  if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
          let b : ℝ := 1 / (2 * (n : ℝ) ^ 6)
          let v : ℝ≥0 := Real.toNNReal (2 * b)
          let gamma : Measure (ℝ × ℝ) :=
            (ProbabilityTheory.gaussianReal 0 v).prod (ProbabilityTheory.gaussianReal 0 v)
          let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
          let k : (ℝ × ℝ) → ℝ := fun x => (1 / (4 * Real.pi * b)) *
            ∫ w : ℝ × ℝ, Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu
          let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
          let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
            Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
          let reference : (ℝ × ℝ) → ℂ := fun x =>
            (((1 / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
              ∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * Pn z))
          let error : (ℝ × ℝ) → ℂ := fun z => (damping z : ℂ) *
            ((∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) *
              Complex.I) ∂nu) - Pn z)
          IsProbabilityMeasure nu ∧ Continuous Pn ∧ Integrable Pn ∧
            IsProbabilityMeasure rho ∧ rho = volume.withDensity (fun x => ENNReal.ofReal (k x)) ∧
              Integrable k ∧ (∫ x : ℝ × ℝ, k x) = 1 ∧ Integrable error ∧
              ∀ x : ℝ × ℝ,
                Integrable (fun z => kernel x z * ((damping z : ℂ) * Pn z)) ∧
                  (n : ℝ) ^ 3 * ‖((k x : ℝ) : ℂ) - reference x‖ < epsilon := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized, hocticExp, horderSix, hweighted,
      hgaussian, hfarPoint, hfarInt, hmiddle, hwindow⟩ :=
    compact_open_domain_six_order_log_cubic_oscillatory_window mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, ?_⟩
  obtain ⟨C, hC, N0, hN0, hwin, hsmall⟩ := hwindow 0
  obtain ⟨CP, hCP, hPenv, hPtail⟩ := hgaussian
  intro epsilon hepsilon
  let c0 : ℝ := 1 / (2 * Real.pi) ^ 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  let eta : ℝ := epsilon / (3 * c0)
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨Ne, hNe, hs⟩ := hsmall eta heta
  obtain ⟨Np, hNp, hPt⟩ := hPtail 1 (by norm_num) 0 3 eta heta
  have hGsmall : ∃ Ng : ℕ, 2 ≤ Ng ∧ ∀ n : ℕ, Ng ≤ n →
      1 ≤ Real.log (n : ℝ) ∧
        (n : ℝ) ^ 3 * ((4 * Real.pi) * (n : ℝ) ^ 6 *
          Real.exp (-(Real.log (n : ℝ)) ^ 2 / 4)) < eta := by
    have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
          4 * ((4 : ℝ) + 6 + |Real.log (4 * Real.pi)|) ≤ Real.log (n : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2,
        hlog.eventually (Filter.eventually_ge_atTop 1),
        hlog.eventually (Filter.eventually_ge_atTop
          (4 * ((4 : ℝ) + 6 + |Real.log (4 * Real.pi)|)))] with n hn h1 h2
      exact ⟨hn, h1, h2⟩
    obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.1 hev
    obtain ⟨J, hJ⟩ := exists_nat_gt (1 / eta)
    refine ⟨max Nl (J + 1), (hNl Nl le_rfl).1.trans (le_max_left _ _), ?_⟩
    intro n hn
    have hl := hNl n ((le_max_left _ _).trans hn)
    have hJn : J < n := by have := (le_max_right Nl (J + 1)).trans hn; omega
    have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hJnR : (J : ℝ) < (n : ℝ) := by exact_mod_cast hJn
    have hinv : 1 / (n : ℝ) < eta := by
      apply (div_lt_iff₀ hnp).2
      have ht := (div_lt_iff₀ heta).1 (hJ.trans hJnR)
      nlinarith
    have hp := log_square_gaussian_six_power_le_rpow 4 (4 * Real.pi) (n : ℝ)
      (by norm_num) (by positivity) hnp hl.2.1 hl.2.2
    have hpow : (n : ℝ) ^ 3 * Real.rpow (n : ℝ) (-4) = 1 / (n : ℝ) := by
      change (n : ℝ) ^ 3 * (n : ℝ) ^ (-4 : ℝ) = _
      rw [show (-4 : ℝ) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num only [_root_.zpow_neg, zpow_natCast]
      field_simp <;> ring
    refine ⟨hl.2.1, ?_⟩
    exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq hpow) hinv
  obtain ⟨Ng, hNg, hG⟩ := hGsmall
  refine ⟨max Ne (max Ng Np), hN0.trans (hNe.trans (le_max_left _ _)), ?_⟩
  intro n hn p Qsample M T nu X kappa a Pn b v gamma rho k damping kernel reference error
  have hnNe : Ne ≤ n := (le_max_left _ _).trans hn
  have hnNg : Ng ≤ n := (le_max_left Ng Np).trans ((le_max_right Ne _).trans hn)
  have hnNp : Np ≤ n := (le_max_right Ng Np).trans ((le_max_right Ne _).trans hn)
  have hnN0 : N0 ≤ n := hNe.trans hnNe
  have hn2 : 2 ≤ n := hN0.trans hnN0
  have hn1 : 1 ≤ n := by omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hw := hwin n hnN0 p
  have hprob : IsProbabilityMeasure nu := hw.1
  letI : IsProbabilityMeasure nu := hprob
  have hPc : Continuous Pn := hw.2.1
  have hPint : Integrable Pn := by
    have h0 := integrable_euclidean_radius_power_gaussian 0 (1 / 2) (by norm_num)
    have h18 := integrable_euclidean_radius_power_gaussian 18 (1 / 2) (by norm_num)
    apply ((h0.add h18).const_mul CP).mono' hPc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by
      calc
        ‖Pn z‖ ≤ CP * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) := hPenv n hn1 p z.1 z.2
        _ = CP * (Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 0 *
            Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2)) +
              Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18 *
                Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2))) := by
          simp only [pow_zero, one_mul]
          rw [show -(1 / 2 : ℝ) * (z.1 ^ 2 + z.2 ^ 2) =
            -(z.1 ^ 2 + z.2 ^ 2) / 2 by ring]
          ring)
  let W : ℝ := (n : ℝ) ^ 3 * Real.log (n : ℝ)
  let window : Set (ℝ × ℝ) := {z | Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ W}
  have hb : 0 < b := by dsimp [b]; positivity
  have hW : 0 ≤ W := mul_nonneg (by positivity) (Real.log_nonneg hnR1)
  have hcentral : (n : ℝ) ^ 3 * (∫ z in window, ‖error z‖) < eta := by
    have hd := pair_gaussian_damped_weighted_error_integral_bound
      (fun z : ℝ × ℝ =>
        (∫ w : ℝ × ℝ, Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) *
          Complex.I) ∂nu) - Pn z) hw.2.2.1 window 0 b hb.le hw.2.2.2.1
    have hcomp : (∫ z in window, ‖error z‖) ≤
        ∫ z in window, ‖(∫ w : ℝ × ℝ,
          Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu) - Pn z‖ := by
      simpa only [pow_zero, one_mul] using hd.2.1
    have hsmalln := (hs n hnNe p).1
    have hsmalln' : (n : ℝ) ^ 3 * (∫ z in window, ‖(∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂nu) - Pn z‖) < eta := by
      simpa only [pow_zero, one_mul] using hsmalln
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcomp (by positivity)) hsmalln'
  have hactualTail : (n : ℝ) ^ 3 * ((2 * Real.pi / b) * Real.exp (-b * W ^ 2 / 2)) < eta := by
    have hpref : 2 * Real.pi / b = (4 * Real.pi) * (n : ℝ) ^ 6 := by
      dsimp only [b]
      field_simp
      ring
    have harg : -b * W ^ 2 / 2 = -(Real.log (n : ℝ)) ^ 2 / 4 := by
      dsimp only [b, W]
      field_simp [hnp.ne']
      ring
    rw [hpref, harg]
    exact (hG n hnNg).2
  have hpolyTail : (n : ℝ) ^ 3 * (∫ z in windowᶜ, ‖Pn z‖) < eta := by
    let tail : Set (ℝ × ℝ) := {z | Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
    have hpt := hPt n hnNp p
    have hptI : IntegrableOn (fun z => ‖Pn z‖) tail := by
      simpa only [pow_zero, one_mul] using hpt.1
    have hptSmall : (n : ℝ) ^ 3 * (∫ z in tail, ‖Pn z‖) < eta := by
      have ht0 : Real.rpow (n : ℝ) 3 * (∫ z in tail, ‖Pn z‖) < eta := by
        simpa only [pow_zero, one_mul] using hpt.2.2
      have hpow3 : Real.rpow (n : ℝ) 3 = (n : ℝ) ^ 3 := by
        change (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3
        exact Real.rpow_natCast (n : ℝ) 3
      rw [hpow3] at ht0
      exact ht0
    have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      nlinarith [Real.sq_sqrt hnp.le, Real.sqrt_nonneg (n : ℝ)]
    have hcube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hnR1)]
    have hWbig : Real.sqrt (n : ℝ) ≤ W :=
      hsqrt.trans (hcube.trans (le_mul_of_one_le_right (by positivity) (hG n hnNg).1))
    have hsub : windowᶜ ⊆ tail := by
      intro z hz
      exact hWbig.trans (le_of_lt (lt_of_not_ge hz))
    have hmono : (∫ z in windowᶜ, ‖Pn z‖) ≤ ∫ z in tail, ‖Pn z‖ :=
      setIntegral_mono_set hptI (Filter.Eventually.of_forall (fun z => norm_nonneg (Pn z)))
        (Filter.Eventually.of_forall (fun z hz => hsub hz))
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hmono (by positivity)) hptSmall
  have hg := gaussian_smoothed_pair_density_damped_reference_bound nu Pn hPc hPint b W hb hW
  refine ⟨hprob, hPc, hPint, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, ?_⟩
  intro x
  have hx := hg.2.2.2.2.2 x
  refine ⟨hx.1, ?_⟩
  have hsum : (n : ℝ) ^ 3 * (∫ z in window, ‖error z‖) +
      (n : ℝ) ^ 3 * ((2 * Real.pi / b) * Real.exp (-b * W ^ 2 / 2)) +
        (n : ℝ) ^ 3 * (∫ z in windowᶜ, ‖Pn z‖) < 3 * eta := by linarith
  have hscale : (n : ℝ) ^ 3 * ‖((k x : ℝ) : ℂ) - reference x‖ ≤
      c0 * ((n : ℝ) ^ 3 * (∫ z in window, ‖error z‖) +
        (n : ℝ) ^ 3 * ((2 * Real.pi / b) * Real.exp (-b * W ^ 2 / 2)) +
          (n : ℝ) ^ 3 * (∫ z in windowᶜ, ‖Pn z‖)) := by
    have h := mul_le_mul_of_nonneg_left hx.2 (show 0 ≤ (n : ℝ) ^ 3 by positivity)
    change (n : ℝ) ^ 3 * ‖((k x : ℝ) : ℂ) - reference x‖ ≤
      (n : ℝ) ^ 3 * (c0 * ((∫ z in window, ‖error z‖) +
        (2 * Real.pi / b) * Real.exp (-b * W ^ 2 / 2) + ∫ z in windowᶜ, ‖Pn z‖)) at h
    nlinarith [h]
  calc
    _ ≤ _ := hscale
    _ < c0 * (3 * eta) := mul_lt_mul_of_pos_left hsum hc0
    _ = epsilon := by dsimp only [eta]; field_simp <;> ring

end
end Shao.OQ3
