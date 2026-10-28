import Shao.OQ3.CompactOpenDomainSmoothedDampedDensity

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_cubic_smoothed_density_uniform_bound
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
      ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, 2 ≤ N ∧
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
          let rho : Measure (ℝ × ℝ) := (nu.prod gamma).map (fun q => q.1 + q.2)
          let k : (ℝ × ℝ) → ℝ := fun x => (1 / (4 * Real.pi * b)) *
            ∫ w : ℝ × ℝ, Real.exp (-((x.1 - w.1) ^ 2 + (x.2 - w.2) ^ 2) / (4 * b)) ∂nu
          IsProbabilityMeasure nu ∧ IsProbabilityMeasure rho ∧
            rho = volume.withDensity (fun x => ENNReal.ofReal (k x)) ∧
              Measurable k ∧ Integrable k ∧ (∫ x : ℝ × ℝ, k x) = 1 ∧
                ∀ x : ℝ × ℝ, 0 ≤ k x ∧ k x ≤ K := by
  classical
  intro tilt D s t A means Y laws Phi
  obtain ⟨lo, hi, hlo, hhi, hbounds, E, hE, hApprox⟩ :=
    compact_open_domain_cubic_smoothed_damped_density_approximation mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR hdet hWC
  obtain ⟨lo2, hi2, hlo2, hhi2, hbounds2, E2, hE2, hfrac, hL, hU, hcA, hRA,
      hpoint, hmom, htaylor, hlogTaylor, hlog, hactual, hquart, hpoly,
      hcgf, hcum, hoctic, hnormalized, hocticExp, horderSix, hweighted,
      hgaussian, hfarPoint, hfarInt, hmiddle, hwindow⟩ :=
    compact_open_domain_six_order_log_cubic_oscillatory_window mu Theta hcompact hTheta
      beta c R hbeta hbetaUpper hc hR hdet hWC
  have hEE : E2 = E := by
    funext p
    apply ContinuousLinearEquiv.ext
    funext w
    exact ((hE2 p).1 w).trans ((hE p).1 w).symm
  subst E2
  obtain ⟨CP, hCP, hPenv, hPtail⟩ := hgaussian
  let Xf : Theta → (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ := fun p z y => z.1 * y 0 + z.2 * y 1
  let kf : Theta → ℕ → (ℝ × ℝ) → ℝ := fun p j z =>
    iteratedDeriv j (ProbabilityTheory.cgf (Xf p z) (laws p)) 0
  let af : Theta → ℕ → (ℝ × ℝ) → Fin 6 → ℂ := fun p n z j =>
    (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
      (kf p (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
  let Sf : Theta → ℕ → (ℝ × ℝ) → ℂ := fun p n z =>
    ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
      ∑ sigma : Fin q.val → Fin 6,
        if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, af p n z (sigma i) else 0
  let Pf : Theta → ℕ → (ℝ × ℝ) → ℂ := fun p n z =>
    Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) * Sf p n z
  let envelope : (ℝ × ℝ) → ℝ := fun z =>
    CP * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18) *
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
  have hEnv : Integrable envelope := by
    have h0 := integrable_euclidean_radius_power_gaussian 0 (1 / 2) (by norm_num)
    have h18 := integrable_euclidean_radius_power_gaussian 18 (1 / 2) (by norm_num)
    apply ((h0.add h18).const_mul CP).congr
    exact Filter.Eventually.of_forall (fun z => by
      change CP * (Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 0 *
        Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2)) +
          Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18 *
            Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2))) = envelope z
      dsimp only [envelope]
      rw [show -(1 / 2 : ℝ) * (z.1 ^ 2 + z.2 ^ 2) =
        -(z.1 ^ 2 + z.2 ^ 2) / 2 by ring]
      ring)
  have hEnv0 (z : ℝ × ℝ) : 0 ≤ envelope z := by dsimp [envelope]; positivity
  let L : ℝ := ∫ z : ℝ × ℝ, envelope z
  have hL0 : 0 ≤ L := MeasureTheory.integral_nonneg hEnv0
  let c0 : ℝ := 1 / (2 * Real.pi) ^ 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  obtain ⟨N, hN, ha⟩ := hApprox 1 (by norm_num)
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, 1 + c0 * L, by positivity, N, hN, ?_⟩
  intro n hn p Qsample M T nu b v gamma rho k
  have hn2 : 2 ≤ n := hN.trans hn
  have hn1 : 1 ≤ n := by omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnCube : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hs : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR1) (sq_nonneg (n : ℝ))]
  have ht := ha n hn p
  have hPc : Continuous (Pf p n) := ht.2.1
  have hPi : Integrable (Pf p n) := ht.2.2.1
  letI : IsProbabilityMeasure nu := ht.1
  have hb : 0 < b := by dsimp [b]; positivity
  have hdensity := gaussian_smoothed_pair_real_density nu b hb
  refine ⟨ht.1, ht.2.2.2.1, ht.2.2.2.2.1, hdensity.2.2.1,
    ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ?_⟩
  intro x
  refine ⟨(hdensity.2.2.2.1 x).1, ?_⟩
  let damping : (ℝ × ℝ) → ℝ := fun z => Real.exp (-b * (z.1 ^ 2 + z.2 ^ 2))
  let kernel : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun x z =>
    Complex.exp (-Complex.I * ((x.1 * z.1 + x.2 * z.2 : ℝ) : ℂ))
  let reference : ℂ := (c0 : ℂ) *
    ∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * Pf p n z)
  have hx := ht.2.2.2.2.2.2.2.2 x
  have hiD : Integrable (fun z : ℝ × ℝ => kernel x z * ((damping z : ℂ) * Pf p n z)) := hx.1
  have herror : (n : ℝ) ^ 3 * ‖(k x : ℂ) - reference‖ < 1 := hx.2
  have hEnvBound (z : ℝ × ℝ) : ‖Pf p n z‖ ≤ envelope z :=
    hPenv n hn1 p z.1 z.2
  have hNormInt : (∫ z : ℝ × ℝ, ‖Pf p n z‖) ≤ L :=
    integral_mono hPi.norm hEnv hEnvBound
  have hd0 (z : ℝ × ℝ) : 0 ≤ damping z := (Real.exp_pos _).le
  have hd1 (z : ℝ × ℝ) : damping z ≤ 1 := by
    apply Real.exp_le_one_iff.2
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le)
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hkNorm (z : ℝ × ℝ) : ‖kernel x z‖ = 1 := by
    simp [kernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hDNorm (z : ℝ × ℝ) :
      ‖kernel x z * ((damping z : ℂ) * Pf p n z)‖ ≤ ‖Pf p n z‖ := by
    rw [norm_mul, hkNorm, one_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hd0 z)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hd1 z)
  have hIntBound :
      ‖∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * Pf p n z)‖ ≤ L :=
    (norm_integral_le_integral_norm _).trans
      ((integral_mono hiD.norm hPi.norm hDNorm).trans hNormInt)
  have hRef : ‖reference‖ ≤ c0 * L := by
    dsimp only [reference]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left hIntBound hc0.le
  have hErrorOne : ‖(k x : ℂ) - reference‖ < 1 :=
    (le_mul_of_one_le_left (norm_nonneg _) hnCube).trans_lt herror
  have hTri : ‖(k x : ℂ)‖ ≤ ‖(k x : ℂ) - reference‖ + ‖reference‖ := by
    have h := norm_add_le ((k x : ℂ) - reference) reference
    simpa only [sub_add_cancel] using h
  have hkAbs : ‖(k x : ℂ)‖ = k x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hdensity.2.2.2.1 x).1]
  rw [hkAbs] at hTri
  linarith

end
end Shao.OQ3
