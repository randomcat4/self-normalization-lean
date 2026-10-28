import Shao.OQ3.CompactOpenDomainSmoothedDampedDensity
import Shao.OQ3.GaussianReferenceDampingError
import Shao.OQ3.DirectionalCGFSixOrderHermiteIntegral

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators RealInnerProductSpace NNReal Topology
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_cubic_smoothed_hermite_density_approximation
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
          let Sn : (ℝ × ℝ) → ℂ := fun z =>
            ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
              ∑ sigma : Fin q.val → Fin 6,
                if (∑ i, ((sigma i).val + 1)) ≤ 6 then ∏ i, a z (sigma i) else 0
          let Pn : (ℝ × ℝ) → ℂ := fun z =>
            Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) * Sn z
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
          IsProbabilityMeasure nu ∧ Continuous Pn ∧ Integrable Pn ∧
            IsProbabilityMeasure rho ∧ rho = volume.withDensity (fun x => ENNReal.ofReal (k x)) ∧
              Integrable k ∧ (∫ x : ℝ × ℝ, k x) = 1 ∧
              ∃ H : MvPolynomial (Fin 2) ℝ,
                (∀ z : ℝ × ℝ, MvPolynomial.eval₂ Complex.ofRealHom
                  ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] H = Sn z) ∧
                let reference : (ℝ × ℝ) → ℝ := fun x => (1 / (2 * Real.pi)) *
                  (∑ d ∈ H.support, H.coeff d *
                    (gaussianHermitePolynomial (d 0)).eval x.1 *
                      (gaussianHermitePolynomial (d 1)).eval x.2) *
                        Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
                ∀ x : ℝ × ℝ,
                  Integrable (fun z => kernel x z * Pn z) ∧
                    (n : ℝ) ^ 3 * |k x - reference x| < epsilon := by
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
    intro w
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
    CP * (Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 20) *
      Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
  have hEnv : Integrable envelope := by
    have h2 := integrable_euclidean_radius_power_gaussian 2 (1 / 2) (by norm_num)
    have h20 := integrable_euclidean_radius_power_gaussian 20 (1 / 2) (by norm_num)
    apply ((h2.add h20).const_mul CP).congr
    exact Filter.Eventually.of_forall (fun z => by
      change CP * (Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 *
        Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2)) +
          Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 20 *
            Real.exp (-(1 / 2) * (z.1 ^ 2 + z.2 ^ 2))) = envelope z
      dsimp only [envelope]
      rw [show -(1 / 2 : ℝ) * (z.1 ^ 2 + z.2 ^ 2) =
        -(z.1 ^ 2 + z.2 ^ 2) / 2 by ring]
      ring)
  have hEnv0 (z : ℝ × ℝ) : 0 ≤ envelope z := by dsimp [envelope]; positivity
  let K : ℝ := (∫ z : ℝ × ℝ, envelope z) + 1
  have hK : 0 < K := by
    have h := integral_nonneg hEnv0
    dsimp only [K]
    linarith
  have hQpoint (n : ℕ) (hn : 1 ≤ n) (p : Theta) (z : ℝ × ℝ) :
      (z.1 ^ 2 + z.2 ^ 2) * ‖Pf p n z‖ ≤ envelope z := by
    have hq : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_left (hPenv n hn p z.1 z.2) hq
    have heq : (z.1 ^ 2 + z.2 ^ 2) * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18) =
        Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 20 := by
      calc
        _ = Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 2 *
            (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18) := by rw [Real.sq_sqrt hq]
        _ = _ := by ring
    calc
      _ ≤ (z.1 ^ 2 + z.2 ^ 2) * (CP * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)) := hh
      _ = CP * ((z.1 ^ 2 + z.2 ^ 2) * (1 + Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ^ 18)) *
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) := by ring
      _ = envelope z := by rw [heq]; rfl
  have hQbound (n : ℕ) (hn : 1 ≤ n) (p : Theta) (hPc : Continuous (Pf p n)) :
      Integrable (fun z : ℝ × ℝ => (z.1 ^ 2 + z.2 ^ 2) * ‖Pf p n z‖) ∧
        (∫ z : ℝ × ℝ, (z.1 ^ 2 + z.2 ^ 2) * ‖Pf p n z‖) ≤ K := by
    have hc : Continuous (fun z : ℝ × ℝ => (z.1 ^ 2 + z.2 ^ 2) * ‖Pf p n z‖) := by
      fun_prop
    have hiQ : Integrable (fun z : ℝ × ℝ => (z.1 ^ 2 + z.2 ^ 2) * ‖Pf p n z‖) := by
      apply hEnv.mono' hc.aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun z => by
        change ‖(z.1 ^ 2 + z.2 ^ 2) * ‖Pf p n z‖‖ ≤ envelope z
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hQpoint n hn p z)
    refine ⟨hiQ, ?_⟩
    exact (integral_mono hiQ hEnv (hQpoint n hn p)).trans
      (le_add_of_nonneg_right (by norm_num))
  have hprobLaw (p : Theta) : IsProbabilityMeasure (laws p) :=
    (hpoint p p.property).2.2.2.2.2.1
  have h0 (p : Theta) (u v : ℝ) :
      0 ∈ interior (ProbabilityTheory.integrableExpSet
        (fun y : Fin 2 → ℝ => u * y 0 + v * y 1) (laws p)) :=
    (hcgf p p.property u v).1
  have hM (p : Theta) (j : ℕ) : Integrable (fun y : Fin 2 → ℝ =>
      Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ j) (laws p) := by
    obtain ⟨Cj, hCj, hBj⟩ := hmom j
    exact (hBj p p.property).1
  refine ⟨lo, hi, hlo, hhi, hbounds, E, hE, ?_⟩
  intro epsilon hepsilon
  obtain ⟨N0, hN0, ha⟩ := hApprox (epsilon / 2) (half_pos hepsilon)
  let c0 : ℝ := 1 / (2 * Real.pi) ^ 2
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  obtain ⟨J, hJ⟩ := exists_nat_gt (c0 * K / epsilon)
  refine ⟨max N0 (J + 1), hN0.trans (le_max_left _ _), ?_⟩
  intro n hn p Qsample M T nu X kappa a Sn Pn b v gamma rho k damping kernel
  have hnN0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := hN0.trans hnN0
  have hn1 : 1 ≤ n := by omega
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hcube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hnR1)]
  have hJn : J < n := by have := (le_max_right N0 (J + 1)).trans hn; omega
  have hJnR : (J : ℝ) < (n : ℝ) := by exact_mod_cast hJn
  have hKsmall : c0 * K / (2 * (n : ℝ) ^ 3) < epsilon / 2 := by
    apply (div_lt_iff₀ (show 0 < 2 * (n : ℝ) ^ 3 by positivity)).2
    have ht := (div_lt_iff₀ hepsilon).1 (hJ.trans hJnR)
    nlinarith [mul_le_mul_of_nonneg_left hcube hepsilon.le]
  have ht := ha n hnN0 p
  have hPc : Continuous Pn := ht.2.1
  have hPi : Integrable Pn := ht.2.2.1
  have hQ := hQbound n hn1 p hPc
  have hb : 0 < b := by dsimp [b]; positivity
  letI : IsProbabilityMeasure (laws p) := hprobLaw p
  obtain ⟨H, hEval, hHermite⟩ :=
    pair_directional_cgf_six_order_gaussian_hermite_integral (laws p) (h0 p) (hM p) n hn1
  have heval : ∀ z : ℝ × ℝ, MvPolynomial.eval₂ Complex.ofRealHom
      ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] H = Sn z := hEval
  refine ⟨ht.1, hPc, hPi, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1,
    ht.2.2.2.2.2.2.1, H, heval, ?_⟩
  intro reference x
  have hiH : Integrable (fun z => kernel x z * Pn z) ∧
      (∫ z : ℝ × ℝ, kernel x z * Pn z) =
        ((2 * Real.pi * (∑ d ∈ H.support, H.coeff d *
          (gaussianHermitePolynomial (d 0)).eval x.1 *
            (gaussianHermitePolynomial (d 1)).eval x.2) *
              Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2) : ℝ) : ℂ) := by
    change Integrable (fun z : ℝ × ℝ => kernel x z *
      (Complex.exp (-((z.1 ^ 2 + z.2 ^ 2 : ℝ) : ℂ) / 2) * Sn z)) ∧ _
    simpa only [kernel, mul_comm, mul_left_comm, mul_assoc] using hHermite x
  have hInv : (((c0 : ℝ) : ℂ) * (∫ z : ℝ × ℝ, kernel x z * Pn z)) =
      ((reference x : ℝ) : ℂ) := by
    rw [hiH.2]
    dsimp only [reference, c0]
    push_cast
    field_simp [Real.pi_ne_zero] <;> ring
  let dampedReference : ℂ := (((c0 : ℝ) : ℂ) *
    ∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * Pn z))
  have hD := pair_gaussian_reference_damping_error_bound Pn hPc hPi hQ.1 b hb.le x
  have hRefBound : ‖dampedReference - ((reference x : ℝ) : ℂ)‖ ≤ c0 * (b * K) := by
    calc
      _ = ‖(((c0 : ℝ) : ℂ) * ((∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * Pn z)) -
          (∫ z : ℝ × ℝ, kernel x z * Pn z)))‖ := by
        rw [← hInv]
        dsimp only [dampedReference]
        congr 1
        ring
      _ = c0 * ‖(∫ z : ℝ × ℝ, kernel x z * ((damping z : ℂ) * Pn z)) -
          (∫ z : ℝ × ℝ, kernel x z * Pn z)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0.le]
      _ ≤ c0 * (b * K) := mul_le_mul_of_nonneg_left
        (hD.2.2.trans (mul_le_mul_of_nonneg_left hQ.2 hb.le)) hc0.le
  have hRefSmall : (n : ℝ) ^ 3 * ‖dampedReference - ((reference x : ℝ) : ℂ)‖ < epsilon / 2 := by
    calc
      _ ≤ (n : ℝ) ^ 3 * (c0 * (b * K)) :=
        mul_le_mul_of_nonneg_left hRefBound (by positivity)
      _ = c0 * K / (2 * (n : ℝ) ^ 3) := by
        dsimp only [b]
        field_simp [hnp.ne'] <;> ring
      _ < _ := hKsmall
  have hOld : (n : ℝ) ^ 3 * ‖((k x : ℝ) : ℂ) - dampedReference‖ < epsilon / 2 :=
    (ht.2.2.2.2.2.2.2.2 x).2
  have htriangle : ‖((k x : ℝ) : ℂ) - ((reference x : ℝ) : ℂ)‖ ≤
      ‖((k x : ℝ) : ℂ) - dampedReference‖ + ‖dampedReference - ((reference x : ℝ) : ℂ)‖ := by
    calc
      _ = ‖(((k x : ℝ) : ℂ) - dampedReference) +
          (dampedReference - ((reference x : ℝ) : ℂ))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hfinal : (n : ℝ) ^ 3 * ‖((k x : ℝ) : ℂ) - ((reference x : ℝ) : ℂ)‖ < epsilon := by
    have htri := mul_le_mul_of_nonneg_left htriangle (show 0 ≤ (n : ℝ) ^ 3 by positivity)
    nlinarith [htri, hOld, hRefSmall]
  refine ⟨hiH.1, ?_⟩
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hfinal

end
end Shao.OQ3
