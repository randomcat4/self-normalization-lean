import Shao.OQ3.CompactOpenDomainHermiteFirstRemainder

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
noncomputable section

set_option maxHeartbeats 2000000 in
theorem compact_open_domain_hermite_local_gaussian_relative_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ)
    (hbeta : 0 ≤ beta) (hc : 0 < c) (hR : 0 ≤ R)
    (hdet : ∀ p ∈ Theta, 0 < (parabolaCovariance
      (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))).det)
    (hWC : ∀ p ∈ Theta, ∀ xi eta : ℝ, R < Real.sqrt (xi ^ 2 + eta ^ 2) →
      ‖jointCharacteristic (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) xi eta‖ ≤
        1 - c * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta))
    (K : ℝ) (hK : 0 ≤ K) :
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
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ p : Theta,
      let X : (ℝ × ℝ) → (Fin 2 → ℝ) → ℝ := fun z y => z.1 * y 0 + z.2 * y 1
      let kappa : ℕ → (ℝ × ℝ) → ℝ := fun j z =>
        iteratedDeriv j (ProbabilityTheory.cgf (X z) (laws p)) 0
      let a : (ℝ × ℝ) → Fin 6 → ℂ := fun z j =>
        (Complex.I ^ (j.val + 3) / ((j.val + 3).factorial : ℂ)) *
          (kappa (j.val + 3) z : ℂ) / (Real.sqrt (n : ℝ) : ℂ) ^ (j.val + 1)
      let Sn : (ℝ × ℝ) → ℂ := fun z =>
        ∑ q : Fin 7, (1 / (q.val.factorial : ℂ)) *
          ∑ sigma : Fin q.val → Fin 6,
            if (∑ l, ((sigma l).val + 1)) ≤ 6 then ∏ l, a z (sigma l) else 0
      let phi : (ℝ × ℝ) → ℝ := fun x =>
        (1 / (2 * Real.pi)) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
      ∀ H : MvPolynomial (Fin 2) ℝ,
        (∀ z : ℝ × ℝ, MvPolynomial.eval₂ Complex.ofRealHom
          ![Complex.I * (z.1 : ℂ), Complex.I * (z.2 : ℂ)] H = Sn z) →
        let reference : (ℝ × ℝ) → ℝ := fun x => (1 / (2 * Real.pi)) *
          (∑ d ∈ H.support, H.coeff d *
            (gaussianHermitePolynomial (d 0)).eval x.1 *
              (gaussianHermitePolynomial (d 1)).eval x.2) *
                Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)
        ∀ x : ℝ × ℝ, Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ K / Real.sqrt (n : ℝ) →
          |reference x - phi x| ≤ (C / (n : ℝ)) * phi x := by
  classical
  intro tilt D s t A means Y laws
  let b : Theta → Fin 4 → ℝ := fun p j =>
    ∫ y : Fin 2 → ℝ, y 0 ^ j.val * y 1 ^ (3 - j.val) ∂laws p
  let P1 : Theta → (ℝ × ℝ) → ℝ := fun p x => (1 / 6 : ℝ) *
    ∑ j : Fin 4, (Nat.choose 3 j.val : ℝ) * b p j *
      (gaussianHermitePolynomial j.val).eval x.1 *
        (gaussianHermitePolynomial (3 - j.val)).eval x.2
  obtain ⟨C0, hC0, hRemainder⟩ :=
    compact_open_domain_hermite_first_correction_remainder_bound
      mu Theta hcompact hTheta beta c R hbeta hc hR hdet hWC
  obtain ⟨C1, hC1, hFirst⟩ := compact_open_domain_first_hermite_correction_uniform
    mu Theta hcompact hTheta beta c R hbeta hc hR hdet hWC
  have hLocal (p : Theta) (x : ℝ × ℝ)
      (hx : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ 1) :
      |P1 p x| ≤ C1 * Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := (hFirst p).2.1 x hx
  let m : ℝ := (1 / (2 * Real.pi)) * Real.exp (-(1 : ℝ) / 2)
  have hm : 0 < m := by dsimp [m]; positivity
  let C : ℝ := C0 / m + C1 * K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (K ^ 2) (1 : ℝ))
  have hN1R : (1 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : 1 ≤ N := by exact_mod_cast hN1R.le
  refine ⟨C, hC, N, hN1, ?_⟩
  intro n hn p X kappa a Sn phi H hEval reference x hx
  have hn1 : 1 ≤ n := hN1.trans hn
  have hnp : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnp
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hK2 : K ^ 2 ≤ (n : ℝ) :=
    (lt_of_le_of_lt (le_max_left _ _) hN).le.trans hNn
  have hKn : K ≤ Real.sqrt (n : ℝ) := by
    nlinarith [Real.sq_sqrt hnp.le, Real.sqrt_nonneg (n : ℝ)]
  have hr1 : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ≤ 1 :=
    hx.trans ((div_le_one hs).mpr hKn)
  have hQ : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := by positivity
  have hQ1 : x.1 ^ 2 + x.2 ^ 2 ≤ 1 := by
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg (x.1 ^ 2 + x.2 ^ 2)) hr1
    nlinarith [Real.sq_sqrt hQ]
  have hphi : 0 ≤ phi x := by dsimp [phi]; positivity
  have hmphi : m ≤ phi x := by
    dsimp only [m, phi]
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp.mpr
      linarith
    · positivity
  have hCorrection : |P1 p x| / Real.sqrt (n : ℝ) ≤ C1 * K / (n : ℝ) :=
    sqrt_sample_scaled_local_correction_bound P1 C1 K hC1.le hLocal n hn1 hKn p x hx
  have hRem : |reference x - phi x * (1 + P1 p x / Real.sqrt (n : ℝ))| ≤
      C0 / (n : ℝ) := (hRemainder n hn1 p H hEval x).2
  have hMain : C0 / (n : ℝ) ≤ ((C0 / m) / (n : ℝ)) * phi x := by
    calc
      _ = ((C0 / m) / (n : ℝ)) * m := by field_simp [hm.ne', hnp.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmphi (by positivity)
  dsimp only [C]
  calc
    _ = |(reference x - phi x * (1 + P1 p x / Real.sqrt (n : ℝ))) +
        phi x * (P1 p x / Real.sqrt (n : ℝ))| := by congr 1 <;> ring
    _ ≤ |reference x - phi x * (1 + P1 p x / Real.sqrt (n : ℝ))| +
        |phi x * (P1 p x / Real.sqrt (n : ℝ))| := abs_add _ _
    _ ≤ C0 / (n : ℝ) + phi x * (C1 * K / (n : ℝ)) := by
      apply add_le_add hRem
      rw [abs_mul, abs_of_nonneg hphi, abs_div, abs_of_nonneg hs.le]
      exact mul_le_mul_of_nonneg_left hCorrection hphi
    _ ≤ ((C0 / m) / (n : ℝ)) * phi x + phi x * (C1 * K / (n : ℝ)) :=
      add_le_add_right hMain _
    _ = ((C0 / m + C1 * K) / (n : ℝ)) * phi x := by ring
    _ ≤ ((C0 / m + C1 * K + 1) / (n : ℝ)) * phi x :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith) hnp.le) hphi

end
end Shao.OQ3
