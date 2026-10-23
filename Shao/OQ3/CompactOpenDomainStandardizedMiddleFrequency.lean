import Shao.OQ3.CompactOpenDomainWhitenedAnnulusGap
import Shao.OQ3.NormalizedIIDPairCharacteristic
import Shao.OQ3.NormalizedIIDPairSuperpolynomialDecay

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Matrix Topology ContDiff BigOperators
noncomputable section

theorem compact_open_domain_standardized_middle_frequency_family
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (Theta : Set (ℝ × ℝ))
    (hcompact : IsCompact Theta)
    (hTheta : Theta ⊆ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))))
    (beta c R : ℝ)
    (hbeta : 0 ≤ beta)
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
      (∀ delta : ℝ, 0 < delta → ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ =>
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta)) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ∧
        (∫ y : Fin 2 → ℝ,
          Real.rpow (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) (8 + delta) ∂laws p) ≤ C) ∧
    let L : ℝ := 1 / Real.sqrt hi
    let U : ℝ := 1 / Real.sqrt lo
    let cA : ℝ := c * Real.rpow U (-beta)
    let RA : ℝ := R / L
    0 < L ∧ 0 < U ∧ 0 < cA ∧ 0 ≤ RA ∧
      (∀ p ∈ Theta,
        0 < s p ∧ 0 < t p ∧ (A p)ᵀ = A p ∧ A p * D p * A p = 1 ∧
        (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 →
          0 < xi * (A p *ᵥ ![xi, eta]) 0 + eta * (A p *ᵥ ![xi, eta]) 1) ∧
        IsProbabilityMeasure (laws p) ∧
        (∀ i : Fin 2, MemLp (fun y : Fin 2 → ℝ => y i) 2 (laws p) ∧
          (∫ y : Fin 2 → ℝ, y i ∂laws p) = 0) ∧
        (∀ i j : Fin 2, ProbabilityTheory.covariance
          (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
            if i = j then 1 else 0) ∧
        (∀ xi eta : ℝ,
          L * Real.sqrt (xi ^ 2 + eta ^ 2) ≤
            Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
              (xi * A p 0 1 + eta * A p 1 1) ^ 2) ∧
          Real.sqrt ((xi * A p 0 0 + eta * A p 1 0) ^ 2 +
              (xi * A p 0 1 + eta * A p 1 1) ^ 2) ≤
            U * Real.sqrt (xi ^ 2 + eta ^ 2)) ∧
        ∀ xi eta : ℝ, RA < Real.sqrt (xi ^ 2 + eta ^ 2) →
          ‖Phi p xi eta‖ ≤ 1 - cA * Real.rpow (Real.sqrt (xi ^ 2 + eta ^ 2)) (-beta)) ∧
      (∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
        Integrable (fun y : Fin 2 → ℝ => (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k) (laws p) ∧
        0 ≤ (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ∧
        (∫ y : Fin 2 → ℝ, (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ k ∂laws p) ≤ C) ∧
      ∀ delta H : ℝ, 0 < delta →
        ∃ gamma : ℝ, 0 < gamma ∧ gamma < 1 ∧
          (∀ p ∈ Theta, ∀ xi eta : ℝ,
            delta ≤ Real.sqrt (xi ^ 2 + eta ^ 2) →
              Real.sqrt (xi ^ 2 + eta ^ 2) ≤ H → ‖Phi p xi eta‖ ≤ gamma) ∧
          ∀ q epsilon : ℝ, 0 < epsilon →
            ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : Theta,
              ∀ xi eta : ℝ,
                delta ≤ Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
                  (eta / Real.sqrt (n : ℝ)) ^ 2) →
                Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
                  (eta / Real.sqrt (n : ℝ)) ^ 2) ≤ H →
                let nu : Measure ℝ := tilt p
                let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
                let M : Shao.Path n → (ℝ × ℝ) := fun z =>
                  ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
                let T : Shao.Path n → (ℝ × ℝ) := fun z =>
                  Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
                let rho : Measure (ℝ × ℝ) := Q.map T
                IsProbabilityMeasure rho ∧
                  Real.rpow (n : ℝ) q *
                    ‖(∫ w : ℝ × ℝ,
                      Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ <
                        epsilon := by
  dsimp only
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
  obtain ⟨lo, hi, hlo, hhi, hspectral, E, hE, hmom, hL, hU, hcA, hRA,
      hfamily, hnat, hgapFamily⟩ :=
    compact_open_domain_whitened_annulus_gap_family
      mu Theta hcompact hTheta beta c R hbeta hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hspectral, E, hE, hmom, hL, hU, hcA, hRA,
    hfamily, hnat, ?_⟩
  intro delta H hdelta
  obtain ⟨gamma, hgamma0, hgamma1, hgap⟩ := hgapFamily delta H hdelta
  refine ⟨gamma, hgamma0, hgamma1, hgap, ?_⟩
  intro q epsilon hepsilon
  have hscalar : ∀ᶠ n : ℕ in Filter.atTop,
      Real.rpow (n : ℝ) q * Real.exp (-(1 - gamma) * (n : ℝ)) < epsilon := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      eventually_real_power_mul_stretched_exponential_lt
        1 (1 - gamma) q epsilon (by norm_num) (sub_pos.mpr hgamma1) hepsilon
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hscalar
  refine ⟨max N0 1, le_max_right _ _, ?_⟩
  intro n hN p xi eta hlow hhigh
  have hn : 1 ≤ n := (le_max_right N0 1).trans hN
  have htilt : IsProbabilityMeasure (tilt p) := by
    have hf : Integrable (fun x : ℝ =>
        Real.exp (p.val.1 * x + p.val.2 * x ^ 2)) mu :=
      interior_subset (hTheta p.property)
    exact isProbabilityMeasure_tilted hf
  letI : IsProbabilityMeasure (tilt p) := htilt
  refine ⟨(iid_parabola_affine_standardized_law (tilt p) n hn
    (means p 0, means p 1) (E p)).2.1, ?_⟩
  have hY : Continuous (Y p) := by
    apply continuous_pi
    intro i
    change Continuous (fun x : ℝ =>
      ∑ j : Fin 2, A p i j * (![x, x ^ 2] - means p) j)
    apply continuous_finsetSum
    intro j hj
    fin_cases j <;> simp <;> fun_prop
  have hPhi : ∀ u v : ℝ,
      (∫ x : ℝ,
        Complex.exp (((u * (E p ((x, x ^ 2) - (means p 0, means p 1))).1 +
          v * (E p ((x, x ^ 2) - (means p 0, means p 1))).2 : ℝ) : ℂ) * Complex.I)
            ∂tilt p) = Phi p u v := by
    intro u v
    have hmap := MeasureTheory.integral_map (μ := tilt p) hY.measurable.aemeasurable
      (show Continuous (fun y : Fin 2 → ℝ =>
        Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I)) by
          fun_prop).aestronglyMeasurable
    change _ = ∫ y : Fin 2 → ℝ,
      Complex.exp (((u * y 0 + v * y 1 : ℝ) : ℂ) * Complex.I) ∂(tilt p).map (Y p)
    rw [hmap]
    apply integral_congr_ae
    filter_upwards [] with x
    have hx := (hE p).2.2.2 x
    change E p ((x, x ^ 2) - (means p 0, means p 1)) = (Y p x 0, Y p x 1) at hx
    rw [hx]
  have hfactor := iid_parabola_standardized_characteristic_factor
    (tilt p) n hn (means p 0, means p 1) (E p) xi eta
  dsimp only at hfactor
  rw [hPhi] at hfactor
  have hnorm :
      ‖(∫ w : ℝ × ℝ,
        Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I)
          ∂(Measure.pi (fun _ : Fin n => tilt p)).map
            (fun z : Shao.Path n => Real.sqrt (n : ℝ) • E p
              (((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ)) -
                (means p 0, means p 1))))‖ ≤ gamma ^ n := by
    rw [hfactor, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hgap p p.property (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ))
        hlow hhigh) n
  have hbase : gamma ≤ Real.exp (-(1 - gamma)) := by
    have h := Real.add_one_le_exp (-(1 - gamma))
    linarith
  have hpower : gamma ^ n ≤ Real.exp (-(1 - gamma) * (n : ℝ)) := by
    calc
      gamma ^ n ≤ Real.exp (-(1 - gamma)) ^ n :=
        pow_le_pow_left₀ hgamma0.le hbase n
      _ = Real.exp (-(1 - gamma) * (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  exact (mul_le_mul_of_nonneg_left (hnorm.trans hpower)
    (Real.rpow_nonneg (Nat.cast_nonneg n) q)).trans_lt
      (hN0 n ((le_max_left N0 1).trans hN))

end
end Shao.OQ3
