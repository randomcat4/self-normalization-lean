import Shao.OQ3.CompactOpenDomainStandardizedLocalGaussian
import Shao.OQ3.UniformPairCharacteristicGaussianError
import Shao.OQ3.ParabolaFin2IIDCharacteristic

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Matrix Topology ContDiff BigOperators
noncomputable section

theorem iid_scaled_euclidean_radius_cubic (n : ℕ) (hn : 1 ≤ n) (u v : ℝ) :
    (n : ℝ) *
      (Real.sqrt ((u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2)) ^ 3 =
        (Real.sqrt (u ^ 2 + v ^ 2)) ^ 3 / Real.sqrt (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let S : ℝ := Real.sqrt (n : ℝ)
  let W : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  have hS : 0 < S := Real.sqrt_pos.mpr hnR
  have hsq : S ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
  have hq : (u / Real.sqrt (n : ℝ)) ^ 2 + (v / Real.sqrt (n : ℝ)) ^ 2 =
      (u ^ 2 + v ^ 2) / (n : ℝ) := by
    rw [div_pow, div_pow, show (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) from hsq]
    ring
  have hr : Real.sqrt ((u / Real.sqrt (n : ℝ)) ^ 2 +
      (v / Real.sqrt (n : ℝ)) ^ 2) = W / S := by
    rw [hq, Real.sqrt_div (by positivity)]
  rw [hr]
  calc
    (n : ℝ) * (W / S) ^ 3 = S ^ 2 * (W / S) ^ 3 := by rw [hsq]
    _ = W ^ 3 / S := by
      field_simp [ne_of_gt hS]

theorem compact_open_domain_standardized_gaussian_error_family
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
      (∀ delta H : ℝ, 0 < delta →
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
                        epsilon) ∧
      (∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
        (∀ p ∈ Theta, ∀ xi eta : ℝ,
          Real.sqrt (xi ^ 2 + eta ^ 2) ≤ delta0 →
            ‖Phi p xi eta‖ ≤ Real.exp (-(xi ^ 2 + eta ^ 2) / 4)) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : Theta, ∀ xi eta : ℝ,
          Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
            (eta / Real.sqrt (n : ℝ)) ^ 2) ≤ delta0 →
          let nu : Measure ℝ := tilt p
          let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let M : Shao.Path n → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : Shao.Path n → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Q.map T
          IsProbabilityMeasure rho ∧
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ ≤
                Real.exp (-(xi ^ 2 + eta ^ 2) / 4)) ∧
      ∃ delta B : ℝ, 0 < delta ∧ delta ≤ 1 ∧ 0 < B ∧
        ∀ n : ℕ, 2 ≤ n → ∀ p : Theta, ∀ xi eta : ℝ,
          Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
            (eta / Real.sqrt (n : ℝ)) ^ 2) ≤ delta →
          let nu : Measure ℝ := tilt p
          let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let M : Shao.Path n → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : Shao.Path n → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Q.map T
          IsProbabilityMeasure rho ∧
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((xi * w.1 + eta * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
                ((Real.exp (-(xi ^ 2 + eta ^ 2) / 2) : ℝ) : ℂ)‖ ≤
              B / Real.sqrt (n : ℝ) * (Real.sqrt (xi ^ 2 + eta ^ 2)) ^ 3 *
                Real.exp (-(xi ^ 2 + eta ^ 2) / 8) := by
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
      hfamily, hnat, hmiddle, hGaussian⟩ :=
    compact_open_domain_standardized_local_gaussian_family
      mu Theta hcompact hTheta beta c R hbeta hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hspectral, E, hE, hmom, hL, hU, hcA, hRA,
    hfamily, hnat, hmiddle, hGaussian, ?_⟩
  have hprob : ∀ p ∈ Theta, IsProbabilityMeasure (laws p) := by
    intro p hp
    exact (hfamily p hp).2.2.2.2.2.1
  have hL2 : ∀ p ∈ Theta, ∀ i : Fin 2,
      MemLp (fun y : Fin 2 → ℝ => y i) 2 (laws p) := by
    intro p hp i
    exact ((hfamily p hp).2.2.2.2.2.2.1 i).1
  have hmean : ∀ p ∈ Theta, ∀ i : Fin 2,
      (∫ y : Fin 2 → ℝ, y i ∂laws p) = 0 := by
    intro p hp i
    exact ((hfamily p hp).2.2.2.2.2.2.1 i).2
  have hcov : ∀ p ∈ Theta, ∀ i j : Fin 2, ProbabilityTheory.covariance
      (fun y : Fin 2 → ℝ => y i) (fun y : Fin 2 → ℝ => y j) (laws p) =
        if i = j then 1 else 0 := by
    intro p hp i j
    exact (hfamily p hp).2.2.2.2.2.2.2.1 i j
  have hthird : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Theta,
      Integrable (fun y : Fin 2 → ℝ =>
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3) (laws p) ∧
      (∫ y : Fin 2 → ℝ,
        (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2)) ^ 3 ∂laws p) ≤ C := by
    obtain ⟨C, hC, hm⟩ := hnat 3
    exact ⟨C, hC, fun p hp => ⟨(hm p hp).1, (hm p hp).2.2⟩⟩
  obtain ⟨delta, B, hdelta0, hdelta1, hB, herror⟩ :=
    uniform_isotropic_pair_characteristic_power_gaussian_error_bound
      Theta laws hprob hL2 hmean hcov hthird
  refine ⟨delta, B, hdelta0, hdelta1, hB, ?_⟩
  intro n hn p xi eta hsmall
  have hn1 : 1 ≤ n := by omega
  have htilt : IsProbabilityMeasure (tilt p) := by
    have hf : Integrable (fun x : ℝ =>
        Real.exp (p.val.1 * x + p.val.2 * x ^ 2)) mu :=
      interior_subset (hTheta p.property)
    exact isProbabilityMeasure_tilted hf
  letI : IsProbabilityMeasure (tilt p) := htilt
  have hpoint : ∀ x : ℝ, E p ((x, x ^ 2) - (means p 0, means p 1)) =
      ((A p *ᵥ (![x, x ^ 2] - means p)) 0,
        (A p *ᵥ (![x, x ^ 2] - means p)) 1) := (hE p).2.2.2
  have hfactor := iid_parabola_fin2_characteristic_factor
    (tilt p) n hn1 (A p) (means p) (E p) hpoint xi eta
  dsimp only at hfactor
  refine ⟨hfactor.2.1, ?_⟩
  rw [hfactor.2.2]
  have he := herror n hn p p.property xi eta hsmall
  calc
    ‖Phi p (xi / Real.sqrt (n : ℝ)) (eta / Real.sqrt (n : ℝ)) ^ n -
        ((Real.exp (-(xi ^ 2 + eta ^ 2) / 2) : ℝ) : ℂ)‖ ≤
        B * (n : ℝ) *
          (Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
            (eta / Real.sqrt (n : ℝ)) ^ 2)) ^ 3 *
              Real.exp (-(xi ^ 2 + eta ^ 2) / 8) := he
    _ = B * ((n : ℝ) *
          (Real.sqrt ((xi / Real.sqrt (n : ℝ)) ^ 2 +
            (eta / Real.sqrt (n : ℝ)) ^ 2)) ^ 3) *
              Real.exp (-(xi ^ 2 + eta ^ 2) / 8) := by ring
    _ = B * ((Real.sqrt (xi ^ 2 + eta ^ 2)) ^ 3 / Real.sqrt (n : ℝ)) *
          Real.exp (-(xi ^ 2 + eta ^ 2) / 8) := by
      rw [iid_scaled_euclidean_radius_cubic n hn1 xi eta]
    _ = B / Real.sqrt (n : ℝ) * (Real.sqrt (xi ^ 2 + eta ^ 2)) ^ 3 *
          Real.exp (-(xi ^ 2 + eta ^ 2) / 8) := by ring

end
end Shao.OQ3
