import Shao.OQ3.CompactOpenDomainWeightedMiddleFrequency
import Shao.OQ3.EuclideanGaussianWeightedTail

namespace Shao.OQ3
open MeasureTheory ProbabilityTheory
open scoped Matrix Topology ContDiff BigOperators
noncomputable section

theorem compact_open_domain_standardized_weighted_gaussian_window_family
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
      (∃ delta B : ℝ, 0 < delta ∧ delta ≤ 1 ∧ 0 < B ∧
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
                Real.exp (-(xi ^ 2 + eta ^ 2) / 8)) ∧
      (∃ deltaInt : ℝ, 0 < deltaInt ∧ deltaInt ≤ 1 ∧ ∀ k : ℕ,
        let envelope : (ℝ × ℝ) → ℝ := fun z =>
          (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ (k + 3) *
            Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 8)
        Integrable envelope ∧ ∃ C : ℝ, 0 < C ∧
          ∀ n : ℕ, 2 ≤ n → ∀ p : Theta,
            let nu : Measure ℝ := tilt p
            let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
            let M : Shao.Path n → (ℝ × ℝ) := fun z =>
              ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
            let T : Shao.Path n → (ℝ × ℝ) := fun z =>
              Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
            let rho : Measure (ℝ × ℝ) := Q.map T
            let small : Set (ℝ × ℝ) := {z |
              Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
                (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ deltaInt}
            let error : (ℝ × ℝ) → ℝ := fun z =>
              ‖(∫ w : ℝ × ℝ,
                Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
                  ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)‖
            let weight : (ℝ × ℝ) → ℝ := fun z => (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k
            IsProbabilityMeasure rho ∧ IntegrableOn (fun z => weight z * error z) small ∧
              0 ≤ (∫ z in small, weight z * error z) ∧
              (∫ z in small, weight z * error z) ≤ C / Real.sqrt (n : ℝ)) ∧
      (∃ Hfar : ℝ, 0 ≤ Hfar ∧ ∀ k : ℕ, ∀ q epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : Theta,
          let nu : Measure ℝ := tilt p
          let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let M : Shao.Path n → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : Shao.Path n → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Q.map T
          let far : Set (ℝ × ℝ) := {z |
            Real.sqrt (n : ℝ) * Hfar < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ∧
              Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3}
          let f : (ℝ × ℝ) → ℝ := fun z =>
            (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
              ‖(∫ w : ℝ × ℝ,
                Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
          IsProbabilityMeasure rho ∧ IntegrableOn f far ∧
            0 ≤ (∫ z in far, f z) ∧
            Real.rpow (n : ℝ) q * (∫ z in far, f z) < epsilon) ∧
      (∀ delta H : ℝ, 0 < delta → ∀ k : ℕ, ∀ q epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ p : Theta,
          let nu : Measure ℝ := tilt p
          let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let M : Shao.Path n → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : Shao.Path n → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Q.map T
          let middle : Set (ℝ × ℝ) := {z |
            delta ≤ Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
              (z.2 / Real.sqrt (n : ℝ)) ^ 2) ∧
            Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
              (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ H}
          let f : (ℝ × ℝ) → ℝ := fun z =>
            (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k *
              ‖(∫ w : ℝ × ℝ,
                Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
          IsProbabilityMeasure rho ∧ IntegrableOn f middle ∧
            0 ≤ (∫ z in middle, f z) ∧
            Real.rpow (n : ℝ) q * (∫ z in middle, f z) < epsilon) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ p : Theta,
          let nu : Measure ℝ := tilt p
          let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let M : Shao.Path n → (ℝ × ℝ) := fun z =>
            ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
          let T : Shao.Path n → (ℝ × ℝ) := fun z =>
            Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
          let rho : Measure (ℝ × ℝ) := Q.map T
          let window : Set (ℝ × ℝ) := {z |
            Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3}
          let error : (ℝ × ℝ) → ℝ := fun z =>
            ‖(∫ w : ℝ × ℝ,
              Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
                ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)‖
          let weight : (ℝ × ℝ) → ℝ := fun z => (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k
          IsProbabilityMeasure rho ∧ IntegrableOn (fun z => weight z * error z) window ∧
            0 ≤ (∫ z in window, weight z * error z) ∧
            (∫ z in window, weight z * error z) ≤ C / Real.sqrt (n : ℝ) := by
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
  obtain ⟨lo, hi, hlo, hhi, hspec, E, hE, hmoment, hL, hU, hcA, hRA,
      hbase, hnat, hmiddle, hlocal, hpoint, hlocalInt, hfarInt, hmiddleInt⟩ :=
    compact_open_domain_standardized_weighted_middle_frequency_family
      mu Theta hcompact hTheta beta c R hbeta hbetaUpper hc hR hdet hWC
  refine ⟨lo, hi, hlo, hhi, hspec, E, hE, hmoment, hL, hU, hcA, hRA,
    hbase, hnat, hmiddle, hlocal, hpoint, hlocalInt, hfarInt, hmiddleInt, ?_⟩
  obtain ⟨delta, hdelta, hdelta1, hsmallInt⟩ := hlocalInt
  obtain ⟨H, hH, hfarFn⟩ := hfarInt
  intro k
  obtain ⟨henvelope, C, hC, hsmallFn⟩ := hsmallInt k
  obtain ⟨NM, hNM, hmiddleFn⟩ :=
    hmiddleInt delta H hdelta k 1 1 (by norm_num)
  obtain ⟨NF, hNF, hfar⟩ := hfarFn k 1 1 (by norm_num)
  obtain ⟨NG, hNG, hgaussFn⟩ :=
    eventually_scaled_euclidean_gaussian_weighted_tail k delta 1 1 hdelta (by norm_num)
  let N : ℕ := max 2 (max NM (max NF NG))
  refine ⟨C + 3, by linarith, N, le_max_left _ _, ?_⟩
  intro n hn p
  have hn2 : 2 ≤ n := (le_max_left 2 _).trans hn
  have hn1 : 1 ≤ n := (by omega : 1 ≤ 2).trans hn2
  have hnM : NM ≤ n := (le_max_left NM _).trans ((le_max_right 2 _).trans hn)
  have hnF : NF ≤ n :=
    (le_max_left NF NG).trans ((le_max_right NM _).trans ((le_max_right 2 _).trans hn))
  have hnG : NG ≤ n :=
    (le_max_right NF NG).trans ((le_max_right NM _).trans ((le_max_right 2 _).trans hn))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsle : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    nlinarith [Real.sq_sqrt hnR.le, sq_nonneg (Real.sqrt (n : ℝ) - 1)]
  let nu : Measure ℝ := tilt p
  let Q : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
  let M : Shao.Path n → (ℝ × ℝ) := fun z =>
    ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
  let T : Shao.Path n → (ℝ × ℝ) := fun z =>
    Real.sqrt (n : ℝ) • E p (M z - (means p 0, means p 1))
  let rho : Measure (ℝ × ℝ) := Q.map T
  let window : Set (ℝ × ℝ) := {z |
    Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3}
  let error : (ℝ × ℝ) → ℝ := fun z =>
    ‖(∫ w : ℝ × ℝ,
      Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho) -
        ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)‖
  let weight : (ℝ × ℝ) → ℝ := fun z => (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ k
  let fs : (ℝ × ℝ) → ℝ := fun z => weight z * error z
  let fc : (ℝ × ℝ) → ℝ := fun z =>
    weight z * ‖(∫ w : ℝ × ℝ,
      Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖
  let fg : (ℝ × ℝ) → ℝ := fun z =>
    weight z * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)
  let small : Set (ℝ × ℝ) := {z |
    Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
      (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ delta}
  let mid : Set (ℝ × ℝ) := {z |
    delta ≤ Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
      (z.2 / Real.sqrt (n : ℝ)) ^ 2) ∧
    Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
      (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ H}
  let far : Set (ℝ × ℝ) := {z |
    Real.sqrt (n : ℝ) * H < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ∧
      Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ (n : ℝ) ^ 3}
  let gtail : Set (ℝ × ℝ) := {z |
    delta * Real.sqrt (n : ℝ) ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2)}
  have hsmall := hsmallFn n hn2 p
  have hmid := hmiddleFn n hnM p
  have hfarBound := hfar n hnF p
  have hgauss := hgaussFn n hnG
  dsimp only at hsmall hmid hfarBound hgauss
  have hrho : IsProbabilityMeasure rho := hsmall.1
  letI : IsProbabilityMeasure rho := hrho
  have hrcont : Continuous (fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) := by
    fun_prop
  have hscaledcont : Continuous (fun z : ℝ × ℝ =>
      Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
        (z.2 / Real.sqrt (n : ℝ)) ^ 2)) := by fun_prop
  have hWin : MeasurableSet window := (isClosed_le hrcont continuous_const).measurableSet
  have hS : MeasurableSet small := (isClosed_le hscaledcont continuous_const).measurableSet
  have hM : MeasurableSet mid :=
    (isClosed_le continuous_const hscaledcont).measurableSet.inter
      (isClosed_le hscaledcont continuous_const).measurableSet
  have hF : MeasurableSet far :=
    (isOpen_lt continuous_const hrcont).measurableSet.inter hWin
  have hG : MeasurableSet gtail := (isClosed_le continuous_const hrcont).measurableSet
  have hfs0 : ∀ z, 0 ≤ fs z := fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hfc0 : ∀ z, 0 ≤ fc z := fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (norm_nonneg _)
  have hfg0 : ∀ z, 0 ≤ fg z := fun z =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) k) (Real.exp_pos _).le
  have hInd0 (A : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ)
      (hf : ∀ z, 0 ≤ f z) (z : ℝ × ℝ) : 0 ≤ A.indicator f z := by
    by_cases hz : z ∈ A
    · simpa only [Set.indicator_of_mem hz] using hf z
    · simp only [Set.indicator_of_notMem hz, le_refl]
  have hIS : Integrable (small.indicator fs) := (integrable_indicator_iff hS).2 hsmall.2.1
  have hIM : Integrable (mid.indicator fc) := (integrable_indicator_iff hM).2 hmid.2.1
  have hIF : Integrable (far.indicator fc) := (integrable_indicator_iff hF).2 hfarBound.2.1
  have hIG : Integrable (gtail.indicator fg) := (integrable_indicator_iff hG).2 hgauss.1
  let g : (ℝ × ℝ) → ℝ :=
    small.indicator fs + mid.indicator fc + far.indicator fc + gtail.indicator fg
  have hg : Integrable g := ((hIS.add hIM).add hIF).add hIG
  have hscaled (z : ℝ × ℝ) :
      Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
        (z.2 / Real.sqrt (n : ℝ)) ^ 2) =
        Real.sqrt (z.1 ^ 2 + z.2 ^ 2) / Real.sqrt (n : ℝ) := by
    rw [div_pow, div_pow, ← add_div, Real.sq_sqrt hnR.le]
    exact Real.sqrt_div (add_nonneg (sq_nonneg _) (sq_nonneg _)) _
  have htriangle (z : ℝ × ℝ) : fs z ≤ fc z + fg z := by
    have ht := norm_sub_le
      (∫ w : ℝ × ℝ,
        Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)
      ((Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) : ℝ) : ℂ)
    have he : error z ≤
        ‖(∫ w : ℝ × ℝ,
          Complex.exp (((z.1 * w.1 + z.2 * w.2 : ℝ) : ℂ) * Complex.I) ∂rho)‖ +
          Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2) := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_pos _).le] using ht
    have hm := mul_le_mul_of_nonneg_left he
      (pow_nonneg (Real.sqrt_nonneg (z.1 ^ 2 + z.2 ^ 2)) k)
    simpa only [mul_add] using hm
  have hdom : ∀ z, window.indicator fs z ≤ g z := by
    intro z
    have h0S := hInd0 small fs hfs0 z
    have h0M := hInd0 mid fc hfc0 z
    have h0F := hInd0 far fc hfc0 z
    have h0G := hInd0 gtail fg hfg0 z
    by_cases hw : z ∈ window
    · by_cases hzS : z ∈ small
      · dsimp [g]
        rw [Set.indicator_of_mem hw, Set.indicator_of_mem hzS]
        linarith
      · have hgt : z ∈ gtail := by
          have hd : delta ≤ Real.sqrt (z.1 ^ 2 + z.2 ^ 2) / Real.sqrt (n : ℝ) := by
            rw [← hscaled z]
            exact (lt_of_not_ge hzS).le
          exact (le_div_iff₀ hs).1 hd
        have hcover : fc z ≤ mid.indicator fc z + far.indicator fc z := by
          by_cases hu : Real.sqrt ((z.1 / Real.sqrt (n : ℝ)) ^ 2 +
              (z.2 / Real.sqrt (n : ℝ)) ^ 2) ≤ H
          · have hm : z ∈ mid := ⟨(lt_of_not_ge hzS).le, hu⟩
            rw [Set.indicator_of_mem hm]
            exact le_add_of_nonneg_right h0F
          · have hfm : z ∈ far := by
              refine ⟨?_, hw⟩
              have hu' : H < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) / Real.sqrt (n : ℝ) := by
                rw [← hscaled z]
                exact lt_of_not_ge hu
              have hp := (lt_div_iff₀ hs).1 hu'
              nlinarith
            rw [Set.indicator_of_mem hfm]
            exact le_add_of_nonneg_left h0M
        dsimp [g]
        rw [Set.indicator_of_mem hw, Set.indicator_of_notMem hzS,
          Set.indicator_of_mem hgt]
        linarith [htriangle z]
    · dsimp [g]
      rw [Set.indicator_of_notMem hw]
      linarith
  have hCFcont := continuous_pair_characteristic rho
  have hfscont : Continuous fs := by
    dsimp [fs, weight, error]
    fun_prop
  have hWI : Integrable (window.indicator fs) :=
    hg.mono' (hfscont.aestronglyMeasurable.indicator hWin)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hInd0 window fs hfs0 z)]
        exact hdom z))
  have hwindowI : IntegrableOn fs window := (integrable_indicator_iff hWin).1 hWI
  have hrpow : Real.rpow (n : ℝ) (1 : ℝ) = (n : ℝ) := by
    rw [Real.rpow_eq_pow, Real.rpow_one]
  have hunit (J : ℝ) (hJ0 : 0 ≤ J) (hJ : (n : ℝ) * J < 1) :
      J ≤ 1 / Real.sqrt (n : ℝ) := by
    apply (le_div_iff₀ hs).2
    calc
      J * Real.sqrt (n : ℝ) ≤ J * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsle hJ0
      _ ≤ 1 := by nlinarith
  have hmidRate : (∫ z in mid, fc z) ≤ 1 / Real.sqrt (n : ℝ) :=
    hunit _ hmid.2.2.1 (by simpa only [hrpow] using hmid.2.2.2)
  have hfarRate : (∫ z in far, fc z) ≤ 1 / Real.sqrt (n : ℝ) :=
    hunit _ hfarBound.2.2.1 (by simpa only [hrpow] using hfarBound.2.2.2)
  have hgaussRate : (∫ z in gtail, fg z) ≤ 1 / Real.sqrt (n : ℝ) :=
    hunit _ hgauss.2.1 (by simpa only [hrpow] using hgauss.2.2)
  have hgint : (∫ z : ℝ × ℝ, g z) =
      (∫ z in small, fs z) + (∫ z in mid, fc z) +
        (∫ z in far, fc z) + (∫ z in gtail, fg z) := by
    dsimp [g]
    have h1 := integral_add ((hIS.add hIM).add hIF) hIG
    have h2 := integral_add (hIS.add hIM) hIF
    have h3 := integral_add hIS hIM
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3,
      integral_indicator hS, integral_indicator hM, integral_indicator hF,
      integral_indicator hG]
  refine ⟨hrho, hwindowI, integral_nonneg hfs0, ?_⟩
  calc
    (∫ z in window, fs z) = ∫ z : ℝ × ℝ, window.indicator fs z :=
      (integral_indicator hWin).symm
    _ ≤ ∫ z : ℝ × ℝ, g z := integral_mono hWI hg hdom
    _ = (∫ z in small, fs z) + (∫ z in mid, fc z) +
        (∫ z in far, fc z) + (∫ z in gtail, fg z) := hgint
    _ ≤ C / Real.sqrt (n : ℝ) + 1 / Real.sqrt (n : ℝ) +
        1 / Real.sqrt (n : ℝ) + 1 / Real.sqrt (n : ℝ) :=
      add_le_add (add_le_add (add_le_add hsmall.2.2.2 hmidRate) hfarRate) hgaussRate
    _ = (C + 3) / Real.sqrt (n : ℝ) := by ring

end
end Shao.OQ3
