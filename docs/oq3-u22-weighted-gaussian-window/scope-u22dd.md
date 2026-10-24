# U22DD189 exact complete declaration freeze

Freeze BEFORE implementation. Retains COMPLETE DC188canonicalpacket andALL44existingstatementletvalues under SAMEE, includingactualweightedlocalerrorandfinitewindowfarCFdecay; inheritedEXPLICITbeta<2/5 unchanged. Adds actual arbitrarynaturalweight/realpower genuineweightedCFIntegrableOn/nonnegativeACTUALLebesgueintegral superpolyon EXACTdelta<=scaledEuclideanradius<=H middleannulus forANYdelta>0/ANYrealH. ONE N beforeALLn>=N/theta; no desiredintegral/integrability/pointwiseerror assumption. ALL51statementletvalues frozen. Middlepointwisesupremum willbeDISCHARGED by inheritedcanonicalmiddlepacket atq+(k+2) withpositiveHdependentfactor, finiteboxboundK=n*(1+absH), trueEuclideanradius scalingprovedexplicitly usingprimarysqrt_div. Hnegative/emptyannulus/k0/negativeq covered. DCauthorPASSfreshfullreviewACTIVE mustqualifybeforeacceptance; DB fullyqualified. Rootv63checked5cd794fe/tree8a399c29 distinctnoticeIDs, PR232frozen lanehead02095unchanged. OriginalB/D,higherEdgeworth/fullfrequency/inversion/exterior/newrhoLaplace OPEN; p54/sourceSong/AngstPoly attributionunchanged. ALL heavyserverONLY CPU14-17 max1 M8192j4 nooldPASSgatereplay.

```lean
theorem compact_open_domain_standardized_weighted_middle_frequency_family
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
      ∀ delta H : ℝ, 0 < delta → ∀ k : ℕ, ∀ q epsilon : ℝ, 0 < epsilon →
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
            Real.rpow (n : ℝ) q * (∫ z in middle, f z) < epsilon
```
