# OriginalRhoTiltedMoments — exact qualified interface

Original p51 S3/S5 actual full quadratic-tilt rho/rho^2 moment producer. All 23 leaves retain the original model assumptions, explicit window, original-n denominators, genuine integrability and factors14/56/8; rho=0 is included without division by rho. Weighted-deletion/S14/S11/fullOQ56 remains OPEN.

Source SHA256: 7efcc429e36c4849009e01f05f1db9c9400165b4d5be1e43a0677b0285fed4bf; bytes: 20086.

Complete source heads:

```lean
theorem actual_quadratic_rho_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o z, h o z = h z o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ z, h o z ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 4 ≤ n)
    (y : ℝ) (hy : 1 ≤ y)
    (hwindow : y ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ))) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ z, h o z ∂μ
    let r : Ω → Ω → ℝ := fun o z => h o z - g o - g z
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let rho : ℝ := Real.sqrt v
    let a : ℝ := y / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let w : Ω → ℝ := fun o => Real.exp (φ o)
    let m : ℝ := ∫ o, w o ∂μ
    let L : Ω → ℝ := fun o => w o / m
    let ν : Measure Ω :=
      μ.withDensity (fun o => ENNReal.ofReal (L o))
    let P₀ : Measure (Fin n → Ω) :=
      Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, φ (ξ j)
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (fun i j => r (ξ i) (ξ j))
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ6.ResidualDeletion.rowSum
        (fun j k => r (ξ j) (ξ k)) i
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, ψ ξ i ^ 2
    let u : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ψ ξ i / ((n : ℝ) - 2)
    let J : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ i : Fin n, u ξ i ^ 2
    let D : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    0 ≤ rho ∧ rho ^ 2 = v ∧
      μ.tilted φ = ν ∧ IsProbabilityMeasure ν ∧
      Pₐ = Measure.pi (fun _ : Fin n => ν) ∧
      IsProbabilityMeasure Pₐ ∧
      MemLp F 2 Pₐ ∧ Integrable (fun ξ => F ξ ^ 2) Pₐ ∧
      Integrable (fun ξ => |F ξ|) Pₐ ∧
      (∀ i : Fin n, MemLp (fun ξ => ψ ξ i) 2 Pₐ) ∧
      Integrable Λsq Pₐ ∧ Integrable J Pₐ ∧
      Integrable D Pₐ ∧ Integrable (fun ξ => |D ξ|) Pₐ ∧
      (∀ ξ, J ξ = Λsq ξ / ((n : ℝ) - 2) ^ 2) ∧
      (∫ ξ, J ξ ∂Pₐ) =
        (∫ ξ, Λsq ξ ∂Pₐ) / ((n : ℝ) - 2) ^ 2 ∧
      (∫ ξ, |D ξ| ∂Pₐ) =
        (∫ ξ, |F ξ| ∂Pₐ) /
          (Real.sqrt (n : ℝ) * ((n : ℝ) - 1)) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤ rho ^ 2 *
        (4 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
          96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤ rho ^ 2 *
        (8 * C ^ 2 * (n.choose 2 : ℝ) +
          48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ∧
      (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
        14 * C ^ 4 * rho ^ 2 * (n : ℝ) ^ 2 * (1 + y ^ 4) ∧
      (∫ ξ, Λsq ξ ∂Pₐ) ≤
        14 * C ^ 4 * rho ^ 2 * (n : ℝ) ^ 2 * (1 + y ^ 2) ∧
      (∫ ξ, J ξ ∂Pₐ) ≤
        56 * C ^ 4 * rho ^ 2 * (1 + y ^ 2) ∧
      (∫ ξ, |D ξ| ∂Pₐ) ≤
        8 * C ^ 2 * rho * (1 + y ^ 2) / Real.sqrt (n : ℝ)

private theorem rho_choose_bounds
    (n : ℕ) (hn : 4 ≤ n) :
    (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 ∧
      6 * (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 ∧
      6 * (n.choose 4 : ℝ) ≤ (n : ℝ) ^ 4 / 4

private theorem rho_coefficient_bounds
    (n : ℕ) (hn : 4 ≤ n)
    (y C : ℝ) (hC : 1 ≤ C) :
    let a : ℝ := y / Real.sqrt (n : ℝ)
    (4 * C ^ 2 * (n.choose 2 : ℝ) +
      48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2 +
      96 * C ^ 4 * (n.choose 4 : ℝ) * a ^ 4) ≤
        14 * C ^ 4 * (n : ℝ) ^ 2 * (1 + y ^ 4) ∧
    (8 * C ^ 2 * (n.choose 2 : ℝ) +
      48 * C ^ 3 * (n.choose 3 : ℝ) * a ^ 2) ≤
        14 * C ^ 4 * (n : ℝ) ^ 2 * (1 + y ^ 2)

private theorem integral_abs_sq_le_second
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → ℝ) (hf : MemLp f 2 P) :
    Integrable (fun z => |f z|) P ∧
      (∫ z, |f z| ∂P) ^ 2 ≤ ∫ z, f z ^ 2 ∂P
```

Validation: qualified complete independent source/proof review, complete actual all-module TYPE/required non-theorem FULLVALUE and transitive axiom audit on the first original object. Old source/check evidence is reused exactly. Prior-freeze/data-contract attachments preserve their original bytes; repair amendments are authoritative for corrected notation. Native212 has 0 source warnings; native213 has 11. Both actual native and same-original-object audits exit0; strict wrapper success is false with the standing134B mathlib stderr (213 also has source stdout warnings), and FIRSTEMPTY is null because it is not a runner field. No merge or root completion is claimed.
