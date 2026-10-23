# Exact actual source energy-weighted regulator square freeze

Root authorization 2026-10-23T19:22:47.042625+00:00. Root fully read all candidate proof, full THREE heads and source contract. Freeze exactly two private + one public full theorem heads and ZERO new global/private definition values. Extra private helper THEOREMS are permitted; any new definition or changed head/assumption/constant requires an explicit literal addendum before implementation.

Author /root/common_energy_square_candidate_author owns ONLY Shao/Probability/SourceLindleyRegulatorEnergyWeightedSecond.lean and assigned new draft outputs. Not alone: preserve every old source/object and other owner. The prior CDF writer has ordinary FINAL and released write authority; new writer activates only on the root-recorded branch below. All Lean/heavy only designated server10-13/root-heavy.lock/M8192/j4/autoImplicitfalse, original pins. UTF8LF from first write, first final whole success same-command-o/directrc; original source-bound all-owned types/values/transitiveAX and fresh author-independent final full review required. No old successful producer/audit replay, no local Lean/cache writes.

Scope: actual E[sum U_i^2 exp(-kappa*y^2 Q_i)], current-coordinate-inclusive prefix energy, same actual fixed-x cond law, all original first-sum source premises unchanged. Nonzero tilted mean, raw2<=2V and min-type survival are paid internally; no result-shaped public premise. Fixed literal C=1024exp(16+3*1024); partial K keeps the original ambient product law. This does not prove full probability/Taylor/C1C2.

Readonly full candidate inputs:
- proof-route-candidate.md SHA256 93bfc51e690dcd9bff1de1e798aa0d8e3a6ecdf6edab21c8fc1b4c071bf074e3
- candidate-check.md SHA256 904ffcaadf314f7071ef320f447c19647d05eaa848a1e602370b261959f72d3d
- candidate-declarations.md SHA256 56e61353894f280409f5a6ac5418908c4a48c3e459477813a72db1ba6411bbca
- source-contract.md SHA256 13455bc5b624c295fdecd687f840201af28a6d0a2e032040076c4bb06a3acf59

Frozen exact complete heads:

```lean
private theorem ews_min_one_mul
    (u v A : ℝ) (hA : 1 ≤ A) (hu : u ≤ A * v) :
    min 1 u ≤ A * min 1 v
```

```lean
private theorem ews_tilted_second_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (N : ℕ) (h κ y : ℝ)
    (hh : 0 < h) (hκ : 0 < κ)
    (hκsmall : κ ≤ (1 / 16 : ℝ)) (hy : 1 ≤ y)
    (hsupport : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hsmall : (κ * y ^ 2) * h ^ 2 ≤ 1)
    (hNV : (1 / 2 : ℝ) ≤
      (N : ℝ) * variance (id : ℝ → ℝ) ν)
    (hΛ : (1 + y) * (N : ℝ) * |∫ a : ℝ, a ∂ν| +
      (1 + y) ^ 3 * (N : ℝ) * (∫ a : ℝ, |a| ^ 3 ∂ν) ≤
        (1 / 2 : ℝ)) :
    let s : ℝ := κ * y ^ 2
    let ρ : Measure ℝ := ν.tilted (fun a => -s * a ^ 2)
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let T : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ρ)
    IsProbabilityMeasure ρ ∧
      (∀ i : Fin N,
        Integrable (fun a : Shao.Path N => (lindleyRegulator a i) ^ 2) T ∧
          (∫ a : Shao.Path N, (lindleyRegulator a i) ^ 2 ∂T) ≤
            (48 * Real.exp (14 + 3 * (1024 : ℝ))) * m3 /
              (Real.sqrt V * Real.sqrt ((i.val + 1 : ℕ) : ℝ)))
```

```lean
theorem sourceTruncation_lindleyRegulator_energy_weighted_second_sum
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (N : ℕ)
    (h2 : Integrable (fun a : ℝ => a ^ 2) ν0)
    (hnorm : (N : ℝ) * (∫ a : ℝ, a ^ 2 ∂ν0) = 1)
    (hmean : (∫ a : ℝ, a ∂ν0) = 0)
    (x ε ε0 κ y : ℝ) (hx : 0 ≤ x) (hε : 0 < ε)
    (hε0 : 0 < ε0) (hε01 : ε0 ≤ 1) (hεsmall : ε ≤ ε0 / 2)
    (hR : Shao.truncationBudget ν0 N x ≤ ε ^ 3 / 8)
    (hκ : 0 < κ) (hκsmall : κ ≤ (1 / 16 : ℝ)) (hy : 1 ≤ y)
    (hwindow : |y - x| ≤ 1 / (2 * (1 + x))) :
    let ν : Measure ℝ := ProbabilityTheory.cond ν0 {a | |a| ≤ ε / (1 + x)}
    let P : Measure (Shao.Path N) := Measure.pi (fun _ : Fin N => ν)
    let μ : ℝ := ∫ a : ℝ, a ∂ν
    let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂ν
    let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂ν
    let V : ℝ := variance (id : ℝ → ℝ) ν
    let Λ : ℝ := (1 + y) * (N : ℝ) * |μ| +
      (1 + y) ^ 3 * (N : ℝ) * m3
    let U : Fin N → Shao.Path N → ℝ := fun i a => lindleyRegulator a i
    let Q : Fin N → Shao.Path N → ℝ := fun i a =>
      Shao.prefixSquares a (i.val + 1)
    let C : ℝ := 1024 * Real.exp (16 + 3 * (1024 : ℝ))
    let F : Shao.Path N → ℝ := fun a =>
      ∑ i : Fin N, U i a ^ 2 * Real.exp (-(κ * y ^ 2) * Q i a)
    IsProbabilityMeasure ν ∧
      (∀ᵐ a : ℝ ∂ν, |a| ≤ ε / (1 + x)) ∧
      (κ * y ^ 2) * (ε / (1 + x)) ^ 2 ≤ 1 ∧
      (3 / 4 : ℝ) ≤ (N : ℝ) * m2 ∧
      (N : ℝ) * V ≤ (4 / 3 : ℝ) ∧
      0 ≤ Λ ∧ Λ ≤ (1 / 2 : ℝ) ∧
      Integrable F P ∧ 0 ≤ (∫ a : Shao.Path N, F a ∂P) ∧
      (∫ a : Shao.Path N, F a ∂P) ≤
        C * (N : ℝ) * m3 / (Real.sqrt κ * (1 + y)) ∧
      (∫ a : Shao.Path N, F a ∂P) ≤
        C * Λ / (Real.sqrt κ * (1 + y) ^ 4) ∧
      (∀ K : ℕ, K ≤ N →
        let FK : Shao.Path N → ℝ := fun a =>
          ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < K),
            U i a ^ 2 * Real.exp (-(κ * y ^ 2) * Q i a)
        Integrable FK P ∧ 0 ≤ (∫ a : Shao.Path N, FK a ∂P) ∧
          (∫ a : Shao.Path N, FK a ∂P) ≤
            C * (N : ℝ) * m3 / (Real.sqrt κ * (1 + y)) ∧
          (∫ a : Shao.Path N, FK a ∂P) ≤
            C * Λ / (Real.sqrt κ * (1 + y) ^ 4))
```
