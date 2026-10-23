# Exact actual growing-region integral declaration freeze

Root authorization at 2026-10-23T19:10:49.413745+00:00. Root completely read the mathematical proof candidate, the full literal public head and the author's complete candidate scrutiny. This freezes exactly ONE public theorem and ZERO new global/private definition values before implementation. Additional private helper THEOREMS are allowed. Any helper definition requires its complete literal value in a separate explicit addendum BEFORE implementation. No mathematical assumption or constant may change silently.

Module ownership: Shao/Probability/SourceGrowingRegionIntegrals.lean only, plus assigned drafts/c12-growing-region-integrals outputs. Writer /root/common_growing_region_candidate_author; not alone, do not modify other owner sources. The previous contour writer explicitly released all write authority and has ordinary FINAL; contour independent review remains in flight. New writer must keep every exact old source/object immutable. No Lean check importing the new contour may run before root's explicit qualified-dependency-ready notice; mathematical proof implementation can be written now. All eventual Lean only server10-13/root-heavy.lock/M8192/j4, original pins, target-only. No local Lean/cache write/lake update/old producer replay.

Readonly mathematical inputs: proof-candidate.md SHA3002a4b1d9f6fb0f153a598d746d9c686a12808f7145525814680fe939c3716b; candidate-declarations.md SHA93407f28dee1b0004b5c51862d3ee47faa6b2182bb4797f21aa0edd69cfbf909; candidate-check.md SHAeaf99be29c0e68b915199cdd788cc7eb7eba2861c1378f8fd0cc1645ef1c36f9. All source-to-statement inputs remain original fixed law/raw clock, real kernel and both same-Xi branches. The only explanatory clarification is downstream macro Lambda means exactly (1+y)n|mu|+(1+y)^3n m3; eta<=Lambda alone cannot pay its mean term. The current public head has no Lambda and retains n|mu|.

The new intermediary envelope's literal200 retains proved one-Gamma8 slack below the existing literal512; source alpha1/1024 and original macro/short tilts do not change. The public theorem exposes actual four-region integrals, full real derivatives and a coarse actual bound; it does not assert final source probability/C1C2 or q>5 vanishing. Independent final complete source/proof/allactualtypes/values/transitiveAX review is mandatory before acceptance.

Frozen full declaration:

```lean
theorem sourceFutureNoiseKernel_growing_region_integrals :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
        (n m : ℕ) (h y lam q w : ℝ),
        Integrable (fun a : ℝ => |a| ^ 3) nu →
        0 < variance (id : ℝ → ℝ) nu →
        0 < h → 0 < m →
        (∀ᵐ a : ℝ ∂nu, |a| ≤ h) →
        (∫ a : ℝ, a ^ 2 ∂nu) ≤
          2 * variance (id : ℝ → ℝ) nu →
        (3 / 4 : ℝ) ≤ (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) →
        (n : ℝ) * (∫ a : ℝ, a ^ 2 ∂nu) ≤ (4 / 3 : ℝ) →
        (1 / 2 : ℝ) ≤ (n : ℝ) * variance (id : ℝ → ℝ) nu →
        (n : ℝ) * |∫ a : ℝ, a ∂nu| ≤ (1 / 2 : ℝ) →
        2 ≤ y → 0 ≤ q → y * h ≤ (1 / 64 : ℝ) →
        |w| ≤ h →
        let mu : ℝ := ∫ a : ℝ, a ∂nu
        let m2 : ℝ := ∫ a : ℝ, a ^ 2 ∂nu
        let m3 : ℝ := ∫ a : ℝ, |a| ^ 3 ∂nu
        let V : ℝ := variance (id : ℝ → ℝ) nu
        let gamma : ℝ := m3 / V
        let Gamma : ℝ := 8 * Real.exp (8 * lam * h) * gamma
        let T : ℝ := (m : ℝ) * m2
        let N : ℝ := q + T
        let Delta : ℝ := (1 + lam * y)⁻¹
        let s : ℝ := lam * y / Real.sqrt N
        let sj : Fin 2 → ℝ := fun j => if j = 0 then 0 else s
        let z : ℝ → ℂ := fun u => (u : ℂ) - (lam : ℂ) * Complex.I
        let G : Fin 2 → Fin 2 → ℝ × ℝ → ℂ := fun d j p =>
          sourceComplexBoundaryContourIntegrand nu m j d y N lam w q
            (z p.1) ((p.2 : ℂ) + (sj j : ℂ) * Complex.I)
        let regions : Fin 4 → Set (ℝ × ℝ) := fun k =>
          if k = 0 then {p | |p.1| ≤ (1 / 128 : ℝ) / Gamma ∧
            |p.2| ≤ (1 / 128 : ℝ) * |p.1| / Gamma}
          else if k = 1 then {p | |p.1| ≤ (1 / 128 : ℝ) / Gamma ∧
            (1 / 128 : ℝ) * |p.1| / Gamma < |p.2|}
          else if k = 2 then {p | (1 / 128 : ℝ) / Gamma < |p.1| ∧
            |p.2| ≤ |p.1| / (4 * h)}
          else {p | (1 / 128 : ℝ) / Gamma < |p.1| ∧
            |p.1| / (4 * h) < |p.2|}
        let J : ℕ → ℝ := fun k =>
          Real.rpow T (-((k : ℝ) + 1) / 2) +
            Real.sqrt y * Delta * Real.rpow T (-(2 * (k : ℝ) + 3) / 4)
        let U : ℝ := J 1 + lam * J 0
        let Vpoly : ℝ := J 3 + 3 * lam * J 2 +
          3 * lam ^ 2 * J 1 + lam ^ 3 * J 0 +
          (s + Delta⁻¹) * U + y * (J 2 + lam * J 1)
        let PJ : ℝ := (T⁻¹ + lam ^ 2) ^ 8
        let R1tail : ℝ := Gamma ^ 15 +
          Real.sqrt y * Delta * Gamma ^ 15 / Real.sqrt Gamma
        let R2tail : ℝ := Gamma ^ 14 +
          Real.sqrt y * Delta * Gamma ^ 14 / Real.sqrt Gamma
        let A : Fin 4 → ℝ := fun k =>
          if k = 0 then T * ((n : ℝ) * |mu| * U + (n : ℝ) * m3 * Vpoly)
          else if k = 1 then Gamma * Delta⁻¹
          else if k = 2 then PJ * R1tail
          else (h * Delta⁻¹) ^ 31 * Gamma ^ 30
        let B : Fin 4 → ℝ := fun k =>
          if k = 0 then U
          else if k = 1 then Gamma ^ 2 * Delta⁻¹ ^ 2 + lam * Gamma * Delta⁻¹
          else if k = 2 then PJ * (R2tail + lam * R1tail)
          else (h * Delta⁻¹) ^ 31 * (Gamma ^ 29 + lam * Gamma ^ 30)
        let Ebase : ℝ := Real.exp
          (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
            (m : ℝ) * lam * |mu| +
            24 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (lam * h) + 200 * lam * h)
        let E512 : ℝ := Real.exp
          (-lam * y * Real.sqrt N + T * lam ^ 2 / 2 +
            (m : ℝ) * lam * |mu| +
            512 * (m : ℝ) * lam ^ 3 * m3 * Real.exp (512 * lam * h) +
            512 * lam * h)
        let Bstar : ℝ := 1 + y + lam + T⁻¹
        let f : ℝ → ℝ := fun r => sourceFutureNoiseKernel nu m y (r, q)
        (1 / 16 : ℝ) ≤ N → N ≤ 7 → y / Real.sqrt N ≤ lam →
        20 * gamma ^ 2 ≤ T →
        (y + lam) * Gamma ≤ (1 / 2048 : ℝ) →
        0 < T ∧ 0 < Gamma ∧ 0 < Delta ∧
          (∀ d j : Fin 2,
            Integrable (G d j) (volume : Measure (ℝ × ℝ))) ∧
          (∀ (d j : Fin 2) (k : Fin 4),
            (∫ p : ℝ × ℝ in regions k, ‖G d j p‖) ≤
              C * Ebase * (if d = 0 then A k else B k)) ∧
          DifferentiableAt ℝ f 0 ∧ DifferentiableAt ℝ f w ∧
          DifferentiableAt ℝ (fun r : ℝ => deriv f r) w ∧
          |deriv f 0| ≤ C * Ebase * (∑ k : Fin 4, A k) ∧
          |deriv (fun r : ℝ => deriv f r) w| ≤
            C * Ebase * (∑ k : Fin 4, B k) ∧
          |deriv f 0| ≤ C * ((n : ℝ) * |mu| + (n : ℝ) * m3) *
            Bstar ^ 128 * E512 ∧
          |deriv (fun r : ℝ => deriv f r) w| ≤ C * Bstar ^ 128 * E512
```
