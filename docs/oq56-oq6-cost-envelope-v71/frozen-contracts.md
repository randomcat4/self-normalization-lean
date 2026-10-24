# Source analytic cost and actual uncentered remainder envelope

The two local interfaces below formalize separate obligations in p39. The first computes the literal p37(1) analytic cost of the explicit candidate D3, with genuine raw full/partial integrability, full I=m^n, a single cap, and the original n in every denominator. The second bounds the actual uncentered-row D2 on the exact source event G, with a fixed admissible envelope coefficient4096. Its separate s*x<=sqrt(n) condition is retained in its own statement; it is not added to the analytic-cost theorem.

Both declarations and every let were frozen before implementation. There are no new public definitions or private helper declarations. The two denominators n^2*sqrt(n) encode the same positive-real n^(5/2). The pointwise envelope specializes to the actual observation arrays using g(o)=integral h(o,y) and r=h-g-g'; choosing C0=4096 in the cost interface is permitted. This describes interface compatibility, not a separately exported joint probability theorem.

All original C12/OQ3/OQ4/OQ56 root groups remain OPEN. The compact continuous-weight cost, actual bad-D2 probabilities, G/H-complement estimates, RS1/RS2, clipping/coding, centered physical Studentizer conversion/zero events and final Gaussian limits remain separate. In particular a large-D3 event is not substituted for an actual bad-D2 event. The p54 repairs, strict-margin/atom-safe obligations and Shao--Zhou external-result attribution remain intact. No novelty or historical priority claim is made. The124 mechanism is not a prerequisite.

## Exact analytic-cost declaration

```lean
theorem actual_quadratic_source_analytic_cost
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 1 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ)))
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let m : ℝ := ∫ o, Real.exp (φ o) ∂μ
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, φ (ξ j)
    let Sminus : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j ∈ Finset.univ.erase i, φ (ξ j)
    let I : ℝ := m ^ n
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (Sminus ξ i) / I
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, ψdel ξ i j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let A : (Fin n → Ω) → ℝ := fun ξ => |D₁ ξ|
    let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |D₁del ξ i|
    let D₃ : (Fin n → Ω) → ℝ := fun ξ =>
      C₀ * (s * x / Real.sqrt (n : ℝ) +
        Λsq ξ / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
    let D₃del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      C₀ * (s * x / Real.sqrt (n : ℝ) +
        Λdelsq ξ i / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
    let fullTest : (Fin n → Ω) → ℝ := fun ξ => x * A ξ + x ^ 2 * D₃ ξ
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      cap ξ i * (|A ξ - Adel ξ i| + x * |D₃ ξ - D₃del ξ i|)
    let sourceCost : ℝ :=
      ((∫ ξ, fullTest ξ * Real.exp (S ξ) ∂P₀) +
        ∑ i : Fin n,
          ∫ ξ, deletedTest ξ i * Real.exp (Sminus ξ i) ∂P₀) / I
    Integrable (fun ξ => fullTest ξ * Real.exp (S ξ)) P₀ ∧
      (∀ i : Fin n, Integrable
        (fun ξ => deletedTest ξ i * Real.exp (Sminus ξ i)) P₀) ∧
      sourceCost =
        x * (∫ ξ, A ξ ∂Pₐ) + x ^ 2 * (∫ ξ, D₃ ξ ∂Pₐ) +
          ∑ i : Fin n,
            ∫ ξ, R ξ i * deletedTest ξ i ∂P₀ ∧
      sourceCost ≤
        64 * C ^ 4 * (1 + C₀) * s * (1 + x) ^ 3 / Real.sqrt (n : ℝ)
```

## Exact actual-envelope declaration

```lean
theorem actual_uncentered_remainder_envelope
    {n : ℕ} (g : Fin n → ℝ) (r : Fin n → Fin n → ℝ)
    (hr : ∀ i j, r i j = r j i) (hn : 3 ≤ n)
    (x : ℝ) (hx : 1 ≤ x) (s : ℝ) (hs : 1 ≤ s)
    (hscale : s * x ≤ Real.sqrt (n : ℝ)) :
    let ψ : Fin n → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, r i j
    let Λsq : ℝ := ∑ i : Fin n, ψ i ^ 2
    let Vsq : ℝ := (∑ i : Fin n, g i ^ 2) / (n : ℝ)
    let W : ℝ := (∑ i : Fin n, g i) / Real.sqrt (n : ℝ)
    let H : Fin n → Fin n → ℝ := fun i j => g i + g j + r i j
    let D₂ : ℝ := Shao.OQ6.FiniteRows.uncenteredSq H / Vsq - 1
    (1 / 2 : ℝ) ≤ Vsq →
      |W| ≤ Real.sqrt x * Real.sqrt (Real.sqrt (n : ℝ)) *
        (4 + Real.sqrt Vsq) →
      |D₂| ≤ 4096 * (s * x / Real.sqrt (n : ℝ) +
        Λsq / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
```
