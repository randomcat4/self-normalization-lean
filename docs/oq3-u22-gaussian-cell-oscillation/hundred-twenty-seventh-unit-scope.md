# OQ3 unit127 (U22at): actual compact rate-to-probability finite cover
Frozen before implementation. Source report.md section4 equation18 finiteexponentialcover; repair01.md section4 bounded-source farfield explanation. Direct consumer actualfarprobability on compact subsets after genuine rate gap. This must obtain every exponential test from the TRUE EReal global Legendre supremum, then choose finitely many through compactness and apply AS to actual iid samplemean. No probability/conclusion/cover premise allowed.
Onepublictheorem0globaldefinitions:
```lean
theorem compact_parabola_rate_probability_upper_bound
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (F : Set (ℝ × ℝ)) (hF : IsCompact F) (c : ℝ)
    (hRate : ∀ w ∈ F, (c : EReal) <
      Shao.Probability.bivariateLegendreRate mu (fun x : ℝ => (x, x ^ 2)) w) :
    let Domain : Set (ℝ × ℝ) :=
      Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))
    let K : (ℝ × ℝ) → ℝ := fun theta =>
      Real.log (∫ x : ℝ, Real.exp (theta.1 * x + theta.2 * x ^ 2) ∂mu)
    let Test : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := fun theta w =>
      theta.1 * w.1 + theta.2 * w.2 - K theta
    ∃ S : Finset Domain, 0 < (S.card : ℝ) + 1 ∧
      (∀ w ∈ F, ∃ theta ∈ S, c < Test (theta : ℝ × ℝ) w) ∧
      ∀ n : ℕ, 1 ≤ n →
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
        let M : Shao.Path n → (ℝ × ℝ) := fun z =>
          ((∑ i : Fin n, z i) / (n : ℝ), Shao.energy z / (n : ℝ))
        P.real (M ⁻¹' F) ≤ ((S.card : ℝ) + 1) * Real.exp (-(n : ℝ) * c)
```
F compact and strict actualrate>c explicit; no bounded-X premise, no uniqueness substituted for rate gap, no unboundedsettightness conclusion. Finitecover chosen once beforealln, explicitpositivecardinalityconstant, n>=1. EmptyFallowed; Legendre+infinity handledthroughsupremum. This does not yet prove that the full original tail outsideAL'sU is such a compact F withthegivenrate gap or zero-boundary control. That later actualconsumer remainsOPEN, along with Edgeworth/cells/rootB-D. Fullfresh independent final source/proof/alltypes/localvalues plus exactserverkernel/allownerAX required.
