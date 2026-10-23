# OQ3 U22BH / unit141 — frozen actual n-cubed Gaussian oscillation scale

FROZEN before implementation. math-theorem/no math-ultra, OQ3 lead author. Independent complete source/proof/allactualownedtype/allvalues and recursive standard3 axiom review before qualification. One public theorem/no global definitions, all server/pin/resource/cache rules unchanged.

Source-bound objective: instantiate the actual thin-Gaussian mean-oscillation producer BG at the actual source smoothing radius h=1/n³. Prove its positivity and thin-radius premise from n>=1, then conclude actual integrability and explicit denominator n³*sqrt(n), i.e. the source n^-7/2 scale. The coefficient still depends explicitly on true map norms and source parameters; no family-uniformity or sample Edgeworth conclusion is claimed.

Exact planned sole import: Shao.OQ3.ParabolaCellAveragedOscillation. BG source9c62faccd8457ea7bdc8526481afd1a045d32a82b6b3f461403073161e3b98a5 authorfirstkernel/wholeownerAXPASS, freshreviewpending. No BH qualification before BG fullqualification. Old unchanged proof/check reuse perrootstreamlined rule; consumed entire interface/values/hash/qualification/scope reviewed.

Exact complete declaration and ALL statement local values:
```lean
theorem actual_parabola_cell_ncube_gaussian_oscillation_bound
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    :
    let h : ℝ := 1 / (n : ℝ) ^ 3
    let A : Set (ℝ × ℝ) := (Set.Ioc aL aR ×ˢ Set.Ioc qL qR) ∩
      {w : ℝ × ℝ | |w.1 - a0| ≤ rho ∧
        0 ≤ w.1 ^ 2 / level ^ 2 - w.2 ∧ w.1 ^ 2 / level ^ 2 - w.2 ≤ rho}
    let B : Set (ℝ × ℝ) :=
      (fun w : ℝ × ℝ => Real.sqrt (n : ℝ) • E (w - y)) '' A
    let g : (ℝ × ℝ) → ℝ := fun v => Real.exp (-Real.sqrt (n : ℝ) *
      (theta.1 * (E.symm v).1 + theta.2 * (E.symm v).2))
    let kappa : ℝ := (|theta.1| + |theta.2|) *
      ‖(E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let R : ℝ := ‖(E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))‖
    let C : ℝ := Real.exp (kappa * R)
    let G : ℝ := R * (1 + 2 * (|a0| + rho) / level ^ 2)
    let Φ : MeasureTheory.Measure (ℝ × ℝ) :=
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)
    MeasureTheory.Integrable (openBallOscillation (B.indicator g) h) Φ ∧
      (∫ z, openBallOscillation (B.indicator g) h z ∂Φ) ≤
        C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) /
          ((n : ℝ) ^ 3 * Real.sqrt (n : ℝ))
```

All displayed arguments universal, with exactly rho>=0, n>=1, geometric anchor y in ORIGINAL closed grid rectangle, and original sidewidth upperbounds. No h positivity/smallness, support, integrability, mean bound or probability comparison assumed. Empty cell allowed. Original Ioc rectangle and CLOSED physical window/two graphs are literal. Existing maxnorm and actual productGaussian retained. All real level uses total division for geometry; physical positivelevel/sourceidentification conditions still apply downstream.

Proof route: n>=1 gives n>0, positive sqrt and n³; sqrt(n)<=n<=n³, hence h>0 and h<=1/sqrt(n). Feed these actual proven premises to BG with the exact theta/E/y/cell/anchor parameters. Its actual function g/indicator/integrability measure and all coefficients coincide with the frozen lets. Exact real division associativity converts h/sqrt(n) to1/(n³sqrt(n)); no asymptotic heuristic or numerical test.

OPEN: uniform actual whitening/operator/cellfamily/parameter constants, source Edgeworth/sampleprobability comparison, exact partition and valid rateanchors/weightedreconstruction/summation/full exterior/originalB/D. Accepted fixedlawA/boundedcompacttiltC scopes retained; originalmoment/saddle/curvature/rategap/p54/strictWC/externalattribution unchanged. A Gaussian-only local smoothing bound is not the root probability theorem.

