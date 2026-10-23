# OQ3 U22BG / unit140 — frozen actual thin Gaussian averaged oscillation

FROZEN before implementation, OQ3 lead author, math-theorem/no math-ultra. Fresh independent complete new source/proof/all actual owner types/all values + recursive standard3 axiom audit required. One public theorem, zero global definitions. All server/resource/version/readonly-cache rules unchanged.

Source purpose: consume accepted AX actual Gaussian average and newly produced BF actual sixarc physical-cell frontier tube, removing the remaining literal Gaussian boundary probability from AX for this actual cell. Prove actual integrability AND explicit h/sqrt(n) bound. Future h=n^-3 gives n^-7/2; the actual substitution and physical sample-law/Edgeworth probability remain separate.

Planned exact imports: Shao.OQ3.StandardizedGaussianCellOscillation; Shao.OQ3.ParabolaCellGaussianTube. AX source3d071a81d880a7ec8dd770a42caad8c6f07118bb86d628fd7e72647c55d81c6d/qualified AWAXreported2c244fe23bc0cb1cfcf2abcdcaff428d824cd3dbdf6c207c900c836ed89d2d integratedv53. BF sourced69ade15367a727e652ab5d192f425ab48ae06a80e131ec1b328e3a237f884f7 author kernel/recursiveAXPASS with fresh independent BEBF reviewrunning. BG qualification must await full BF independent qualification. Old unchanged dependency proofs/checks reused; consumed full interfaces/values/hash/qualification/scope verified perrootstreamlinedrule.

Exact full declaration, all quantified objects and ALL statement local values:
```lean
theorem actual_parabola_cell_thin_gaussian_oscillation_bound
    (n : ℕ) (hn : 1 ≤ n) (theta : ℝ × ℝ)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (y : ℝ × ℝ)
    (aL aR qL qR level a0 rho : ℝ) (hrho : 0 ≤ rho)
    (hy : y ∈ Set.Icc aL aR ×ˢ Set.Icc qL qR)
    (hawidth : aR - aL ≤ 1 / (n : ℝ)) (hqwidth : qR - qL ≤ 1 / (n : ℝ))
    (h : ℝ) (hh : 0 < h) (hsmall : h ≤ 1 / Real.sqrt (n : ℝ)) :
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
        C * (8 * kappa * (R + 1) ^ 2 + 768 * (G + 1)) * h / Real.sqrt (n : ℝ)
```

The anchor y is explicitly in the ORIGINAL CLOSED grid rectangle. This is geometric anchor data, not an assumed minimizer, and does not assert y in A or any rate property. The actual Ioc-cell A and physical window remain unchanged. Derive ||w-y||<=1/n from the actual two coordinate intervals and grid width bounds; do not assume AX's support premise as a new conclusion. Empty A allowed. rho>=0/n>=1/h>0/h<=1/sqrt(n) all explicit; level arbitrary total-division geometry, original positivephysicallevel conditions remain for probability identification. E actual equivalence but not asserted true covariance whitening/uniformoperatorcontrol. Existing maximum norm and actual productGaussian retained.

Proof: derive exact AX support for d=1 and R=normE. Consume its actual Integrable and integral-bound interface. Feed BF actual tube to get boundary term<=768*C*(G*h/sqrt(n)+h²). Under hsmall, (R/sqrt(n)+h)²<=((R+1)/sqrt(n))² and h²<=h/sqrt(n). Nonnegative kappa,R,C,G and n's positive sqrt justify all products/division, giving exact displayed coefficient. No Gaussian density/sample-law equality, boundarynull, desiredoscillationbound, geometrycover, Edgeworth or rate conclusion is supplied as a premise.

The functions A,B,g,kappa,R,C,G,Phi are exactly frozen above. Additional proof lets can name s=sqrt(n) and the actual integral value, with exact values. No newglobaldefinition. Every prooflocal value must be reviewed; no hidden nonintegrable-integral convention. OriginalB/D OPEN, accepted correctedfixedlawA/boundedcompacttiltCscope unchanged. Still need h=n^-3 substitution, uniformtruewhitening/cellfamily, actualEdgeworth comparison, exactpartition/rateanchors/full exterior and originalB/D; all p54/WC/attribution constraints retained.

