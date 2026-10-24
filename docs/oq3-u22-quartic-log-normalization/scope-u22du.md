# Unit206 / U22DU: genuine directional-moment scaling and Euclidean frequency scaling

Freeze COMPLETE declarations/allLvalue BEFORE implementation. Anyactualpairmeasure withgenuineEuclideanradialmI ->genuineSIGNEDdirectionalunscaled/scaledmI andactualmoment homogeneity forallnaturalmincluding0/allrealuvs including0/negative. ExactliteralEuclideanfrequencyradius scalesbyabs(s). QualifiedDJ fullactualinterface/allfvalue source/object/receipt/full93qualifiedreview reused; pinnedprimarySqrt andBochner/L1normintegralAPIexistingobjects only. This is a necessary normalizationdependency, NOTactualIID/Edgeworth/root closure; no targeterror/coherence ornewsourceassumption. DSfreshreviewongoing independent; DUdoesnotconsumeDS/DQ/DR. OriginalrootsB/D andsourcep54/strictbeta/externalattribution unchanged.

```lean
theorem pair_projection_moment_homogeneity
    (law : Measure (Fin 2 → ℝ)) (m : ℕ)
    (hI : Integrable
      (fun y : Fin 2 → ℝ => Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ^ m) law)
    (u v s : ℝ) :
    let L : (Fin 2 → ℝ) → ℝ := fun y => u * y 0 + v * y 1
    Integrable (fun y => L y ^ m) law ∧
      Integrable (fun y : Fin 2 → ℝ => ((s * u) * y 0 + (s * v) * y 1) ^ m) law ∧
      (∫ y : Fin 2 → ℝ, ((s * u) * y 0 + (s * v) * y 1) ^ m ∂law) =
        s ^ m * (∫ y, L y ^ m ∂law)

theorem euclidean_frequency_radius_scalar_mul (s u v : ℝ) :
    Real.sqrt ((s * u) ^ 2 + (s * v) ^ 2) =
      |s| * Real.sqrt (u ^ 2 + v ^ 2)
```
