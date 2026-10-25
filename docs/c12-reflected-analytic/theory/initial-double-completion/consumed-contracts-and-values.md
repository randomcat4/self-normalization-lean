# Existing qualified consumed contracts / relevant values, no old proof re-review


## library/Shao/C2/BridgeUpperAffineIdentification.lean:39 — bridge_upper_formula

```lean
theorem bridge_upper_formula {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ)
    (hT : 0 < T) (hy : y < a) (hz : z < a) :
    upperCompletion (bridgeLaw B P) a y T z =
      1 - Real.exp (-2 * (a - y) * (a - z) / T)
```


## library/Shao/C2/BridgeLowerIdentification.lean:55 — bridge_lower_formula

```lean
theorem bridge_lower_formula {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y T z : ℝ)
    (hT : 0 < T) (hy : -a < y) (hz : -a < z) :
    lowerCompletion (bridgeLaw B P) a y T z =
      1 - Real.exp (-2 * (a + y) * (a + z) / T)
```


## library/Shao/C2/BrownianKilledSineIdentification.lean:133 — bridge_interval_eq_image

```lean
theorem bridge_interval_eq_image {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (a y U z : ℝ) (ha : 0 < a) (hy : |y| < a)
    (hU : 0 < U) (hz : |z| < a) :
    intervalCompletion (bridgeLaw B P) a y U z = intervalImageCandidate a z U y
```


## library/Shao/C2/IntervalImageCandidateSpatial.lean:10 — finiteSpatialImages

```lean
def finiteSpatialImages (j : ℕ) (a z T y : ℝ) : ℝ :=
  iteratedDeriv j (fun w => Real.exp (-imageA a w z 0 / T)) y +
    iteratedDeriv j (fun w => Real.exp (-imageA a w z 1 / T)) y +
    iteratedDeriv j (fun w => Real.exp (-imageA a w z (-1) / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z 0 / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z (-1) / T)) y
```


## library/Shao/C2/IntervalImageCandidateSpatial.lean:17 — imageCandidateSpatial

```lean
def imageCandidateSpatial (j : ℕ) (a z T y : ℝ) : ℝ :=
  finiteSpatialImages j a z T y + spatialTailSum j a z T y
```


## library/Shao/C2/IntervalImageCandidateSpatial.lean:20 — intervalImageCandidate

```lean
def intervalImageCandidate (a z T y : ℝ) : ℝ :=
  imageCandidateSpatial 0 a z T y
```


## library/Shao/C2/IntervalImageCandidateSpatial.lean:59 — intervalImageCandidate_eq_images

```lean
theorem intervalImageCandidate_eq_images (a z T y : ℝ) :
    intervalImageCandidate a z T y =
      1 + Real.exp (-imageA a y z 1 / T) + Real.exp (-imageA a y z (-1) / T) -
        Real.exp (-imageB a y z 0 / T) - Real.exp (-imageB a y z (-1) / T) +
          ∑' n : ℕ, spatialTailBlock 0 a z T y n
```


## library/Shao/C2/IntervalImageSpatialDerivatives.lean:11 — spatialTailSum

```lean
def spatialTailSum (j : ℕ) (a z T y : ℝ) : ℝ :=
  ∑' n : ℕ, spatialTailBlock j a z T y n
```


## library/Shao/C2/IntervalImageExponents.lean:7 — imageA

```lean
def imageA (a y z m : ℝ) : ℝ := 8 * m ^ 2 * a ^ 2 + 4 * m * a * (z - y)
```


## library/Shao/C2/IntervalImageExponents.lean:8 — imageB

```lean
def imageB (a y z m : ℝ) : ℝ := 2 * (y + (2 * m + 1) * a) * (z + (2 * m + 1) * a)
```


## library/Shao/C2/BridgeEndpointIndependence.lean:96 — bridge_endpoint_hasLaw

```lean
theorem bridge_endpoint_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    HasLaw (fun ω => (bridgeNoise B ω, B 1 ω))
      ((bridgeLaw B P).prod (gaussianReal 0 1)) P
```


## library/Shao/C2/BrownianBridgeLaw.lean:23 — bridgeLaw

```lean
def bridgeLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Measure BridgeNoise :=
  P.map (bridgeNoise B)
```


## library/Shao/C2/BrownianBridgeLaw.lean:39 — isProbabilityMeasure_bridgeLaw

```lean
theorem isProbabilityMeasure_bridgeLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) : IsProbabilityMeasure (bridgeLaw B P)
```


## library/Shao/C2/BrownianBridgeLaw.lean:45 — ae_bridgeNoise_eq

```lean
theorem ae_bridgeNoise_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : BridgeTime,
      (bridgeNoise B ω).val t =
        B ⟨(t : ℝ), t.property.1⟩ ω - (t : ℝ) * B 1 ω
```


## library/Shao/C2/BridgeDomination.lean:13 — BridgeTime

```lean
abbrev BridgeTime := unitInterval
```


## library/Shao/C2/BridgeDomination.lean:14 — BridgeNoise

```lean
abbrev BridgeNoise := {g : C(BridgeTime, ℝ) // g 0 = 0 ∧ g 1 = 0}
```


## library/Shao/C2/BridgeDomination.lean:16 — bridgePath

```lean
def bridgePath (y T z : ℝ) (g : BridgeNoise) : C(BridgeTime, ℝ) :=
  ⟨fun t => (1 - (t : ℝ)) * y + (t : ℝ) * z + Real.sqrt T * g.val t,
    by fun_prop⟩
```


## library/Shao/C2/BridgeDomination.lean:20 — strictUpper

```lean
def strictUpper (a y T z : ℝ) : Set BridgeNoise :=
  {g | ∀ t : BridgeTime, bridgePath y T z g t < a}
```


## library/Shao/C2/BridgeDomination.lean:23 — strictLower

```lean
def strictLower (a y T z : ℝ) : Set BridgeNoise :=
  {g | ∀ t : BridgeTime, -a < bridgePath y T z g t}
```


## library/Shao/C2/BridgeDomination.lean:26 — strictInterval

```lean
def strictInterval (a y T z : ℝ) : Set BridgeNoise :=
  strictUpper a y T z ∩ strictLower a y T z
```


## library/Shao/C2/BridgeDomination.lean:29 — upperCompletion

```lean
def upperCompletion (P : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  P.real (strictUpper a y T z)
```


## library/Shao/C2/BridgeDomination.lean:32 — lowerCompletion

```lean
def lowerCompletion (P : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  P.real (strictLower a y T z)
```


## library/Shao/C2/BridgeDomination.lean:35 — intervalCompletion

```lean
def intervalCompletion (P : Measure BridgeNoise) (a y T z : ℝ) : ℝ :=
  P.real (strictInterval a y T z)
```


## library/Shao/C2/BridgeDomination.lean:38 — bridgePath_endpoints

```lean
theorem bridgePath_endpoints (y T z : ℝ) (g : BridgeNoise) :
    bridgePath y T z g 0 = y ∧ bridgePath y T z g 1 = z
```


## library/Shao/C2/BridgeDomination.lean:49 — measurableSet_strictUpper

```lean
theorem measurableSet_strictUpper (a y T z : ℝ) :
    MeasurableSet (strictUpper a y T z)
```


## library/Shao/C2/BridgeDomination.lean:60 — measurableSet_strictLower

```lean
theorem measurableSet_strictLower (a y T z : ℝ) :
    MeasurableSet (strictLower a y T z)
```


## library/Shao/C2/BridgeDomination.lean:117 — completion_bounds

```lean
theorem completion_bounds (P : Measure BridgeNoise) [IsProbabilityMeasure P]
    (a y T z : ℝ) :
    0 ≤ upperCompletion P a y T z ∧ upperCompletion P a y T z ≤ 1 ∧
    0 ≤ lowerCompletion P a y T z ∧ lowerCompletion P a y T z ≤ 1 ∧
    0 ≤ intervalCompletion P a y T z ∧ intervalCompletion P a y T z ≤ 1
```


## library/Shao/Probability/SourceScalarInitialBudget.lean:511 — finite_second_scalar_closed_cdf_budget

```lean
theorem finite_second_scalar_closed_cdf_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (mu : Measure ℝ) [IsProbabilityMeasure mu]
        (n : ℕ) (hn : 0 < n),
        Integrable (fun z : ℝ => z ^ 2) mu →
        (∫ z : ℝ, z ∂mu) = 0 →
        (0 < ∫ z : ℝ, z ^ 2 ∂mu) →
        let sigma : ℝ := Real.sqrt (∫ z : ℝ, z ^ 2 ∂mu)
        let normalizedLaw : Measure ℝ := Measure.map
          (fun z : ℝ => z / (sigma * Real.sqrt (n : ℝ))) mu
        let R : ℝ := Shao.truncationBudget normalizedLaw n 0
        let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => mu)
        let W : Shao.Path n → ℝ := Shao.C1.normalizedEndpoint
        ∀ v : ℝ,
          |P.real {a : Shao.Path n | W a ≤ v} -
            (gaussianReal 0 1).real (Set.Iic v)| ≤ C * R
```


## library/Shao/Basic/TruncationBudget.lean:24 — truncationF

```lean
def truncationF (z : ℝ) : ℝ := z ^ 2 * min |z| 1
```


## library/Shao/C1/Normalization.lean:15 — normalizedEndpoint

```lean
def normalizedEndpoint (a : Path n) : ℝ :=
  if energy a = 0 then 0 else prefixSum a n / Real.sqrt (energy a)
```


## library/Shao/C2/EndpointCDFTransfer.lean:68 — lower_set_discrepancy

```lean
theorem lower_set_discrepancy
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (s : Set ℝ) (hs : IsLowerSet s) :
    |μ.real s - ρ.real s| ≤ δ
```


## library/Shao/C2/EndpointCDFTransfer.lean:82 — antitone_unit_expectation_error

```lean
theorem antitone_unit_expectation_error
    (μ ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hCDF : ∀ x : ℝ, |μ.real (Set.Iic x) - ρ.real (Set.Iic x)| ≤ δ)
    (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ w, 0 ≤ f w) (hf1 : ∀ w, f w ≤ 1) :
    |(∫ w : ℝ, f w ∂μ) - ∫ w : ℝ, f w ∂ρ| ≤ δ
```

## library/Shao/C2/IntervalImageSpatialConvergence.lean:20 — spatialTailBlock

```lean
def spatialTailBlock (j : ℕ) (a z T y : ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv j (fun w => Real.exp (-imageA a w z ((n : ℤ) + 2 : ℤ) / T)) y +
    iteratedDeriv j (fun w => Real.exp (-imageA a w z (-((n : ℤ) + 2) : ℤ) / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z ((n : ℤ) + 1 : ℤ) / T)) y -
    iteratedDeriv j (fun w => Real.exp (-imageB a w z (-((n : ℤ) + 2) : ℤ) / T)) y
```

## library/Shao/Probability/TruncationIntegrals.lean:26 — truncationBudget

```lean
noncomputable def truncationBudget (ν : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * ∫ z : ℝ, truncationF ((1 + t) * z) ∂ν
```

## library/Shao/Probability/TruncationIntegrals.lean:125 — truncationBudget_mono

```lean
theorem truncationBudget_mono (ν : Measure ℝ) (n : ℕ)
    (h2 : Integrable (fun z : ℝ => z ^ 2) ν) (s t : ℝ)
    (hs : -1 ≤ s) (hst : s ≤ t) :
    truncationBudget ν n s ≤ truncationBudget ν n t
```

## library/Shao/C1/Normalization.lean:30 — normalizedEndpoint_of_energy_eq_zero

```lean
@[simp] theorem normalizedEndpoint_of_energy_eq_zero (a : Path n)
    (hQ : energy a = 0) : normalizedEndpoint a = 0
```
