# EnergyLinearTiltCentering declaration and signature ledger

Frozen source SHA256 `82f48c2123d499eed5a7ac8974ff7d51d18e09987539f8323dece141e08bbe16`.

The actual module owns **10 new constants=9 explicit declarations (2 transparent definitions+7 theorems)+1 generated helper**. Ownership is enumerated by `env.getModuleIdxFor?` then its owning module name, with no namespace/name-root restriction. Every actual full signature is the curated output of server `#check @name`; every axiom record is the actual transitive `#print axioms name` result. All10 names, signatures and records match exactly.

All10 records are within `{propext,Classical.choice,Quot.sound}`:9 use that full set,1 only `propext`. Raw audit/binary remain server-only. This author ledger records mechanical evidence, not independent certification.

| Declaration | Kind | Actual transitive axioms |
|---|---|---|
| `Shao.OQ4.energyLinearCenteringK` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCenteringK._proof_1` | generated helper | propext |
| `Shao.OQ4.energyLinearCenteringThreshold` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCentering_K_pos` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCentering_endpoints` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCentering_exists` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCentering_height_bounds` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCentering_initial_mean` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCentering_interval_growth` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearCentering_law` | explicit theorem | propext, Classical.choice, Quot.sound |

## Shao.OQ4.energyLinearCenteringK

```lean
Shao.OQ4.energyLinearCenteringK : ℝ → ℝ → ℝ
```

## Shao.OQ4.energyLinearCenteringK._proof_1

```lean
Shao.OQ4.energyLinearCenteringK._proof_1 : (3 + 1).AtLeastTwo
```

## Shao.OQ4.energyLinearCenteringThreshold

```lean
Shao.OQ4.energyLinearCenteringThreshold : ℝ → ℝ → ℝ
```

## Shao.OQ4.energyLinearCentering_K_pos

```lean
Shao.OQ4.energyLinearCentering_K_pos : ∀ (M T : ℝ), 0 ≤ M → 0 ≤ T → 0 < Shao.OQ4.energyLinearCenteringK M T
```

## Shao.OQ4.energyLinearCentering_endpoints

```lean
Shao.OQ4.energyLinearCentering_endpoints : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyLinearCenteringThreshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 →
                  ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                    Shao.OQ4.energyLinearMean ν h s (-(Shao.OQ4.energyLinearCenteringK M T / h ^ 2)) < 0 ∧
                      0 < Shao.OQ4.energyLinearMean ν h s (Shao.OQ4.energyLinearCenteringK M T / h ^ 2)
```

## Shao.OQ4.energyLinearCentering_exists

```lean
Shao.OQ4.energyLinearCentering_exists : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyLinearCenteringThreshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 →
                  ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                    ∃ θ, |θ| ≤ Shao.OQ4.energyLinearCenteringK M T / h ^ 2 ∧ Shao.OQ4.energyLinearMean ν h s θ = 0
```

## Shao.OQ4.energyLinearCentering_height_bounds

```lean
Shao.OQ4.energyLinearCentering_height_bounds : ∀ (M T h : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyLinearCenteringThreshold M T ≤ h →
        0 < Shao.OQ4.energyLinearCenteringK M T ∧
          Shao.OQ4.energyLogThreshold M T ≤ h ∧ 2 ≤ h ∧ 0 < Shao.OQ4.energyLinearCenteringK M T / h ^ 2
```

## Shao.OQ4.energyLinearCentering_initial_mean

```lean
Shao.OQ4.energyLinearCentering_initial_mean : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyLinearCenteringThreshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 →
                  ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                    Shao.OQ4.energyLinearMean ν h s 0 = ∫ (x : ℝ), x ∂Shao.OQ4.energyTiltedLaw ν h s ∧
                      |∫ (x : ℝ), x ∂Shao.OQ4.energyTiltedLaw ν h s| ≤ Shao.OQ4.energyLinearVarianceA M T / h ^ 2
```

## Shao.OQ4.energyLinearCentering_interval_growth

```lean
Shao.OQ4.energyLinearCentering_interval_growth : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyLinearCenteringThreshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 →
                  ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                    ∀ (x y : ℝ),
                      x < y →
                        -(Shao.OQ4.energyLinearCenteringK M T / h ^ 2) ≤ x →
                          y ≤ Shao.OQ4.energyLinearCenteringK M T / h ^ 2 →
                            1 / 2 * (y - x) ≤ Shao.OQ4.energyLinearMean ν h s y - Shao.OQ4.energyLinearMean ν h s x
```

## Shao.OQ4.energyLinearCentering_law

```lean
Shao.OQ4.energyLinearCentering_law : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyLinearCenteringThreshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 →
                  ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                    ∃ θ,
                      |θ| ≤ Shao.OQ4.energyLinearCenteringK M T / h ^ 2 ∧
                        Shao.OQ4.energyLinearMean ν h s θ = 0 ∧
                          MeasureTheory.IsProbabilityMeasure (Shao.OQ4.energyLinearTiltLaw ν h s θ) ∧
                            (∀ᵐ (x : ℝ) ∂Shao.OQ4.energyLinearTiltLaw ν h s θ, |x| ≤ 2 * h) ∧
                              MeasureTheory.Integrable (fun x => x) (Shao.OQ4.energyLinearTiltLaw ν h s θ) ∧
                                MeasureTheory.Integrable (fun x => x ^ 2) (Shao.OQ4.energyLinearTiltLaw ν h s θ) ∧
                                  MeasureTheory.Integrable (fun x => |x| ^ 3) (Shao.OQ4.energyLinearTiltLaw ν h s θ) ∧
                                    ∫ (x : ℝ), x ∂Shao.OQ4.energyLinearTiltLaw ν h s θ = 0
```
