# EnergyLinearTiltVarianceWindow declaration and signature ledger

Frozen source SHA256 `a0059db361b524332d85c73eb13577b67de5df1fe4d7f41c3cd2aba9072e5c73`.

The actual compiled module owns **15 new constants=11 explicit declarations (4 transparent definitions+7 theorems)+4 generated helpers**. Every owning module index is checked using `env.getModuleIdxFor?` then its module name; no namespace or name-root filter is applied. All15 actual full signatures were obtained with server `#check @name`; all15 transitive axiom sets were obtained with `#print axioms name`. Names, counts, signature records and axiom records match exactly.

All15 actual records pass `{propext,Classical.choice,Quot.sound}`:11 use the full set,4 only `propext`. The actual full audit and binary remain server-only. This author ledger records mechanical evidence, not independent certification.

| Declaration | Kind | Actual transitive axioms |
|---|---|---|
| `Shao.OQ4.energyLinearVarianceA` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVarianceB` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVarianceB._proof_1` | generated helper | propext |
| `Shao.OQ4.energyLinearVarianceB._proof_2` | generated helper | propext |
| `Shao.OQ4.energyLinearVarianceC` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVarianceC._proof_1` | generated helper | propext |
| `Shao.OQ4.energyLinearVarianceThreshold` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVarianceThreshold._proof_1` | generated helper | propext |
| `Shao.OQ4.energyLinearVariance_constants_nonneg` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVariance_exponential_bound` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVariance_fraction_bounds` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVariance_height_bounds` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVariance_initial_bounds` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVariance_moment_bounds` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearVariance_window` | explicit theorem | propext, Classical.choice, Quot.sound |

## Shao.OQ4.energyLinearVarianceA

```lean
Shao.OQ4.energyLinearVarianceA : ℝ → ℝ → ℝ
```

## Shao.OQ4.energyLinearVarianceB

```lean
Shao.OQ4.energyLinearVarianceB : ℝ → ℝ → ℝ → ℝ
```

## Shao.OQ4.energyLinearVarianceB._proof_1

```lean
Shao.OQ4.energyLinearVarianceB._proof_1 : (1 + 1).AtLeastTwo
```

## Shao.OQ4.energyLinearVarianceB._proof_2

```lean
Shao.OQ4.energyLinearVarianceB._proof_2 : (5 + 1).AtLeastTwo
```

## Shao.OQ4.energyLinearVarianceC

```lean
Shao.OQ4.energyLinearVarianceC : ℝ → ℝ → ℝ → ℝ
```

## Shao.OQ4.energyLinearVarianceC._proof_1

```lean
Shao.OQ4.energyLinearVarianceC._proof_1 : (4 + 1).AtLeastTwo
```

## Shao.OQ4.energyLinearVarianceThreshold

```lean
Shao.OQ4.energyLinearVarianceThreshold : ℝ → ℝ → ℝ → ℝ
```

## Shao.OQ4.energyLinearVarianceThreshold._proof_1

```lean
Shao.OQ4.energyLinearVarianceThreshold._proof_1 : (7 + 1).AtLeastTwo
```

## Shao.OQ4.energyLinearVariance_constants_nonneg

```lean
Shao.OQ4.energyLinearVariance_constants_nonneg : ∀ (M T K : ℝ),
  0 ≤ M →
    0 ≤ T →
      0 ≤ K →
        0 ≤ Shao.OQ4.energyLinearVarianceA M T ∧
          0 ≤ Shao.OQ4.energyLinearVarianceB M T K ∧ 0 ≤ Shao.OQ4.energyLinearVarianceC M T K
```

## Shao.OQ4.energyLinearVariance_exponential_bound

```lean
Shao.OQ4.energyLinearVariance_exponential_bound : ∀ (M T K h t : ℝ),
  0 ≤ M →
    0 ≤ T →
      0 ≤ K →
        Shao.OQ4.energyLinearVarianceThreshold M T K ≤ h → |t| ≤ K / h ^ 2 → Real.exp (2 * h * |t|) ^ 2 ≤ Real.exp 2
```

## Shao.OQ4.energyLinearVariance_fraction_bounds

```lean
Shao.OQ4.energyLinearVariance_fraction_bounds : ∀ (X h : ℝ),
  0 ≤ X → 1 ≤ h → 8 * X ≤ h → X / h ≤ 1 / 8 ∧ X / h ^ 2 ≤ 1 / 8 ∧ X / h ^ 2 ≤ 1 / 2
```

## Shao.OQ4.energyLinearVariance_height_bounds

```lean
Shao.OQ4.energyLinearVariance_height_bounds : ∀ (M T K h : ℝ),
  0 ≤ M →
    0 ≤ T →
      0 ≤ K →
        Shao.OQ4.energyLinearVarianceThreshold M T K ≤ h →
          Shao.OQ4.energyLogThreshold M T ≤ h ∧
            2 ≤ h ∧
              8 * Shao.OQ4.energyLinearVarianceA M T ≤ h ∧
                8 * Shao.OQ4.energyLinearVarianceB M T K ≤ h ∧ 8 * Shao.OQ4.energyLinearVarianceC M T K ≤ h ∧ 8 * K ≤ h
```

## Shao.OQ4.energyLinearVariance_initial_bounds

```lean
Shao.OQ4.energyLinearVariance_initial_bounds : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T K h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      0 ≤ K →
        Shao.OQ4.energyLinearVarianceThreshold M T K ≤ h →
          |s| ≤ T →
            MeasureTheory.Integrable (fun x => x ^ 2) ν →
              MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
                ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                  ∫ (x : ℝ), x ∂ν = 0 →
                    ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                      MeasureTheory.Integrable (fun x => |x|) (Shao.OQ4.energyTiltedLaw ν h s) ∧
                        |∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s - 1| ≤
                            Shao.OQ4.energyLinearVarianceA M T / h ∧
                          |∫ (x : ℝ), x ∂Shao.OQ4.energyTiltedLaw ν h s| ≤ Shao.OQ4.energyLinearVarianceA M T / h ^ 2 ∧
                            ∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s ≤ 2 ∧
                              ∫ (x : ℝ), |x| ∂Shao.OQ4.energyTiltedLaw ν h s ≤ 3 ∧
                                |∫ (x : ℝ), x ∂Shao.OQ4.energyTiltedLaw ν h s| ≤ 1 ∧
                                  ∫ (x : ℝ), |x| ^ 3 ∂Shao.OQ4.energyTiltedLaw ν h s ≤
                                    Shao.OQ4.energyLinearVarianceA M T
```

## Shao.OQ4.energyLinearVariance_moment_bounds

```lean
Shao.OQ4.energyLinearVariance_moment_bounds : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T K h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      0 ≤ K →
        Shao.OQ4.energyLinearVarianceThreshold M T K ≤ h →
          |s| ≤ T →
            MeasureTheory.Integrable (fun x => x ^ 2) ν →
              MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
                ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                  ∫ (x : ℝ), x ∂ν = 0 →
                    ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                      ∀ (t : ℝ),
                        |t| ≤ K / h ^ 2 →
                          |∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t -
                                  ∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s| ≤
                              Shao.OQ4.energyLinearVarianceB M T K / h ^ 2 ∧
                            |∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t - 1| ≤
                                Shao.OQ4.energyLinearVarianceA M T / h + Shao.OQ4.energyLinearVarianceB M T K / h ^ 2 ∧
                              Shao.OQ4.energyLinearVarianceA M T / h + Shao.OQ4.energyLinearVarianceB M T K / h ^ 2 ≤
                                  1 / 4 ∧
                                |Shao.OQ4.energyLinearMean ν h s t| ≤ Shao.OQ4.energyLinearVarianceC M T K / h ^ 2 ∧
                                  Shao.OQ4.energyLinearVarianceC M T K / h ^ 2 ≤ 1 / 2
```

## Shao.OQ4.energyLinearVariance_window

```lean
Shao.OQ4.energyLinearVariance_window : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (M T K h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      0 ≤ K →
        Shao.OQ4.energyLinearVarianceThreshold M T K ≤ h →
          |s| ≤ T →
            MeasureTheory.Integrable (fun x => x ^ 2) ν →
              MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
                ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                  ∫ (x : ℝ), x ∂ν = 0 →
                    ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                      ∀ (t : ℝ),
                        |t| ≤ K / h ^ 2 →
                          MeasureTheory.IsProbabilityMeasure (Shao.OQ4.energyLinearTiltLaw ν h s t) ∧
                            MeasureTheory.Integrable (fun x => x) (Shao.OQ4.energyLinearTiltLaw ν h s t) ∧
                              MeasureTheory.Integrable (fun x => x ^ 2) (Shao.OQ4.energyLinearTiltLaw ν h s t) ∧
                                MeasureTheory.Integrable (fun x => (x - Shao.OQ4.energyLinearMean ν h s t) ^ 2)
                                    (Shao.OQ4.energyLinearTiltLaw ν h s t) ∧
                                  ∫ (x : ℝ),
                                        (x - Shao.OQ4.energyLinearMean ν h s t) ^
                                          2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t =
                                      ∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t -
                                        Shao.OQ4.energyLinearMean ν h s t ^ 2 ∧
                                    (1 / 2 ≤
                                          ∫ (x : ℝ),
                                            (x - Shao.OQ4.energyLinearMean ν h s t) ^
                                              2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t ∧
                                        ∫ (x : ℝ),
                                            (x - Shao.OQ4.energyLinearMean ν h s t) ^
                                              2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t ≤
                                          2) ∧
                                      HasDerivAt (Shao.OQ4.energyLinearMean ν h s)
                                        (∫ (x : ℝ),
                                          (x - Shao.OQ4.energyLinearMean ν h s t) ^
                                            2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t)
                                        t
```
