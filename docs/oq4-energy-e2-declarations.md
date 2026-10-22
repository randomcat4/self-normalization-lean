# EnergyE2Bounds declaration and signature ledger

Frozen source SHA256 `41b7343861549f55ae86cddb514a5ed55612448b1ab0efc1e3bb580182746ca8`.

The actual compiled module owns **10 new constants=9 explicit declarations (3 definitions+6 theorems)+1 generated helper**. All source-body declarations with `env.getModuleIdxFor? name == none` after33 old imports were separately enumerated. Their10 names and transitive axiom records equal the complete module-owner enumeration after34 actual imports. Neither enumeration filters namespaces,name roots,private declarations or generated helpers.

Every full signature below is the curated actual server `#check @name` output; every axiom set is the actual transitive `#print axioms name` result. All10 names/signatures/axiom records match exactly.9 use `{propext,Classical.choice,Quot.sound}`,1 only `propext`; no unexpected axiom. The only generated helper is `Shao.OQ4.energyE2Constant._proof_1`.

Raw source-audit/module-audit logs and binary stay server-only in repro_outputs/oq4-energy-e2/. This ledger records author mechanical evidence, not independent final certification.

| Declaration | Kind | Actual transitive axioms |
|---|---|---|
| `Shao.OQ4.energyE2Conclusion` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2Constant` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2Constant._proof_1` | generated helper | propext |
| `Shao.OQ4.energyE2Constant_dominates` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2Threshold` | explicit definition | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2_abs_sub_zero_bound` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2_common_bounds` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2_fixed_law_bounds` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2_log_bound` | explicit theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyE2_mean_small` | explicit theorem | propext, Classical.choice, Quot.sound |

## Shao.OQ4.energyE2Conclusion

```lean
Shao.OQ4.energyE2Conclusion : MeasureTheory.Measure ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop
```

## Shao.OQ4.energyE2Constant

```lean
Shao.OQ4.energyE2Constant : ℝ → ℝ → ℝ
```

## Shao.OQ4.energyE2Constant._proof_1

```lean
Shao.OQ4.energyE2Constant._proof_1 : (1 + 1).AtLeastTwo
```

## Shao.OQ4.energyE2Constant_dominates

```lean
Shao.OQ4.energyE2Constant_dominates : ∀ (M T : ℝ),
  0 ≤ M →
    0 ≤ T →
      1 ≤ Shao.OQ4.energyE2Constant M T ∧
        Shao.OQ4.energyLinearCenteringK M T ≤ Shao.OQ4.energyE2Constant M T ∧
          Shao.OQ4.energyLinearCenteringK M T *
                (Shao.OQ4.energyLinearVarianceA M T + 2 * Shao.OQ4.energyLinearCenteringK M T) ≤
              Shao.OQ4.energyE2Constant M T ∧
            Shao.OQ4.energyLinearVarianceA M T +
                  Shao.OQ4.energyLinearVarianceB M T (Shao.OQ4.energyLinearCenteringK M T) ≤
                Shao.OQ4.energyE2Constant M T ∧
              Real.exp 2 * Shao.OQ4.energyLinearVarianceA M T ≤ Shao.OQ4.energyE2Constant M T
```

## Shao.OQ4.energyE2Threshold

```lean
Shao.OQ4.energyE2Threshold : ℝ → ℝ → ℝ
```

## Shao.OQ4.energyE2_abs_sub_zero_bound

```lean
Shao.OQ4.energyE2_abs_sub_zero_bound : ∀ (f f' : ℝ → ℝ) (C t : ℝ),
  Continuous f → (∀ (u : ℝ), HasDerivAt f (f' u) u) → (∀ (u : ℝ), |u| ≤ |t| → |f' u| ≤ C) → |f t - f 0| ≤ C * |t|
```

## Shao.OQ4.energyE2_common_bounds

```lean
Shao.OQ4.energyE2_common_bounds : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyE2Threshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 → ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M → ∃ θ, Shao.OQ4.energyE2Conclusion ν M T h s θ
```

## Shao.OQ4.energyE2_fixed_law_bounds

```lean
Shao.OQ4.energyE2_fixed_law_bounds : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (T h s : ℝ),
  0 ≤ T →
    Shao.OQ4.energyE2Threshold (∫ (x : ℝ), |x| ^ 3 ∂ν) T ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
            ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
              ∫ (x : ℝ), x ∂ν = 0 → ∃ θ, Shao.OQ4.energyE2Conclusion ν (∫ (x : ℝ), |x| ^ 3 ∂ν) T h s θ
```

## Shao.OQ4.energyE2_log_bound

```lean
Shao.OQ4.energyE2_log_bound : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyE2Threshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 →
                  ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                    ∀ (t : ℝ),
                      |t| ≤ Shao.OQ4.energyLinearCenteringK M T / h ^ 2 →
                        |Real.log (Shao.OQ4.energyLinearNormalizer ν h s t)| ≤
                          Shao.OQ4.energyLinearCenteringK M T *
                              (Shao.OQ4.energyLinearVarianceA M T + 2 * Shao.OQ4.energyLinearCenteringK M T) /
                            h ^ 4
```

## Shao.OQ4.energyE2_mean_small

```lean
Shao.OQ4.energyE2_mean_small : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (M T h s : ℝ),
  0 ≤ M →
    0 ≤ T →
      Shao.OQ4.energyE2Threshold M T ≤ h →
        |s| ≤ T →
          MeasureTheory.Integrable (fun x => x ^ 2) ν →
            MeasureTheory.Integrable (fun x => |x| ^ 3) ν →
              ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
                ∫ (x : ℝ), x ∂ν = 0 →
                  ∫ (x : ℝ), |x| ^ 3 ∂ν ≤ M →
                    ∀ (u : ℝ),
                      |u| ≤ Shao.OQ4.energyLinearCenteringK M T / h ^ 2 →
                        |Shao.OQ4.energyLinearMean ν h s u| ≤
                          (Shao.OQ4.energyLinearVarianceA M T + 2 * Shao.OQ4.energyLinearCenteringK M T) / h ^ 2
```
