# EnergyLinearTiltComparisons declaration and signature ledger

Frozen source SHA256 `f1aa93d33998f5365d236b9f96e2e04cab4e6235672a7b634988cd2330497cd4`.

The actual compiled module owns **10 new constants=8 explicit theorems+2 generated helpers**. There are **0 definitions**, 2 explicit grouped conclusion theorems and 6 explicit supporting theorems. The two grouped conclusions contain exactly the four raw and three normalized frozen comparisons.

All declarations are enumerated by exact owner module index (`env.getModuleIdxFor?`, then `env.header.moduleNames[idx] == Shao.OQ4.EnergyLinearTiltComparisons`), with no namespace/name-root filter. This includes the generated `Shao.OQ4.energyLinearSecondNumerator.eq_1` under the imported definition's name. Each full signature below is the curated output of actual server `#check @name`; each axiom set is the actual transitive `#print axioms name` result. All10 names and signature/axiom records match, with no omissions or extras.

All10 passed the standard whitelist:9 use `{propext,Classical.choice,Quot.sound}`,1 only `{propext}`. Raw audit remains server-only at `repro_outputs/oq4-energy-linear-comparisons/audit.log`. This mechanical author ledger is not independent final certification.

| Declaration | Kind | Actual transitive axioms |
|---|---|---|
| `Shao.OQ4.energyLinearComparison_abs_exp_sub_one` | explicit support theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearComparison_div_deviation` | explicit support theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearComparison_exp_sub_one_bound` | explicit support theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearComparison_power_deviation` | explicit support theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearComparison_power_integrable` | explicit support theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearComparison_power_integrable._simp_1_1` | generated helper | propext |
| `Shao.OQ4.energyLinearComparison_reciprocal_bound` | explicit support theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinearSecondNumerator.eq_1` | generated helper | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinear_normalized_comparisons` | explicit conclusion theorem | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyLinear_raw_comparisons` | explicit conclusion theorem | propext, Classical.choice, Quot.sound |

## Shao.OQ4.energyLinearComparison_abs_exp_sub_one

```lean
Shao.OQ4.energyLinearComparison_abs_exp_sub_one : ∀ (y : ℝ), |Real.exp y - 1| ≤ Real.exp |y| * |y|
```

## Shao.OQ4.energyLinearComparison_div_deviation

```lean
Shao.OQ4.energyLinearComparison_div_deviation : ∀ (A b L D τ u v : ℝ),
  0 < L →
    0 ≤ D →
      0 ≤ τ →
        0 ≤ u → 0 ≤ v → 1 / L ≤ D → |A - b| ≤ D * τ * v → |L - 1| ≤ D * τ * u → |A / L - b| ≤ D ^ 2 * τ * (v + |b| * u)
```

## Shao.OQ4.energyLinearComparison_exp_sub_one_bound

```lean
Shao.OQ4.energyLinearComparison_exp_sub_one_bound : ∀ (h t x : ℝ),
  |x| ≤ 2 * h → |Real.exp (t * x) - 1| ≤ Real.exp (2 * h * |t|) * |t| * |x|
```

## Shao.OQ4.energyLinearComparison_power_deviation

```lean
Shao.OQ4.energyLinearComparison_power_deviation : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (k : ℕ) (t : ℝ),
              |∫ (x : ℝ), x ^ k * Real.exp (t * x) ∂Shao.OQ4.energyTiltedLaw ν h s -
                    ∫ (x : ℝ), x ^ k ∂Shao.OQ4.energyTiltedLaw ν h s| ≤
                Real.exp (2 * h * |t|) * |t| * ∫ (x : ℝ), |x| ^ (k + 1) ∂Shao.OQ4.energyTiltedLaw ν h s
```

## Shao.OQ4.energyLinearComparison_power_integrable

```lean
Shao.OQ4.energyLinearComparison_power_integrable : ∀ (ν : MeasureTheory.Measure ℝ)
  [MeasureTheory.IsProbabilityMeasure ν] (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (k : ℕ) (t : ℝ),
              MeasureTheory.Integrable (fun x => x ^ k * Real.exp (t * x)) (Shao.OQ4.energyTiltedLaw ν h s)
```

## Shao.OQ4.energyLinearComparison_power_integrable._simp_1_1

```lean
@Shao.OQ4.energyLinearComparison_power_integrable._simp_1_1 : ∀ {α : Type u_1} [inst : Preorder α] (a : α),
  (a ≤ a) = True
```

## Shao.OQ4.energyLinearComparison_reciprocal_bound

```lean
Shao.OQ4.energyLinearComparison_reciprocal_bound : ∀ (ν : MeasureTheory.Measure ℝ)
  [MeasureTheory.IsProbabilityMeasure ν] (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 → ∀ (t : ℝ), 1 / Shao.OQ4.energyLinearNormalizer ν h s t ≤ Real.exp (2 * h * |t|)
```

## Shao.OQ4.energyLinearSecondNumerator.eq_1

```lean
Shao.OQ4.energyLinearSecondNumerator.eq_1 : ∀ (ν : MeasureTheory.Measure ℝ) (h s t : ℝ),
  Shao.OQ4.energyLinearSecondNumerator ν h s t = ∫ (x : ℝ), x ^ 2 * Real.exp (t * x) ∂Shao.OQ4.energyTiltedLaw ν h s
```

## Shao.OQ4.energyLinear_normalized_comparisons

```lean
Shao.OQ4.energyLinear_normalized_comparisons : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (t : ℝ),
              |Shao.OQ4.energyLinearMean ν h s t - ∫ (x : ℝ), x ∂Shao.OQ4.energyTiltedLaw ν h s| ≤
                  Real.exp (2 * h * |t|) ^ 2 * |t| *
                    (∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s +
                      |∫ (x : ℝ), x ∂Shao.OQ4.energyTiltedLaw ν h s| * ∫ (x : ℝ), |x| ∂Shao.OQ4.energyTiltedLaw ν h s) ∧
                |∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyLinearTiltLaw ν h s t -
                        ∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s| ≤
                    Real.exp (2 * h * |t|) ^ 2 * |t| *
                      (∫ (x : ℝ), |x| ^ 3 ∂Shao.OQ4.energyTiltedLaw ν h s +
                        (∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s) *
                          ∫ (x : ℝ), |x| ∂Shao.OQ4.energyTiltedLaw ν h s) ∧
                  ∫ (x : ℝ), |x| ^ 3 ∂Shao.OQ4.energyLinearTiltLaw ν h s t ≤
                    Real.exp (2 * h * |t|) ^ 2 * ∫ (x : ℝ), |x| ^ 3 ∂Shao.OQ4.energyTiltedLaw ν h s
```

## Shao.OQ4.energyLinear_raw_comparisons

```lean
Shao.OQ4.energyLinear_raw_comparisons : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (t : ℝ),
              |Shao.OQ4.energyLinearNormalizer ν h s t - 1| ≤
                  Real.exp (2 * h * |t|) * |t| * ∫ (x : ℝ), |x| ∂Shao.OQ4.energyTiltedLaw ν h s ∧
                |Shao.OQ4.energyLinearFirstNumerator ν h s t - ∫ (x : ℝ), x ∂Shao.OQ4.energyTiltedLaw ν h s| ≤
                    Real.exp (2 * h * |t|) * |t| * ∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s ∧
                  |Shao.OQ4.energyLinearSecondNumerator ν h s t - ∫ (x : ℝ), x ^ 2 ∂Shao.OQ4.energyTiltedLaw ν h s| ≤
                      Real.exp (2 * h * |t|) * |t| * ∫ (x : ℝ), |x| ^ 3 ∂Shao.OQ4.energyTiltedLaw ν h s ∧
                    0 ≤ Shao.OQ4.energyLinearThirdNumerator ν h s t ∧
                      Shao.OQ4.energyLinearThirdNumerator ν h s t ≤
                        Real.exp (2 * h * |t|) * ∫ (x : ℝ), |x| ^ 3 ∂Shao.OQ4.energyTiltedLaw ν h s
```
