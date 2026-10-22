# EnergyPathLaw 全部新增常量与完整签名

冻结源 SHA256 `4feb2d7024c75f6cabeab4f46bf81d5430f70a5d30cc86de8dde3250b3191536`。

实际目标模块拥有22个常量：9个公开定理、1个透明定义、4个私有定理、8个生成常量。通过 getModuleIdxFor? 后检查实际模块名 Shao.OQ4.EnergyPathLaw 全取；不按命名空间或根名称筛选。所有22个签名和22个传递公理记录均来自服务器实际 #check @name 与 #print axioms name，并严格逐名对应。16个使用标准三公理，6个仅用 propext；没有额外公理。

所有原始审计日志和编译产物仅保留在服务器；此处是整理后的签名账，不是独立最终审稿票。

| 常量 | 类别 | 实际传递公理 |
|---|---|---|
| `Shao.OQ4.energyPathIntegrand` | 透明定义 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathIntegrand.eq_1` | 生成常量 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathIntegrand_integrable` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathIntegrand_le` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathIntegrand_measurable` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathIntegrand_nonneg` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathLaw_integral` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathLaw_integral_iid` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathLaw_real_apply` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.energyPathLaw_withDensity` | 公开定理 | propext, Classical.choice, Quot.sound |
| `Shao.OQ4.finitePi_withDensity` | 公开定理 | propext, Classical.choice, Quot.sound |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density` | 私有定理 | propext, Classical.choice, Quot.sound |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_1` | 生成常量 | propext |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_2` | 生成常量 | propext |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_3` | 生成常量 | propext |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_4` | 生成常量 | propext |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_5` | 生成常量 | propext |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_6` | 生成常量 | propext, Classical.choice, Quot.sound |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_7` | 生成常量 | propext |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_density_integrable` | 私有定理 | propext, Classical.choice, Quot.sound |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_energy_le` | 私有定理 | propext, Classical.choice, Quot.sound |
| `_private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.finitePi_withDensity_lintegral` | 私有定理 | propext, Classical.choice, Quot.sound |

## Shao.OQ4.energyPathIntegrand

```lean
@Shao.OQ4.energyPathIntegrand : {n : ℕ} → ℝ → ℝ → Shao.Path n → ℝ
```

## Shao.OQ4.energyPathIntegrand.eq_1

```lean
@Shao.OQ4.energyPathIntegrand.eq_1 : ∀ {n : ℕ} (h s : ℝ) (a : Shao.Path n),
  Shao.OQ4.energyPathIntegrand h s a = if a ∈ Shao.closedStrip h then Real.exp (s * (Shao.energy a - ↑n) / h ^ 2) else 0
```

## Shao.OQ4.energyPathIntegrand_integrable

```lean
Shao.OQ4.energyPathIntegrand_integrable : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h → |s| ≤ T → MeasureTheory.Integrable (Shao.OQ4.energyPathIntegrand h s) (MeasureTheory.Measure.pi fun x => ν)
```

## Shao.OQ4.energyPathIntegrand_le

```lean
@Shao.OQ4.energyPathIntegrand_le : ∀ {n : ℕ} (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        ∀ (a : Shao.Path n), Shao.OQ4.energyPathIntegrand h s a ≤ Real.exp (-s * ↑n / h ^ 2) * Real.exp (4 * T * ↑n)
```

## Shao.OQ4.energyPathIntegrand_measurable

```lean
@Shao.OQ4.energyPathIntegrand_measurable : ∀ {n : ℕ} (h s : ℝ), 0 ≤ h → Measurable (Shao.OQ4.energyPathIntegrand h s)
```

## Shao.OQ4.energyPathIntegrand_nonneg

```lean
@Shao.OQ4.energyPathIntegrand_nonneg : ∀ {n : ℕ} (h s : ℝ) (a : Shao.Path n), 0 ≤ Shao.OQ4.energyPathIntegrand h s a
```

## Shao.OQ4.energyPathLaw_integral

```lean
Shao.OQ4.energyPathLaw_integral : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            MeasureTheory.Integrable (Shao.OQ4.energyPathIntegrand h s) (MeasureTheory.Measure.pi fun x => ν) ∧
              (∫ (a : Fin n → ℝ), Shao.OQ4.energyPathIntegrand h s a ∂MeasureTheory.Measure.pi fun x => ν) =
                Real.exp (-s * ↑n / h ^ 2) * Shao.OQ4.energyNormalizer ν h s ^ n *
                  (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real (Shao.closedStrip h)
```

## Shao.OQ4.energyPathLaw_integral_iid

```lean
@Shao.OQ4.energyPathLaw_integral_iid : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (p : MeasureTheory.Measure Ω)
  [MeasureTheory.IsProbabilityMeasure p] (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (X : Fin n → Ω → ℝ),
              (∀ (i : Fin n), Measurable (X i)) →
                ProbabilityTheory.iIndepFun X p →
                  (∀ (i : Fin n), ProbabilityTheory.IdentDistrib (X i) id p ν) →
                    MeasureTheory.Integrable
                        (fun ω => Shao.OQ4.energyPathIntegrand h s (Shao.Probability.samplePath X ω)) p ∧
                      ∫ (ω : Ω), Shao.OQ4.energyPathIntegrand h s (Shao.Probability.samplePath X ω) ∂p =
                        Real.exp (-s * ↑n / h ^ 2) * Shao.OQ4.energyNormalizer ν h s ^ n *
                          (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real (Shao.closedStrip h)
```

## Shao.OQ4.energyPathLaw_real_apply

```lean
Shao.OQ4.energyPathLaw_real_apply : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (A : Set (Shao.Path n)),
              MeasurableSet A →
                (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real A =
                  ∫ (a : Fin n → ℝ) in A,
                    ∏ i,
                      Shao.OQ4.energyWeight h s (a i) /
                        Shao.OQ4.energyNormalizer ν h s ∂MeasureTheory.Measure.pi fun x => ν
```

## Shao.OQ4.energyPathLaw_withDensity

```lean
Shao.OQ4.energyPathLaw_withDensity : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s) =
              (MeasureTheory.Measure.pi fun x => ν).withDensity fun a =>
                ENNReal.ofReal (∏ i, Shao.OQ4.energyWeight h s (a i) / Shao.OQ4.energyNormalizer ν h s)
```

## Shao.OQ4.finitePi_withDensity

```lean
Shao.OQ4.finitePi_withDensity : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (d : ℝ → ENNReal),
  Measurable d →
    ∀ [MeasureTheory.IsProbabilityMeasure (ν.withDensity d)] (n : ℕ),
      (MeasureTheory.Measure.pi fun x => ν.withDensity d) =
        (MeasureTheory.Measure.pi fun x => ν).withDensity fun a => ∏ i, d (a i)
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density

```lean
Shao.OQ4.energyPath_closed_density✝ : ∀ (ν : MeasureTheory.Measure ℝ) (n : ℕ) (h s : ℝ),
  0 < Shao.OQ4.energyNormalizer ν h s →
    ∀ a ∈ Shao.closedStrip h,
      Shao.OQ4.energyNormalizer ν h s ^ n * ∏ i, Shao.OQ4.energyWeight h s (a i) / Shao.OQ4.energyNormalizer ν h s =
        Real.exp (s * Shao.energy a / h ^ 2)
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_1

```lean
@Shao.OQ4.energyPath_closed_density._simp_1_1✝ : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2],
  (2 = 0) = False
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_2

```lean
@Shao.OQ4.energyPath_closed_density._simp_1_2✝ : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3],
  (3 = 0) = False
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_3

```lean
@Shao.OQ4.energyPath_closed_density._simp_1_3✝ : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4],
  (4 = 0) = False
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_4

```lean
@Shao.OQ4.energyPath_closed_density._simp_1_4✝ : ∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀]
  [NoZeroDivisors M₀] {a b : M₀}, a ≠ 0 → b ≠ 0 → (a * b = 0) = False
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_5

```lean
@Shao.OQ4.energyPath_closed_density._simp_1_5✝ : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀]
  (n : ℕ), a ≠ 0 → (a ^ n = 0) = False
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_6

```lean
@Shao.OQ4.energyPath_closed_density._simp_1_6✝ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ),
  a ≠ 0 → (a ^ n = 0) = False
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_closed_density._simp_1_7

```lean
@Shao.OQ4.energyPath_closed_density._simp_1_7✝ : ∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ),
  (↑n + 1 = 0) = False
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_density_integrable

```lean
Shao.OQ4.energyPath_density_integrable✝ : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun a => ∏ i, Shao.OQ4.energyWeight h s (a i) / Shao.OQ4.energyNormalizer ν h s)
          (MeasureTheory.Measure.pi fun x => ν)
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.energyPath_energy_le

```lean
@Shao.OQ4.energyPath_energy_le✝ : ∀ {n : ℕ} (h : ℝ), ∀ a ∈ Shao.closedStrip h, Shao.energy a ≤ 4 * ↑n * h ^ 2
```

## _private.Shao.OQ4.EnergyPathLaw.0.Shao.OQ4.finitePi_withDensity_lintegral

```lean
Shao.OQ4.finitePi_withDensity_lintegral✝ : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (d : ℝ → ENNReal),
  Measurable d →
    ∀ [MeasureTheory.IsProbabilityMeasure (ν.withDensity d)] (n : ℕ) (F : Shao.Path n → ENNReal),
      Measurable F →
        (∫⁻ (a : Fin n → ℝ), F a ∂MeasureTheory.Measure.pi fun x => ν.withDensity d) =
          ∫⁻ (a : Fin n → ℝ), (∏ i, d (a i)) * F a ∂MeasureTheory.Measure.pi fun x => ν
```
