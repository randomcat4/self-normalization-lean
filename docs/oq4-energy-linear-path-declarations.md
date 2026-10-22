# EnergyLinearPathLaw 声明清单

源码 SHA256：`039ad7326ea9a80e476f50bf3f46dd0078c2c61f6786f15a6d72f3ba0c227afb`；18042字节。

实际12条公开定理、1条公开定义、2条显式私有定理、8条自动生成声明；完整模块拥有23条声明。完整源码无过滤检查与导入模块检查的名称、种类、签名类型、公理集合逐项一致（导入后私有名显示的†标记仅属于声明名头部，不属于类型）。

## 公开定理

### `Shao.OQ4.energyLinearPathIntegrand_nonneg`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathIntegrand_nonneg : ∀ {n : ℕ} (h t : ℝ) (a : Shao.Path n),
  0 ≤ Shao.OQ4.energyLinearPathIntegrand h t a
```

### `Shao.OQ4.energyLinearPathIntegrand_measurable`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathIntegrand_measurable : ∀ {n : ℕ} (h t : ℝ),
  0 ≤ h → Measurable (Shao.OQ4.energyLinearPathIntegrand h t)
```

### `Shao.OQ4.energyLinearPathIntegrand_closed_bounds`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathIntegrand_closed_bounds : ∀ {n : ℕ} (h t : ℝ),
  ∀ a ∈ Shao.closedStrip h,
    Real.exp (-|t| * h) ≤ Shao.OQ4.energyLinearPathIntegrand h t a ∧
      Shao.OQ4.energyLinearPathIntegrand h t a ≤ Real.exp (|t| * h)
```

### `Shao.OQ4.energyLinearPathIntegrand_le`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathIntegrand_le : ∀ {n : ℕ} (h t : ℝ) (a : Shao.Path n),
  Shao.OQ4.energyLinearPathIntegrand h t a ≤ Real.exp (|t| * h)
```

### `Shao.OQ4.energyLinearPathIntegrand_integrable`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
Shao.OQ4.energyLinearPathIntegrand_integrable : ∀ (ρ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ρ]
  (n : ℕ) (h t : ℝ),
  0 ≤ h → MeasureTheory.Integrable (Shao.OQ4.energyLinearPathIntegrand h t) (MeasureTheory.Measure.pi fun x => ρ)
```

### `Shao.OQ4.energyLinearPathLaw_withDensity`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
Shao.OQ4.energyLinearPathLaw_withDensity : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
  (n : ℕ) (T h s t : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyLinearTiltLaw ν h s t) =
              (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).withDensity fun a =>
                ENNReal.ofReal (Real.exp (t * Shao.prefixSum a n) / Shao.OQ4.energyLinearNormalizer ν h s t ^ n)
```

### `Shao.OQ4.energyLinearPathLaw_integral`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
Shao.OQ4.energyLinearPathLaw_integral : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s t : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            MeasureTheory.Integrable (Shao.OQ4.energyLinearPathIntegrand h t)
                (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyLinearTiltLaw ν h s t) ∧
              (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real (Shao.closedStrip h) =
                Shao.OQ4.energyLinearNormalizer ν h s t ^ n *
                  ∫ (a : Fin n → ℝ),
                    Shao.OQ4.energyLinearPathIntegrand h t
                      a ∂MeasureTheory.Measure.pi fun x => Shao.OQ4.energyLinearTiltLaw ν h s t
```

### `Shao.OQ4.energyLinearPathLaw_sandwich`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
Shao.OQ4.energyLinearPathLaw_sandwich : ∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s t : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            Shao.OQ4.energyLinearNormalizer ν h s t ^ n * Real.exp (-|t| * h) *
                  (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyLinearTiltLaw ν h s t).real (Shao.closedStrip h) ≤
                (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real (Shao.closedStrip h) ∧
              (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real (Shao.closedStrip h) ≤
                Shao.OQ4.energyLinearNormalizer ν h s t ^ n * Real.exp (|t| * h) *
                  (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyLinearTiltLaw ν h s t).real (Shao.closedStrip h)
```

### `Shao.OQ4.energyLinearPathLaw_integral_iid`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral_iid : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (p : MeasureTheory.Measure Ω)
  [MeasureTheory.IsProbabilityMeasure p] (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ)
  (T h s t : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (X : Fin n → Ω → ℝ),
              (∀ (i : Fin n), Measurable (X i)) →
                ProbabilityTheory.iIndepFun X p →
                  (∀ (i : Fin n), ProbabilityTheory.IdentDistrib (X i) id p (Shao.OQ4.energyLinearTiltLaw ν h s t)) →
                    MeasureTheory.Integrable
                        (fun ω => Shao.OQ4.energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω)) p ∧
                      (∫ (ω : Ω), Shao.OQ4.energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p =
                          ∫ (a : Fin n → ℝ),
                            Shao.OQ4.energyLinearPathIntegrand h t
                              a ∂MeasureTheory.Measure.pi fun x => Shao.OQ4.energyLinearTiltLaw ν h s t) ∧
                        (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real (Shao.closedStrip h) =
                          Shao.OQ4.energyLinearNormalizer ν h s t ^ n *
                            ∫ (ω : Ω), Shao.OQ4.energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p
```

### `Shao.OQ4.energyLinearPathLaw_probability_iid`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathLaw_probability_iid : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω]
  (p : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure p] (ν : MeasureTheory.Measure ℝ)
  [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ) (T h s t : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (X : Fin n → Ω → ℝ),
              (∀ (i : Fin n), Measurable (X i)) →
                ProbabilityTheory.iIndepFun X p →
                  (∀ (i : Fin n), ProbabilityTheory.IdentDistrib (X i) id p (Shao.OQ4.energyLinearTiltLaw ν h s t)) →
                    (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyLinearTiltLaw ν h s t).real (Shao.closedStrip h) =
                      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h}
```

### `Shao.OQ4.energyLinearPathLaw_base_probability_iid`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathLaw_base_probability_iid : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω]
  (p : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure p] (ν : MeasureTheory.Measure ℝ)
  [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ) (T h s : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (X : Fin n → Ω → ℝ),
              (∀ (i : Fin n), Measurable (X i)) →
                ProbabilityTheory.iIndepFun X p →
                  (∀ (i : Fin n), ProbabilityTheory.IdentDistrib (X i) id p (Shao.OQ4.energyTiltedLaw ν h s)) →
                    (MeasureTheory.Measure.pi fun x => Shao.OQ4.energyTiltedLaw ν h s).real (Shao.closedStrip h) =
                      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h}
```

### `Shao.OQ4.energyLinearPathLaw_iid`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathLaw_iid : ∀ {Ω₀ : Type u_1} {Ω : Type u_2} [inst : MeasurableSpace Ω₀]
  [inst_1 : MeasurableSpace Ω] (p₀ : MeasureTheory.Measure Ω₀) [MeasureTheory.IsProbabilityMeasure p₀]
  (p : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure p] (ν : MeasureTheory.Measure ℝ)
  [MeasureTheory.IsProbabilityMeasure ν] (n : ℕ) (T h s t : ℝ),
  0 ≤ T →
    1 ≤ h →
      |s| ≤ T →
        MeasureTheory.Integrable (fun x => x ^ 2) ν →
          ∫ (x : ℝ), x ^ 2 ∂ν = 1 →
            ∀ (X₀ : Fin n → Ω₀ → ℝ),
              (∀ (i : Fin n), Measurable (X₀ i)) →
                ProbabilityTheory.iIndepFun X₀ p₀ →
                  (∀ (i : Fin n), ProbabilityTheory.IdentDistrib (X₀ i) id p₀ (Shao.OQ4.energyTiltedLaw ν h s)) →
                    ∀ (X : Fin n → Ω → ℝ),
                      (∀ (i : Fin n), Measurable (X i)) →
                        ProbabilityTheory.iIndepFun X p →
                          (∀ (i : Fin n),
                              ProbabilityTheory.IdentDistrib (X i) id p (Shao.OQ4.energyLinearTiltLaw ν h s t)) →
                            MeasureTheory.Integrable
                                (fun ω => Shao.OQ4.energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω)) p ∧
                              p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} =
                                  Shao.OQ4.energyLinearNormalizer ν h s t ^ n *
                                    ∫ (ω : Ω),
                                      Shao.OQ4.energyLinearPathIntegrand h t (Shao.Probability.samplePath X ω) ∂p ∧
                                Shao.OQ4.energyLinearNormalizer ν h s t ^ n * Real.exp (-|t| * h) *
                                      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h} ≤
                                    p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} ∧
                                  p₀.real {ω | Shao.Probability.samplePath X₀ ω ∈ Shao.closedStrip h} ≤
                                    Shao.OQ4.energyLinearNormalizer ν h s t ^ n * Real.exp (|t| * h) *
                                      p.real {ω | Shao.Probability.samplePath X ω ∈ Shao.closedStrip h}
```

## 公开定义

### `Shao.OQ4.energyLinearPathIntegrand`

种类：definition；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathIntegrand : {n : ℕ} → ℝ → ℝ → Shao.Path n → ℝ
```

## 显式私有定理

### `_private.Shao.OQ4.EnergyLinearPathLaw.0.Shao.OQ4.energyLinearPath_density_mul`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPath_density_mul✝ : ∀ {n : ℕ} (h t L : ℝ) (a : Shao.Path n),
  Real.exp (t * Shao.prefixSum a n) / L ^ n * Shao.OQ4.energyLinearPathIntegrand h t a =
    1 / L ^ n * (Shao.closedStrip h).indicator (fun x => 1) a
```

### `_private.Shao.OQ4.EnergyLinearPathLaw.0.Shao.OQ4.energyLinearPath_iid_real_apply`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPath_iid_real_apply✝ : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (p : MeasureTheory.Measure Ω)
  [MeasureTheory.IsProbabilityMeasure p] (ρ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ρ] {n : ℕ}
  (X : Fin n → Ω → ℝ),
  (∀ (i : Fin n), Measurable (X i)) →
    ProbabilityTheory.iIndepFun X p →
      (∀ (i : Fin n), ProbabilityTheory.IdentDistrib (X i) id p ρ) →
        ∀ (A : Set (Shao.Path n)),
          MeasurableSet A →
            (MeasureTheory.Measure.pi fun x => ρ).real A = p.real {ω | Shao.Probability.samplePath X ω ∈ A}
```

## 自动生成声明

### `Shao.OQ4.energyLinearPathIntegrand.eq_1`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathIntegrand.eq_1 : ∀ {n : ℕ} (h t : ℝ) (a : Shao.Path n),
  Shao.OQ4.energyLinearPathIntegrand h t a = if a ∈ Shao.closedStrip h then Real.exp (-t * Shao.prefixSum a n) else 0
```

### `Shao.OQ4.energyLinearPathLaw_integral._simp_1_1`

种类：theorem；传递公理：`propext`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral._simp_1_1 : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : OfNat α 2] [NeZero 2],
  (2 = 0) = False
```

### `Shao.OQ4.energyLinearPathLaw_integral._simp_1_2`

种类：theorem；传递公理：`propext`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral._simp_1_2 : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : OfNat α 3] [NeZero 3],
  (3 = 0) = False
```

### `Shao.OQ4.energyLinearPathLaw_integral._simp_1_3`

种类：theorem；传递公理：`propext`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral._simp_1_3 : ∀ {α : Type u_1} [inst : Zero α] [inst_1 : OfNat α 4] [NeZero 4],
  (4 = 0) = False
```

### `Shao.OQ4.energyLinearPathLaw_integral._simp_1_4`

种类：theorem；传递公理：`propext`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral._simp_1_4 : ∀ {M₀ : Type u_1} [inst : Mul M₀] [inst_1 : Zero M₀]
  [NoZeroDivisors M₀] {a b : M₀}, a ≠ 0 → b ≠ 0 → (a * b = 0) = False
```

### `Shao.OQ4.energyLinearPathLaw_integral._simp_1_5`

种类：theorem；传递公理：`propext`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral._simp_1_5 : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [IsReduced M₀]
  (n : ℕ), a ≠ 0 → (a ^ n = 0) = False
```

### `Shao.OQ4.energyLinearPathLaw_integral._simp_1_6`

种类：theorem；传递公理：`propext, Classical.choice, Quot.sound`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral._simp_1_6 : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {a : G₀} (n : ℤ),
  a ≠ 0 → (a ^ n = 0) = False
```

### `Shao.OQ4.energyLinearPathLaw_integral._simp_1_7`

种类：theorem；传递公理：`propext`。

```lean
@Shao.OQ4.energyLinearPathLaw_integral._simp_1_7 : ∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZero R] (n : ℕ),
  (↑n + 1 = 0) = False
```
