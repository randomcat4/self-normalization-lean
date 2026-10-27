# 完整消费接口与定义

仅复制精确签名和所需定义，复用旧合格证明证据。末行的 := by 只标明签名边界，不含旧证明体。

## actualNormalizationDefinitions

来源：C:/game/shao lean/library/Shao/OQ6/ActualMomentNormalization.lean，行 20–41。

```lean
noncomputable def actualCoordinateMean
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) (i : Fin n) : ℝ :=
  ∫ ω, Y i ω ∂ν

noncomputable def actualCenteredFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Y i ω - actualCoordinateMean ν Y i

noncomputable def actualNormalizationScale
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∫ ω, (actualCenteredFamily ν Y i ω) ^ 2 ∂ν)

noncomputable def actualNormalizedFamily
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y : Fin n → Ω → ℝ)
    (i : Fin n) (ω : Ω) : ℝ :=
  Shao.OQ6.QuantizedObservationCoding.deterministicAffineObservation
    (actualCoordinateMean ν Y i) (actualNormalizationScale ν Y) (Y i) ω
```

## deterministicAffineObservation

来源：C:/game/shao lean/library/Shao/OQ6/QuantizedObservationCoding.lean，行 17–19。

```lean
def deterministicAffineObservation
    {X : Type*} (a s : ℝ) (Y : X → ℝ) (x : X) : ℝ :=
  (Y x - a) / s
```

## actual_normalization_sequence_limits

来源：C:/game/shao lean/library/Shao/OQ6/NormalizedAnalyticCostLimits.lean，行 14–49。

```lean
theorem actual_normalization_sequence_limits
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k) :
    let μ : ℕ → Fin n → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualCoordinateMean ν (Y k)
    let s : ℕ → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizationScale ν (Y k)
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let ρ : ℕ → ℝ := fun k => 4 * ε k * Real.sqrt (n : ℝ)
    (∀ (k : ℕ) (i : Fin n), |μ k i| ≤ ε k) ∧
    (∀ k : ℕ, |s k - 1| ≤ 2 * ε k * Real.sqrt (n : ℝ) ∧ (1 / 2 : ℝ) < s k) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => μ k i) Filter.atTop (nhds (0 : ℝ))) ∧
    Filter.Tendsto s Filter.atTop (nhds (1 : ℝ)) ∧
    Filter.Tendsto ρ Filter.atTop (nhds (0 : ℝ)) ∧
    (∀ (k : ℕ) (i : Fin n), Measurable (η k i) ∧ MemLp (η k i) 2 ν) ∧
    (∀ (k : ℕ) (i : Fin n) (ω : Ω), |η k i ω| ≤ 2 * |ξ i ω| + 1) ∧
    (∀ (i : Fin n) (ω : Ω), Filter.Tendsto (fun k : ℕ => η k i ω) Filter.atTop (nhds (ξ i ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Wη k ω) Filter.atTop (nhds (W ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Vη k ω) Filter.atTop (nhds (V ω))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, |η k i ω - ξ i ω| ∂ν)
      Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ i : Fin n, Filter.Tendsto (fun k : ℕ => ∫ ω, (η k i ω - ξ i ω) ^ 2 ∂ν)
      Filter.atTop (nhds (0 : ℝ))) := by
```

## actual_normalized_raw_numerator_bad_event_limsup

来源：C:/game/shao lean/library/Shao/OQ6/NormalizedRawNumeratorBuffer.lean，行 16–79。

```lean
theorem actual_normalized_raw_numerator_bad_event_limsup
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (Y : ℕ → Fin n → Ω → ℝ)
    (hY : ∀ (k : ℕ) (i : Fin n), Measurable (Y k i))
    (ε : ℕ → ℝ) (hε : ∀ k : ℕ, 0 < ε k)
    (hεsmall : ∀ k : ℕ, ε k < 1 / (4 * Real.sqrt (n : ℝ)))
    (hεlim : Filter.Tendsto ε Filter.atTop (nhds (0 : ℝ)))
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω), |Y k i ω - ξ i ω| ≤ ε k)
    (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (x : ℝ) (hx : 0 ≤ x) :
    let η : ℕ → Fin n → Ω → ℝ := fun k => Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω => Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + W ω - Wη k ω + x * b ω * (Vη k ω - V ω)
    let E : ℕ → Set Ω := fun k => {ω : Ω | x * |Dη k ω| > Vη k ω / 4}
    let Eorig : Set Ω := {ω : Ω | x * |D1 ω| > V ω / 8}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    let p0 : ℝ := ν.real Z
    let U : ℕ → Set Ω := fun N => ⋃ k : ℕ, ⋃ (_ : N ≤ k), E k
    let L : Set Ω := ⋂ N : ℕ, U N
    (∀ k : ℕ, Measurable (Dη k)) ∧
    (∀ k : ℕ, MeasurableSet (E k)) ∧
    MeasurableSet Eorig ∧
    MeasurableSet Z ∧
    (∀ N : ℕ, MeasurableSet (U N)) ∧
    MeasurableSet L ∧
    (∀ ω : Ω, 0 ≤ V ω) ∧
    (∀ (k : ℕ) (ω : Ω), 0 ≤ Vη k ω) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Wη k ω) Filter.atTop (nhds (W ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Vη k ω) Filter.atTop (nhds (V ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Dη k ω) Filter.atTop (nhds (D1 ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => x * |Dη k ω| - Vη k ω / 4)
      Filter.atTop (nhds (x * |D1 ω| - V ω / 4))) ∧
    (∀ ω : Ω, 0 < V ω → x * |D1 ω| ≤ V ω / 8 →
      x * |D1 ω| - V ω / 4 ≤ -(V ω / 8) ∧ -(V ω / 8) < 0) ∧
    (∀ ω : Ω, 0 < V ω → x * |D1 ω| ≤ V ω / 8 →
      ∀ᶠ k : ℕ in Filter.atTop, x * |Dη k ω| ≤ Vη k ω / 4) ∧
    L ⊆ Eorig ∪ Z ∧
    Antitone U ∧
    (∀ k : ℕ, ν (E k) ≠ ⊤) ∧
    ν Eorig ≠ ⊤ ∧
    ν Z ≠ ⊤ ∧
    (∀ N : ℕ, ν (U N) ≠ ⊤) ∧
    ν L ≠ ⊤ ∧
    ν L ≤ ν (Eorig ∪ Z) ∧
    ν (Eorig ∪ Z) ≤ ν Eorig + ν Z ∧
    Filter.Tendsto (fun N : ℕ => ν (U N)) Filter.atTop (nhds (ν L)) ∧
    (∀ k : ℕ, 0 ≤ ν.real (E k) ∧ ν.real (E k) ≤ 1) ∧
    (∀ N : ℕ, 0 ≤ ν.real (U N) ∧ ν.real (U N) ≤ 1) ∧
    Filter.Tendsto (fun N : ℕ => ν.real (U N)) Filter.atTop (nhds (ν.real L)) ∧
    ν.real L ≤ ν.real Eorig + p0 ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in Filter.atTop,
      ν.real (E k) ≤ ν.real Eorig + p0 + δ) ∧
    Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Eorig + p0 := by
```
