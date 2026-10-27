# unit232：实际上尾余项事件的严格好集付款候选

状态：`STAGE1_DESIGN_ONLY_NOT_FROZEN_NO_IMPLEMENTATION`。这是一个建议声明；没有证明体，没有声明冻结，也没有 Lean / 服务器检查。其正确性和形式接口仍须由主实例冻结并安排独立审查。

建议只做一个固定概率律、固定有限行、固定 `z ≥ 1` 的序列付款定理。`η` 必须是现有 `actualNormalizedFamily ν (Y k)`；`Q`、`Dη` 和两个坏事件逐字保留实际定义。`H` 由应用方给定，但必须同时交付可测性和明确的 `1/8` 余量。收敛、好集上最终安全、概率最终界均是结论。

## 建议的完整声明头

未来建议模块名为 `Shao/OQ6/NormalizedUpperErrorGoodsetPayment.lean`，命名空间为 `Shao.OQ6.NormalizedUpperErrorGoodsetPayment`。只建议导入已合格的 `Shao.OQ6.NormalizedRawNumeratorBuffer`；该模块已传递导入实际归一化与序列 API。以下代码是完整类型建议，故意没有赋值号或证明体，不是可编译源文件。

```lean
theorem actual_normalized_upper_error_goodset_payment
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
    (herr : ∀ (k : ℕ) (i : Fin n) (ω : Ω),
      |Y k i ω - ξ i ω| ≤ ε k)
    (D1 D2 : Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (z : ℝ) (hz : 1 ≤ z)
    (H : Set Ω) (hH : MeasurableSet H)
    (hgood : ∀ ω : Ω, ω ∈ H →
      0 < Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2) ∧
      z * |D1 ω| ≤ Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2) / 8 ∧
      z ^ 2 * |D2 ω| ≤ (1 / 8 : ℝ)) :
    let η : ℕ → Fin n → Ω → ℝ := fun k =>
      Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν (Y k)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : ℕ → Ω → ℝ := fun k ω => ∑ i : Fin n, η k i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : ℕ → Ω → ℝ := fun k ω =>
      Real.sqrt (∑ i : Fin n, (η k i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      W ω - Wη k ω + z * b ω * (Vη k ω - V ω)
    let Dη : ℕ → Ω → ℝ := fun k ω => D1 ω + Q k ω
    let E : ℕ → Set Ω := fun k =>
      {ω : Ω | z * |Dη k ω| > Vη k ω / 4}
    let E2 : Set Ω := {ω : Ω | z ^ 2 * |D2 ω| > (1 / 4 : ℝ)}
    let Z : Set Ω := {ω : Ω | V ω = 0}
    (∀ (k : ℕ) (i : Fin n), Measurable (η k i)) ∧
    (∀ k : ℕ, Measurable (Q k) ∧ Measurable (Dη k) ∧
      MeasurableSet (E k)) ∧
    (MeasurableSet E2 ∧ MeasurableSet Z) ∧
    (∀ (i : Fin n) (ω : Ω),
      Filter.Tendsto (fun k : ℕ => η k i ω) Filter.atTop (nhds (ξ i ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Wη k ω)
      Filter.atTop (nhds (W ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Vη k ω)
      Filter.atTop (nhds (V ω))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Q k ω)
      Filter.atTop (nhds (0 : ℝ))) ∧
    (∀ ω : Ω, Filter.Tendsto (fun k : ℕ => Dη k ω)
      Filter.atTop (nhds (D1 ω))) ∧
    (∀ ω : Ω, ω ∈ H → (7 / 8 : ℝ) ≤ 1 + D2 ω ∧ 0 < b ω) ∧
    (∀ ω : Ω, ω ∈ H → ∀ᶠ k : ℕ in Filter.atTop,
      0 < Vη k ω ∧ z * |Dη k ω| ≤ Vη k ω / 4) ∧
    E2 ⊆ Hᶜ ∧
    Z ⊆ Hᶜ ∧
    ν.real E2 ≤ ν.real Hᶜ ∧
    ν.real Z ≤ ν.real Hᶜ ∧
    (∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in Filter.atTop,
      ν.real (E k) ≤ ν.real Hᶜ + δ) ∧
    Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Hᶜ
```

建议未来源设置 `set_option autoImplicit false`，使用 `noncomputable section`、`open MeasureTheory`、`open scoped BigOperators Classical Topology`。没有额外类型类、隐藏结构或存在量词见证。

## 输入和结论的边界

`H` 的三项条件是显式应用前提，不是归一化后的安全性回调。尤其没有输入 `Tendsto η`、`Tendsto Vη`、`Tendsto Dη`、`eventually Eᶜ`、概率极限、无原子尾概率或可调用的 source 定理。所有这些所需收敛与最终安全均由真实归一化输入导出。`hgood` 对原族、原余项和固定分母修正作 `1/8` 约束，其阈值严格小于实际坏事件的 `1/4`；允许 `hgood` 内部在 `1/8` 处取等号。

这里的最终性顺序是 `∀ ω ∈ H, ∀ᶠ k, ...`，不声称存在对全部 `H` 同时有效的统一 `k`。第二坏事件 `E2` 不依赖 `k`。概率界对固定的同一个 `ν` 成立；没有把不同 `k` 的法则或样本空间混在一起。`E` 不换成包络 `B` 的事件。两个标量概率各自有界，不声称二者之和有同一个单倍好集付款界。

`D2` 在 `H` 外不必满足正性；实数平方根在那里仍是现有的全域函数，这已经足够定义 `Q` 和事件。`z ≥ 1` 与好集分母余量会在 `H` 内导出 `1 + D2 ≥ 7/8`，不是另加全局分母假设。此核不需要独立性、原空间标准 Borel、原法则无原子、四矩、混合四矩或额外 L¹ 余项。上游 source upper 的完整可用条件仍须另行交付。

这是任意合法 `ε : ℕ → ℝ` 和 `Y : ℕ → Fin n → Ω → ℝ` 的序列核；不要求 `ε` 单调。它没有独立建立连续参数 `ε ↓ 0` 的滤子接口。以后若要把 p54 的连续参数记号逐字闭合，须对实际同一个参数化编码族作任意趋零序列实例化并使用相应序列判据，或另行提供等价滤子版本。不能把本候选直接记为全参数 F6 已接受。

## 当前判定

`DESIGN_CANDIDATE / NOT_FROZEN / NOT_IMPLEMENTED / NOT_MACHINE_CHECKED`。在固定律序列核范围内，已识别到完整的现有数学路线，没有必须回调目标性质的缺口。精确 Lean 声明和未来证明仍未机械检查。实际 p54 F4/F5、原模型同见证编码实例化、连续参数桥、source upper 应用、CDF、Shao–Zhou 外部结果应用以及 OQ56/root 闭合均不在本单元完成范围内。
