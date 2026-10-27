# unit232 来源、既有接口和实现路线

状态：仅 Stage1 接口设计；本件不提供新 Lean 证明，不冻结声明，不作独立认证。

## 完整读取范围与准确归属

完整读取 p54（6045B）和 p51（17326B），其中 p51 S19–S25 是当前直接来源，S3/S15–S18 与 p54 F4/F5 给未来实际好集的责任边界。也完整读取已验收 `ActualMomentNormalization.lean`、`NormalizedEventTransport.lean`、`NormalizedRawNumeratorBuffer.lean`；读取 `NormalizedAnalyticCostLimits.lean` 第 1–172 行的完整 `actual_normalization_sequence_limits`（含证明），以及相邻 `actual_projection_tilt_and_truncated_cost_limits` 的完整声明头。没有读取或复制 unit228 或 unit231 的未合格实现。

当前 curated snapshot 为 v128 / PR471，数学 main `8ece8d08e99f2888ec333f0db2fbb0980e5901c4`。额外发现的 `NormalizedRawNumeratorBuffer.lean` 仍在当前 v128 receipt 的 exact source map 中，hash `76bb9359913e6734026e09ada5890767207b0a2fa0c89e44ccc0db8403fce7cb`，12075B。因此它是可复用的既有合格 API，不是新来源、未合格作者稿或本单元新证明。这里只核对其合格绑定并设计消费者；没有重跑旧 kernel/AX 或重新开展独立全证明审查。

## 来源对应

| 原文接口 | 本候选对象/责任 | 明确限制 |
|---|---|---|
| p51 S20/S21 | `η k = actualNormalizedFamily ν (Y k)`，真实均值和真实总方差尺度；`ξ` 可测、中心 L²、总能量 1，`Y` 可测且点态一致 `ε k` 近似 | `Y` 是传入的实际近似族，不在此重新构造完整观测编码见证；不把 `η` 或其收敛当输入 |
| p51 S22/S23 | `Q = W - Wη + z*b*(Vη-V)`，`Dη = D1 + Q`，`b = sqrt(1+D2)` | 和现有 signed transport 的左结合式有显式代数一致性；不是新统计量 |
| p54 F4 | `H` 可测且原族上 `0<V`、`z*abs D1≤V/8`、`z²*abs D2≤1/8` | 原文 `V≥1/sqrt 2` 更强；未来 source good set 可以实例化。绝不假定只用 `G_y` 就有确定余量 |
| p54 F6 分子 | `E k = {z*abs(Dη k)>Vη k/4}`；每个 `ω∈H` 最终不在 `E k`；`limsup ν.real(E k)≤ν.real(Hᶜ)` | 不在等号原子处交换尾概率极限；不替换成 `B` 事件 |
| p54 F6 分母 | 固定 `E2={z²*abs D2>1/4}` 满足 `E2⊆Hᶜ` | 未编码变动 `D2`，没有为其制造 `k` 依赖 |
| p54 F5 | 本核保留付款 `ν.real Hᶜ` 原样 | 未来实际集中结论必须另证；本件不发明指数率或归一相对尾率 |
| p51 S24/S25、p54 S19 budgets | 既有解析费用/预算路线的邻接接口 | 本件没有消费未合格228/231，也没有合并费用、严格预算或 source upper 定理 |

源文中 source-specific 上尾可取 `D1=D`、`D2=e=widetilde d_y`、`z=y`，`H=H_{n,y}=G_y∩C_n`（在真实增强概率空间上的原事件拉回）。以后应用方必须证明同一个 `ν`、`ξ`、`Y`、`D1/D2` 的绑定及 `hgood`；若借 `e=d`，必须在该好集上实际证明，而不能把 `D2` 静默替成未截断 `d`。原文 F4 的 `d≥-1/8` 与 clipped equality 是应用层责任，非本核额外结论。

## 已有 API 的确切作用

1. `ActualMomentNormalization.actual_moment_normalization_spec` 已从真实输入推出 `s>1/2`、`η` 可测/L²/中心、总能量 1，以及 `ρ=4εsqrt n` 的点态界：`|Vη-V|≤ρ(1+V)`、`|Wη-W|≤sqrt n*ρ(1+V)`、`|η_i-ξ_i|≤4ε+ρ|ξ_i|`。所以不存在必须由调用方交付的归一化收敛假设。
2. `NormalizedAnalyticCostLimits.actual_normalization_sequence_limits` 直接把这些界转成所有样本的 `η/Wη/Vη` 收敛，且其前提正是候选的原族与 `Y/ε` 前提。它返回的额外 L¹/L² 误差极限不必用于付款核；没有必要重做原 producer。
3. `NormalizedEventTransport.actual_normalized_signed_distance_transport` 的实际 `Dη` RHS 为 `D1 + W - Wη + z*b*(Vη-V)`；候选明确分成 `Q` 再 `D1+Q`。二者由环代数恒等，通常不是定义展开后的 `rfl`。未来消费者须作这一确切 RHS 的改写。其已验收阈值距离身份对应 p51 S23，未要求尾无原子。
4. `NormalizedRawNumeratorBuffer.actual_normalized_raw_numerator_bad_event_limsup` 用同样原始前提已返回 `Wη/Vη/Dη` 收敛、`1/8` 余量下的逐点最终安全、真实坏事件可测性、尾并集 `U`/极限交集 `L`、`L⊆Eorig∪Z`、`Antitone U`、`ν.real(U N)→ν.real L`、概率 `[0,1]` 界。它的最终标量界是 `ν.real Eorig + p0`。本单元应使用它的中间覆盖和极限，不能只代入最终标量界再声称付了一份 `ν.real Hᶜ`。

## 建议的具体实现路线（非证明体）

第一步复用 sequence limits 的完整输出，给出候选前六项中所需的可测性与逐点极限；`Q→0` 和 `Dη→D1` 是固定实数 `z*b ω` 与两个已知差的四则连续性。任意 `D2 ω` 都是有限实数，`b ω` 固定于 `k`，因此这一环不需要全局 `1+D2>0`。有限求和、平方、平方根和可测实函数运算给 `Q/Dη/E/E2/Z` 的可测性。

第二步按 `x=z`（`hz` 提供 `0≤z`）调用已验收 raw-numerator theorem，并显式桥接它和候选的 `Dη` RHS。其严格间隙为 `z*abs D1 - V/4 ≤ -V/8 <0`；这使每个 `ω∈H` 最终安全，即使 `z*abs D1 = V/8` 也成立。`Vη→V>0` 同时给最终 `Vη>0`。这不是一个输入回调，也不是对 `{z*abs D1=V/4}` 的零质量断言。

第三步在 raw-numerator theorem 的原有记号下，令 `Eorig={z*abs D1>V/8}`、`Z={V=0}`、`U N=⋃k,⋃(_ : N≤k),E k`、`L=⋂N,U N`。显式 `hgood` 排除 `H∩Eorig` 和 `H∩Z`，于是把已验收的覆盖 `L⊆Eorig∪Z` 收紧为 `L⊆Hᶜ`。所有这些是证明内部普通定义，不能成为新的调用方数据或假设。

第四步直接复用同一 theorem 的 `ν.real(U N)→ν.real L`，再结合 `E k⊆U N`（`N≤k`）和 `ν.real L≤ν.real Hᶜ` 得任意正容差的最终概率界。复用其确切 limsup 风格时，`ν.real(E k)≥0` 给 coboundedness，`≤1` 给显式上有界；从每个正容差最终界去掉容差。这样只付 `ν.real Hᶜ` 一次。无须引入未查明名称的 Portmanteau 或 reverse-Fatou API，也无须另写 DCT 包装。

第五步，固定事件 `E2` 在 `H` 上被 `1/8<1/4` 排除；`Z` 在 `H` 上被 `V>0` 排除。各自集合包含与有限实测度单调性给各自的概率界。由 `z≥1`、`z²|D2|≤1/8` 还可导出好集内的 `1+D2≥7/8` 和 `b>0`，对应候选额外输出的分母可用性。

这是实现依赖顺序和检查计划，不是已实施证明。没有新 `.lean`、局部 proof、source 冻结或数学检查。

## 已实际见于合格源的概率/滤子调用

以下是上面 raw-numerator 合格源中实际存在的调用形式，不是猜测库函数名；其原调用上下文、可测性和有限性也已完整阅读。未来可优先直接投影现有 theorem 输出，减少再次展开这些库细节。

```lean
measure_ne_top ν S
measureReal_mono hsubset
tendsto_measure_iInter_atTop (μ := ν)
  (fun N => (hUm N).nullMeasurableSet) hUanti ⟨0, hfinite (U 0)⟩
(ENNReal.continuousAt_toReal (hfinite L)).tendsto.comp hUmeasurelim
Filter.eventually_atTop.1 hevent
Filter.eventually_atTop.2 ⟨N, hN⟩
hUreallim.eventually (gt_mem_nhds hc)
Filter.isCoboundedUnder_le_of_le (Filter.atTop : Filter ℕ)
  (x := (0 : ℝ)) (fun k : ℕ => (hprob k).1)
Filter.limsup_le_of_le hcobounded heventual
```

其中 `IsProbabilityMeasure ν` 蕴含本核需要的有限测度；`measure_ne_top` 覆盖所有 `E/U/L/Hᶜ`。`E/U/L` 的可测性来自实际可测函数和可数并交。`ν.real(E k)∈[0,1]` 使实数 `Filter.limsup` 不会依赖无界序列的约定。好集可测性显式保留。未查询本机/服务器 Mathlib，也未声称在本轮重新验证这些 API；合格 producer 的确切头和调用是复用依据。

## 真正未闭合的接口

- 该固定律序列候选内：未发现数学上必须补充的前提；尚缺未来冻结、Lean 实现、独立完整证明/actual TYPE 审查和精确源 server kernel/transitive-axiom receipt。这些是认证工作，不可写成现已通过。
- 原模型应用层：必须绑定实际观测因子/增强空间、同一个 canonical coding witness、原行总能量、实际 `D` 与 clipped `e` 以及拉回的 `G_y∩C_n`。普通 `Y` 数据本身不证明它来自 full observation coding；上游需交付该身份。
- F4/F5：必须从实际 S16 或 S18 集中事件证明原模型严格余量和实际好集失败率。`ν.real Hᶜ` 在本核保持未估计。本核既未给 F5，也没有借 `B_y` 的假尾界替代它。
- 连续参数 F6：候选只给任意合法自然数序列的最终界与 limsup；实际全参数 `ε↓0` 尚须绑定参数化族并提供相应序列判据/滤子版本。没有假定任何尾概率在等号处连续。
- 之后的 source upper 及解析费用/严格预算组合（包括独立 unit231 的职责）、相对误差吸收、CDF/零 physical denominator 比较、Shao–Zhou 定理实际应用和 OQ56/root 均仍未在此闭合。

## 复用的完整声明头

下列声明头从已绑定只读源精确抽取，止于各自证明体之前；因此保留所有参数、类型、ordinary let 的 RHS 和完整结论。它们是既有 API 证据，不是本单元新实现。

### actual_moment_normalization_spec

Source: C:/game/shao lean/library/Shao/OQ6/ActualMomentNormalization.lean:217 through 251. Header text only; LF in this artifact.

```lean
theorem actual_moment_normalization_spec
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ Y : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ)))
    (herr : ∀ (i : Fin n) (ω : Ω), |Y i ω - ξ i ω| ≤ ε) :
    let μ : Fin n → ℝ := actualCoordinateMean ν Y
    let Z : Fin n → Ω → ℝ := actualCenteredFamily ν Y
    let s : ℝ := actualNormalizationScale ν Y
    let η : Fin n → Ω → ℝ := actualNormalizedFamily ν Y
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
    let ρ : ℝ := 4 * ε * Real.sqrt (n : ℝ)
    (1 / 2 : ℝ) < s ∧
    (∀ i : Fin n, Measurable (η i)) ∧
    (∀ i : Fin n, MemLp (η i) 2 ν) ∧
    (∀ i : Fin n, Integrable (η i) ν) ∧
    (∀ i : Fin n, Integrable (fun ω => (η i ω) ^ 2) ν) ∧
    (∀ i : Fin n, (∫ ω, η i ω ∂ν) = 0) ∧
    (∑ i : Fin n, ∫ ω, (η i ω) ^ 2 ∂ν) = 1 ∧
    (∀ (i : Fin n) (ω : Ω), s * η i ω + μ i = Y i ω) ∧
    (∀ ω : Ω,
      Real.sqrt (∑ i : Fin n, (η i ω - ξ i ω) ^ 2) ≤ ρ * (1 + V ω)) ∧
    (∀ ω : Ω, |Vη ω - V ω| ≤ ρ * (1 + V ω)) ∧
    (∀ ω : Ω, |Wη ω - W ω| ≤ Real.sqrt (n : ℝ) * ρ * (1 + V ω)) ∧
    (∀ (i : Fin n) (ω : Ω), |η i ω| ≤ 2 * |ξ i ω| + 4 * ε) ∧
    (∀ (i : Fin n) (ω : Ω), |η i ω - ξ i ω| ≤ 4 * ε + ρ * |ξ i ω|)
```

### actual_normalization_sequence_limits

Source: C:/game/shao lean/library/Shao/OQ6/NormalizedAnalyticCostLimits.lean:14 through 49. Header text only; LF in this artifact.

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
      Filter.atTop (nhds (0 : ℝ)))
```

### actual_normalized_signed_distance_transport

Source: C:/game/shao lean/library/Shao/OQ6/NormalizedEventTransport.lean:19 through 36. Header text only; LF in this artifact.

```lean
theorem actual_normalized_signed_distance_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (ξ Y : Fin n → Ω → ℝ)
    (D1 D2 : Ω → ℝ) :
    let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let Dη : ℝ → Ω → ℝ := fun z ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
    let comparisons : Set (ℝ → ℝ → Prop) := {R | R = (fun a b : ℝ => a ≤ b) ∨ R = (fun a b : ℝ => a < b) ∨ R = (fun a b : ℝ => b ≤ a) ∨ R = (fun a b : ℝ => b < a) ∨ R = (fun a b : ℝ => a = b)}
    (∀ (z : ℝ) (ω : Ω),
      Wη ω + Dη z ω - z * Vη ω * b ω =
        W ω + D1 ω - z * V ω * b ω) ∧
    (∀ (z : ℝ) (R : ℝ → ℝ → Prop), R ∈ comparisons →
      {ω : Ω | R (Wη ω + Dη z ω) (z * Vη ω * b ω)} =
        {ω : Ω | R (W ω + D1 ω) (z * V ω * b ω)})
```

### actual_normalized_raw_numerator_bad_event_limsup

Source: C:/game/shao lean/library/Shao/OQ6/NormalizedRawNumeratorBuffer.lean:16 through 79. Header text only; LF in this artifact.

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
    Filter.limsup (fun k : ℕ => ν.real (E k)) Filter.atTop ≤ ν.real Eorig + p0
```

