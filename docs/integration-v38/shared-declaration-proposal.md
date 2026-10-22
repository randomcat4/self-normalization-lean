# Shared bivariate Legendre interface — declaration proposal v1

状态：`PROPOSED / NOT_FROZEN / NOT_LEAN_CHECKED / INDEPENDENT_REVIEW_REQUIRED`。

本稿只提出 root 公共接口，不是独立声明审查票或数学闭合声明。作者上下文为 `/root/global_rate_scope`，只拥有 `drafts/shared-global-rate/`。没有写生产 Lean、运行 Lean、执行 probe、修改分线文件/共享缓存或合并。四个建议公共 theorem 的陈述尚须另一全新上下文审查，再由 root 冻结。所有原 OQ3 根仍 `OPEN`。

基线绑定：main v36 `82294da791784f3ac34ca52b96e21ef23f8a5329`，accepted `f2a39a09ebd50648bd61d68d7018aa01a9810ea0`，同树 `b6e72c992deceb0df88e772e50b2c42ba58ac4b4`。PR146 指定 head `5d14dbdb619fd7d2eb97ec31e049053de53be871`，`SourceGlobalExponentialTests.lean` SHA256 `24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df`。Lean pin 为 `leanprover/lean4:v4.36.0-rc1`，mathlib pin 为 `807d3836b165983210ee2ecf3cd28f239436949c`。

## 1. 语义决策

建议生产文件为 `Shao/Probability/BivariateLegendre.lean`，namespace 沿现有 `Shao.Probability`。统计量用任意 `W : Ω → ℝ × ℝ`，参数、均值均用 `ℝ × ℝ`，显式写二项配对而不引入矩阵/内积/EuclideanSpace API。公共模块不能 import `Shao.OQ3.*`，不能定义 sourceEll、原子律、抛物线模型、尾域或 saddleRate。

三项公共定义：真实指数可积域 `bivariateMGFDomain`；只在域子类型上的实值 `bivariateLogMGF`；取值 `EReal` 的 `bivariateLegendreRate`。不新增竞争的实值 globalRate，不把候选常数定义成 supremum，也不把一般率函数定义成支撑律的 KL 下确界。

`bivariateMGFDomain` 对任意测度可定义；`bivariateLogMGF` 和 `bivariateLegendreRate` 显式要求 `[NeZero μ]`。这是比概率律弱的合法技术门：对域内参数，`integral_exp_pos` 从真 Integrable 与测度非零推出配分严格正，所以域内的 Real.log 是真实实数对数。OQ3 的真实概率实例自动产生此门。允许非零无限测度有空域，可完整写清空上确界；概率消费者不出现空域。选择 `[NeZero μ]` 不是给无界概率模型增加矩条件。

原 root-contract 的 `domK = {θ | Integrable exp(θ·W) P}` 原样保留：不把正积分重复塞成额外域条件，不用开域/内部代替整个 domK，不擅自断言 domK 全空间、有非空内部或 K 可微。

## 2. 建议最小 imports 与三个定义

以下是精确的候选声明文字，尚未经过 Lean elaboration。显式基础 imports 的源文件均已只读定位；没有运行依赖图/缓存 readiness 或 import smoke。root 可在未来实际实现时去除已由其他项公开传递的重复 import，但不得用 OQ3 import 掩盖缺项。

```lean
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic

namespace Shao.Probability
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]

def bivariateMGFDomain (μ : Measure Ω) (W : Ω → ℝ × ℝ) : Set (ℝ × ℝ) :=
  {θ | Integrable
    (fun ω => Real.exp (θ.1 * (W ω).1 + θ.2 * (W ω).2)) μ}

def bivariateLogMGF (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (θ : bivariateMGFDomain μ W) : ℝ :=
  Real.log (∫ ω, Real.exp
    ((θ : ℝ × ℝ).1 * (W ω).1 + (θ : ℝ × ℝ).2 * (W ω).2) ∂μ)

def bivariateLegendreRate (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (z : ℝ × ℝ) : EReal :=
  ⨆ θ : bivariateMGFDomain μ W,
    (((θ : ℝ × ℝ).1 * z.1 + (θ : ℝ × ℝ).2 * z.2 -
      bivariateLogMGF μ W θ : ℝ) : EReal)

end Shao.Probability
```

`W` 的全局 Measurable/AEMeasurable 不是这三个定义与下列序论桥的必要前提；每个可用参数的指数函数已由 Integrable 自带 AEStronglyMeasurable 和有限积分。概率学应用仍应在其下游模型证明 `W` 可测，不能由这个弱接口推断 `W` 自身可测。尤其域可能仅含零，不能据此推出坐标可积、有限矩或任何导数。

定义里先在 ℝ 算出有限 `θ·z − K(θ)`，再整体强制到 EReal，最后取 iSup；不使用 EReal 减法、`∞ − ∞` 或 `.toReal`。不存在域外 `bivariateLogMGF μ W θ` 的合法调用。后续如确需全参数扩展 K，可另审为域内 coe、域外 top 的对象，本轮不增加该定义。

## 3. 四个建议公共 theorem 的完整类型

所有签名处于同一 `namespace Shao.Probability`，具有 `variable {Ω : Type*} [MeasurableSpace Ω]`。以下只列声明类型，不给 Lean 证明体。

### T1 — 域内真实正配分与 log 的语义

```lean
theorem bivariateLogMGF_spec
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (θ : bivariateMGFDomain μ W) :
    (0 < (∫ ω, Real.exp
      ((θ : ℝ × ℝ).1 * (W ω).1 + (θ : ℝ × ℝ).2 * (W ω).2) ∂μ)) ∧
    Real.exp (bivariateLogMGF μ W θ) =
      (∫ ω, Real.exp
        ((θ : ℝ × ℝ).1 * (W ω).1 + (θ : ℝ × ℝ).2 * (W ω).2) ∂μ)
```

可核验实现路线：`θ.property` 正是 Integrable；`MeasureTheory.integral_exp_pos θ.property` 给严格正；展开定义后 `Real.exp_log`。不需要 `IsFiniteMeasure μ`，更不需要正积分作为新的 consumer 前提。

### T2 — 每个真实可积指数测试低于全局率

```lean
theorem bivariateLegendreRate_test_le
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (z : ℝ × ℝ) (θ : bivariateMGFDomain μ W) :
    (((θ : ℝ × ℝ).1 * z.1 + (θ : ℝ × ℝ).2 * z.2 -
      bivariateLogMGF μ W θ : ℝ) : EReal) ≤
      bivariateLegendreRate μ W z
```

可核验实现路线：展开 rate，对那个 θ 用 `le_iSup`。这一结论不需要率函数有限，不依赖概率界、紧性、KL 变分式或梯度。

### T3 — 全部测试上界 + 一个真实达到参数 ⇒ 真实有限候选率

```lean
theorem bivariateLegendreRate_eq_of_attained_bound
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (z₀ : ℝ × ℝ) (L : ℝ)
    (hupper : ∀ θ : bivariateMGFDomain μ W,
      (θ : ℝ × ℝ).1 * z₀.1 + (θ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ ≤ L)
    (θ₀ : bivariateMGFDomain μ W)
    (hattain :
      (θ₀ : ℝ × ℝ).1 * z₀.1 + (θ₀ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ₀ = L) :
    bivariateLegendreRate μ W z₀ = (L : EReal)
```

可核验实现路线：`iSup_le` 与 `EReal.coe_le_coe_iff` 给上界；T2 在 θ₀ 给下界，再用 hattain 和 `le_antisymm`。θ₀ 是域内证人，所以空域绝不可能被这个 theorem 的前提掩盖。不能把 θ₀ 当任意实参数后忘掉可积性。

### T4 — 逐点严格指数分离 ⇒ 同一扩展率的唯一全局极小点

```lean
theorem bivariateLegendreRate_unique_minimizer_of_tests
    (μ : Measure Ω) [NeZero μ] (W : Ω → ℝ × ℝ)
    (D : Set (ℝ × ℝ)) (z₀ : ℝ × ℝ) (L : ℝ)
    (hz₀ : z₀ ∈ D)
    (hupper : ∀ θ : bivariateMGFDomain μ W,
      (θ : ℝ × ℝ).1 * z₀.1 + (θ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ ≤ L)
    (θ₀ : bivariateMGFDomain μ W)
    (hattain :
      (θ₀ : ℝ × ℝ).1 * z₀.1 + (θ₀ : ℝ × ℝ).2 * z₀.2 -
        bivariateLogMGF μ W θ₀ = L)
    (hsep : ∀ z ∈ D, z ≠ z₀ →
      ∃ θ : bivariateMGFDomain μ W,
        L < (θ : ℝ × ℝ).1 * z.1 + (θ : ℝ × ℝ).2 * z.2 -
          bivariateLogMGF μ W θ) :
    bivariateLegendreRate μ W z₀ = (L : EReal) ∧
      (∀ z ∈ D,
        bivariateLegendreRate μ W z₀ ≤ bivariateLegendreRate μ W z ∧
        (bivariateLegendreRate μ W z = bivariateLegendreRate μ W z₀ ↔ z = z₀))
```

这是实际域 D 上唯一全局极小性：hz₀ 明确保证候选在域中；最后的双条件排除全部同值点；第一个比较防止候选只是唯一达到值却非极小。对 `z ≠ z₀`，T3、hsep、`EReal.coe_lt_coe_iff`、T2 和 `lt_of_lt_of_le` 实际给更强的 `I(z₀) < I(z)`，随后得到所列结论。hsep 的 θ 可依赖 z，只要求有限实参数和它自己的可积证明，不要求同一个 θ 分离所有点，也不要求统一正间隙。

T4 刻意不用 `IsMinOn`，避免另加 Filter/Extr import，且直接把成员性、全域比较、等号唯一性写在类型中。可通过普通逻辑得到 `∃! z, z ∈ D ∧ ∀ y ∈ D, I z ≤ I y`；建议不再导出重复 wrapper。实现所需内部零参数/简单重写辅助可为 private/local，不扩成公共辅助定理群。

## 4. 域、空域、扩展值与其他边界

| 情形 | 本接口的精确行为/限制 |
|---|---|
| θ 不在 domK | 子类型拒绝把该 θ 交给 logMGF；不可将 Bochner `integral_undef = 0`、`log 0 = 0` 当作域外 K 值。 |
| θ 在 domK、μ 非零 | 指数真 Integrable；实积分有限且严格正；K 是真实有限实数。T1 负责正值说明。 |
| μ = 0 | domK 本身仍可定义；logMGF/rate 的 `[NeZero μ]` 门不满足，故不冒称 log0 是真实 log 配分。 |
| 非零无限测度且 domK 空 | rate 的 iSup 索引空，值为 EReal.bot。T2 无域内 θ；T3/T4 无 θ₀，无法伪造有限候选。例：无限计数测度、W 恒零，所有指数均为1而不可积。此为定义边界说明，不是本轮额外 Lean 定理。 |
| 概率律 | 零参数 `(0,0)` 的指数恒1，`integrable_const` 给域成员；积分1、K(0)=0。T2 因此给 `0 ≤ I(z)`，所有 z 均非 bot；空域情形不可能发生。这里只是直接核查路径，可在未来实现内部证明，不再另添公共 wrapper。 |
| 非概率非零有限测度 | 零测试为 `−log μ.real univ`，一般不保证非负；四个 theorem 均未错误宣称非负。 |
| I(z)=top | T2 与 hsep 的有限实下界继续合法；T4 的唯一极小性不要求 off-candidate 率有限。 |
| 候选率 | T3 的 coe L 明确有限，故非 top、非 bot；只有此处可安全讨论对应实值，不应先 `.toReal` 再比较。 |
| domK 只有零、或边界参数 | 定义与序论接口照常成立；不预设开性、极值参数唯一、可微、严格凸、矩生成函数邻域有限。 |
| D 空、候选不在 D | T4 的 hz₀ 排除；不把空集上的真空最小性叫做存在唯一极小点。 |
| D 非闭或不紧 | T4 不要求其闭/紧，逐点分离足够；但无法推出 D\U 的统一正间隙、远区概率指数界或 Cramér 上界。 |

不在本轮增加 KL 函数、熵对偶性或 entropy minimizer 接口。特别是有界支撑的 PR146 给 domK 全空间，只是 THIS P 的下游事实；四个公共 theorem 没有也不能把它推广为一般无界概率律的全域有限 K/普遍 KL 对偶性。

## 5. PR146 的逐项消费者桥

公共接口最终冻结且证明验收后，OQ3 下游适配文件可 import 公共模块与 `Shao.OQ3.SourceGlobalExponentialTests`。以下适配是未来 OQ3/root 消费层的责任，不是本公共模块的 import 或本轮已完成代码。

固定 PR146 的同一个 q/w/hw/hm，令：

```lean
μ := Shao.OQ3.originalMeasure Shao.OQ3.sourceEll w
W := fun x : ℝ => (x, x ^ 2)
z₀ := (q / 4, q)
θraw := (8 * Shao.OQ3.sourceEll, -Shao.OQ3.sourceEll)
L := Shao.OQ3.saddleRate Shao.OQ3.sourceEll q w
D := {z : ℝ × ℝ |
  0 < z.2 ∧ (Real.sqrt q / 4) * Real.sqrt z.2 ≤ z.1}
```

| 公共输入/输出 | PR146 或已接受定义的生产路径 |
|---|---|
| 同一个真实概率 μ / 非零实例 | hm 的 k=0 行化简为 `HasSum w 1`；已接受 `originalMeasure_isProbabilityMeasure sourceEll w hw hs` 给 IsProbabilityMeasure；mathlib 的 `IsProbabilityMeasure.neZero` 给 `[NeZero μ]`。不能让 μ 是 tilted 的不可积退化零测度。 |
| 每个 θ=(s,t) 的域成员 | `source_saddle_exponential_value_bound q w hw hm` 的第一项在 s/t 返回 `.1 : Integrable exp(...) μ`。展开 W/domK 后这是精确成员证明。它也证明 THIS μ 的 domK=univ，但无需公共化该特例。 |
| 正积分 | 同项的 `.2.1` 是真 `0 < ∫exp(...)`，与公共 T1 完全同义。domK 不重复携带它；它不会被丢弃为“无需核查”，而是由公共非零+Integrable 原理重建。 |
| hupper | 第一项同一次结果 `.2.2` 正是 θ·z₀−log integral≤L。展开域内 logMGF 后直接重写，无 KL 转换。 |
| θ₀ : domK | 第一项在 θraw 两坐标处的 Integrable；构造 `⟨θraw, hi⟩`。不能仅凭第二合取取等式推定其可积。 |
| hattain | 上界 theorem 的第二合取项给 θraw 的测试值=L。子类型选择的可积证明不改变积分函数/K 值。 |
| hz₀ | 1<q 保证 q>0，`Real.mul_self_sqrt (le_of_lt hq)` 给 `(sqrt q /4)*sqrt q=q/4`；因此 z₀ 在精确弱尾域。这里只使用消费者已有 sqrt API，不给公共模块加 sqrt import。 |
| hsep | 对 z=(a,c)∈D 且 z≠z₀，从 pair 不等得到 a≠q/4∨c≠q；实调 `exists_source_tail_exponential_separator q hq0 hq1 w hw hm a c hc0 htail hne`。证人 s/t 的 hi 构造 θ:domK，hp 与 T1 一致，最后严格实不等式恰为 hsep。 |
| 候选率 | T3 或 T4 第一输出：真实 domK 上的 EReal supremum在 `(q/4,q)` 等于 `(saddleRate sourceEll q w : EReal)`。 |
| 全域唯一极小性 | T4 第二输出覆盖所有 c>0、弱尾不等式的 (a,c)，且仅候选取等；包括 c<1、c>1+H、不可实现矩点和 p=0/1 对应边界，因为 PR146 separator 的完整类型没有删除它们。 |

候选严格正率仍另消费既有 `saddleRate_pos`，它的实际前提为 ell≠0、所有 w_i>0 与四个 HasSum；本共享 theorem 不偷加全质量严格正，也不从 q-window 自动推正率。C 的最终 limitingMass 需要在下游提供原有同一 q/w 的严格正性和完整 hm，不能重选律。

本公共桥完成后仍不证明：K 的一/二阶导数、梯度等于倾斜均值、Hessian 等于真实协方差、开域/局部逆图、t₀<0/鞍点方程的分析解释、geometric scale 与 canonical K Hessian 的识别、完整 rootA/C 装配、无界 rootB 的正率间隙/远区概率界、R1(9)/(10) 的一般 KL 恒等式与 data processing。这些保持原负责人和未完成状态。

## 6. 独立声明审查的交付门

新上下文应仅接收本稿、source-map 与必要源；不得继承本作者的“看起来直接”作为接受理由。逐项核查：

1. NeZero+Integrable 是否真实足够给严格正实配分，且所有域外/零测度路径均受阻。
2. iSup 的索引确实是完整 domK 子类型，未只取局部参数、支撑参数或候选参数。
3. 所有强制转换先完成实数测试再进入 EReal，没有对 top/bot 做减法或 `.toReal`。
4. T3 的 θ₀ 确实在域；T4 的 hz₀、所有 z∈D、`z≠z₀` 与逐点存在量词完整，结论确实同时保证极小与等号唯一。
5. PR146 两个 actual 完整类型与 consumer 表逐项对应，同 P/q/w、完整 c>0 弱尾域，候选 positivity/derivative 义务未被伪称消除。
6. 仅凭源码读取不能签发 Lean 通过或缓存准备票；本稿未编译，未来 root 的实现/服务器机械门与新上下文完整证明审查另行执行。

本稿不自认证；下一状态只能由 root 接收独立声明审查后决定冻结、修订或拒绝。
