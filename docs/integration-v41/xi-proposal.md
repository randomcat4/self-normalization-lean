# 实际 Ξ 全实平面一、二阶 u 导数：精确声明候选 v2

状态：`PROPOSED_PENDING_INDEPENDENT_DECLARATION_REVIEW`。本文件是声明和数学证明路线，不是 Lean 源文件；下列 Lean 代码只列完整 header 与类型，故意不附 proof body。未运行 Lean，未编写生产证明。冻结权属于 root；独立声明审查前停止。

版本续记：root 已通知 v40 accepted dc1604d8e9c88781166a0c797f45b84ff013673a、main 5591a25ddc767e6edfd618a88855075c2af7e375；公共 Probability 源未变，保留已核前置源 SHA256，不重查 API/缓存。

## 承重范围与输入契约

- 原目标：`supplement.tex` 的 `h:supp:highderivatives(b)`，LF2595–2605；证明 LF3355–3356。
- 消除义务：实际 `quadraticFullNoiseChar ν` 在每个 `(u0,v0) ∈ ℝ²` 的一、二阶 u 导数存在，导数等于实际概率律下的加权积分，并有 `67/3 * gamma` 与 `70/3 * h * gamma` 的全局界。
- 直接消费者：源文 `D_{n-i}''` 与 `(u E_{n-i})''` 的全局噪声因子项，以及后继实际乘积求导模块。此节点只覆盖引理 (b)；锥内 (a)、高频 (c)/(d)、反演、去平滑与原 C1/C2 根结论仍未闭合。
- 唯一源律是 `ν : Measure ℝ`；所有新声明都使用既有 `quadraticFullNoiseLaw ν` 和 `quadraticFullNoiseChar ν`，没有自由的 Ξ 乘子或替代噪声律。
- 全部输入恰为既有支持/矩接口的输入：`IsProbabilityMeasure ν`、三阶绝对矩可积、实际方差正、`h > 0`、`ν` 几乎处处 `|a| ≤ h`，以及实际 `gamma ≤ 2*h`。不要求 `ν` 中心化，不要求 `u0 ≠ 0`、`v0 ≠ 0`，不输入导数存在性、正则性、积分公式或目标界。
- `gamma` 始终是 `(∫ a : ℝ, |a|^3 ∂ν) / variance (id : ℝ → ℝ) ν`；没有另设可自由选择的 gamma。

## 最小生产文件 header

拟文件：`Shao/Probability/QuadraticFullNoiseDerivatives.lean`。

```lean
import Shao.Probability.QuadraticFullNoise

set_option autoImplicit false

namespace Shao.Probability

open MeasureTheory ProbabilityTheory
```

文件最后为 `end Shao.Probability`。不需要新 public definition、`BigOperators` scope、局部 `NormedSpace` instance、`QuadraticCharacteristicPower` import，或新的泛型概率空间。唯一 import 已传递包含 `RealDeriv` 与 `ParametricIntegral`：`QuadraticFullNoise → QuadraticChordMoments → QuadraticChordNoise → LowFrequencyDamping → QuadraticCharacteristic`。这些是已接受生产源码的明确 import 边，不是根据名字猜测。

## 两个待冻结的公开声明

只新增下面两个 public theorem。第一项合取给出两个真实 HasDerivAt 和对应的标准 deriv 积分身份；第二项合取给出两个全局界。d1、d2 是定理类型中的局部 let 绑定，明确展开为实际律下的积分，不是额外 public definition 或自由函数。

### 1. 两次实际 HasDerivAt 及其积分身份

```lean
theorem quadraticFullNoiseChar_derivatives
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂ν) /
      variance (id : ℝ → ℝ) ν ≤ 2 * h)
    (u0 v0 : ℝ) :
    let d1 : ℂ := ∫ z : ℝ × ℝ,
      Complex.I * (z.1 : ℂ) *
        Complex.exp (((u0 * z.1 + v0 * z.2 : ℝ) : ℂ) * Complex.I)
      ∂quadraticFullNoiseLaw ν
    let d2 : ℂ := ∫ z : ℝ × ℝ,
      -((z.1 ^ 2 : ℝ) : ℂ) *
        Complex.exp (((u0 * z.1 + v0 * z.2 : ℝ) : ℂ) * Complex.I)
      ∂quadraticFullNoiseLaw ν
    HasDerivAt (fun u : ℝ => quadraticFullNoiseChar ν u v0) d1 u0 ∧
    HasDerivAt
      (fun u : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v0) u)
      d2 u0 ∧
    deriv (fun u : ℝ => quadraticFullNoiseChar ν u v0) u0 = d1 ∧
    deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v0) u) u0 = d2
```

第一、二个合取项分别是实际特征积分及其实际标准一阶导数函数的 HasDerivAt；第三、四个合取项是前两项的标准导数值身份，供下游直接重写使用。第二阶左端没有换成候选导数。全部四个输出共享同一、完全量化的输入契约。

### 2. 两个实际导数的显式全局常数界

```lean
theorem quadraticFullNoiseChar_derivative_bounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun a : ℝ => |a| ^ 3) ν)
    (hV : 0 < variance (id : ℝ → ℝ) ν)
    (h : ℝ) (hh : 0 < h)
    (hs : ∀ᵐ a : ℝ ∂ν, |a| ≤ h)
    (hgamma : (∫ a : ℝ, |a| ^ 3 ∂ν) /
      variance (id : ℝ → ℝ) ν ≤ 2 * h)
    (u0 v0 : ℝ) :
    let gamma := (∫ a : ℝ, |a| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν
    ‖deriv (fun u : ℝ => quadraticFullNoiseChar ν u v0) u0‖ ≤
      (67 / 3 : ℝ) * gamma ∧
    ‖deriv
      (fun u : ℝ => deriv (fun r : ℝ => quadraticFullNoiseChar ν r v0) u) u0‖ ≤
      (70 / 3 : ℝ) * h * gamma
```

没有另列标准导数包装、范数包装或定义展开包装为额外公开节点。这两个声明是本次独立声明审查的完整对象；没有隐藏 section 变量。

## 完整数学证明路线

以下给出可直接转写的完整数学论证；它未被机械检查或独立证明验收。

### A. 只提取既有实际律与矩数据

固定上述所有输入，记 `μ = quadraticFullNoiseLaw ν`，`gamma` 为声明中的实际商。

1. 由 `quadraticFullNoise_law_data ν h3 hV h hh hs` 的第三个分量获得 `IsProbabilityMeasure μ`，在局部登记这一 instance。因此 `μ` 有限，常数 1 可积。
2. 由 `quadraticFullNoise_support_moments ν h3 hV h hh hs hgamma` 提取：
   - `∀ᵐ z ∂μ, |z.1| ≤ 34*h ∧ |z.2| ≤ 64*h^2`；
   - `Integrable (fun z => |z.1|) μ`，记为 `hM1`；
   - `Integrable (fun z => z.1^2) μ`，记为 `hM2`；
   - `∫ |z.1| dμ ≤ (67/3)*gamma`，记为 `bM1`；
   - `∫ z.1^2 dμ ≤ (70/3)*h*gamma`，记为 `bM2`。
3. 这些矩数据已在既有实际构造中证明，不能变成新定理的输入。尤其无需重新构造噪声、独立副本或 Brownian 对象。支撑数据确保实际矩来源为有界噪声；新求导中最小的统一支配函数直接使用已接受的 `hM1`、`hM2`。支配函数不依赖频率，不需要拿较粗的 `34*h` 常数界替代精确矩预算。

### B. 相位、加权积分与逐点导数

对任意实数 `t` 和 `z : ℝ×ℝ`，固定 `v0` 并记

\[
 E(t,z)=\exp\bigl(i(tz_1+v_0z_2)\bigr),\qquad
 F_1(t,z)=iz_1 E(t,z),\qquad
 F_2(t,z)=-z_1^2 E(t,z).
\]

上述复数表达式与第一个公开定理中的强制类型转换、相位方向完全相同。因 `t,z1,v0,z2` 都为实数，复指数指数的实部为 0，所以对所有 `t,z` 都有

\[
 |E(t,z)|=1,\qquad |F_1(t,z)|=|z_1|,\qquad
 |F_2(t,z)|=z_1^2.
\]

对固定 `t`，三个 `z` 函数均连续，故关于实际 `μ` 强可测/几乎处处强可测。`E(t,·)` 被常数 1 支配而可积；`F1(t,·)` 被可积函数 `|z1|` 支配而可积；`F2(t,·)` 被可积函数 `z1²` 支配而可积。可积性可逐项用 `Integrable.mono'` 给出，支配函数正是本步骤的三个范数恒等式。

固定任意 `z`，实变量 `t` 的仿射实相位 `t*z1+v0*z2` 的导数为 `z1`。将它用 `HasDerivAt.ofReal_comp` 视为复值函数，再乘 `Complex.I` 并用复指数链式法则 `.cexp`，得

\[
 \frac{d}{dt}E(t,z)=iz_1E(t,z)=F_1(t,z).
\]

乘上与 `t` 无关的 `iz1`，利用 `i²=-1`，得

\[
 \frac{d}{dt}F_1(t,z)=(iz_1)^2E(t,z)=-z_1^2E(t,z)=F_2(t,z).
\]

这两个逐点 `HasDerivAt` 对每个实数 `t` 都成立。对现有库的复指数链式法则，已有接受代码 `QuadraticCharacteristicPower.lean:60–70` 给出同一导数表达式，`:96 起的 weighted_exp_integral_hasDerivAt` 给出加权版本的同一化简方法；本节点只需相同的 `ofReal_comp`、`mul_const`、`.cexp`、`const_mul` 组合及 `push_cast`/环恒等式化简，不需要引入新外部数学引理。

### C. 两次在真实积分内求导

第一次应用 `hasDerivAt_integral_of_dominated_loc_of_deriv_le`，取参数域 `s = Set.univ`、目标点 `u0`、`F = E`、`F' = F1`、`bound z = |z.1|`、测度 `μ`。逐项核对它的七个条件：

1. `Set.univ` 是 `u0` 的邻域。
2. 对所有 `t`，`E(t,·)` 几乎处处强可测，因此也在 `u0` 邻域最终如此。
3. `E(u0,·)` 被 1 支配，故可积。
4. `F1(u0,·)` 几乎处处强可测。
5. 对所有 `z,t` 有 `‖F1(t,z)‖ = |z1|`，从而满足“对几乎处处 z，对所有 t∈s”的统一界；这里量词顺序没有互换。
6. `bound` 可积，恰由 `hM1`。
7. 逐点导数 `HasDerivAt (fun t => E(t,z)) (F1(t,z)) t` 对所有 `z,t` 成立，因此也满足其 AE 形式。

该 API 返回 `Integrable (F1 u0) μ ∧ HasDerivAt (fun t => ∫ E(t,z) dμ) (∫ F1(u0,z) dμ) u0`。第二个分量在展开既有 `quadraticFullNoiseChar` 后就是第一公开定理的首个 HasDerivAt 分量，且对每个真实点 `u0` 都成立。

第二次同一 API 取 `F = F1`、`F' = F2`、`bound z = z.1^2`、仍取 `s=univ` 和同一个实际律 `μ`。`F1(u0,·)` 的可积性见步骤 B；`F2` 的可测性、逐点导数、对所有 `t` 的范数界见步骤 B；`bound` 可积恰为 `hM2`。因此

\[
 \operatorname{HasDerivAt}\left(t\mapsto\int F_1(t,z)d\mu(z)\right)
       \left(\int F_2(u_0,z)d\mu(z)\right)u_0.
\]

还须将这一式的函数确认为实际标准一阶导数：对任意实数 `r`，将已证明的第一阶 HasDerivAt 在 `(r,v0)` 处取 `.deriv`，即得

\[
 \operatorname{deriv}\bigl(t\mapsto\Xi(t,v_0)\bigr)(r)
       =\int F_1(r,z)d\mu(z).
\]

这是所有实数 `r` 上的等式，因此给出 `u0` 邻域的 `EventuallyEq`。对上面的加权积分 `HasDerivAt` 用 `HasDerivAt.congr_of_eventuallyEq`，方向取“实际 deriv 函数 = 加权积分函数”，得到第一公开定理的第二个 HasDerivAt 分量。仅在 `u0` 单点的等式不足以做这一步；本路线已明确使用所有 `r` 处的第一阶结果。

对两个 HasDerivAt 各取一次 `.deriv` 得到第一公开定理的第三、四个合取项。由此二阶结论明确是标准嵌套 `deriv` 的积分值，而非只证明一个新命名函数的导数。

### D. 精确常数界

由第一公开定理的第三个合取项、复积分三角不等式和逐点范数式，

\[
 |\Xi_u(u_0,v_0)|
 =\left|\int F_1(u_0,z)d\mu(z)\right|
 \le\int |z_1|d\mu(z)
 \le\frac{67}{3}\,\gamma.
\]

Lean 中可直接对 `hM1` 使用 `norm_integral_le_of_norm_le`，AE 比较由 `‖F1‖ = |z1|` 提供，然后传递 `bM1`，得到第二公开定理的第一个合取项。

由第一公开定理的第四个合取项同理，

\[
 |\Xi_{uu}(u_0,v_0)|
 =\left|\int F_2(u_0,z)d\mu(z)\right|
 \le\int z_1^2d\mu(z)
 \le\frac{70}{3}\,h\gamma.
\]

Lean 中使用 `hM2`、`‖F2‖ = z1²` 与 `bM2`，得到第二公开定理的第二个合取项。这里 `z1² ≥ 0` 恒成立，复数范数化简成实数时不会遗留绝对值符号或符号条件。

### E. 全域、非中心与边界核对

- `u0` 与 `v0` 任意，证明没有除以它们、没有频率截断、没有锥条件，故 `(0,v0)`、`(u0,0)` 及 `(0,0)` 全部覆盖。
- 只对实数 u 求导，结果为复数；未声称复频率整函数或对 v 求导。
- `ν` 的均值没有出现在声明或支配求导步骤中；方差是实际 `variance id ν`，没有替换成未中心化二阶矩。源律可非中心。
- `hV > 0` 保留实际噪声构造的非退化条件；不覆盖方差零且任意指定 gamma 的其他构造。
- `hgamma` 原样保留为既有实际矩接口的输入。无需新第三矩/第四矩、独立性输入、微分正则性或假定目标界。

## 最小依赖与审查门

数学新义务只有三类：相位的逐点实导数、两次满足统一支配条件的积分求导、范数积分比较。它们都已有明确 Mathlib API 和已接受同型用例，详见 `source-map.md`。无需重新证明现有完整 Ξ、moments 或 Brownian。

本轮唯一服务器操作是限定文件和限定符号的只读 API/source/olean 存在性研究，退出码 0；没有启动 Lean/Lake，没有读取全部缓存，没有修改远端文件。指定 `ParametricIntegral`、`RealDeriv`、`Deriv.Basic`、`Bochner.Basic` 的 olean 均存在。只读检查发现历史 `workspaces/lead-c12` 没有 `QuadraticFullNoise.lean`，因此本提案的完整噪声契约以 root 指定的 v39 accepted 源及已核 SHA256 的本地 curated snapshot 为准，没有把旧工作树当作当前验收版本。

下一步严格为：独立审查两项完整合取声明及来源对应 → root 冻结 → 才能另行授权生产 proof body → 服务器针对性编译、完整独立证明审查与传递公理审计。此后续节点不计入 已合入的 v40，也不据此宣布 C1/C2 根闭合。
