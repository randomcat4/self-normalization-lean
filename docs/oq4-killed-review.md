# F-K1/F-K2/F-K3 单步被杀余弦独立审查 v1

STATUS: CORRECT

LEAN_STATUS: LEAN_FULLY_CHECKED

JUSTIFICATION: 最终代码与冻结的三个有限接口逐项一致。任意实频率和阈值的精确恒等式、闭区间严格退出、全局大跳几何、超越量可积性及 `1/48` 三阶残差常数均有完整证明。独立服务器目标检查、九个新增常量的动态传递公理审计及禁用项扫描通过。裁决仅限冻结的单步接口。

## 审查对象与版本

审查日期：2026-10-21；独立服务器检查完成于 `2026-10-21T09:13:02Z`。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-killed-cosine-v1.md` | `483de76802e3d17e6fc797e6d78d59bffa8ef0491bbc7bba2b760c3dc97d51ac` |
| 当前匿名 `drafts/oq4/killed/proof.md` | `5da3ddc40c1555d96e5efcf802bbe1385fd36e68905289ef07142a8e37b66a3f` |
| 本机 `drafts/oq4/killed/KilledCosine.lean` | `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8` |
| 远程 `Shao/OQ4/KilledCosine.lean` | `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8` |
| 远程已审 R0 依赖 `Shao/OQ4/CosineCoefficients.lean` | `8fa6f094c330a8006c5664f8912cafd035524cc461df95e81446d2384a46c104` |

远程工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。目标本机与远程哈希一致，实际服务器检查前后目标哈希一致。以下 Lean 行号均对应该最终版本。

审查者独立读取冻结声明、新匿名推导及最终代码，未读取作者 receipt、作者会话或其他票。匿名证明头部的检查自述未用作认证证据。该匿名文件本轮仅更新第 3 行检查自述，数学推导内容保持一致并已核对。没有修改实现、冻结前提、公共接口或缓存，唯一写入为本报告。

## 定义与概率律语义

冻结第 5–8 行对应 Lean 第 16–25 行：`Kcos` 为闭区间条件 `|z+y|≤h` 下保留余弦的普通积分；`cosineCoefficient`、`sineCoefficient` 分别为自由的一步 `∫cos(ay)`、`∫sin(ay)`。三者没有被定义成特征值或长时间核。

`ν : Measure ℝ` 使用 Mathlib 的标准实数 Borel 可测空间，而非一个另行量化的任意实数可测结构。F-K1 和 F-K3 都显式保留 `[IsProbabilityMeasure ν]`；没有原子排除、格点排除或密度假设。

## F-K1：任意 a,h,z 的精确恒等式

STATUS: CORRECT

JUSTIFICATION:

1. 冻结第 10–12 行与 Lean 第 41–44 行完全一致：`a,h,z : ℝ` 没有正性、边界内或矩条件。退出项为集合积分 `{y | h<|z+y|}`，即严格离开闭区间。
2. 第 28–38 行的辅助声明将严格退出集合积分精确改写成“若 `|z+y|≤h` 则 0，否则余弦”的积分。退出集合 Borel 可测，逐点等价由全序的 `¬(|z+y|≤h) ↔ h<|z+y|` 给出。辅助等式本身对任意测度成立；主结论另有概率律，所以实际被积函数都可积，不依赖不可积积分的默认值。
3. 第 45–59 行对完整余弦及自由正弦/余弦分别用连续可测性、绝对值界 `1` 和概率测度证明可积。第 60–79 行证明闭区间可测、内部截断可积、外部截断为完整函数减内部函数而可积。因而第 80–85 行有限分解积分所需的全部可积条件真实满足。
4. 第 86–90 行直接使用 `cos(a(z+y))=cos(az)cos(ay)-sin(az)sin(ay)`。两项常数乘积可积，积分相减与常数提出均有明确条件。第 91 行只作实数代数移项，得到冻结的两个负号和乘积次序，没有偷偷假定 `η=0` 或 `ρ>0`。
5. 等号边界属于内部；`h=0`、`h<0`、`a=0` 或负 `a` 均未排除。特别是 `h<0` 时内部为空、外部为全空间，分解与余弦加法仍成立。原子落在边界时也没有丢失。

未发现关键缺口。

## F-K2：任意大跳的正部几何界

STATUS: CORRECT

JUSTIFICATION:

1. 冻结第 14–19 行与 Lean 第 94–96 行一致：`h>0`、`|z|≤h`、每个 `y:ℝ`，相位为 `a=π/(2h)`，右侧保留完整的 `max (|y|-(h-|z|)) 0`。`_hz` 在这一更强的几何证明中未使用，但仍留在冻结公开签名中，没有缩小量词。
2. 第 97–103 行确证 `a>0`；在保留区间的分支左侧恰为零，右侧由正部非负得到非负。事件在等号处选择保留分支。
3. 退出分支第 105–115 行有 `u=|z+y|>h`，并精确证明 `a*h=π/2`、`cos(a*h)=0`。通过余弦偶性将两个边界统一到 `u`；实际调用 `Real.abs_cos_sub_cos_le` 为全局余弦 Lipschitz 界，得到 `|cos(a(z+y))|≤a(u-h)`。移除绝对值时使用的 `a>0`、`u-h≥0` 都已确证。
4. 第 116–121 行以三角不等式得到 `u-h≤|y|+|z|-h=|y|-(h-|z|)`，再比较正部并乘非负 `a`。没有限制离边界距离、跳跃大小或所处三角函数周期；大跳跨越任意多个半周期仍被同一全局界覆盖。
5. `|z|=h` 时距离为零，点态界仍成立。代码全程没有除以 `cos(az)`，也没有在其边界零点外定义相对残差；两端点 `cos(±π/2)=0` 与冻结语义一致。

未发现关键缺口。

## F-K3：超越量可积与期望残差

STATUS: CORRECT

JUSTIFICATION:

1. 冻结第 21–24 行与 Lean 第 124–136 行一致：保留概率律、`h>0`、`|z|≤h`、id/平方/第三绝对幂三项可积性、均值零和二阶矩一，`β` 为真实第三绝对矩。结论的合取第一项显式返回超越量可积性，第二项精确使用 `π³β/(48h³)` 和原始超越量积分。
2. 第 138–144 行从 `|z|≤h` 得到 `d=h-|z|≥0`，超越函数 `ψ(y)=max(|y|-d)0` 连续可测，且逐点 `0≤ψ≤|y|`。`hId.abs` 及 `Integrable.mono'` 因此证明 `ψ` 可积。这一步只消耗原始一阶矩；在端点 `d=0` 时 `ψ=|y|`，可积性同样完整。
3. 第 147–150 行在已经独立审查并实际编译的 R0 `cosine_coefficients_h_bound` 中取 `Y=id`。所需三个可积条件、均值、二阶矩和 `h>0` 全部由当前原始假设供应，得到 `|η|≤π³β/(48h³)`。常数没有改为隐藏的未给定量，也没有额外的第四矩或对称性。
4. 第 151–160 行先用严格退出集合等式，再使用 F-K2 的逐点界和可积控制函数 `a*ψ`，合法得到 `|∫退出余弦|≤a∫ψ`。退出余弦在概率律下本身也为有界 Borel 可积函数，因而这是真实积分估计。
5. 第 161–182 行由 `|sin(az)|≤1`、F-K1 的精确恒等式和三角不等式，得到 `|Kcos-ρcos(az)|≤|η|+a∫ψ`。第 166–167 行将 `az` 精确改写为 `πz/(2h)`；最后合并 R0 和超越量上界，正好得到冻结式。
6. 原子、格点、任意大跳和 `|z|=h` 均保留；未除以端点为零的余弦，未把自由 `ρ` 当作杀死核特征值。没有新增有界支持、非格点、密度、对称性、指数矩或高阶矩条件。

未发现关键缺口。

## 独立服务器核验及全部新增声明公理

使用项目钉死环境：Lean `4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。本轮通过 `tools/server.py` 的新共享连接协议执行，未使用旧直连作为自动重试；该请求正常返回远程 `exit_code=0`、空 `stderr`。所有 Lean 仅在指定服务器执行，未安装本机 Lean，未补缓存，未生成作者模块的 olean。

实际目标命令：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KilledCosine.lean
```

退出 `0`，无警告。随后将最终目标源、三个主定理的 `#print axioms` 以及动态审计命令经标准输入送入服务器 `taskset -c 0-3 lake env lean --stdin`，退出 `0`。

动态审计遍历 `env.constants.toList`，筛选 `env.getModuleIdxFor?` 为 `none` 的当前模块常量，并保留 `Shao.OQ4` 命名空间，故排除了已导入 R0 的十一项常量。对全部新增声明调用 `Lean.collectAxioms`，逐项执行白名单检查。实际新增为七个显式声明及两个自动生成方程声明，共九项：

```text
Shao.OQ4.Kcos: [propext, Classical.choice, Quot.sound]
Shao.OQ4.Kcos.eq_1: [propext, Classical.choice, Quot.sound]
Shao.OQ4.cosineCoefficient: [propext, Classical.choice, Quot.sound]
Shao.OQ4.sineCoefficient: [propext, Classical.choice, Quot.sound]
Shao.OQ4.sineCoefficient.eq_1: [propext, Classical.choice, Quot.sound]
Shao.OQ4.integral_strict_exit_cosine_eq: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killed_cosine_identity: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killed_cosine_boundary_bound: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killed_cosine_residual_bound: [propext, Classical.choice, Quot.sound]
NEW_DECL_COUNT 9
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
```

目标源的 `sorry|admit|axiom|unsafe|native_decide` 词项扫描为空。全部新增声明的传递公理均在许可白名单内，R0 依赖的远程源哈希与此前独立认证的最终版本一致。

## 裁决范围与根状态

**F-K1/F-K2/F-K3 的冻结单步接口可记为 LEAN_FULLY_CHECKED。** 本票只认证普通一步积分恒等式、闭边界几何和矩残差，不修改共同 path/kernel 接口。

从该逐点单步残差到 R3 仍需占据输入 O0 与边界平均支付；R3、R4、B1、终端块及长时间 K/Kv 均未在本票关闭。**完整 OQ4 和全部其他根组保持 OPEN。**
