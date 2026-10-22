# 实际 Ξ 导数节点独立声明审查

STATUS: CORRECT

本票仅认可待冻结声明的原文忠实性、完整量词、类型设计及现有 API 适配。它不是证明验收，也不是 Lean 编译或公理审计结果。按任务要求未运行 Lean/Lake，未编写 proof body，未修改任何生产源或其他作者文件；此票完成后 STOP。

## 被审对象及身份

- 审查者：新鲜独立上下文 `/root/xi_derivative_statement_review`；不是提案或证明作者。
- `proposal.md` SHA256：`46bfabdcdfc54701b3303c8ae1cc9e8ae6297794807af8dd201a4018d5581795`。
- `source-map.md` SHA256：`3a7af71ae90ad61a3d5ee37ba3ee28de89160c73e167a14486a5fd5aa42020b9`。
- 基线：v40 accepted `dc1604d8e9c88781166a0c797f45b84ff013673a`，main `5591a25ddc767e6edfd618a88855075c2af7e375`。按 root 通知与 TEAM 记录，公共 Probability 源沿用未变的 v39 内容。
- 独立读取并核实 `QuadraticFullNoise.lean` SHA256 `a280ff36549f2c59356fd4fa89b3e442eece91f2a0e3bb4eea553d3605e1a116`，原 `supplement.tex` SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`，原 `main.tex` SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，均与来源表一致。
- 唯一待冻结公开面：`proposal.md:39–62` 的 `quadraticFullNoiseChar_derivatives` 和 `:70–84` 的 `quadraticFullNoiseChar_derivative_bounds`。新增 public theorem 恰为 2；新增 public definition 为 0。

## 完整类型与量词核对

1. **输入没有隐藏量词或结论性前提。** 两个完整签名分别在 `proposal.md:40–47`、`:71–78` 显式量化同一个实概率律 `ν`、三阶绝对矩可积、实际 `variance id ν > 0`、实数 `h > 0`、AE 支撑和实际商 `gamma ≤ 2*h`。它们逐项吻合已接受 `QuadraticFullNoise.lean:275–279` 的输入；没有新增中心化、导数存在、可微正则性、自由 Ξ、自由噪声律或目标界。实际 gamma 的商中分子为绝对三阶矩、分母为方差，而不是未中心化二阶矩（`proposal.md:45–46,76–79`）。
2. **真实对象及相位方向准确。** `QuadraticFullNoise.lean:26–31` 把律固定为实际双 Fin8 弦族和标量输入的 map，并把特征函数定义为该律下的复指数积分。`proposal.md:48–55` 的 d1、d2 都在同一 `quadraticFullNoiseLaw ν` 上积分。相位与既有定义逐字同形；对实 u 的第一乘子为 `I*z.1`，第二乘子为 `-((z.1^2:ℝ):ℂ)`，与原 `main.tex` LF675–678 的正号傅里叶约定一致。
3. **标准导数没有被候选函数代替。** `proposal.md:56` 是真实特征函数的 `HasDerivAt`；`:57–59` 是其标准一阶 `deriv` 函数的 `HasDerivAt`。`:60–62` 分别给同一个一阶 `deriv` 及标准嵌套 `deriv` 的积分值身份。d1、d2 仅是该定理类型内的局部 `let : ℂ`，不能由调用者自由指定，也不增加公开定义。四项合取的关联和局部 let 范围正确。
4. **全平面和非中心范围完整。** 两个签名的 `u0 v0 : ℝ` 都没有附加条件（`proposal.md:47,78`），故包含两个坐标轴及原点。求导方向是实变量 u、值域为 ℂ，固定的 v0 仍任意；没有误写为复变量导数。源律没有均值为零前提，实际方差定义原样保留。方差正和 h 正是既有构造输入，不是频率排除条件。
5. **范数和常数准确。** `proposal.md:80–84` 对真实一阶及嵌套二阶导数取复数范数，实数常数显式写成 `(67 / 3 : ℝ)` 和 `(70 / 3 : ℝ)`，不存在自然数除法。第二界确为 `(70/3)*h*gamma`。它们恰由 `QuadraticFullNoise.lean:283,285–286,291` 的两个可积性和两个预算对应得到，没有把 Y 的绝对矩项 `:284,287` 误当作 Z 的二阶矩。

## 原文契约及承重范围

原 `supplement.tex` LF2602–2605 要求全实平面上的 `|Xi_u| ≤ C*gamma`、`|Xi_uu| ≤ C*h*gamma`；LF3355–3356 明确把它们分别约化到 `E|Z|`、`EZ²`。已接受的真实矩恰给 LF497–498 的 `67/3`、`70/3`，因此 `proposal.md:70–84` 给出原 (b) 的显式、更精确常数版本。`proposal.md:39–62` 所增加的真实 `HasDerivAt` 和积分身份补足这一步使用导数所需的分析义务，没有改变源数学对象。`proposal.md:9–14,195–201` 对范围的说明与这两个完整签名一致。

这票不覆盖原引理 (a)、(c)、(d)，也不覆盖后继乘积、反演、去平滑或 C1/C2 根闭合；原文 LF2593 的直接消费者只是后继用途。

## Mathlib API 与必要 import 核对

- `proposal.md:21–28` 的一个生产 import、`autoImplicit false`、命名空间与 `open MeasureTheory ProbabilityTheory` 足以表达两套声明；无未声明 section 变量。没有求和符号，因此不需要新增 `BigOperators` scope；定理命题中使用已有非可计算积分/导数常量，不要求为此新增 public definition 或 `noncomputable section`。
- 已直接读取 import 边：`QuadraticFullNoise:1 → QuadraticChordMoments:1 → QuadraticChordNoise:1 → LowFrequencyDamping:1 → QuadraticCharacteristic:5–6`。末端明确导入 `RealDeriv` 与 `ParametricIntegral`；ℝ→ℂ 的标准实标量结构已有实例。无需导入 `QuadraticCharacteristicPower`，其中 private 引理也没有被当作可访问接口。
- 复用 `source-map.md:52–66` 已只读取得的 `hasDerivAt_integral_of_dominated_loc_of_deriv_le` 精确签名，不追加服务器查询。取 `α=ℝ×ℝ`、实参数、复值、`s=univ`，两个 dominator 分别为真实可积的 `|z.1|` 和 `z.1^2`。相位及两个加权相位连续可测，复指数的范数恒为 1；统一界与逐点导数均对所有 z、所有实频率成立，符合该接口的 AE 外层、全邻域内层量词，没有交换量词。
- `source-map.md:68–105` 所列 `.ofReal_comp`、`.deriv`、`.congr_of_eventuallyEq` 及积分范数比较与两个目标的类型相配。已接受 `QuadraticCharacteristicPower.lean:60–69` 直接展示同相位的实到复 `.ofReal_comp`、`.mul_const I`、`.cexp` 组合；`:80–123` 展示两次统一支配积分求导；`:143–165` 展示把第二次结果通过全域第一导数等式接回标准 `deriv`。这里仅以这些既有代码核对接口形状，没有把新节点当作已编译。
- `proposal.md:160–169` 明确使用每个实数 r 处的第一阶身份来得到邻域最终相等，再用 `congr_of_eventuallyEq` 转移第二个 `HasDerivAt`。它没有用单点值相等替代函数邻域相等；这个连接满足标准嵌套导数的要求。
- `norm_integral_le_of_norm_le` 分别接到两个实际可积 dominator 后，所需右端正好是现有两个矩积分；没有额外独立性、有限 iid、源中心化或调用者正则性前提。

## 裁决与停止

关键缺口：无。两项完整声明可由 root 按被审 SHA256 冻结。

机械状态：`NOT_RUN_STATEMENT_REVIEW_ONLY`。这张 CORRECT 票不认证 Lean elaboration 已实际通过，不认证完整证明、公理依赖或新增完成数量；这些仍须在冻结后由分离的作者、服务器检查和新鲜独立证明审查处理。审查者到此 STOP。
