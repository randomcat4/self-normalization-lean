# 正部 Laplace 尾积分与 S1 独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 严格尾积分、实际高斯半质量及显示 BE→S1/真实有限和实例

LEAN_STATUS: 独立服务器无-o目标检查及完整源动态审计均 exit 0，无警告

JUSTIFICATION: 最终源满足冻结全部接口。支付对任意概率 law 真正可积且在[0,1]；严格尾积分在正半轴 Lebesgue 限制测度下真正可积，并通过实际 weighted layer-cake 得到精确恒等式。实际高斯的对称与无原子性证明两项半质量。S1 保留 q≥1、C_BE≥0、1≤β≤L 和真实 CDF 输入，积分比较的有符号下界也单独证明可积，常数恰为1+C_BE。真实有限乘积实例未作条件化。全部29个新增常量通过传递公理白名单，禁用项为空。

## 隔离与冻结对象

审查日期：2026-10-21。先仅阅读冻结声明和匿名推导，完成并冻结 `laplace-tail-math-review-v1.md`，之后才读取本单元最终实现。未读取作者 receipt、summary、declarations、作者会话或其他审稿票。数学票未因后续形式检查改写；其冻结 SHA256 为 `d0427c345f92601aa67e25ae0193d30528bfd61f16c7a63aa85977681ff6fe7e`。

没有修改数学/实现、冻结声明、公共文件、Git 或缓存，没有生成目标 olean。只写所分配两份审查报告。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-laplace-tail-v1.md` | `871f99a3c95fc3aca755fc507a278c63e2fa1c896f53689add04d8b808c320a1` |
| 所审匿名 `drafts/oq4/laplace/proof.md` 快照 | `a367fe447ae78287d4474f8b10f6c3141be22f34865606e940eb74d4ee76d62e` |
| 本机 `drafts/oq4/laplace/LaplaceTail.lean` 与远程 `Shao/OQ4/LaplaceTail.lean` | `5ceb63a9c3955f8479b6c0def43e9c2fdeb9ac2f915aa23553cb2243c3f8ffb9` |
| 已审直接依赖 `IntervalConcentration.lean`，本机/远程一致 | `491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875` |
| 共同 `Shao/Probability/MeasurablePath.lean`，本机 library/远程一致 | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |
| 共同 `Shao/Basic/FinitePath.lean`，本机 library/远程一致 | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 指定服务器 mathlib `MeasureTheory/Integral/Layercake.lean` | `4e3f33d393572ba2892fc8340ab76e0d7e6845a5b5ab41e245825fb71df4a670` |
| 指定服务器 mathlib `Analysis/SpecialFunctions/Gamma/Basic.lean` | `7b2b7c58ee2bef6efd8a96b41cf72f39bd6c698be34bc36c3c31111a01b52926` |

以下行号均为最终 `LaplaceTail.lean` 的一基行号。

## 支付与两侧真实可积性

第12–16行定义实际正部支付、概率 law 下支付积分和权重，表达式精确为冻结的 `1-exp(-max(x,0)/L)` 与 `L⁻¹exp(-u/L)`。第18–43行在任意实数 Borel 概率 μ、L>0 下给支付逐点[0,1]、真正 Integrable 和积分[0,1]。可测性来自连续性，真可积性来自有限概率测度上的绝对值≤1；没有 μ 的矩、密度或支持前提。

第49–51行先证明 ENNReal 尾测度函数反单调可测，再与 toReal 可测映射复合得到真实严格尾函数可测。实际概率 μ 保证尾质量有限并在[0,1]。

第53–73行证明权重仅在 **Ioi 0 的 Lebesgue 限制测度**下 IntegrableOn，且其积分为1；没有错误地宣称该权重在整个实轴可积。第75–84行用可积权重支配可测的 `weight*μ.real(Ioi u)`，明确返回右侧尾积分的真正 IntegrableOn，未要求 μ 有一阶矩。

## 严格尾恒等式与 layer-cake 应用

第87–101行通过真正导数、连续权重的区间可积性及 FTC，证明权重从0到v的原函数恒等式。此辅助结论对负 v 也用带方向区间积分，主证明只在 v=max(x,0)≥0 处使用。

第103–139行实际应用 `lintegral_comp_eq_lintegral_meas_lt_mul`。独立服务器核对该 API 的完整签名：要求 f a.e.非负和可测、g 在每个正的有限区间0..t可积、g 在 Ioi 0 上非负；结论使用严格集合 `{a | t<f a}`。本处 f=max(x,0)、g=实际权重，所有要求都明确供应。

第126–131行在 u>0 上逐点证明 `{x | u<max(x,0)}=Ioi u`，然后用概率测度的 `measure_ne_top` 正当化 real/ENNReal 的转换。因此尾事件精确为 **x>u**，与 CDF 的≤u互补；未将它换成≥u或丢弃 μ 的原子。

最后由两个非负积分的 lintegral 表达式改写回真实实积分。虽然该转换公式本身允许不可积情形，本源已经独立证明并在此使用了 `integrable_positiveLaplace` 与 `integrable_laplaceTail`；故这里两侧实际可积有限，不是两侧默认0。无界支持及任意原子均保留。

## 实际高斯两项半质量

第141–165行的 γ 明确是 `gaussianReal 0 1`。第143行以真实方差参数1≠0实例化其 NullSingletonClass；第145–154行用实际 `gaussianReal_map_neg` 和可测负号推送的半直线原像得到 γ.real(Ioi 0)=γ.real(Iio 0)。第155–161行用真实零点无原子性连接 Iic 0 与 Iio 0，再用有限概率补集总质量1，得实际 γ.real(Ioi 0)=1/2。

第167–171行通过已审的实际 `standardNormalCDF_eq_real` 与上述真实半质量，证明 Φ(0)=1/2。两项都是无额外输入的实际高斯结论，而非抽象对称/中心质量假设。

## 积分一阶权重与实际 S1

第174–199行分别用实际指数/Gamma 积分接口证明 `u*weight` 在 Ioi 0 下真正可积及其积分=L，均使用 L>0；没有用 μ 的一阶矩替代它。

第202–218行是较强的辅助尾界：q≥1保证正 sqrt(q)，在显示 CDF 输入取 x=u/sqrt(q) 后，正分母将原像精确识别为 Iic u。实际 Φ 的1-Lipschitz及本模块 Φ(0)=1/2 控制 Φ(u/sqrt(q))，实际概率补集关系给严格 Ioi 尾下界。u≥0包括0，原子不影响该补集公式。

第221–225行的 S1 完整签名保留 μ 为任意概率 law、自然 q≥1、C_BE≥0、1≤β≤L 及对所有实 x 的真实归一化 CDF 误差。L>0从1≤β≤L推得，没有新增矩、中心、密度或“大q”条件。

第229–241行将可能为负的比较函数 `weight*(1/2-u/sqrt(q)-ε)` 精确分解为权重与 u权重的实标量线性组合，单独证明其真正可积并计算积分。第242–248行使用它与真实尾函数两侧可积性进行积分单调比较，再用已证严格尾恒等式。第249–253行只使用 C_BE≥0、β≤L 和正分母放大误差，给准确 `1/2-(1+C_BE)L/sqrt(q)`。

这里仅用一次 CDF 误差；没有误换成1+2C_BE。小 q 时显示下界可以为负，定理没有要求其为正；独立的 `laplacePayment_bounds` 仍供应 A_L≥0。C_BE=0 与 β=L 的端点不被排除。

## 真实未条件化有限和实例

第255–280行定义源 A_q 为真正 Π_q 下的 prefixSum 正部支付，直接用可测前缀复合和[0,1]有界性证明产品被积函数 Integrable，给[0,1]界。此部分甚至允许 q=0；涉及归一化 S1 的下一接口仍明确要求 q≥1，没有默认除0。

第282–287行完整保留自然 q≥1、C_BE≥0、1≤β≤L，以及真实 Π_q 下实际 prefixSum/sqrt(q) 的全部 CDF 输入，不加入 ν 的矩、均值、密度、格点或有界支持条件。

第288–296行构造真实未条件化 `law=Π_q`、可测 `X=prefixSum(·,q)` 和推送 μ，并证明 μ 是概率测度。第297–304行用可测归一化半直线的真实 map_apply 将产品输入精确转成 μ 的 CDF 前提。第306–310行使用 μ 下真正支付可积性和推送积分公式，精确识别为原产品支付，再调用前述 S1；产品可积性也已经独立证明，没有生存条件化或默认0。

## 独立服务器与运输证据

已读 SERVER.md。先通过共享 broker 做只读有界健康探测，得到实际远程最终 SHA 与 UTC `2026-10-21T13:49:14Z`、exit0，确认本轮运输正常。之后同一 broker 正常完成检查，无拒绝、无不确定状态、无重放或备用通道调用。

在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`，远程脚本明确 `set -e`、`set -o pipefail`，先激活环境再 cd，顺序运行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/LaplaceTail.lean
{ 最终完整源码 + #print/#check 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，不生成目标 olean，不构建/更新 Lake 或获取缓存。目标及源加附录无警告，broker exit_code=0、stderr 为空。分别输出 `TARGET_CHECK_EXIT=0` 与 `SOURCE_DYNAMIC_AUDIT_EXIT=0`，UTC 为 `2026-10-21T13:50:08Z`。目标前后 SHA 均等于本机最终值，共同/已审依赖也逐项一致。

动态遍历实际 `env.constants.toList` 中**全部** `env.getModuleIdxFor? declName = none` 声明，无 namespace/root 筛选。对每项调用 `Lean.collectAxioms`，若任何传递公理不在 `{propext, Classical.choice, Quot.sound}` 中立即报错。完整最终源在 stdin 中实际检查，结果为：

```text
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 29
SOURCE_DYNAMIC_AUDIT_EXIT=0
```

实际23个显式声明全部被枚举：

```text
Shao.OQ4.positiveLaplace
Shao.OQ4.laplacePayment
Shao.OQ4.laplaceWeight
Shao.OQ4.positiveLaplace_bounds
Shao.OQ4.integrable_positiveLaplace
Shao.OQ4.laplacePayment_bounds
Shao.OQ4.laplaceWeight_nonneg
Shao.OQ4.measurable_strictTail
Shao.OQ4.integrable_laplaceWeight
Shao.OQ4.integral_laplaceWeight
Shao.OQ4.integrable_laplaceTail
Shao.OQ4.laplaceWeight_primitive
Shao.OQ4.laplacePayment_eq_strictTail
Shao.OQ4.standardGaussian_positive_mass
Shao.OQ4.standardNormalCDF_zero
Shao.OQ4.integrable_mul_laplaceWeight
Shao.OQ4.integral_mul_laplaceWeight
Shao.OQ4.strictTail_lower_bound_of_cdf
Shao.OQ4.laplacePayment_lower_bound_of_cdf
Shao.OQ4.finiteSumLaplacePayment
Shao.OQ4.iid_integrable_positiveLaplace
Shao.OQ4.finiteSumLaplacePayment_bounds
Shao.OQ4.finiteSumLaplacePayment_lower_bound_of_cdf
```

6个实际生成辅助声明同样全部审计：

```text
Shao.OQ4.laplacePayment_eq_strictTail._simp_1_1
Shao.OQ4.laplacePayment_eq_strictTail._simp_1_2
Shao.OQ4.standardGaussian_positive_mass._simp_1_1
Shao.OQ4.standardGaussian_positive_mass._simp_1_2
Shao.OQ4.standardGaussian_positive_mass._simp_1_3
Shao.OQ4.standardGaussian_positive_mass._simp_1_4
```

29项传递公理均为标准白名单子集；23项显式声明使用标准三项。严格尾恒等式、实际高斯半质量、μ版本 S1 与有限和版本 S1 另逐项独立 `#print axioms`，同样只有标准三项。没有 sorryAx 或新增公理。

最终远程源禁用项正则 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 扫描输出：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

本票只关闭正部支付的严格尾解析、实际标准高斯半质量，以及从明确 BE-CDF 前提到 S1 和真实未条件化有限和实例的约化。没有将 BE 前提或正态近似的适用矩类视为已证。

**BE、SP、S2/S3、无条件 S/AC/O0/R3/R4、B1、长期 K/Kv、4/π、E1–E6、完整 OQ4 及其他全部根组保持 OPEN。**

## Superseding current-source：必要格式精确复查

CURRENT_STATUS: CORRECT

CURRENT_SCOPE: FULLY_CHECKED

CURRENT_SOURCE_SHA256: `664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2`

本节为实际格式门发现末尾 CRLF/冗余空行后产生的新源复查，**取代上文关于“当前最终源”的指向**。上文 `5ceb63a9c3955f8479b6c0def43e9c2fdeb9ac2f915aa23553cb2243c3f8ffb9` 保留为历史已审源；当前认可源为本节664df6版本，数学接口和原有证明审查结论不变。未改原匿名 proof 快照或原数学票。

### 独立精确变换

在服务器只读打开历史源 `repro_outputs/oq4-laplace/LaplaceTail.before-format-5ceb.lean` 与当前 `Shao/OQ4/LaplaceTail.lean`，实际计算：

```text
old.replace(b'\r\n', b'\n').rstrip(b'\n') + b'\n' == new
EXACT_REQUESTED_TRANSFORM True
OLD_BYTES 15121   OLD_CRLF 5
NEW_BYTES 15112   NEW_CRLF 0
NEW_SINGLE_TERMINAL_LF True
```

旧字节 SHA256 实际为历史5ceb63a9全值，新字节 SHA256 实际为当前664df6aa全值，且上述两个预期哈希与精确变换均经断言核验。UTC `2026-10-21T14:21:01Z`，broker exit0、stderr为空。本机当前源同为15112字节、CRLF数0、相同664df6aa全值。

因此变化仅为5个 CRLF 的 CR 删除及末尾4个冗余 LF 删除；保留单个末尾 LF。全部定义、声明、证明体与非空代码行完全相同，原文代码行号继续适用。没有数学、前提、签名或 proof 快照变化。

### 当前源独立认证

对当前新哈希再次执行实际无-o目标检查及完整当前源加动态审计附录的 Lean stdin 检查。脚本保持 `set -e`、`set -o pipefail`，先 activate 后 cd；两个 Lean 过程顺序运行、均 `taskset -c 0-3`，均不带 `-o`。未生成目标 olean、改缓存或依据作者 receipt/olean 哈希替代核验。

两过程实际输出：

```text
CURRENT_SOURCE_TARGET_EXIT=0
CURRENT_ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 29
CURRENT_SOURCE_DYNAMIC_AUDIT_EXIT=0
CURRENT_PROHIBITED_TOKEN_HITS []
```

动态遍历全部实际 `getModuleIdxFor? = none` 常量，无 namespace/root 筛选；对每项 collectAxioms 并强制仅允许 `{propext, Classical.choice, Quot.sound}`。当前实际29项名称与上文23项显式声明及6项辅助声明一致，全部通过。严格尾恒等式、实际高斯半质量、μ版本S1与有限和S1另逐项 `#print axioms` 均仍为标准三项；主尾公式及两个S1完整签名也实际复核无变化。

目标和完整源审计均无警告，broker exit0、stderr为空；UTC `2026-10-21T14:21:47Z`。当前源检查前后哈希均为664df6aa全值。`IntervalConcentration.lean`、共同 `MeasurablePath.lean` 与 `FinitePath.lean` 的实际服务器哈希仍分别为上表491e088f、827dc47b、89826289全值，与本机一致。

原形式票追加前11001字节的 SHA256 为 `dddb41a790d67a1bcc306c8f4cb79a71fb467eac138aa39dc73d1271bef0818c`，正文完整保留，仅追加本节。原数学票仍为冻结 SHA256 `d0427c345f92601aa67e25ae0193d30528bfd61f16c7a63aa85977681ff6fe7e`；原匿名 proof 仍为 `a367fe447ae78287d4474f8b10f6c3141be22f34865606e940eb74d4ee76d62e`。审查票继续使用 UTF-8、LF、无BOM。

**当前新源 STATUS CORRECT / FULLY_CHECKED；认证范围仍仅为原票所述显示BE→S1有限约化，全部完整根保持 OPEN。**
