# 实际有限生存 Laplace 独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 原始 SP 与 uniform BE-CDF 输入下的实际有限最大值/单侧闭生存

LEAN_STATUS: 独立服务器无-o目标、完整源全部新增常量审计及21个指定OQ4模块共存均 exit 0，无警告

JUSTIFICATION: 当前49241958源完整实现实际跨维乘积 law 的投影和 Antitone，不将非增性或 Summable 作为外部前提。公共含零最大值、a0=1、真可积支付、三个真实级数及由原始 SP 导出的等价式均正确。实际闭事件 Markov 支付保留原子和零路径，5+3C_BE 与6+3C_BE常数精确。30个实际新增常量全部通过标准三公理审计，新旧可测性定理实际可共存。

## 审查隔离、停点与当前源

当前形式审查日期：2026-10-22（本地时区）；服务器检查 UTC 见下文。已完成的数学票 `finite-survival-laplace-math-review-v1.md` 保持冻结，SHA256 为 `062f91c75cf38e1d53089c7c3267db55be9ee51a33c9080a5a0e3c4801372c82`，未重复旧数学审查或改写其内容。

原63f候选在读取/编译前收到协调方的同名冲突通知，本审查者没有对其作形式认证。恢复后只读取当前49241958最终源；先静态核对，收到协调方远端effects确认后才执行独立服务器检查。未读取作者 receipt、summary、declarations、作者会话或其他审稿票，不依据作者检查回执/olean哈希替代验证。

只写所分配审查报告，未修改数学、源、冻结声明、共同文件、Git 或缓存，未生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-finite-survival-laplace-v1.md` | `988db8de1f059c3cc49dacdd72346a1459b7e40773ef96f4c19370221634ec76` |
| 所审匿名 `drafts/oq4/survival/proof.md` 快照，保持不变 | `83c93e47bf987d500f2d05e17920893b3211e19d390c78d0fcf17f26837aad37` |
| 本机 `drafts/oq4/survival/FiniteSurvivalLaplace.lean` 与远程 `Shao/OQ4/FiniteSurvivalLaplace.lean` | `49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb` |
| 直接已审依赖 `LaplaceTail.lean`，本机/远程一致 | `664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2` |
| 直接已审依赖 `LaplaceGenerating.lean`，本机/远程一致 | `eab53afb87248fc0f9b94ddf84e986eedae51f2446e9b7ea176e517c4a861ed8` |
| 共同直接依赖 `Shao/Basic/ClosedSurvival.lean`，本机 library/远程一致 | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同直接依赖 `Shao/Probability/FiniteIID.lean`，本机 library/远程一致 | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同可测性依赖 `Shao/Probability/MeasurablePath.lean`，本机 library/远程一致 | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |
| 共同定义 `Shao/Basic/FinitePath.lean`，本机 library/远程一致 | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |

以下行号均为当前最终 `FiniteSurvivalLaplace.lean` 的一基行号。

## 真实定义、可积性与长度0

第11–21行直接定义公共 `maxWithZero` 的负指数、公共最终 `prefixSum` 正部的负指数，以及各自真实 Π_j/Π_k 下的积分均值。没有另造抽象最大值 law 或生存条件化测度。共同 `FinitePath.lean` 第101–102行的 maxWithZero 是所有0≤k≤j的前缀最大值；第132–140行给其序比较和非负性，零前缀确在其中。

第23–61行分别给两指数被积函数的实际可测性、[0,1]逐点界及概率乘积下的真正 Integrable，L>0为完整可积/有界接口前提。第63–81行据真实积分比较给均值[0,1]。正部支付的可测性在第135–138行再次明确给出，真正可积性和[0,1]界由已审 `iid_integrable_positiveLaplace`、`finiteSumLaplacePayment_bounds` 对相同真实 Π_k 提供。没有要求 ν 的任何矩、密度或支持条件，也没有利用不可积默认0。

第83–98行从公共含零前缀最大值证明空路径 H0=0，再按空维真实概率产品积分常数1给 a_L(0)=1；该结论甚至对所有实 L 成立。第100–106行对**全部自然 k**使用真实 endpoint 支付可积性和积分相减，证明 A_L(k)=1-b_L(k)，含 k=0。空前缀的 b0=1 与 A0=0也由定义直接保留。

数学票所记冻结第7行 API 次序事项仍保留：当前实际代码明确使用 `finiteSumLaplacePayment ν k L`，即 k步产品与尺度L；它符合冻结给出的自然支付语义。没有按手写 `ν L k` 错置实数尺度和自然长度，也没有改动冻结文本或前提。

## 跨维 Π law 与真正 Antitone

第109–121行的 `prefix_projection_map_pi` 对每个自然 n（包括0）证明实际前 n 坐标投影将 Π_(n+1) 精确推送为 Π_n。证明只使用未条件化乘积坐标的实际 `iIndepFun_pi`、固定注入 `Fin.castSucc` 的独立子族、各坐标真实边缘 ν 和标准联合law公式。没有在生存事件后重用独立性。

第123–132行从公共有限和定义证明 k≤n 时投影前缀与原前缀相同，随后以真正0..n与0..n+1的最大值比较得 H_n(proj a)≤H_(n+1)(a)。

第141–166行将上述事实转成实际均值非增性。投影可测；第147–153行对投影后的短维指数函数在长维 Π 上直接用[0,1]界证明真实可积。第154–159行使用投影推送恒等式与可测 map 积分得到精确短维均值。第160–165行在两侧真实可积时，以 L>0 将 H 的序比较反向传给负指数，再积分。最后用逐后继非增推出 Antitone。非增性不是最终定理的输入。

## 三个真实级数与非循环 SP 改写

第168–181行分别用实际均值/支付[0,1]界，调用已审几何支配证明，明确返回 G、endpoint B级数和payment W级数的 Summable，分母始终为正自然 k+1。G 的真实第0项 a0包含。

第184–203行只接受原始点态 SP 形式 `G=exp(laplaceW(endpointMean))`，未接受所需归一化等价式。实际对数 HasSum 减去真实 payment HasSum，结合第195行 A=1-b 的逐项恒等式，产生 endpoint 级数的真实 HasSum 与 `B=-log(1-s)-W`。由1-s>0才使用 exp/log 消去，推出 `(1-s)⁻¹exp(-W)`。没有通过默认tsum0改写，也没有用所需一侧生存结论反过来证明 SP。

## Uniform BE、实际系数与常数

第205–213行完整签名仅要求 ν 为任意实数 Borel 概率律、C_BE≥0、β≥1，以及每个正自然 k/每个实 x 的真实 Π_k 普通和 CDF 误差。唯一 SP 输入是所有 L>0、0<s<1 上的原始 `G=exp(B)`；没有额外 Summable、Antitone、归一化 SP 或所需生存界参数。

第214–223行取真实 L=d+β≥β≥1，并对每个 k≥1 调用实际 `finiteSumLaplacePayment_lower_bound_of_cdf`，得 S1 序列输入，所有正 sqrt(k) 条件完整。第224–227行从原始 SP 导出该 L 的等价式；第228–230行将实际 A、实际 a、已证 bounds/Antitone 与该等价式供应已审生成函数系数定理。第231–232行精确化简 `2+3(1+C_BE)=5+3C_BE`，得到冻结 a_m 界。

β 是显式 CDF 误差参数；当前签名没有把它偷换成未经证明的矩，也没有均值/方差/密度条件或其自动推出 BE 的断言。

## 闭上生存与真实 Markov 支付

第234–240行唯一名 `measurableSet_closedUpper_laplace` 使用共同 `mem_closedUpper_iff_maxWithZero_le`，得到 **闭**事件与 H≤d的逐点等价并证明可测，所有自然 m与实 d均有效，包含0前缀和原子。

第243–263行保留 d≥0、L>0，实际对闭事件指示函数作积分比较。事件内 H≤d使 exp(d/L)exp(-H/L)≥1，事件外右侧非负。第260–261行明确给出指示函数及指数支付常数倍的真正 Integrable，后续积分指示公式精确给 Π_m.real(closedUpper d)≤exp(d/L)a_L(m)。没有用默认0或严格生存事件替代它。

第266–292行保留全部 uniform CDF 与原始 SP 输入，d≥0、m≥1。以 L=d+β>0得 d/L≤1；乘真实非负 a_m 后用 exp(d/L)≤exp(1)，再乘实际系数界，指数常数精确成为6+3C_BE。d=0、m=1、零路径与边界原子均无例外或排除条件。

## 独立服务器目标、全新常量与共存

收到协调方远端effects允许后，在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 实际只读核对 HEAD=`f73e3ca6534783c94dc6855fe4277a83b145dcf0`。脚本使用 `set -e`、`set -o pipefail`，先 activate 后 cd，依次运行三个单 Lean 过程，均 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/FiniteSurvivalLaplace.lean
{ 完整49241958源 + #check/#print 与动态全常量附录; } | lake env lean --stdin
lake env lean --stdin < 指定21模块共同import与新旧名称检查
```

均不带 `-o`，不生成目标 olean、不构建/更新 Lake、不写共享缓存。broker正常，未出现不确定执行/重放或调用备用通道。三过程实际全部exit0、无警告，stderr为空；UTC=`2026-10-21T16:06:36Z`：

```text
TARGET_CHECK_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 30
SOURCE_DYNAMIC_AUDIT_EXIT=0
ACCEPTED_21_MODULE_COEXIST_EXIT=0
ALL_21_SOURCE_AND_4_COMMON_HASHES_UNCHANGED True
PROHIBITED_TOKEN_HITS []
```

动态审计遍历完整当前源实际 `env.constants.toList` 中全部 `env.getModuleIdxFor? declName = none` 声明，无namespace/root筛选。每项调用 collectAxioms，若不在 `{propext, Classical.choice, Quot.sound}` 中立即报错；数量来自实际枚举，不采用作者数量自述。实际28个显式声明为：

```text
Shao.OQ4.maxLaplaceIntegrand
Shao.OQ4.endpointLaplaceIntegrand
Shao.OQ4.maxLaplaceMean
Shao.OQ4.endpointLaplaceMean
Shao.OQ4.measurable_maxLaplaceIntegrand
Shao.OQ4.measurable_endpointLaplaceIntegrand
Shao.OQ4.maxLaplaceIntegrand_bounds
Shao.OQ4.endpointLaplaceIntegrand_bounds
Shao.OQ4.integrable_maxLaplaceIntegrand
Shao.OQ4.integrable_endpointLaplaceIntegrand
Shao.OQ4.maxLaplaceMean_bounds
Shao.OQ4.endpointLaplaceMean_bounds
Shao.OQ4.maxWithZero_empty
Shao.OQ4.maxLaplaceMean_zero
Shao.OQ4.finiteSumLaplacePayment_eq_one_sub_endpoint
Shao.OQ4.prefix_projection_map_pi
Shao.OQ4.prefix_projection_prefixSum
Shao.OQ4.prefix_projection_max_le
Shao.OQ4.measurable_paymentLaplaceIntegrand
Shao.OQ4.maxLaplaceMean_antitone
Shao.OQ4.summable_maxLaplace_series
Shao.OQ4.summable_endpointLaplace_series
Shao.OQ4.summable_paymentLaplace_series
Shao.OQ4.maxLaplace_original_sp_to_normalized
Shao.OQ4.maxLaplaceMean_bound_of_cdf_and_original_sp
Shao.OQ4.measurableSet_closedUpper_laplace
Shao.OQ4.closedUpper_probability_le_laplace
Shao.OQ4.closedUpper_bound_of_cdf_and_original_sp
```

另2个实际生成声明 `Shao.OQ4.maxLaplaceIntegrand.eq_1`、`Shao.OQ4.maxLaplaceMean.eq_1` 同样完整审计。30项均恰为标准三公理；Antitone、原始SP改写、实际系数界、Markov支付与最终闭上界另逐项 `#print axioms`，同样只有三项。没有 sorryAx 或新增公理。

共存过程只import以下指定接受/当前模块，未加入未审 Reflected：

```text
DelayedRecurrence, OvershootSum, OvershootMoment, VarianceScaling, Foundations,
CosineCoefficients, KilledCosine, OccupationPayment, AveragedResidual,
KilledKernel, KilledIteration, KernelRecurrence, CosinePowers, KilledPathLaw,
KernelAbsorption, BoundaryOccupation, KilledBlockBounds, IntervalConcentration,
LaplaceTail, LaplaceGenerating, FiniteSurvivalLaplace
```

实际同时 `#check Shao.OQ4.measurableSet_closedUpper` 与 `#check Shao.OQ4.measurableSet_closedUpper_laplace` 均成功，最终主界在该共同环境中也实际检查签名与公理成功。因此当前源不再有旧通知中的名称共存障碍。

上述21个OQ4源及表列4项共同源全部在三过程前后实际SHA比对一致；目标前后都为49241958全值，两项Laplace依赖分别664df6aa、eab53afb全值，四共同依赖与本机已读版本一致。禁用项对当前完整源扫描正则 `\b(sorry|admit|axiom|unsafe|native_decide)\b`，无命中。

## 认证边界

本票只关闭真实有限维上侧的条件推导。原始SP仍是明确输入，uniform BE-CDF仍是明确输入；Antitone、可积/可和性和实际Markov支付已内部证明。没有由未提供的矩条件推断这些概率输入。

**BE、SP、无条件一侧S、反号law上侧、最终双侧S/AC/O0、B1、长期K/Kv、4/π、完整OQ4与其他全部完整根保持 OPEN。**
