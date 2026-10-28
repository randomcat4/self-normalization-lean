# Unit249 最终独立完整审查

STATUS: CORRECT

**qualified=true。** 该结论只适用于源码 SHA256 `19c3e659b538c19d7e73a55bcaec1dc6727b435665e215890cc6c219c88704a0`（240965B、3825LF），以及其首次成功原对象 SHA256 `8e5eeb1aaf9baf837af468ec4c27e81fb5529442cfb32b37178e2da13dbc51a9`（6134960B）。完整源码、来源到声明、证明、全部实际所属 TYPE、必需 VALUE 和递归公理审查已完成。没有未解决的数学、类型、对象来源或公理缺口。

本审稿人一直是与作者隔离的同一独立角色，未修改声明或证明，未执行 Lean、服务器或网络操作。此前封存的两个源码版本、失败记录、全部 SOURCE 报告和阶段释放文件保持原字节。

## 成功对象及完整机器依据

native03 实际 RC0，34.30809280462563 秒，源码错误 0；receipt SHA256 `abdee1daea2a20316545b2c1c991077eeb6111ca881a774206b9a1a29556e513`。native01 的加法接口 RC1/noO 和 native02 的默认有限心跳上限 RC1/noO 原样保留，所以本对象是第 3 次尝试产生的首次成功原对象。对象 mtime_ns 为 `1793189737900074934`。

same-FIRSTO audit01 实际 RC0，6.689817851409316 秒；receipt SHA256 `ba9b154ea9bf5b7ab2254d5c3d2db75b3ad85528e51c97c3cc6f25e2cc8f36b5`。审计只导入自己的原对象，`no_o=true`；native 结果、审计前对象、审计后规范元数据和 server binding 的完整 path/hash/bytes/mtime 元组相同。source 元组和 receipt 元组也逐项连接一致。source、保护对象和 before/after 均保持；无外部 timeout、cleanup、ownership 错误或存活 owned 进程。

实际模块索引发现方式是 `env.getModuleIdxFor? anchor` 后遍历 **ALL env.constants without namespace filter**。实际所属项恰为 1：

`Shao.OQ6.OriginalSameWitnessPhysicalRelativeTailApplication.actual_original_same_witness_physical_relative_tail_application`

其 constantKind 为 thmInfo，isTheorem=true，bodyExpressionPresent=true，levelParams=[u]。sourceDeclaredCount、publicSourceTheoremCount、实际模块 owner/theorem 数均为 1；非定理、生成 helper 和必需非定理 VALUE 为 0。VALUE 文件为实际空字节，不以未读取代替空范围。

本审稿人独立解析每 owner 的原始 JSON，并仅用原字面 JSON、完整 TYPE 和 COUNT 块重建整个原审计 stdout：**2411259B，SHA256 `17065e980268e0464fba56bfe12f585da4d2fa37d9f778e0a98055d43471b9dd`**，与三处绑定的原 stdout 完全相同。没有下载或保存 raw log；没有以规范化摘要替代实际完整类型。metadata 的实际类型也逐字节重建为当前 `actual-owned-types.txt`。

五份传输文件的本地字节数和 SHA256，均与传输绑定及对应 server 元组匹配：TYPE、VALUE、metadata、summary、server binding。首次只读传输截断的失败仍保留；最后传输恢复的是相同的原始未压缩字节，不改变数学或机器材料。

## 全部 15262LF 实际 TYPE 的无损覆盖

当前 TYPE 文件为 2410690B，SHA256 `698a313c286145d713d9678cd37a33981a7dd69721242b3da252db3023a73793`。实际 metadata 为 2429231B，SHA256 `84ffb0f28deed832f4344e63a12566aeea54d7468719694351292207a1713930`。完整类型无省略标记、printer-failure 或 bad-proof 标记。

合格248证据 `d58d36550e44bb91d9a7dd131386c1d44525764ca697999100520f7418efa690` 明确覆盖其完整实际 TYPE，且实际仅有一个 owner。旧 TYPE `75eddcda040855dcfff59b515c05b0cde9b57cbfef013ad6262c38ef9f69f747`、2347133B，当前仍与该合格输入绑定相同；其独立最终报告及 manifest 也绑定复用。本次没有重新审查或重跑旧248 proof/TYPE/AX。

当前实际 TYPE 的数学表达式与旧完整类型的关系，已经独立按实际字符跨度证明，而非根据描述性相似度推测。仅允许公开完整定理名的 header 改名，且已证明替换没有触及任何其他旧类型内容。连续空白折叠为一个空格、保留全部非空白字符及 token 边界后，当前完整类型长 250822 个 UTF-16 字符，旧类型长 230947。零起点半开区间如下：

| 当前区间 | 覆盖依据 |
| --- | --- |
| [0,169839) | 与已合格旧 TYPE 的 [0,169839) 完整相同，含全部原 telescope、global 和 selected-model 上下文 |
| [169839,169844) | 新增 `(And ` 结构，直接检查 |
| [169844,230944) | 与旧 [169839,230939) 的完整旧支付分支相同，61100 字符 |
| [230944,230945) | 两参数之间的空白分隔 |
| [230945,250813) | 全新完整实际类型参数，19868 字符，已直接完整阅读 |
| [250813,250814) | 新增 And 的结尾，已核对恰有两个完整参数 |
| [250814,250822) | 与旧 [230939,230947) 的完整外层结尾相同 |

新参数对应原实际 TYPE 的第14711–15262行，原 UTF-8 字节 [2359053,2410680)。其完整原字节提取和完整空白折叠提取分别另存，均有哈希。**19868 字符的完整新类型已逐项阅读，不是只读结构摘要。**

把已合格旧表达式、完整已读新表达式和显式 And 结构重新连接，恢复全部当前规范字符；再逐个非空白 chunk 用该恢复表达式供值，并配入当前每段实际 trivia，恢复全部当前原始 UTF-8 字节，与完整 TYPE 文件相同。原始字节分区也连续覆盖全部当前内容。旧范围复用、全部新增范围及完整 whitespace/trivia 均无遗漏；详见 ACTUAL-TYPE-LOSSLESS-COVERAGE.json。这不是把库函数名相似或作者自评当作类型覆盖。

## 新实际类型到冻结声明的逐项核对

新实际参数从固定 Cenv、aenv、t0、Menv 及其原非负/正性开始，cPaid 的 RHS 恰为原 remainderWindowScale 与 min(1,sqrt(t0)/2) 的 min。cPaid>0 是结论；随后一个共同的 eventually-atTop 自然数集合给出 n≥4、1+rho≤sqrt(n) 和 1≤cPaid*n^(1/6)，之后才量化 w、z。guard 未成为额外用户假设，rho 没有移到 n 之后。

完整实际 hW、hWR、hSq、hSqBound、hEnv 使用原 mΩ/μ，hEnv 使用原 μ.prod μ。没有新增 Measurable w、独立性、混合矩或第三模型。mN 的 Pi 空间、P 的 Pi 法则和所有积分显式仍为原 mΩ/μ；Fin.fintype 为原有限指标实例。原 g/r/rho/β/cWindow、cg/m₀ 和 selected-model 上下文在精确相同的旧实际前缀中已全部覆盖。

新 L0 的有限和、自然数平方、截断 min(|z*ξ0|,1) 与原 head 相同。sourceCost0 的完整项和部分项均实际读到：full exp 权重、erase-i exp 权重、原 residualStatisticDDeleted、绝对值删除差，以及 studentizerClipBudget/Deleted 的 512/rho/1 参数、分母 full weight integral 全部保持。没有换成未加权费用或推断 cost-smallness。

Tphysical 的实际 ite 使用真实 sqrt(centeredSq)=0 时取0，否则取 (projectionW+residualStatisticD)/sqrt(centeredSq)；Real.decidableEq 是通常实数等式判定，不增加前提。R 的实际 RHS 是 exp(-(t0/2)*n^(1/3))，仍用原 t0，而非辅助平方参数。

外部 `ScalarShaoZhouFiniteCostTailInput.{u}` 与 cBudget、C1–C4 的量词保持；strict moment alternative 是原 β=0 或正 β 的原 cWindow/β/p/n 范围。实际 lower 为 Ψ*(exp(-C1*L0)*(1-C2*cost)-R)，upper 为 Ψ*(exp(C3*L0)*(1+C4*cost)+2*R)。事件使用原 P.real 和闭条件 z≤Tphysical。没有除以 Ψ、要求 Ψ>0、要求 1-C2*cost 为正或作 CDF/atom 推广。

全部隐式 Real 运算、范数、Borel/积分、有限指标和 Nat/Real 数值实例均随完整新类型实际读取，与冻结的类型和作用域相符。

## 完整 SOURCE 和修复联合

本角色最初完整覆盖全部3824行源码和原 p51/p54，并阅读全部独特上下文、155 public/159 optional ordinary、28 have（27完整显式类型，唯一 h248 推断）、所有实例、选择和匹配。六段巨大复写类型按精确字符映射到已完整读过的 head，未用摘要代替承重语义。

其后同一独立角色只审实际第3768行的加法接口修复及完整局部上下文，再审唯一35B/1LF有限 `set_option maxHeartbeats 800000 in`。当前新1–14行对应旧1–14；当前第15行选项直接覆盖；新16–3825精确对应已审旧15–3824。数学声明和证明覆盖由这些精确联合组成，没有重做旧完整证明。2129个映射对象按实际新字节独立定位及逐项平移，错误0；28事实片段哈希、730let、8letI和159 optional映射保持。原始失败、后续修复及本次成功均是各自精确源版本的独立事实，没有覆盖或回写旧裁决。

p54 对 p51 S6 任意多项式条件 p 矩变化率的修正保持；该错误速率从未被恢复。Shao–Zhou 有限费用输入仍明确是外部依赖；248/236 的精确既有证据按既定规则复用。source-to-statement、完整证明和当前实际对象表达的结论一致。

## 公理、warnings 和最终范围

唯一实际 owner 的递归公理恰为 **propext、Classical.choice、Quot.sound**。JSON 与完整 stdout 重建、公理数组、body存在和原对象来源均已核对；非定理 VALUE 范围确实为空。没有 sorry/admit、新 axiom、unsafe 或 native_decide。当前模块的全部实际 owner 均获覆盖，不以命名空间过滤代替模块索引发现。

native 的全部60个源码 warning header 已逐条读取：2个 letI 风格建议、56个 binder-name 未显式引用提示、2个 `<;>` tactic linter 提示；原环境 stderr warning 也保持。完整 native stdout/stderr 的字节和哈希独立核对到 receipt 绑定。native 和 audit 的 `strictWrapperSuccess=false`、native success=false 保留，其原因是严格 empty-stdout 策略，不改写成 true；最终资格依据实际RC0、完整证明审查、原对象和全公理材料。FIRSTEMPTY=null 且不是 runner 返回的字段，不宣称其为 true。不清 warnings，不重编源或对象。

本次 qualified=true 只认证这个 **同 witness、原物理闭尾、原 weighted finite-cost 条件下的 Gaussian-relative 付款应用**。它没有证明外部 SZ 输入本身、weighted-cost rate/smallness、最终 beta-term 吸收、CDF/atom 定理、完整 S11/S15/DC、C2/C12/OQ56 或 root 完成。fullOQ56 和 root 仍 OPEN，Root integration acceptance 留给 coordinator。

requestedModel=gpt-6.1-sol；requestedEffort=xhigh。实际 backend/model/effort、input、cachedInput、output、reasoningSubset 不可见，均为 null。本审稿人所有 Lean/lake/PP/AX/server/network/upload/Git/publication/children/Goal/schedule/sidebar 操作为0。最终材料封存后本角色六零 FINALWRITE 释放。
