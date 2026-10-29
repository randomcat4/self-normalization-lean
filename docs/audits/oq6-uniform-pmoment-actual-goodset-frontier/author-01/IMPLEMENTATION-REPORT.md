# unit266 冻结共同好事件接口：本地完整实现报告

状态：LOCAL_SOURCE_AND_PROOF_COMPLETE_NOT_KERNEL_CHECKED。本轮按精确冻结的一个公共定理完成完整证明文本和原字节组装源码；没有运行 Lean、AX、工具链、服务器、网络或 Git/API。全文源码共348行；本报告是作者说明，不是独立审阅或机器资格。

## 精确授权与组装

实现激活 SHA256 `354fd95040c237b72a87bf43b82bf488e3722d88a014da2354a746a50d871a33`，5321B；冻结声明 SHA256 `7d9dc129606948670f17c5aecd59cdf363ca19748757f59ff5fb776ca324f195`，1807B。十五项输入在开始时全部逐项核验哈希及字节。新 `author-01/READ_ACK.json` 在实现之前已写；旧 proposal、READ_ACK、READY 和全部冻结字节保持原样。

`UniformPMomentActualGoodsetFrontier.lean` 严格按 `freeze-01/PREAMBLE.txt + freeze-01/HEAD.txt + author-01/PROOF.txt + freeze-01/CLOSING.txt` 原字节连接。公共定理为 `Shao.OQ6.UniformPMomentActualGoodsetFrontier.uniform_pmoment_original_boundedPolylog_goodset_frontier`，声明未改一个字节。PROOF 从 `:= by` 开始，只在该证明内设置 `maxHeartbeats 800000`；没有改全局选项、导入或公共声明。未新增私有或公共 helper declaration，显式 cg 补集桥仅为本证明内的局部 `have`。

## 完整证明路线及源码定位

1. 源84–100：先引入模型外的 tB、cg，调用冻结 unit265 `actual_uniform_pmoment_low_energy`，提取 cg>0 和全模型低能量包。固定 C、a、t0、M 后，对原 `eventually_boundedPolylog_product_joint_failure` 使用自然数 atTop 的阈值刻画得到 N0，再取 N=max(4,N0)。直到取得此 N 后才引入 n、Ω、μ、g、r、w、C0、rho、z；由 N≤n 同时得到 n≥4 和本 n 的全模型集中包。因此模型可以随 n 改变，cg 只依赖 p、B，N 的构造只使用原数值集中窗口。

2. 源101–126：定义与冻结结论相同的 q、K、G、C2、H、e1 及 Pn。Pn 是当前 μ 的原 `sampleLaw n μ`。对 unit265 的全模型包逐层提取真实有限乘积闭低能量界 `{sampleEnergy≤n/2}`。`sampleLaw` 与 unit265 显式 P 的区别仅为同一 pi 法则的定义展开，平方和 S 与 sampleEnergy 的区别仅为同一有限和的定义展开；没有更换可测空间、法则、样本或积分。此处没有调用旧存在性 cg 低能量定理。

3. 源127–174：局部 hNormalized 将原 normalizedGoodEvent 的补集精确拆成严格低能量 A 与原归一化上尾 U。n>0 来自 N≥4，故能量除法可按正分母转写；A 包含于 unit265 的闭低能量事件，用原测度单调性取得 exp(−cg*n) 付款。原 `OriginalNormalizedUpperTail.original_normalized_upper_tail` 用当前 μ、g 的真实可测、L²、均值0、二阶矩1和 z≥1，支付 U 的 `4exp(−z√n/2)`。两项用有限并集不等式相加。严格/闭低能量之间只用包含，未要求等号概率0。

4. 源175–262：由坐标 g、两坐标 r、有限和及平方构造原上三角和、原行能量、投影能量和投影和的可测性，得到 G、C2、H 的可测性。H 精确是 G∩C2，C2 仍只有原上三角和和原行向量的两个界，没有新增 squareSum(w) 测试。这一段按原 P54ActualGoodsetFrontier 的有限可测结构重新放入本冻结量词内，并非修改已接受旧源。

5. 源263–280：使用同一 `bounded_remainder_small_window` 得到 V>0、z|D|/V≤1/8、z²|delta|≤1/32、|delta|≤1/32。由下界得到真实 `centered_studentizer_factorization`，保留 sqrt(centeredSq)>0 及 sqrt(centeredSq)=V sqrt(1+delta)。没有从裁剪量替代真实 delta 来声称这个因式分解。

6. 源281–306：定义 Bad=原 `boundedProductFailure`，只把 squareSum(w) 的额外失败用作付款者；证明 C2ᶜ⊆Bad 与 Hᶜ⊆Gᶜ∪Bad。模型前提取的 hConc 在本模型下给 `3exp(−q)`。用旧 `normalizedGoodEvent_eq_projectionGood` 的原事件恒等式把局部显式 cg 付款送到当前 G。没有把目标概率界作为前提，也没有用旧最终 H 定理的模型相关 cg 偷换指数。

7. 源307–346：完整组装可测性、十四项安全结论、两类零事件包含和最后付款。分子 `≤V/8`、`<V/4`，delta 的 `≤1/32`、`>−1/8`，裁剪收缩、`z²|e1|<1/8`、裁剪分母正性与真实因式分解均保留。最后的系数、符号和指数精确为 `3exp(−q)+exp(−cg*n)+4exp(−z√n/2)`。

## 前提、边界与来源检查

冻结真实 p 矩可积且≤B、二阶矩1、均值0、左右退化、逐点核对称、真实产品包络、w 的非负/数值高度/平方可积及积分上界全部通过原参数保留。没有新增原子连续性、标准 Borel、可数生成、模型固定不变、最终异常概率或物理尾前提。N≥4 给本证明所有正样本量与余项几何分母条件；p=3、B=1、C/a/M=0 均未排除，p=2 仍由冻结条件排除。

作者全文重读了新348行 SOURCE：本轮显示1–180与181–348，无截断缺口。数学依赖的原完整读取沿用 proposal-01/DEPENDENCY-READ-MAP.json 的精确哈希及范围；本轮另外完整读取新激活、冻结三段和 unit265 的实际 native01a 诊断全文。额外有界定义核对为 `OriginalGhostGoodEvent.lean` 1–31（sampleSum/sampleEnergy）与 `CompactGoodEvent.lean` 400–414（既有 eventually_atTop.mp 用法）；两个可选搜索文件名不存在的读取诊断未产生任何数学、执行或源码效果，不被当作检查结果。未重新宣称独立接受旧证明。

原标准化上尾继续归属于项目原 `OriginalNormalizedUpperTail` → `OriginalSelfNormalizedTail` 的 Shao–Zhou (92) / 自归一化输入链。本实现仅拼接已有上尾结果，不将其改称新证明或外部 SZ 存在性证书。p54 对条件标准化 p 矩只要求统一最终有界/收敛的修正保持不变，未恢复错误的任意多项式 p 矩变化率。

## 资格门与仍开放范围

本轮明确读到 unit265 firstnative01a 已自然结束 RC1/no object，诊断仅一处原源228的形式化失败；其冻结类型和数学 SOURCE 已由 lead 报告独立接受，proof-only 修复由别的作者进行。这里仅按其不可变冻结声明写本地消费者。**unit265 尚非 qualified；在 lead 提供其 qualified actualTYPE/FIRSTO 的精确绑定之前，unit266 不得进入消费者机器检查。**本轮不读取或修改别的作者修复文本，也不代替其修复。

本 SOURCE 尚待 fresh independent complete source-to-statement/proof review、全部实际拥有者 TYPE（及非定理 VALUE 如有）、同一原始对象的服务器内核/传递公理审计。标准白名单仍为 propext、Classical.choice、Quot.sound；静态禁用词扫描不代替实际 AX。局部 `have` 可能生成的实际常量数量尚未知，不能把源码只有一个公共定理解释成全部拥有者只有一个。

本单元未证明对任意 C0、rho 的 e1=delta；C0=0 的裁剪预算说明该等同仍需要实际预算支配桥。统一物理有限费用、共同吸收/相对窗口、p54 实际条件/三角法则及均值/方差付款、externalSZ、DC、fullOQ56/root 均保持开放。安全与真实零事件付款没有被写成这些范围的完成证据。

## 静态结果、用量和权力释放

静态检查只包括精确冻结组装、UTF-8/LF/无BOM/单一终LF、禁止证明逃逸词、公共声明与 proof-local 选项及输入保持检查；详见 STATIC-CHECKS.json。它不是 elaboration、内核或公理审计。完整新数学证明需要 lead 安排独立审阅；作者不自盖独立接受章。

请求配置仍为 gpt-6.1-sol/xhigh；实际 model/backend/effort 未被工具公开，均记 null。input、cachedInput、output、reasoningSubset 分别 null，不用请求配置推断实际模型或用量。

最后写 LASTFINALWRITE.json 后释放本 author-01 的全部作者写入、执行、发布和子实例权力，authorRoleRetained=false；不会因原提案保留角色状态而继续写入。角色实际 proofWriter/heavy/inflight/uncertain/pendingExternal/children 均0，依据是所有本地读取和写入均已同步结束，且本角色未派发任何远程、Lean、API或子实例任务。本释放不宣称其他 owner 或整个项目为零活动。后续新激活由 lead 决定。
