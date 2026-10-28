# Unit249 作者实现路线

本产物的作者判断为 **PROVED（未经 Lean 内核检查）**。实现完整覆盖冻结的
`actual_original_same_witness_physical_relative_tail_application`，没有修改公开
前导、声明或结尾。独立 SOURCE/证明审查、指定服务器 native 和原对象所有实际
声明的传递公理审计，仍须由 lane lead 另行组织；本作者没有给予自己的证明独立
验收，也没有运行任何 Lean、服务器或发布操作。

原始目标是 p54 §2/F6 后、与 p51 S1–S8 及 p54 修复配套的同模型原物理统计量
尾界。本轮直接承接已合格248及冻结 stage1 的来源与陈述对照证据；没有重新
审阅248证明或声称重新读完原始 p51/p54。新工作只消除248物理尾界的两项显式
异常损失在共同窗口内的 Gaussian-relative 费用义务。p54 对任意多项式条件
p 矩变差断言的修复保持原状，没有恢复被否定的断言。

唯一直接 producer 是 qualified248 的公开定理，源码 SHA256 为
`50cc9872e1d6148e4a81f0d49da391a1b4b749b682c91b4ba347ae22bad00433`；其合格
证据 SHA256 为 `d58d36550e44bb91d9a7dd131386c1d44525764ca697999100520f7418efa690`。
该公开定理在任何全局 let、cg 或 m₀ 选择之前，作为 h248 恰好调用一次。随后
从这个结果唯一选择 cg 与 m₀，提取原 hm₀、hcg，定义相同 μ₀ 并保留相同的
可数生成局部可测结构。全部旧解析、编码、完整/删除加权 sourceCost、费用与
物理比较条款通过 hRetained248/hOldPayments248 直接传递。没有消费独立的
235、237、239 selector，没有第三个模型或新的概率律。

新数学还消费已合格236的公开标量接口。其一次实际 t0/cg 应用给出原费用
吸收，另一次在内联参数 `(2*cPaid)^2` 上的应用只消费非空窗口字段。后一次
不改变最终 R 的指数，也不生成普通辅助标量或新的自然数截断选择。

固定原模型、rho 与固定 Cenv、aenv、t0、Menv 后，cPaid 是冻结的两个尺度的
最小值。tailScale 的正性由既有 bounded_scales_pos 给出，余项尺度正性由
remainderWindowScale_bounds 给出，另一个最小值正性由236实际 t0/cg 的第一
字段给出。由此 cPaid>0，且分别不超过原余项窗口尺度和236吸收窗口尺度，
同时 cPaid≤1。Real.sqrt_sq 将内联236参数的窗口尺度精确化为 cPaid，所以
得到 eventually n≥4 且 1≤cPaid*n^(1/6)。

Real.tendsto_sqrt_atTop 与 pinned tendsto_natCast_atTop_atTop 的复合给出
sqrt(n)→atTop。将固定实阈值 1+rho 的上尾集合沿该趋向拉回，得到同一个原
rho 的 eventual studentizer guard。这个 guard 与旧248 eventual 谓词、
cPaid 非空窗口和236实际费用吸收谓词先相交，然后才引入后置 w、z。

给定共同 eventual n 及冻结的晚给 w、z，非负 n^(1/6) 把 paid 窗口同时送入
原余项窗口和236窗口。旧248在前者给出同一原物理统计量的费用尾界；236在
后者给出 `2*payment1≤R*Psi(z)`。z≥1 和 sqrt(n)≥0 给出
`payment≤payment1`，因此下损失不超过 R*Psi，上损失不超过 2*R*Psi。
最后仅做实数多项式因式分解，得到冻结的新相对尾界。

全量证明见 AUTHOR-PROOF.md；28个实际 have 及其完整冻结类型、源码区间见
FACT-COORDINATES.json；MANIFEST.json 绑定全部 public/type-only/operative let、
实例、选择、原有 let 的 intro 和内部模式绑定。类型里的重复 let 作为类型
绑定逐项登记，不伪计为额外模型选择。h248 是唯一许可推断 Prop 的 have；
另外27个 have 均显式给出完整类型。冻结的155条 public ordinary、159条
optional ordinary 和28条事实目录没有扩展。

原 `T=(W+D)/s` 与 `s=0→T=0` 分支、完整 weighted sourceCost、外部 SZ 输入、
原 strict-moment 窗口、cg/m₀ 和所有量词顺序均保留。没有除以 Psi，没有要求
Psi>0、成本非负或成本小。没有证明成本的趋小速率、最终 beta 吸收、CDF、
atom/zero-denominator 全链或 full OQ56/root 完成。

配置请求 gpt-6.1-sol/xhigh；实际后端/模型/effort 和输入、缓存输入、输出、
reasoning subset 计数未暴露，全部记录为 null。所有运行断言只涉及本作者角色，
不冒称观察了 lane 或服务器的全局运行状态。
