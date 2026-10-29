# Unit265 U0 独立声明与统一性审阅

STATUS: CORRECT — DECLARATION_ACCEPTED_FOR_U0_ONLY

审阅者 `/root/oq56_unit265_review` 是独立审阅者、非作者。本次接受冻结的 `actual_uniform_pmoment_low_energy` 的数学真实性、量词与来源作用域；没有发现需要修改冻结声明的关键缺口。尚无本单元生产 SOURCE/PROOF、实际 TYPE 或服务器内核/公理结果供本轮评审，因此本结论不是实现合格或机器通过。更广统一物理相对尾引擎未冻结、未证明。

## 精确对象与阅读覆盖

激活文件 SHA256 `bfc7eddeec4b662ce5aac0d45f802b92c1129d69846106de35281a7eba8f0718`，3700B；其十个输入的 SHA256、字节数均精确吻合。十项均严格 UTF-8、无 BOM、无 CR、单一终 LF。本轮完整阅读冻结 JSON（55行）、PREAMBLE（11行）、HEAD（34行）、CLOSING（2行）、19059B/266行提案、提案 MANIFEST（165行）、READY-CHECKPOINT（88行）、SUPPLEMENT（59行），以及两份直接相关导入源全文：ConditionalStandardizedLowEnergy 1–447、OriginalLowEnergyTail 1–320。

一次合并工具输出曾截断 ConditionalStandardizedLowEnergy 中段；随后分别完整显示 1–230、231–447，覆盖全部缺口。OriginalLowEnergyTail 另分 1–160、161–320 完整显示。接受范围不依赖被截断的结果。READ_ACK 在输入全文完成之前已写，诚实保留 READING_STARTED；本报告、清单和完成检查点记录现在的全文完成状态，不回写该初始记录。

额外原始语义核对：p54.md 全文（6045B，SHA256 `e03649e1324def02de3ff234bcc94c9e1cb643e074a324e1817ef940f5e01c43`）；p51.md 明确有界的 1–42、325–355；263 SOURCE 明确有界的 1–80、171–190，用于核对旧定理的模型/最终事件量词。提案 DEPENDENCY-READ-MAP.json 全文只作其作者阅读范围的来源记录，不把作者的已读范围转记为本审阅者全文阅读。未重审旧262/263全部证明/TYPE/AX，也未把递归导入库全部声称为本轮完整审阅。

## 冻结声明的数学检查

HEAD 1–10 先固定实数 p、B，条件为 2<p≤3、B≥1；定义 q=p/2、t=(1/(4B))^(2/(p−2))、cg=t/4，然后才在 11–16 引入任意可测 Ω、概率 μ 和 g。t、cg 不是对模型选择的存在性见证，故共同常数的依赖确实只有 p、B。g 的要求是可测、L²、二阶矩等于1、p矩可积且不超过 B。没有均值0、核分解、外部 SZ 或目标尾界假设；这些不是本引理所需。

令 a=1/(4B)、r=2/(p−2)。由 B≥1 有 0<a≤1/4≤1，由 p>2 有 r>0，因此 0<t=a^r≤1、cg>0；同时 1<q≤3/2。所有非整数幂的底非负，a、t 严格正；幂合成恒等式合法，且

    r(q−1) = [2/(p−2)] [(p−2)/2] = 1,
    t^(q−1) = a,   B t^(q−1)=1/4,   B t^q=t/4.

没有在 p=2 处使用除法：该端点明确排除。p=3 保留，得到 q=3/2、t=(4B)^−2。B=1 合法；p趋近2时 t 可以趋0，但每个固定合法 p 下仍严格正，声明不声称跨 p 的共同正下界。

标量不等式 exp(−u)≤1−u+u^q 对 u≥0、1≤q≤2 成立。核对如下：exp(−u)≤1/(1+u)；在 0<u≤1 时，1/(1+u)=1−u+u²/(1+u)≤1−u+u²≤1−u+u^q；在 u≥1 时，u^q≥u，右边至少1，而 exp(−u)≤1；u=0 时两边等于1。ConditionalStandardizedLowEnergy 153–197 正是此完整分支，不能只取其中 u≤1 的分支用于无界 g。

代入 u=t g²，得到 (t g²)^q=t^q |g|^p。这里使用 g²=|g|²、2q=p，g=0 时两边都是0，因为 q,p>0；没有把负 g 当作负底实幂。hg2 保证 g² 可积，hgp 保证 |g|^p 可积；f=exp(−t g²) 可测且 0<f≤1，所以概率测度下可积，L≥0。积分后用真实二阶矩1、p矩≤B及 t^q≥0，得到

    L ≤ 1−t+t^q E|g|^p ≤ 1−t+t^q B
      = 1−3t/4 ≤ exp(−3t/4).

最后一步是 1+x≤exp(x)，x=−3t/4。线性上界非负也与 t≤1 一致。导入源 297–318 的实幂乘法及平方换算、319–356 的积分步骤均与此相符；它的 2β 在这里由显式 B 替换，不能直接套其带特殊条件模型的外层定理来跳过新任意模型量词。

对每个自然数 n，HEAD 22–27 明确构造当前 μ 的原有限乘积法则 P，非编码或条件替代法则。有限乘积概率测度与积分乘法不需要 Ω 标准 Borel、可数生成或坐标空间非原子。S 是有限可测平方和，闭事件 {S≤n/2} 可测；F=exp(−tS)=∏ᵢf(ζᵢ) 可测可积，有限乘积积分给 EF=L^n。L≥0 允许由 L≤exp(−3t/4) 提升到自然数幂，得到 EF≤exp(−3tn/4)。这一步的独立性由 P 的产品定义提供，未隐藏加入独立样本假设。

令 ε=exp(−tn/2)>0。闭低能量事件包含于 {ε≤F}，因 t>0，S≤n/2 蕴含 −tS≥−tn/2；非负 Markov 给 ε P{S≤n/2}≤EF。故

    P{S≤n/2} ≤ exp(−3tn/4)/exp(−tn/2)
               = exp(−tn/4)=exp(−cg n).

常数与方向精确一致；不需要把 ≤ 改成 <，没有原子连续性前提。n=0 时 Fin 0 乘积空间有唯一空函数，P为概率法则、S=0、F=1、L^0=1，低能量闭事件是全空间，最终界为1≤1。没有将旧 OriginalLowEnergyTail 的严格事件在 n=0 时概率0误当成本声明的闭事件。

## 来源统一性障碍与 U0 分解

旧263 HEAD 15–41 先固定 Ω、μ、h 和数值资料，42–43 才有 ∃c>0 与 eventually n；w,z 在 47–56 的最终事件内部。因而旧结论允许固定模型下的 w 随 n 变化，却不能直接换成模型随 n 变化后的共同阈值。一般量词反例 property(n,j):=j<n 已足够否定这种交换；选择公理不能修复它。

OriginalLowEnergyTail 全文确认旧低能量常数由当前模型的 E min(g²,k)→1 选择 k，随后 K=k、s=1/(8K)、c=s/4（70–98），确有模型依赖。提案稀疏例也正确：j≥2 时 g_j 以1−1/j概率为0、以1/(2j)概率各取±sqrt(j)，单位二阶矩，p矩为 j^((p−2)/2)。在样本量 j，闭低能量事件恰为全零，其概率(1−1/j)^j趋 e^−1，不可能被共同正 c 的 exp(−cj) 一致控制。其 p矩不统一有界，故不反驳新U0，也不反驳旧逐模型结果。

p54 F1/F2 所保留的是标准化 p矩最终≤2β，并且统一于 λ,m；p54明确否定任意多项式 p矩变化率，F3 保留。U0 用 B=2β 后，t=(1/(8β))^(2/(p−2)) 与 ConditionalStandardizedLowEnergy 的常数吻合，只需要真实统一矩上界和单位二阶矩，不恢复过强速率句。它不处理非零核均值的确定性阈值付款。

提案 U0→U1→U2→U3 是有效的数学依赖分解，U0严格弱于物理相对尾。U0现在能供同一cg；U1仍须把它送入实际好事件和物理有限费用桥，并在模型量词之前给共同 Nconc。原固定模型的 hAll 不能冒充该输出。U2才可对共同cg作纯数值异常吸收、相对误差代数和共同窗口；U3才绑定实际条件法则、标准化核、包络、m/n窗口及均值付款。声明和提案均没有把 U1 两条物理尾不等式作为未经证明前提塞进冻结U0。

提案中辅助数值核对也相符：单位二阶矩在概率测度下给 β≥1；产品包络和 Ew²≤Menv 给 rho≤Menv；令窗口指数 qW=(p−2)/(2p)，则 1/p+qW=1/2，因此 m≥n/2 与 β*≤2β 的共同窗口折损是2^−1/2；率项换到原 n 时必须保留2^(p/2)、sqrt(2)。这些说明分解可用，不是已接受完整物理引擎的证据。

## 组装、裁决与下一边界

PREAMBLE 两个项目导入和 Pow.Real 导入、autoImplicit=false、universe u、命名空间与 noncomputable section 均逐字核对。HEAD 精确终止于声明，不含证明；授权的组装方式是 PREAMBLE+HEAD+从 `:= by` 开始的 PROOF+CLOSING。CLOSING 的两个 end 分别关闭 section 与命名空间，当前无需修正。let mN 与标准 pi 可测结构定义相同，P 类型中已显式绑定该结构，未改变实际法则；其实际 elaboration 仍须后续服务器核验。

本轮关键缺口：无。所需最小声明修正：无。对数学真实性和声明语义裁决为 CORRECT；对生产证明与机器证书裁决为 NOT_YET_REVIEWED / PENDING。本工作是已知 Laplace/乘积/Markov 工具的项目承重接口，不作新颖性主张。

后续保持同一独立审阅角色，等待 lead 明确激活完整新 SOURCE/PROOF 与实际全部 TYPE 的最终审阅。不得因本声明通过就把实现、外部SZ、统一物理桥、p54完整应用、DC、fullOQ56或root标为关闭。未启动 Lean、AX、工具链探测、服务器、网络、Git/API、子代理、Goal、计划或侧栏动作；未改冻结、作者、library、coordination。完成时实际 proof-writer/heavy/inflight/uncertain/pendingExternal/children 均0。

请求配置 gpt-6.1-sol/xhigh；实际 model/backend/effort 未被工具公开，均记 null；input/cachedInput/output/reasoningSubset 分别 null，不从请求值推断实际用量。
