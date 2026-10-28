# 261 完整新源码与证明独立审阅

结论：`CORRECT`，适用范围为本次精确新源码的陈述与完整证明审阅。`sourceAccepted=true`；`qualified=false`、`machinePending=true`。未发现关键数学缺口。该判断不替代尚未提供的 261 服务器内核、所有实际拥有者完整类型／必要值及递归公理证据。

精确源码为 `author-01/OriginalCurrentLevelPhysicalFiniteCostTail.lean`，SHA256 `1ae7e408e77d15677f56b9c33b34dfc8898a8a0ea80ebf99e98be48c16f3e732`，24766 字节、432 LF。完整 1–432 行均已实际读取，包括 109–429 行的全部 321 行新证明。源码严格等于冻结前文＋96 行冻结声明＋PROOF.txt＋冻结结尾；UTF-8 无 BOM、无 CR、单一末尾 LF。独立字节与禁用构造检查见 SOURCE-BYTE-CHECK.json，未见 sorry、admit、axiom、unsafe、native_decide。作者报告及作者静态检查只属于绑定记录，不作为证明成立的依据。

1. 冻结陈述与见证唯一性（1–133 行）。13–108 行逐字保留已审冻结声明。原始 Ω／mΩ／μ／h、投影 g、退化核 r、原始 v 与 rho、包络及所有窗口／矩条件均未修改。113–118 行只调用并解包一次 259，取得同一 m₀、hm₀、hcg、hRetained、cg 与 hPhysicalAll。此时尚未引入包络参数、n、z、p 或外部常数；124 行先给出 cg，126 行才进入固定包络参数下的 eventually-n，因此没有把 cg 或同一编码见证偷换成依赖当前水平的选择。132 行略去未使用的公开 D2 let 是定义性归约；142 行重新展开的内部 D2 正是同一个冻结裁剪定义，不改变声明。

2. 原测度与规范模型（134–250 行）。mN/P 使用原始 mΩ/μ；mN₀/P₀ 使用唯一 μ.trim hm₀；mAug 与 ν 使用同一 m₀ 和独立均匀实辅助坐标。ε_k=1/(8 sqrt(n)(k+1))、四进制生成序列编码、量化 Y、实际均值／尺度归一化 η 都与 259 的 294–402 行逐一定义相同。ξ0、ξ、q、A/B、真删点 Adelete/Bdelete、M/Mdelete、Anew/AdeleteNew、完整与删点指数及全 Iη 分母均未替换。211 行的 hFrontier 与 225 行的 hPhysicalAll 来自这同一见证，并在同一 n/z 上使用。213–222、227–237 行对长合取的解包顺序已对照 259 的完整声明核实；尤其 hSourceLim/hSourceNonneg/hSourceCubic 是原始 P 下字面 sourceCost0 的结论，不是删点自身归一化或裁剪模型的费用。

3. 严格矩预算与原始极限（251–288 行）。cSZ、C2、C4 的正性均取自显式 hSZ 的正确合取位置。257 行以 cBudget=cSZ 调用同一 hMomentPacket，β、cWindow 与原始矩窗口完全匹配。hLJoin 把增强空间上的截断矩总和等同原始 P 的 Loriginal；266–267 行仅沿此精确等式转换 Lη 极限。268–273 行由既有联合严格费用／矩最终指标提取每坐标 δη<1/2 与 Lη<cSZ z²。固定 n/z 后才在 k 上取 eventually，未交换 n 与 k 的极限。η 的可测性、独立性、L²、均值零、总二阶矩一及几乎处处 Vη>0，都从 259 的同一 hηpacket 精确投影；hD2bounds 给出点态 1+D2≥1/2，足以满足 260 的正性条件。未增加第三阶矩或指数矩条件。

4. 真实删点因子、非负性与支配（289–348 行）。完整因子是 259 的 (M,Anew,B) 三元可测表示的第二／第三投影，分子和 D2 则使用原 G1/G2；投影的可测性由连续坐标投影得到。删点因子同样从 (Mdelete,AdeleteNew,Bdelete) 投影，定义域严格是 `{j // j≠i}→ℝ`，所以不能读取被删 η_i。AdeleteNew 没有被任意替代物覆盖。328–330 行的 B≥0 来自 |D2|≤B；344–346 行的 Bdelete≥0 来自 hFor 的原始真删点非负结论。hFor 的四次十项解包后，第 45 项确为 ∀iζ，0≤A0delete∧0≤B0delete，已完整核对 259 的合取结构；不是靠名称猜测。Anew/AdeleteNew 的非负性和 |Dη|≤Anew 均沿原 hAnew/hAdeleteNew/hSigned 投影。

5. 完整 Iη 的可积性与原始裁剪分布（349–378 行）。每项 t−t²/2≤1/2 由 (t−1)²≥0，故 Sη≤n/2；实指数有界于常数 exp(n/2)。hSηm 与 ν 的概率性因此给出完整 exp(Sη) 可积；hIηpositive 来自同一分析包，不假设新的指数矩。完整／真删点费用的加权可积性和 sourceCostη→sourceCost0 则直接来自同包。370–373 行使用 259 的点态 W=projectionW∘q、V=projectionV∘q 和字面 b/D2 定义，证明带投影零时取零的 codedClip=T0∘q；随后把 259 的 map(T0∘q)ν=map(T0)P 精确改写为 260 所需分布等式。右侧确为原始 P，而非 P₀。

6. 四项费用和 260 的完整实例化（379–409 行）。三个静态费用分别是原始 P 上 T0≠physical 的事件、ν 上 V=0 的事件和 ν 上 z²|D2|>1/4 的事件；每项原事件均独立保留且≤同一 payment。移动费用为 ν{z|Dη_k|>Vη_k/4}，384–387 行使用 259 的 ∀γ>0 eventually≤payment+γ，既未从 limsup 擅推逐项界，也未把它替换成固定事件。389–395 行实例化 260 的 X=(Fin n→Ω×ℝ)、O=(Fin n→Ω)、对应显式 mAug/mN、ν/P 和同一 η；原始 Ω 的宇宙层 u 与 hSZ.{u} 相容。完整检查的条件对应如下：

| 260 的输入 | 261 的实际来源 |
|---|---|
| 两个概率测度、n≥1、原 ξ 可测、D/D2/原裁剪/物理量可测 | hνprob/hPprob、hn1、hξPacket、hD1aug/hD2aug、hT0Original/hPhysicalMeas |
| η 可测、独立、L²、零均值、总二阶矩一、D2 与 Vη 正性 | hηm/hηindep/hη2/hηmean/hηenergy/hD2pos/hηpos |
| 同一个外部广 L² 尾界输入及当前 z≥1 | 原 hSZ、原 z/hz，没有构造或放宽外部定理 |
| 完整／真删点可测因子和点态非负／几乎处处支配 | hFullFactorScalar/hDeletedFactorScalar/hFullNonneg/hDeletedNonneg/hDom |
| 完整指数可积且 Iη>0；完整与真删点加权费用可积 | hTilt、同一 hFullInt/hDeletedInt |
| 最终严格矩预算、Lη→Loriginal、字面 sourceCostη→sourceCost0 | hBudget/hLoriginalLim/hSourceLim |
| 原始裁剪分布、原始裁剪差异／编码零／D2／移动上误差支付 | hClippedLaw/hEclipFee/hZpay/hE2pay/hUpperPayPayment |

所有四个 p 参数均取冻结 payment，因此 hPayment 的四个 le_rfl 是真实相等输入，不是新增费用假设。260 在同一个 k 过滤器内部交合 hBudget 与移动费用的最终性；不要求任何未提供的统一常数指标。402–409 行取得的结论因此正是原始 P 的 physical 弱尾事件，下界−2payment、上界+4payment。physical 在 sqrt(centeredSq)=0 时取 0，原定义从未改变。

7. 三次费用替换（410–432 行）。正态尾非负来自已读取的 standardNormalTail_basic 完整声明；指数严格为正。C2/C4 正性和 sourceCost0≤cubicCost 给出下因子逆向／上因子正向单调。423–428 行只乘以非负前因子，再加减相同费用，所以即使 1−C2·sourceCost0 或 1−C2·cubicCost 为负，推理仍成立；没有把“有意义的正下界”当作额外前提。429 行准确组合费用非负、三次上界及四个尾界，覆盖冻结声明全部结论。

承载证据与适用范围：本上下文先前已完整读取 259 的 1114 行和 260 的 338 行以及必要定义，精确范围和哈希见 READ_ACK.json／STATEMENT-REPORT.md；本阶段只对新 261 及相关承载实例化做完整审阅，复用二者已有独立合格证明／首对象／机器证据，没有重跑旧检查、重做旧资格审阅或复制大型 TYPE。作者 manifest、首阶段冻结片段及 release 的 11 个直接绑定已重新匹配。新源码只有一个明写 theorem；实际拥有者及生成名仍须由服务器返回，不把源码声明数冒充实际计数。

待机器阶段：lead 提供这个精确源码的实际原生退出码、首个原始对象、全实际拥有者完整 TYPE／所有必要非 theorem VALUE、递归公理白名单与命令／源对象绑定后，本同一独立上下文继续最终核验。现在不写 FINALWRITE、不释放独占审阅写权限。所有实际模型／后端／推理强度和用量字段未暴露，记 null；仅请求值 gpt-6.1-sol／xhigh 已知。ExternalSZ、CDF、relative-tail、DC、fullOQ56、root 均为 OPEN；本单元只是显式 hSZ 条件下原始模型当前水平有限费用尾界。
