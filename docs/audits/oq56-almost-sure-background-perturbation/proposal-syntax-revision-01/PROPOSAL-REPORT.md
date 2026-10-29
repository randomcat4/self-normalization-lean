# unit280：共同满测样本事件与背景扰动提案

状态：PROPOSED_ONLY_NOT_FROZEN_NOT_IMPLEMENTED_NOT_CHECKED。本件依据新 ACT 在获授权的 sibling proposal-syntax-revision-01 中交付完整纯语法修订。初封存后曾在旧 scope 子目录追加六文件，父已记录全部哈希并停止该写入；这些现场字节全部保留。旧 scope 的 noWriteAfter 契约不被追认为满足。数学签名、裸 RHS 和所有非定义 HEAD 不变。此文件是父级冻结前的精确接口提案与完整数学路线，不是已实施的 Lean 证明，也不是独立审查结论。授权身份为 /root/oq56_unit280_author；本次唯一写目录为 proposal-syntax-revision-01，原 proposal-01 整树只读。请求模型为 gpt-6.1-sol、xhigh；实际 backend/model/effort 与输入、缓存输入、输出、推理子集用量未由工具暴露，全部记 null。

## 1. 原始来源与本单元真实缺口

已完整阅读绑定的 p41 与 p51，以及 next-source-dependency-280.md。p41 §2 的 (4) 固定原 n 的分母及背景缩放核，(5) 从乘积包络得到 |F_A|≤ℓ²/2 与系数一的中心化范数扰动；其中原包络只在 μ.prod μ 几乎处处成立。278 已把确定性有限结论做成精确合格生产者，但它要求每个不同样本索引对逐点满足该包络。本单元支付从总体 AE 到真实有限 iid 样本共同事件的这一层，随后消费 278。

p51 S1 的任意可测空间因子讨论不要求在本单元先造标准 Borel 编码；坐标投影、有限产品测度、真实乘积可测残差已经足够。p51 S6 的真实条件第一投影、核均值和方差修正不是本单元结论。

设 Ω 为任意可测空间，μ 为概率测度，n 为任意自然数，Pₙ=Measure.pi (fun _ : Fin n => μ)。r:Ω→Ω→ℝ、w:Ω→ℝ。基础概率前提只有 hw:∀ᵐ o∂μ,0≤w(o) 与 hr:∀ᵐ p∂μ.prod μ,|r(p.1,p.2)|≤w(p.1)w(p.2)。没有非原子、标准 Borel、可测单点、r 对称、r 对角为零、典范性、g 均值零、g 方差一或任何矩条件。

## 2. 已有公开接口的定向检索与复用裁定

首写前先检查 curated library 中 map/pair/AE/envelope/sample 的公开声明及实际使用处。初始 P41、Probability、Basic 目录在此本地 curated 布局中不存在，随即改为整个实际 library 树定向查找；缺目录没有被当作不存在生产者的证据。检索范围和附加读取的真实 SHA256/bytes 均在 API-BINDINGS.json。

公开 P35.map_sampleCoordinate_pair 是 realLaw 的无限样本接口；P52 的两个 pair 接口是固定层分布；DoubleGhostSignInvariance.ghostMatrix_ae_envelope 给四角差分的 ghostMatrix 包络，不能反推出原始 r 样本条目的包络。CanonicalDoubleGhostRowMoments.canonical_ghost_mean 内的 hPair 是局部证明事实；P35.noise_affine_null 内的 hpair 是私有证明中的 API 示例，均不能跨模块调用。未在本次读取的 curated 范围找到同范围公开任意 Ω 的单样本原始残差共同事件生产者；这不是全库以外的不存在断言。

因此只提议一个 P41 内私有 T01 坐标对保持测度辅助项；它消费现有 Mathlib 独立坐标、两独立函数的联合分布和求值保持测度接口，不另造通用概率框架、不改 shared Probability/Basic。API-BINDINGS.json 与 USED-MATHLIB-PUBLIC-HEADS.txt 保存实际钉死 Mathlib 807d3836b165983210ee2ecf3cd28f239436949c 的完整来源 HEAD 及其上下文。没有为此联网、拉取源码、探测工具链或运行 Lean。

278 的精确消费绑定是源码 8481562684fc7a3c5455e8ab99d6f85b15f4778860fa414da93099b83b4adcb8 /30148B，以及 qualified-evidence 的 a5f3c16017165189da76dd7691b9ff10c3200eba203541dce25fe21a017054c1 /18854B。其首次成功原对象是 fbd3913b99528f0e63e8301180570ff9c7c0b95af37a4eff6509e9e52003149c /1519024B。复用原独立完整审查、native03 RC0 与同原对象 audit01 RC0；原 strictWrapperSuccess=false、16 warnings 的记录仍被如实保留，不能写成 strict wrapper PASS。这里不重审旧完整证明、不重跑 producer 或 AX。

实际完整读取并 lossless 匹配了三个被调用定理 T12/T13/T19 的未省略 TYPE，及九个直接/值依赖定义的完整 TYPE/VALUE。两份 USED-278-FULL 文件从精确 metadata 抽取，与绑定原 TYPE/VALUE 文本逐项重建相符；仅派生阅读件统一 LF，原输入字节不变。279 未合格证明、结果及其物理重标号均不作为供应。

## 3. 两个固定定义与确切量词

D01 sampleEnvelopeEvent n r w 的 RHS 是样本集合 E={x | (∀i,0≤w(xᵢ)) ∧ (∀i j,i≠j→|r(xᵢ,xⱼ)|≤w(xᵢ)w(xⱼ))}。E 只依赖 n/r/w，与 g、背景 B 及其选择规则无关。定义本身不需要可测空间或可测性前提；它只是集合。没有把任意 AE 谓词自动命名为可测集合。

D02 sampleBackgroundBounds n r w x 把三个实际 finite 消费结论固定为一个 Prop，避免在点态与 AE 两个接口中复制整段目标。固定 x 后先量化任意有限实向量 v:Fin n→ℝ，再量化所有 B:Finset(Fin n)。其 RHS 依次是：

1. 对所有 n/B，|blockPairSum (anomaly B) rₓ|≤(anomalyWeight B wₓ)²/2。
2. 在 4≤n 时，对所有 i∈B，|adjustedRow v rₓ i-backgroundRow B v rₓ i|≤ℓ wₓ(i)/((n:ℝ)-2)。
3. 同在 4≤n，并额外 3≤B.card 时，|sqrt(blockCenteredEnergy B (adjustedRow v rₓ))-sqrt((B.card:ℝ)-1)·backgroundStudentizer B v rₓ|≤ℓ·sqrt(backgroundWeightEnergy B wₓ)/((n:ℝ)-2)。

这里 rₓ(i,j)=r(xᵢ,xⱼ)、wₓ(i)=w(xᵢ)，ℓ=∑a∈univ\B wₓ(a)。上式的三种系数与分母逐字沿用合格 278；没有把半系数放宽为一，也没有为中心化范数引入二倍常数。完整定型 HEAD、定义 RHS 和 PRE/CLOSE 在 PROPOSED-HEADS.json，其余文本不是声明冻结。

D02 量化任意有限 v，故实际来源的任意 g:Ω→ℝ 直接用 v(i)=g(xᵢ) 实例化。即使只需要点态结论，也不添加与结论无关的 Eg=0、Eg²=1 或 g 可测性。D02 是实际有限结论包，不是新定义统计量来替代原对象。

## 4. T01：真实不同坐标对的保持测度

固定 i,j:Fin n 且 hij:i≠j。每个求值 eᵢ(x)=xᵢ 可测；现成 measurePreserving_eval 给 eᵢ 推前 μ。把 iIndepFun_pi 中各坐标输入函数取为 Ω 上恒等函数，便得到 Pₙ 下全体求值函数相互独立。这一实例只要求每个 μ 是概率测度及恒等函数可测。取两个不同指标，iIndepFun.indepFun hij 给 eᵢ 与 eⱼ 独立。

Pₙ 本身是概率测度，因而满足 map_prod_eq_prod_map_map 所需有限测度条件。以两个可测求值函数的 AEMeasurable 证书应用该接口，联合映射 x↦(xᵢ,xⱼ) 的推前为 (Pₙ.map eᵢ).prod(Pₙ.map eⱼ)。分别用 measurePreserving_eval 的 map_eq，右边即 μ.prod μ。该映射的可测性由两个求值的可测性取有序对给出。可测性与推前相等合成 T01 的 MeasurePreserving。

此处严格使用指标 i≠j，没有使用样本取值 xᵢ≠xⱼ。μ 可有原子，Ω 的对角集合甚至不必单独讨论其可测性。r 的原对角值保留任意，不用零替换；同一次观测可在多个不同索引中重复出现。若这些重复值位于总体包络的例外处，它们由真实坐标对的拉回零测集排除；没有假设所有重复都不发生。

## 5. T02：把两个 AE 前提放进同一事件

对每个 i，将 hw 用 eᵢ 的保持测度所给 QuasiMeasurePreserving.ae 拉回，得到 Pₙ-AE 的 0≤w(xᵢ)。对每个有序指标对 i≠j，将 hr 用 T01 所给保持测度的同一 AE 拉回接口，得到 Pₙ-AE 的 |r(xᵢ,xⱼ)|≤w(xᵢ)w(xⱼ)。此拉回接口的完整输入是任意 Prop 谓词的 AE 事实，不要求谓词先是可测集合；可测的是映射，绝对连续性控制例外零测集。

Fin n 以及其有序指标对均有限，所以有限多个零测例外的并仍为零测。对 i=j 的分支，目标是 i≠i→...，逐点真，不要求 r(xᵢ,xᵢ) 任何额外条件。把全体单坐标事实和全体有序不同指标事实的有限 AE 合取同时取得，正是 D01 的成员关系。n=0 或 n=1 时，对应空量化或空的不同指标约束自动有效，不需要 n≥4。

原来源 w≥1 若以 AE 形式给出，只需对其同一 AE 点使用 0≤1≤w(o) 得到 hw。提案没有把 AE 的 w≥1 升级为处处前提。

## 6. T03/T04：可测集合与实概率一另行支付

T03 明确要求 Measurable(Function.uncurry r) 与 Measurable w。对每个 i，函数 x↦w(xᵢ) 可测，故集合 {x|0≤w(xᵢ)} 可测。对每个 i,j，坐标对可测，复合 r 的绝对值可测；两个坐标权重的乘积可测，因此 {x||r(xᵢ,xⱼ)|≤w(xᵢ)w(xⱼ)} 可测。D01 的成员约束是这些集合的有限交；i=j 的蕴含约束为全空间。故 E 可测。只需这两个可测函数条件，无需 Ω 标准 Borel、可分、可测单点或非原子。

T04 在同样两项可测性与 hw/hr 下给出 Pₙ(E)=1（ENNReal）和 Pₙ.real(E)=1（Real）的合取。由 T02，Pₙ(Eᶜ)=0；由 T03 E 可测，加上 Pₙ 是概率测度，分割 univ=E⊔Eᶜ 的测度给 Pₙ(E)+0=1，故 Pₙ(E)=1。Measure.real 的定义是测度值取 toReal，因而实概率也是一。

AE 本身并不推出原 σ 域中 E 可测。T04 的函数可测性是为了与 T03 一起交付普通可测概率事件的自然来源接口；它们不是 T02 的隐藏前提。纯粹外测度的满测/实值恒等式可能可在更弱条件推出，提案不为此增加同义包装或声称可测性不再需要。

## 7. T05/T06：同一事件内消费三个合格有限生产者

给定任意 x∈E，解开 D01 恰得到 hwₓ:∀i,0≤wₓ(i) 与 hrₓ:∀i j,i≠j→|rₓ(i,j)|≤wₓ(i)wₓ(j)。接着任取 v 和 B，按以下真实参数顺序消费：

- 278.anomaly_pair_envelope_bound B rₓ wₓ hwₓ hrₓ 给 D02 的第一项。它没有 n 或 card B 下界，也不要求 rₓ 对称。
- 给定 hn:4≤n，278.adjustedRow_sub_backgroundRow_bound B v rₓ wₓ hn hwₓ hrₓ i hi 给每个 i∈B 的第二项。它的域明确是 B 内的行，不能扩成所有 i。
- 再给定 hm:3≤B.card，278.background_centered_norm_perturbation B v rₓ wₓ hn hm hwₓ hrₓ 给第三项。系数一来自已接受中心化收缩/范数 Lipschitz 生产者，本单元不重复证明它。

这些三项正好构成 D02，所以得到 T05。T06 在 T02 的同一 AE 样本 x 上附加 T05 的确定性结果，返回 x∈E ∧ D02(x)。不是先为每个 B 或每个 v 建立不同事件再作未经许可的不可数交：全部 v/B 的量化都在固定 x∈E 后由确定性定理完成。

任意选择器 S:(Fin n→Ω)→Finset(Fin n)，包括依赖全样本的选择，均可在每个 x∈E 中用 B=S(x) 实例化。若希望再选来源投影值，取 v(i)=g(xᵢ)。这没有宣称 S、g、所选统计量或其阈值事件可测，也没有凭此给所选统计量作概率表达式。需要这些结论时必须另行证明对应选择规则与实际函数的可测性。

## 8. 对角、对称、大小、零值与缩放核检查

不同的是索引，而非观测值；所有包络消费保留原 r，不做对角改写。被消费的三个界不要求对称。p41(4) 完整分子恒等式若未来需要，须显式增加点态 r 对称性并调用 278 原 T10；当前没有这项消费者需要，故本提案不加入该恒等式，也不把 AE 对称性直接当处处对称性。

共同事件与异常块半系数界覆盖每个 n。n≥4 仅在行差与范数的条件分支出现，card B≥3 仅在范数分支出现。B=∅ 时行量化空、范数条件为假，而第一项仍由 278 有效；B=univ 时 A=∅、ℓ=0，界自然给零扰动。n=0 产品法则及空量化被保留。中心化能量为零、背景 Studentizer 为零时，第三项只是已接受平方根范数差，没有除以这些量，也没有要求它们严格正。

所有行分母都是原实数 ((n:ℝ)-2)。背景 s_B 来自 278 的 backgroundRow，严格对应 h_B(o,o′)=g(o)+g(o′)+((B.card-2)/(n-2))r(o,o′) 的有限尺度；本单元没有把分母换为 B.card-2，也没有新定义以改变物理统计量。279 的 B→Fin(card B) 物理重标号、物理样本 m≥4 的限制是独立工作；本有限 card B≥3 不被冒称为原物理统计量在 m=3 的推广。

## 9. 无环声明次序与交付边界

次序为 D01、D02、T01、T02、T03、T04、T05、T06。D01/D02 只依赖已接受有限对象与基本集合/逻辑；T01 只依赖 Mathlib；T02 依赖 D01/T01；T03 依赖 D01；T04 依赖 D01/T02/T03；T05 依赖 D01/D02 与合格 278 T12/T13/T19；T06 依赖 T02/T05。T01 是唯一私有项，其他是公开定义/定理。没有循环、前向引用或私有旧模块跨界调用。

完整 8 个 HEAD 和 2 个 RHS 已定型为提案字符串，未冻结。两个定义的最终 proposed HEAD 直接在末行末尾包含唯一 :=，RHS 仍是原裸 body。完整组装式为 head + LF + definitionRhs + finalLF；不需要额外 separator 组件或格式 wrapper。SYNTAX-DIFF.json 保存 pureTypedHEAD 来源说明，不作为冻结 HEAD。ASSEMBLED-DEFINITIONS.txt 给出两项完整结果，静态 guard 对最终 HEAD+RHS 各断言恰好一个 :=。没有 Lean proof body、sorry、admit、新 axiom、unsafe 或 native_decide；未运行编译、前缀、AX、SSH、网络、上传、Git/API、子智能体、资源修改、日程或 Goal。STATIC-TEXT-GUARD.json 是纯本地文本结构检查，不是 Lean、语义独审或内核证书。

## 10. 保持 OPEN 的范围

本单元不支付条件真第一投影 g_R、条件核均值/方差、r_R 的典范化与原 r 的误差、实际条件交互集中、p41(3) 的异常块几何、稀有块指数积分与大 K/Q 付款、条件背景引擎接入外部 SZ、PE-L/NR/DC、外部 hSZ/hSZC 存在性或完整 OQ56/root。

原无条件 PE-R 保留 α_p=2(p-2)/(2p-1) 与原窗口。不能把 276 条件全窗中任意 α>0 的结论变成本单元或无条件原模型的结论。这里没有尾概率估计或定理完成声明。

作者完整路线已给出，但独立 SOURCE/语义审查仍待父级委任；只有父级可冻结精确声明并在后续授权下启动实施。当前无持久等待、无排队任务。封存后作者释放全部本次提案写权。
