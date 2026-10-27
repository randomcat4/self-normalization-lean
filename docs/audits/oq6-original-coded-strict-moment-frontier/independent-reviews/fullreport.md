# Unit231 新鲜独立完整 SOURCE／证明审查

STATUS: CORRECT

SOURCE_STATUS: SOURCE_ACCEPTED_FOR_NATIVE

QUALIFIED: false

KERNEL_STATUS: PENDING

审查对象为 `Shao.OQ6.OriginalCodedStrictMomentFrontier.actual_original_coded_source_z_strict_moment_frontier` 的唯一新源：SHA256 `885505f80bd8640a95a13d17694373faec66ece6a4df10614d456c475e20d227`，32683B、566LF、0CR、UTF-8 无 BOM。此结论是完整源码、题意、冻结声明和所消费接口的独立人工语义裁决，允许该精确版本进入首次 native。没有运行 Lean，尚无 unit231 首次原对象、实际全部所属 TYPE／必要 VALUE 或递归公理资格；本报告不把人工检查称为机械通过。

审查者为 `/root/oq56_original_coded_strict_frontier231_source_review`，是从未作者的新上下文，仅写 `drafts/oq56/unit231/source-review-01/**`。先完整读并核验了 activation `233a46a41653efebc43f2efc6da932a7fce74303438f726010ba49eee2bcb396`／3131B，实际 ACK 已记录。按 math-theorem 的新上下文验缝角色执行，未使用 math-ultra。请求配置是 gpt-6.1-sol／xhigh；工具未暴露的实际 model、effort 与 input、cached input、output、reasoning subset 四项使用量均为 null。本人没有改动源码、冻结、共享文件或其他所有者文件；没有 Lean、服务器、网络、传输、Git／API 或子实例操作。

## 已完整覆盖的输入及复用边界

逐行完整读了新源 1–566，包括 16–208 全声明与 209–563 全证明；完整读了 p51 的 355LF。冻结 preamble、head、closing 与当前源逐字节相等，并独立从冻结 head 解析全部 63 个公开普通数据 let，逐项比较名字、类型和 RHS 与库存。16 个声明参数、两个声明局部实例、六个模型量词、五族八名存在性见证、19 个目标块均按实际声明核对，未以作者计数代替实际返回类型。

完整读取实际依赖声明：226 的 16–384、229 的 12–45、230 的 23–67、原投影 producer 的 186–279、独立 Q 包络的 178–241、解析极限的 173–241、scalar code 的 313–335、quantizer 的 94–110；并读实际均值／尺度／归一化、编码、截断 integrand、原 D／J／clipping／删除量定义。所需 Pi／Prod 可测 API、完整 map 积分 API 和同 pinned commit 下的两条保测可积复合签名均实际阅读。`API-COVERAGE.json` 保留完整所消费 producer 声明与逐字段拆包对应，不包含旧 producer 证明体。

SOURCE-AND-ROUTE 的来源／路线／接口范围叙述及 proof-local 计划、固定 API 段被阅读；其中重复的 producer 声明由上述实际源声明阅读覆盖。作者报告只是待核对说明，没有用它替代证明阅读。旧 226／229／230 的精确 qualified evidence 与其独立最终证据按绑定复用，不重新审旧证明、不运行旧 producer／leaf AX。226 当前源、229 当前源、230 repair-01 当前源分别与旧资格绑定相同。旧资格中的 native 实际成功与 wrapper 布尔值、历史失败保留等含义维持原样，本报告没有重定义旧证据。unit228 不是选中证明依赖；未阅读、复制、修补或运行其证明。

## 题意、量词和普通数据

p51 本身标记 UNCERTIFIED_REPAIR_CANDIDATE。当前单元机械化其中 S19 的原 IID p 矩预算以及 S20–S24、S4 末段连续截断预算的一个精确承重接口。外部 Shao–Zhou 随机区间／CDF 引擎及 DC 结果仍归原外部依赖。本单元不认证整份 p51 补证、不主张新颖性，也没有闭合一般 S15、S25 加权费用、S27 CDF 或 OQ56 根范围。

原 Ω／mΩ／μ／h 及 g、r、v、rho 的定义在选择 m₀ 前固定。`v` 明确使用原 mΩ×mΩ 与 μ.prod μ；证明从未用约化积分重新定义 g、r、v 或 rho。p∈(2,3] 的 hgp 与 β 只在原 μ 上。cWindow 的公式只依赖 p、cBudget，出现在 m₀ 和所有 n／C0／z 前，不依赖当前样本或近似索引。未增加约化／增广 p 矩、hY、积分运输 callback 或严格余量等 caller 前提。

63 个普通值逐项类型／RHS 相符。其作用域可分为：原始六值 g/r/v/rho/β/cWindow；同一个 m₀ 的 μ₀；固定 n/C0/z 下的 mN/mN₀/P/P₀/N/K/ε、ξ0、原 D1/D2/A0/B0 及原长度删除量；固定的 Uniform(Ioo 0 1) 增广 mAugLocal/mAug/νlocal/ν/q；当前同一可数生成结构的 cCode、ξlocal/Ylocal/ξ/Y/a/s/ηlocal/η/C；原与近似 W/V、b/Qε/Dη、完整及删除 H/M/A 包络；最后 Fz/δ0/δν/δη/L0/Lν/Lη/scalarBudget。所有序列都仅由显式 k 索引派生，ν、q、m₀ 不随 k 改变。原 n 的 D 分母 √n(n−1)、J 删除分母 (n−2)² 和 clipping 参数 1 保留，未把删一统计量系数改成 n−1 样本版本。

证明内普通 `let` 只有冻结许可的 zeroSection 与 tailIndex。zeroSection 的类型为 `(Fin n → Ω) → (Fin n → Ω × ℝ)`，RHS 是 `fun ζ i => (ζ i, 0)`；tailIndex 的类型是 ℕ，RHS 是 `max kb kq`。模型和可测标量函数来自原定存在性接口，kb/kq 来自既定尾存在性。额外三个概率实例全部取自 226，声明内两个 m₀ 实例仅被复装。没有额外普通值、顶层辅助定理或 caller 假设。

## 完整证明核对

**原投影与窗口（212–227）。** `actual_quadratic_source_moments` 在辅助 n=3、x=0 的条件均满足，首两项确为原 μ 上 g 的可测性与 L²。这里没有替换目标 n。230 在原 mΩ 下显式实例化，取得 β 非负、cWindow 正及其 p 次幂的精确等式和严格小量。hgp 的 `change` 只展开同一个原投影定义。

**公共模型与序列（228–304）。** 整个源码只对 226 做一次产生 m₀/hm₀/hcg 的调用。该见证先于 ∀ n≥4、C0≥0、z≥1，之后仅调用同一返回包的 forall 部分。εk=1/(8√n(k+1)) 正且严格小于 1/(4√n)，因 n≥4 且 k≥0；倒数序列分解证明趋零。K=4√n 固定，`hScale` 只是精确环等式。ε0 的包只提供不依赖当前 ε 的法则、原 ξ 事实及原 A/B/H 输入，未把 ε0 的 η 或其编码因子化当成所有 k 的事实。

**截面、均值与编码（305–339）。** zeroSection 的可测性按每个坐标 eval 与 Prod.mk 证明；ξi∘zeroSection=ξ0i 是逐点定义等式。截面允许第二坐标 0 不在 Uniform 支持内，因为这里只证明函数可测，既不积分该截面也不声称其保测。构造无需 Ω 默认值或 StandardBorel Ω。由此得到约化 ξ0 可测，结合 q 的保测律与 226 原约化均值零，经完整强可测 map 积分定理得到增广 ξ 均值零。ξlocal 的可测性来自同一约化 gcoord；scalar-code 的 [1/3,2/3] 范围、可测性及 comap 正好满足 quantizer 全部输入。quantizer 返回第1项可测与第3项逐点误差，取 `.1` 和 `.2.2.1` 正确。P08 覆盖每一个 k/i 和全部样本，未添加回调。

**当前 k 的归一化与因子化（340–387）。** 每个 k 都重新实例化同一 hModelAll 的 εk 包，未再次选择 m₀。独立解析得 226 外层 65 个字段、literal 后缀 52 个字段，固定包 rcases 分别消耗全部字段。当前包前18项忽略后，第19项开始正好是 scale/local/independence/L²/均值/能量/零事件等。当前 literal 的第38/39项正好是 full/delete factorization；之前37项被跳过，第40项起由 tail Prop 承接。将其 θ 取为当前 εk 后 M/Anew/B 与 Mdelete/AdeleteNew/Bdelete 逐点定义相等，C 为同一当前 ηk。删一函数域只含 `{j // j ≠ i}`，没有被删坐标。`hNowScalar` 的 G2 与 z 处 G1 来自当前同一 C；G1/G2 不是 ε0 的见证。P09、P12、P13、P14 因而对全部 k 成立。

**Qε 的真实 L¹（388–446）。** 所消费 Q 包络的实际输入与 226 提供的 D1/D2/A/B 的可测性、L¹、非负和绝对控制全部匹配；删除量作为固定实函数传入，无隐藏删除可积性前提。独立解析实际包络为36个字段，拆包全匹配。Qε=Dη−D1∘q 的代数等式与 signed 恒等式没有分母除法，因此也覆盖原 V=0 点。包络系数 ρ=4εk√n 等于 Kεk；H 正是当前声明的 H，未换成含 η 的随 k 支配函数。得到 Qε 可测、Qε 和 |Qε| 真正可积、|Qε|≤M、|Dη|≤Anew，以及有限 ∫|Qε|≤Kεk∫H。∫|Qε| 非负，右端趋零，夹逼给真实 L¹→0，未使用总化 Bochner 积分默认零充当可积性。

**Fz 和原法则运输（447–493）。** 完整解析 API 在当前 ν/ξ/Y/ε 和 x=z 下实例化，其前提仅需要 L²、均值零、总能量1及逐点 ε 误差。独立派生的返回顶层字段数为32；第12/13项确为 Fz(ξ)/Fz(η) 真实可积性，第18/19项为坐标／总预算趋向 δν/Lν。其余尾项被 Prop 变量承接，不会进入结论。Fz(t)=(zt)² min(|zt|,1) 精确保持 source z；未改成 1+z。由 hm₀ 得原→约化 id 可测，P₀=map id P 的方向正确构造保测 id。Fz∘ξ0 在 mN₀ 上可测；q.integrable_comp 的正向把增广可积性送回约化目标，id.integrable_comp_of_integrable 再拉回原产品。分别沿 q、id 的 map 积分等式给 δνi=∫P₀Fzξ0i=δ0i；有限求和给 Lν=L0。极限因此到达原 P 的预算。没有任意 f 的运输假设，也没有使用可测嵌入或逆映射。

**原 IID 定量预算和同一尾段（494–547）。** `hIIDAll n hn1 z hz` 仍保存原 mΩ，P 与声明显式原产品相同；`Shao.truncationF (z*t)` 的实际定义与 Fz t 相等。230 完整返回包与11个绑定一致，提供标量预算真实可积性、逐坐标等于 scalarBudget、总和 n 倍恒等式、非负性、p 矩速率和 β=0 时全部零。窗口的正 β 分支是闭端点 `z≤...`；严格预算来自预留 cWindow^p=min(1/2,cBudget)/2，而非偷偷把窗口改为开端点。β=0 分支直接保留。cBudget 任意正且没有被识别为外部 cSZ。

只在该确切窗口内才向 229 提供已经证明的 δνi<1/2 和 Lν<cBudget·z²。229 采用同一实际 ν/ξ/Y/ε/η，返回第5个结论正好是 `∃kb,∀k≥kb` 的全体有限坐标及总预算严格界。任取 τ>0，Q-L¹ 极限给 `∃kq,∀k≥kq,∫|Qεk|<τ`。tailIndex=max kb kq 使两个尾段共同成立。k0 可以依赖固定模型/n/C0/z/τ，没有宣称跨 n、z 或模型统一速率；原归一化、signed 恒等式、全部标量因子化本来对每个 k 成立，因此同一尾段保留它们。

**最终组装（548–563）。** 已逐项核对构造器与实际目标的右结合结构；P10 中四个断言的最后两个由 Q 包络的成对返回值提供。`hCurrent` 与 `hQEnvelope` 的各级 `.2` 投影指向其实际字段；没有漏掉真实可积性、严格不等号、全样本量词或同一索引条件。源在第564/566行按冻结 closing 结束。

## 19 个目标块逐项覆盖

| 冻结块 | 精确证明覆盖 | 审查结果 |
|---|---|---|
| P01 | 212–218、233：原 g 可测／L² | CORRECT；原 μ，辅助 n 不污染目标 |
| P02 | 219–227、233：β、cWindow 与两条 p 次幂关系 | CORRECT；常数先于 n/z |
| P03 | 228–239：同一 μ₀ 概率 | CORRECT；无第二模型 |
| P04 | 273–304、548：P₀/map id/ν/q | CORRECT；map 方向、空间明确 |
| P05 | 305–314、548：ξ0 约化可测 | CORRECT；具体可测截面 |
| P06 | 245–268、549：全部 ε 正小及趋零 | CORRECT；n≥4 保证分母正 |
| P07 | 288–304、315–323、550：ξ 可测/L²/均值0/能量1 | CORRECT；均值经实际 q 律 |
| P08 | 324–339、551：Ylocal/Y 可测及逐点 ε 误差 | CORRECT；全部 k/i/x |
| P09 | 340–384、552：当前 η 归一化/独立/正分母 | CORRECT；每个当前 εk |
| P10 | 396–437、560–563：Q/Dη 等式和两条包络界 | CORRECT；逐点含 V=0 |
| P11 | 400–446、553：Q 与绝对值真实 L¹及趋零 | CORRECT；同一个固定 H |
| P12 | 363–384、554：完整三元标量因子化 | CORRECT；当前 Ck、θ=εk |
| P13 | 363–384、554：删一三元因子化 | CORRECT；仅 j≠i，原 n |
| P14 | 385–387、555：Dη/D2 的 G1/G2 | CORRECT；同一当前 Ck |
| P16 | 447–477、556：四处具体 Fz 真实可积性 | CORRECT；未靠默认积分 |
| P17 | 478–488、557：δν=δ0 和 Lν=L0 | CORRECT；q/id 两次运输 |
| P18 | 494–511、557–559：原标量恒等式、速率、零 β | CORRECT；原 μ 与源 z |
| P19 | 447–493、559：每坐标及总预算无条件极限 | CORRECT；不以窗口作前提 |
| P20 | 512–547、559：原窗口严格预算和共同 k0 | CORRECT；闭窗口、β=0、同尾段 |

冻结编号没有 P15；实际19块正好是 P01–P14 与 P16–P20，不是漏证。

## 边界、禁止项与实际检查状态

n≥4、z≥1、C0=0、任意 cBudget>0、p 接近2的开端点和 p=3的闭端点、β=0／正 β、闭窗口右端、每个 k（包括0）、每个 τ>0、原 V=0 和编码 Vη 零集均由对应量词或已核对 producer 接口覆盖。没有要求原 g 无原子或全 Ω 可分离；编码只恢复实际可数生成可测信息，不升级为恢复原完整 sigma 域。没有把无权 L¹ 偷换成 weighted 收敛，也没有给出单位231未陈述的 p0 指数小、CDF、原子尾连续性或全根结论。

静态扫描未见 sorry、admit、新 axiom、unsafe、native_decide。只有一个新公开 theorem，没有新顶层 helper。此次独立字段计数脚本的一项预设把解析包总字段数误填为35；实际平衡括号分割得到32，已修正审查脚本预设并在 `STATIC-COUNT-CORRECTION.json` 保留此纯审查计数事件。所消费第12/13、18/19项从始至终正确；源、冻结和证明没有因此变更。这个本地计数事件不是数学／Lean 失败或通过。

没有已识别的数学、量词、来源或实质接口缺口。下一步是 lead 对该精确源首次服务器 native；成功后仅在同一首次原对象上取得全部实际所属 TYPE／必要非定理 VALUE／递归公理审计。由本同一独立上下文合并源审与该机器证据；在那之前 qualified=false、kernel pending。若 native 报告实际 elaboration 问题，需保留失败并仅处理受影响源／证据，不能把本次 SOURCE 接受预先升级为 Lean 通过。
