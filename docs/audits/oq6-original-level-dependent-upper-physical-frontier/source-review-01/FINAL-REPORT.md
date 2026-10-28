# Unit259 最终独立完整审查

STATUS: CORRECT

**接受精确 unit259，qualified=true，machinePending=false，issues=[]。** 本资格仅属于修复02源码 `1136c7f4cd654dc8fcf0ddc9b8c4575f901175e8b785c42aa9fd3926f562a172`，70472B/1114LF，以及首次成功原对象 `cd0c255925d57fc97b6da2768ce59371eb637297bbf90f5f2177ab8b64da10ac`，12314088B。同一独立上下文已经完成完整 SOURCE→statement/proof、两次受影响修复和全部实际机器证据审阅。Root 整合验收另属 Root；外部 SZ/CDF/relative-tail/DC、full OQ56、root 均继续 OPEN。

## 独立审查、精确覆盖与旧证据复用

reviewer 是 `/root/oq56_unit259_review`，与原作者及两名 fresh repair 作者分离；唯一写入范围始终为原激活的 `source-review-01`。未改写源码、冻结、library、共享实现、既有 SOURCE/STATEMENT/REPAIR 报告或失败证据。请求模型为 gpt-6.1-sol/xhigh；实际 model/backend/effort 及 input/cachedInput/output/reasoningSubset usage 不可见，均为 null。没有 Lean/lake/PP/AX、服务器、网络、上传、Git/API、子代理、Goal、计划或侧栏操作。

完整数学审查的精确联合为：SOURCE-REPORT `4ada7152813534cd16863b4d60a764e64d38adc00fe00f1d81d6d1fc0888e3cf`，11127B；REPAIR01-REPORT `7bce591579bdb2253ae1c46476cda93ace9922a3f952befc48281f66179b059f`，4076B；REPAIR02-REPORT `ce4ce324258c6ca0cdea07d9d90ab1b49dcb2310ddf7f7af5497952e74f23d4e`，3419B。前者覆盖原完整1111LF源与315LF新证明，第一补审覆盖四处 intro 名称删除，第二补审覆盖 hAug 的三行定义性类型对齐。最终 source1–13 为冻结 preamble，14–793 为冻结780LF head，794–1111 为318LF proof，1112–1114 为冻结 closing；完整拼接与所有未变字节再次核实。

257/258 的 qualified 证据、已接受独立完整审查与原对象仅按精确绑定复用，没有重审旧完整 proof/TYPE 或重跑旧 kernel/AX。本新单元所需承重接口、原 p51/p54 含义与新交互已经在 SOURCE 阶段实际审查。当前 final 不以新增上下文或 Root 接收为由重做旧生产者。

## 实际类型的完整阅读方法与结果

完整 actual-owned-types.txt 为 `8dbb466f2a8f08ec1700088aca5772451f1f9587673706db20812fb67c54201e`，1702026B/12903LF；完整 metadata 为 `f3cf475ec9ac942cfe680a7860feab5a6fbc8bdef43922221299f3c47022f101`，1720975B。全部 TYPE 与 metadata 中逐 owner 的完整 type 逐字相同。

为了实际读完高度重复的 pp.all 展开，本次使用**可逆的完整数学 token 阅读**：只将重复的括号表达式和完整常量/宇宙拼写替换为字典引用，保留每个 owner 的整个类型主干。MACHINE-TYPE-READ-MAP.json `557d114203e269d11dd14a5191fd3af2da08284bff3e7f50105d7ba480e0d0b9`，163184B，记录全部107项 K 常量别名、282项 D 表达式和3个完整主干。每一个 K/D 的右侧均实际阅读；公共主干0–87274字符按五段无缝完整阅读，两个辅助主干7656/281字符完整阅读。字典逐层展开后与原 TYPE 的空白规范化文本逐字相等，原始 TYPE 字节另与 metadata/raw stdout 严格核对。没有用摘要、名称列表或源声明代替实际 TYPE，也没有谎称直接显示12903行原始展开；这一读取表示可完整展开复核。

实际 owner 按完整 module-index 扫描独立重算如下，均 thmInfo、bodyExpressionPresent=true：

| owner（共同前缀 actual_original_level_dependent_upper_physical_frontier） | TYPE LF | 类型含义 | 递归公理 |
|---|---:|---|---|
| 公共定理本身 | 12396 | 完整同见证 current-z strict/cost/upper/physical frontier | propext, Classical.choice, Quot.sound |
| `._proof_1_2` | 490 | 在原 n≥4 和保留上下文中排除 ¬(1≤n)，供 upper 合同的样本数下界 | 同上 |
| `._simp_1_1` | 17 | 任意 DivisionSemiring 上有限和的逐项除法等于和后除法 | 同上 |

合计实际3 owner、3 theorem、0 non-theorem、0必要 VALUE、12903TYPELF；VALUE文件确为空，标准空文件哈希 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。实际公理出现次数由三份列表派生，各为3。无 sorryAx、目标新公理、未覆盖 private/generated/异名前缀 owner 或不支持的 constant kind。

完整审计输入实际只 import 新模块，用 anchor 的 getModuleIdxFor? 得真实 module index，再遍历全部 env.constants，无 namespace 过滤。每个 owner 输出完整类型和 Lean.collectAxioms 递归列表；若存在 def/opaque，则要求完整 VALUE。actual 库存全为 theorem，故空 VALUE 是已满足的空义务。两个生成项均实际阅读，不因非公开而省略。

## 编译后完整类型与原数学陈述对应

实际公共 TYPE 最初保留任意可测 Ω、原概率 μ、h 的产品可测/L²/对称/中心化与投影二阶矩1，g/r/v/rho 定义未改变。第94行仍先形成 μ0 的 trim 见证，所有 n/current z/epsilon/p/budget 均在同一 m0/hm0/hcg 之后。没有新增 Ω 标准 Borel 前提；实数 Borel/Polish 实例仅服务具体编码。

实际 TYPE 第98行起保留整个 all-n/y/epsilon 旧包；5137行起保留当前 z 的 literal analytic consumer 与原 μ p 矩严格预算。全部 signed Q/Deta、原/约化/增强 law、删一保留坐标、full/partial 加权可积性与连续极限、正完整 Ieta/I0 均在实际类型中。部分项的比率仍以 full I 归一，不是重新用删一 normalizer。

实际 TYPE 第8677行才在同一 m0 内给出 cg；随后 envelope 参数、eventually-n、w、z 与三个独立 tilt/envelope/geometry 条件保留。新段原 μ 的 hSq/hSqBound/hEnv 和后段 hgp（第11214行）仍明确使用 mΩ/μ；没有因局部 m0 实例偷换为 μ0。beta=0/正 beta、2<p≤3、正 cBudget 和精确 cWindow/beta-window 均在原量词位置。

新 current-z canonical lets、实际 eta=actualNormalizedFamily、signed correction 和所有成本与冻结声明一致。Hsource 的可测性只在原 mN；Ssafe 在 mN0/mN、Jsafe 在 mAug。id:P→P0 和 q:ν→P0 的方向正确，ν.real(Jsafeᶜ)=P0.real(Ssafeᶜ)=P.real(Ssafeᶜ)≤P.real(Hsourceᶜ) 的链完整保留，未声称 q 到原 P 或 Hsource 约化可测。

physical 保留真实 centeredSq 分母为零时取0的原统计量；physicalBad 仍为原P下 E2original、Z0、Eclip、Zphysical 的四事件并。当前512*rho*z clipping、Hsource 上1/32余量、真实分母正与因式分解、精确 clipped 推前法则均保留。对所有 BorelEvent 的物理/编码clipped加性差值由原P.real(Eclip)支付，没有用 Gaussian 尾/CDF结论替代。

实际 E_k= {z|Deta_k|>Veta_k/4}、same-eta 点态收敛、Jsafe最终安全、E2/Z包含、eventual每正gamma及limsup付款均完整出现。跨空间两项和明确为 ν.real(E_k)+P.real(physicalBad)，其上界是2*payment+gamma、limsup≤2*payment。最后一个 k0 仍让六项 strict/cost 与两项概率界对全部k≥k0同时成立；没有删去正 tau/delta/gamma 或制造任意收敛速率。

## 首个成功原对象、命令与执行状态

实际第三次 Lean 尝试标签为 author-kernel-03b：RC0，24.655418870970607s，receipt `4a299add4c13b3c31101e67967a120ef22059f2270bfb3523683f807326bfd5c`。同首对象 import-only audit：RC0，6.953496638685465s，receipt `13e16f1b95ab4feba01402757d2ed33d11633721fd51ae2d09814c099e1af4d6`。两次自然结束，allOwnedEnded=true，无timeout、cleanup、ownershipIssue或postError；受保护记录 before=after，派生数分别28458/28468。

首对象路径为服务器 `.lake/build/lib/lean/Shao/OQ6/OriginalLevelDependentUpperPhysicalFrontier.olean`，mtime_ns=1793216061783219116。native后、audit前、audit后均完全同一个路径/大小/mtime/SHA256指纹；没有审计重编译。native argv 指定 -o 该对象，audit argv 无-o且只import该模块。两次真实CPU before/after均52–55，实际argv均 -M8192 -j4。

现有命令/STOP回执窄投影 `7e0eff01281cb3416e8e6763a39926a2e7491a0848e5cd0bdad8e279a6b6d5ee`，14903B，完整读过。额外现有 pin/CPU窄投影 `233845ae096ab176872a7dcd8f07b5f3e9ccdb5ef9ce16cef7c28f600badd7ad`，4844B，补齐原工作树 lean-toolchain 全文 `leanprover/lean4:v4.36.0-rc1\n`，29B，SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；native/audit前后/current完整指纹相同。Mathlib HEAD为 `807d3836b165983210ee2ecf3cd28f239436949c`。补充共享mathlib路径的当前pin相同，其历史alias映射为null，未误称它也有before绑定；主工作树pin已完整绑定。此补充只读已有回执/字节，没有pin或Lean重放。

完整AUTHOR-STOP内容可由窄投影无损重构为1417B、哈希 `04a33c3003d7b7e9bece586316ce3e4d128e749c00881c488b8376a525f9606f`，与原指纹一致，明确不为warning重编译，仅审计同首O。native/audit两个严格wrapperSuccess都false，外层transport exit_code都是1，原记录保留；本资格依据真实Lean0/0、首对象、完整所属证据，而没有把严格空流封装改写成成功。

## 元数据、诊断与失败保留

五份归一文本均与server文件map/binding哈希及字节数一致。全部rawOwnedJSON字段、owner components/name、宇宙参数、类型与body/kind/AX逐项核对；从JSON/完整TYPE/空VALUE/count块在内存无损重构原审计stdout，得到1703707B、SHA256 `742b6b33113ccbf219204f204265c1d5b1c309ef5b8e786b4ebd543bf5e57bb8`，与原receipt/binding完全一致。完整normalizer适配脚本和audit输入均实际读取；没有在本地执行它们或复制对象/cache/raw log。

正确诊断投影按每条精确模块前缀header扫描，独立派生44warning/0error，其中8style、36unused；分类与 corrected actual projection 的44条位置/内容标题/完整消息哈希及字节数逐项相等。6条letI与2条intro合并建议不影响证明。unused的前提名称、p矩/窗口/包络binder和未使用textual lets已与完整实际TYPE对照：前提仍在forall中，未使用let不等于数学假设丢失。原完整消息保持server；本地读取的是其完整分类/位置/标题/块指纹，而不冒称新传输了raw日志。stderr134B与已接受相同环境warning哈希一致，未宣称mathlib工作树洁净。

早先native01/02的RC1/noO和两次局部修复证据保留。03标签曾因配置键映射在STARTED/Lean之前失败，原失败/输入/config保留且LeanCalls=0；03b是实际第三次Lean，不是第四次数学检查。两份旧不完整regex/parser投影明确保留为历史解析失败，最终44计数来自corrected原stdout扫描，没有为修正诊断计数重跑Lean。P175已有一次metadata adoption未重放。

原p54条件p矩收敛/最终统一有界修复、固定clip1三次费用反例、外部结果归属均保持。当前资格是冻结条件下同一current-z过程的完整strict/cost/upper/physical接口与加性法则比较，未关闭外部source/SZ/CDF/relative/DC或原root。

FINAL-VERDICT给出精确资格，FINAL-COVERAGE记录完整阅读/可逆TYPE映射/原对象/源与回执绑定，MANIFEST封存所有本reviewer文件。最后单独写FINALWRITE，以writers/heavy/inflight/pendingExternal/children/uncertain六零释放本任务全部权限，随后不再写入。本次审查没有需要作者或lead修复的未决问题。
