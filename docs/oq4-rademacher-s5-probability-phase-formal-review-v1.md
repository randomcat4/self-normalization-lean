# OQ4 S5 完整独立审查

STATUS: CORRECT
REVIEW_CONTEXT: OQ4 lifetime context99 / fresh independent final reviewer
FINAL_SOURCE: drafts/oq4/rademacher-s5-implementation-v1/Source.lean
FINAL_SOURCE_BYTES: 56403
FINAL_SOURCE_SHA256: 5b492c8193434dbe2db6be8cc82ca653d329a0e6b5c587aa6cf5204953e48397
PHASE_A: CORRECT
PHASE_B: PRIVATE_FULL_SOURCE_AND_ALL_OWNED_NATIVE_AUDIT_PASS
SEMANTIC_TYPE_AND_DEFINITION_REVIEW: CORRECT
CANONICAL_OR_EMIT_AUTHORIZATION: NONE
NEW_RAW_LEAF_INCREMENT: 0
S5_SPECTRUM_OQ4_ROOT_CLOSURE_CLAIM: NONE

冻结范围内的数学、最终完整 Source、全部实际所属常量的类型/安全/公理，以及所有实际项目依赖的源/对象绑定均通过本次独立审查。原始问题到冻结声明、匿名完整证明和最终全部 Source 的审查在 Phase A 完成；Phase B 对同一原字节 Source 完整执行一次私有无对象输出检查，随后全文审阅所有 156 项实际类型及 41 个完整透明定义值。没有关键数学或形式语义缺口。

本结论适用于指定的私有 Source 与锁定依赖环境，不声称已完成 canonical 编译、对象生成、集成或一般 OQ4 根闭合。后续是否授权 canonical/emit 属父实例，当前没有该授权。本审查已结束，不再运行 Lean。

## 1. 固定门、运行与不变性

父实例先全文接收 Phase A 报告，再明确释放 Phase B。Phase A 历史报告及其输入读取清单保持原字节；本报告附录完整保留它的原文，包含当时尚未执行机械门的历史状态，不能把历史 pending 误读为本报告的最终状态。

本次 Phase B 只读 A5 的 author-v1/round-004/Source.lean，在自己的 `A5/independent-bounded-v1/` 写入精确副本、私有目标、纯机械后缀及审计产物。私有完整目标的前 56403 字节从 offset 0 与冻结 Source 完全相同，之后才追加 12126 字节审计后缀。没有截断、重排、包装或删去任何证明。

运行目录 W 为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`，分支 `feat/oq4-s5-assembly`，HEAD `e9b5eae51b09ad370f125e02754495b90c9185ae`。私有目标位于 `repro_outputs/oq4-rademacher-s5-implementation-v1/independent-bounded-v1/round001/private/Shao/OQ4/RademacherS5Assembly.lean`。实际 argv 由 check-receipt.json 完整记录：固定绝对 Lean 二进制、CPU18–21、`-M8192 -j4 -DautoImplicit=false -R <private-root> <whole-target>`，没有 `-o`、lake env、ulimit-v 或 RLIMIT_AS。

Lean 实际版本为 4.36.0-rc1，commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e。二进制 SHA256 `db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00`。环境严格以 `os.environ.copy()` 后 update 锁定的 server-only runtime-env-v1.json 构造；没有重建或下载环境。

| 四份锁定清单 | SHA256 |
| --- | --- |
| stable-base-v1.json | de59d7517e0d2a2e7238e3dc2fe108451504b23b76634a27a94e9105acbda8f8 |
| selected-runtime-bindings-v1.json | 1cbfc8108ec6023513de37620639001cffda9b146225e474e77ca80fa9505148 |
| runtime-project-view-v1.json | 5d15db7618cb40c5289947dfbb673f59d03169eeb8915dac7b6b914c015da94a |
| runtime-env-v1.json | 0422a5231ebf0307bb20673d611323a9ea3e35a017b4e03bbe8b00cdf24bf243 |

运行前后分别重新计算四组实际映射和集合成员：OQ4 sources 51，受保护其他 sources/config 220，HEAD sources/config blobs 271，旧 build artifacts 108。每个实际键的哈希和整个 membership 都与冻结 base 精确一致，不只比较条目数量。五个上游 refs 的值均与 base 精确一致；HEAD、branch、packages symlink、pins/config、全部 32 个源和 olean 绑定及 32 个 alias 集合/哈希/resolve 均不变。symlink 比较按双方 Path.resolve()，没有把一个合法对象路径中的 symlink 误作不一致。

S5 canonical source 和整个 `.lake/build` 中 `RademacherS5Assembly*` 前缀在 pre/post 都不存在。旧对象没有被复写。pre guard SHA `a76e2bd42af32a637373a100b6c95d9f2d72d3342c61edfb4abc7902e72cec12`，post guard SHA `6d2f41eaa7dd1955d9472417327c488a30ddae35bc55468a0ce1630612f232e7`，完整 guard 文件留服务器。

round001 首次完整 Source+全部 audit 成功，subprocess exit code 0。没有失败轮、没有后处理失败，也没有 Lean 重跑。唯一完整检查调用 1 次；另有固定二进制 `--version` 元数据查询 1 次。实际 instrumented_native_seconds 为 16.598921086639166，仅覆盖本次完整检查子进程，不声称是全部审查耗时。实际 trustLevel=1025，skipKernelTC=false，autoImplicit=false。后缀未跳过内核类型检查。

## 2. 实际所属范围与全部安全/公理账

在完整 Source 精化后的实际环境里，分别计算 imported-map 差集、getModuleIdxFor? 所示 main-module ownership，以及 foldStage2；三套**精确名称数组相同**，长度 156。没有以命名空间或预期的公开项数量作为 owned 筛选条件。

逐项实际分类为 41 个公开透明定义、20 个公开定理、13 个显式 private 定理、82 个 generated 定理；合计 41 definitions / 115 theorems。13 个 private 项由 Source 实际 private 声明名字对照精化后的 `_private...` 精确名字认定；82 个 generated 是实际集合余项，随后逐项审阅其类型，不是把 156−61 的算术当作独立证明。

82 个生成项中有 **11 项名字不在本 S5 命名空间**，实际 owner 仍是本 S5 模块，包括 S2.K.eq_1、S3.K/p.eq_1、S4.K/N/Q/QK/p.eq_1、S4.b.congr_simp、BrownianSup.U.congr_simp、Shao.closedStrip.eq_1。它们都是本轮精化触发的定义方程/同余定理，已经包含在三套 156 名称清单、全部类型、人读和公理审计中，没有因名字看似上游而漏检。

本审查全文连续读取 `actual-owned-interfaces.md` 的全部 109959 Unicode chars：半开区间 [0,22000)、[22000,44000)、[44000,66000)、[66000,88000)、[88000,109959)。因此实际读入 156 项完整类型和全部 41 项透明定义值，也读入选定移位/强制转换的 pp.all 表示。逐项判断与字符覆盖记录见 actual-semantic-ledger.json。普通定义值没有 `⋯` 或 `...` 截断；某些 generated congr 类型中的 proof-irrelevant transport 参数由标准 pretty-printer 抑制，不代表删去数学前提。

另由本审查自己的后处理脚本从上述人读 MD 重新解析156个 type 和41个 definitionValue 的完整文字，逐项重新计算SHA256；197个指纹全部精确等于原生ledger中的对应字段。该后处理只读取既定PASS产物，没有再运行Lean。

owned-axioms-ledger.json 的全部 156 行分别审查 owner、kind、unsafe、partial、axioms 和类型/定义值指纹。其 typeRefs/valueRefs 完整名称数组用于机器闭包核验；本报告不把所有这些引用字符串或 raw Expr 冒充人逐词全文理解。安全/公理行的人读视图另存 owned-safety-row-view.json。

156 项 owned：unsafe=0、partial=0、new-axiom kind=0。每项 collectAxioms 的实际集合都属于 `{propext, Classical.choice, Quot.sound}`，总并集恰为这三项。没有 sorry/admit/native_decide 或不受允许的新公理；Phase A 去注释文字扫描与本次实际全 owned 的公理/安全检查一致。

## 3. 实际类型和完整定义值的语义裁决

41 个实际定义逐项均与冻结含义一致：

| 定义组 | 实际核验 |
| --- | --- |
| N、root、height、phaseFloor、upperHeight、delta、coeff、E、F、Ncell | 固定 CP/S4 别名，真实自然数时间、rpow 根、floor+1 弱边界与固定 π²/(4c³) |
| x | 实数乘法 c*rpow((n:ℝ),−(1:ℝ)/6)，没有整数除法或自然幂替换 |
| p、K、b | 同一实际 S4 产品弱事件概率、killedMass 与 Brownian 概率 |
| pathLaw、V、selfNormalizedEvent | Fin n 的固定 Rademacher 产品律、真实 energy 的 sqrt、全部 k≤n 的乘法弱事件 |
| Q、QK、Qsource | 精确原高度/原 x，实际分子和原 Brownian 分母，无自由概率比 |
| shift | 实际多态 `{α}→(Nat→α)→Nat→Nat→α`，value 直接为 S4.shift |
| cubeSeq、cubeMinusOneSeq、upSeq、downSeq、nearestSeq、phaseSeq、phaseOffset | 同一 CP 自然数索引和固定加法截尾；0/1/interior 分支分别复用 down/up/nearest |
| Cluster | 同一 CP 严格自然数子列聚点定义 |
| PositiveTime、ProbabilityLegal、LogIdentities、LegalAt | 正时间、实际概率正性和 log 身份均在输出谓词中，未成为额外公开前提 |
| ShiftedObjects | 所有相位、概率和对数项使用同一 σ(j+J)，实数值/自然时间类型正确 |
| TailS4Inputs、S4ReturnOutputs | 原索引 S4 输出、每个 J≥Ncell 的同一全 j 尾输入及逐项对象桥 |
| MainLimits、MainOutputs | 六项实际误差极限、同一合法 Npos 和每个 ε 的共同尾段 |
| CPPhaseOutputs、PhaseLimits、PhaseOutputs | 确定性相位与实际概率结论分开，严格子列/合法尾段及任意固定额外 J 同步 |

`pp.all=true` 实际完整读取 shift 的 type/value，TailS4Inputs 的 type/value，S4ReturnOutputs 的 type/value，ShiftedObjects 的 type/value，以及 S5_S4_EVENTUAL 的 type。明确显示：`shift phaseFloor` 的 α 为 Nat；之后才有 `Nat.cast Real`；`shift height` 的 α 为 Real；`shift (fun (n : Nat)=>n)` 的 α 为 Nat；S4Outputs 的 n_ 参数仍为 Nat→Nat。不存在因期望类型导致将移位自然数函数误精化成实数函数的情况。属性 elab_without_expected_type 保持冻结数学，实际内核类型风险已由此关闭。

20 个公开实际类型均保持 Phase A 逐项冻结对应：definition_bridges、zero_time、positive_time、actual_path_energy、actual_source_event、positive_time_S4_bridges、S5_DOM、S5_S4_EVENTUAL、S5_MAIN、S5_CUBE_GEOMETRY、S5_CUBE、S5_ROUNDING、phase_index_bridges、S5_PHASE、S5_CLUSTER_BOUND_Q、S5_CLUSTER_BOUND_QK、S5_CLUSTER_REALIZE、S5_CLUSTER、S5_NOT_CONVERGENT、S5_UNIT_CLUSTER。完整类型显示固定 c>0、实际 IsBrownianReal B P、原自然数域及全部目标结论，没有增加正性、极限、sqrt 桥、WeakCell 或相位实现作为公开自由前提。

13 个显式 private 类型也逐项符合源码推理：critical_inputs/actual_s4 从固定 c>0 产生实际输入和输出；legal_of_s4 只是局部转换已取得的具体 S4 条件；ratio_from_log_error/difference_from_ratio 的局部参数在最终调用处已被证明；cp_phase_of_data/cp_phase_shift/actual_phase_limits/phase_outputs_of_cp 保留同一 σ；up/down/nearest_actual_phase 给固定 CP 截尾见证；main_outputs_proof 的唯一数学参数条件仍是 c>0。

82 个 generated 类型逐项为定义方程、参数同余、自然数尾阈值的算术反证、非零幂/积的 simplification 身份，以及 x 实数分母的数值类型类证明；没有独立插入概率公理、额外模型或更强新前提。它们的证明值虽不作为人读数学稿复制，仍全部进入 ci.value? true 的递归审计。

## 4. 全部递归闭包与实际依赖绑定

审计从 ALL 156 owned 常量出发，对每个 ci.type 和 `ci.value? true` 的 getUsedConstants 递归到闭包稳定，包含 opaque 和 theorem proof values，而非仅透明定义或公开头。共 61540 个实际常量。每个可达 project 常量按实际 owner 识别，逐项执行 type/value refs、unsafe、partial、kind、collectAxioms 检查：797 项，分属 26 个模块，176 definitions / 621 theorems，所有项目安全计数均0，公理并集仍恰为标准三项。

26 个实际 owner 精确匹配32冻结绑定的子集；每个 owner 的源与 olean 指纹、路径均逐一验证。原生后缀还逐个导出实际 imported project module 的 Lean.findOLean 路径，后处理对其 resolve 路径与对应绑定的 olean.resolve()、内容 SHA256 再比较。32 个实际导入模块均精确绑定；不存在有绑定却未导入的 runtime 模块。不能因为冻结有32项，就要求每项都进入证明闭包。

6 个实际已导入但未进入 proof/type-value closure 的模块单列为：Shao.Basic.Events、Shao.Basic.OrderedSelection、Shao.C1.Normalization、Shao.C2.TwoSided、Shao.OQ4.CosineCoefficients、Shao.OQ4.KilledCosine。它们不被记成实际证明依赖，也不被删掉导入绑定校验。

actual-dependency-bindings.json 的全部字段已完整读入，包含26模块源/olean绑定、6个import-only绑定、全部32实际resolve结果、每模块常量数与项目种类计数。project roster规范化SHA256为 `85591e9cbff3809930431835ecbf87ee90a218093859e9bf1648c271ef224a8b`。797项逐常量的完整机器审计行和61540项闭包行保留在服务器 audit-native.json；这不是新的上游证明全文人读审查，也不声称人全文读过约56MB机器文件。

## 5. 数学结论、风险边界与来源

完整数学推导和原文行映射见下附的 Phase A 原报告。其承重判断经实际类型确认仍成立：固定 Rademacher 产品律给真实 V=√N a.e. 并识别源事件；正时间精确 x√N=h；同一 S4_EVENTUAL/全 j 尾移位产生实际 log Q−qδ→0 和最终正性；CP 弱相位界提供 F 有界性，从而实际相对及绝对误差均消失；同一 CP 严格索引族转移实际端点、内部相位及每个 d；任意严格 τ 的实际有限极限转成同一 F 的有限极限完成包含方向，每个区间 L 以 d=log L/q 的 CP3 实现完成反向；实际序列不收敛由同一已证差误差与 CP 不收敛推出。

没有以 CP 的确定性结论冒充概率结论，没有把 sqrt/正性/概率极限/弱相位条件作新公开自由前提，没有变化 c、strict 事件、其他 cosets、一般分布、均匀 x OQ4、精细立方根 O 率或强 Brownian O 率扩张。n=0 与早期低高度项保持原定义；合法概率对数在共同正性尾段解释。

读取隔离沿袭分两段记录，均仅来自父实例 provenance 元数据，不作为本审查数学证据：

1. 作者96早期声明定位 regex 曾回显 FinitePath 21行及 MeasurablePath 20行上游证明体片段，共41行；父当时明确允许继续，之后改为 proof-mask。父给出旧 receipt.json SHA256 `b704cdbc6ad85b939de56c1ec58eae5c7a0083fad85c6578ad37769405007cac` 的 boundaries.initial_locator_exception 指针。本审查没有读取该旧 receipt、这41行或其推理。
2. 作者 native 阶段定位 elab_without_expected_type 时曾接收 Mathlib/Order/Defs/Unbundled.lean 五条属性示例的单行 lemma，含短证明项。本审查未读取该文件或五项短证明。不能把这一新例外误记成作者整个生命周期仅有五条暴露。

本审查自身只读取 Phase A 列明的公开头/透明定义，以及 Phase B 明确允许的 S4 纯机械 suffix/driver/recovery 模板；没有读取旧 S4 审查结论、旧 Source.exact 或任何额外上游证明。另读取标准 Lean.Util.Path 的 findOLean **单行 API 头**，用于实际导入路径绑定，无数学证明体。没有读作者 progress/receipt reasoning、其他S5审查结论或 author-v1 下其他轮的证明。原稿完整 Source 的读取由本任务明确授权。

使用 math-theorem 技能及其必要 refs；传输和本地非 ASCII 文本处理采用 windows-gbk-utf8 技能的显式 UTF-8 约定。没有新增代理或外部消息/发布动作，没有修改任何目标Source、冻结输入、author-v1、公共源、缓存、既有对象或 Git。

## 6. 固定产物、核验范围与停止

| 产物 | 字节 | SHA256 |
| --- | ---: | --- |
| actual-owned-interfaces.md | 113352 | c238f118c54250ed2cccb00b2bc8f8d2f47e25f36f9699d8202b8ce32389bd65 |
| owned-axioms-ledger.json | 356750 | c4b2b69b04d5227e97abcc88f0350fe11db25133dc28ab8c0c3232856b447be4 |
| actual-dependency-bindings.json | 38317 | d86de2b7e96ba429760fc17c9d6c5d1354887ffdd4c7d7070b39578844150cec |
| check-receipt.json | 4720 | 1b6dfb3d2dba205fabf52e9fc01bcbf0d8116a741b036948cece6bae7fc451bb |

这些四份既定产物在父实例并行读取前已固定，之后没有改写。check receipt完整字段也由本审查读入。精确 suffix SHA `423907285e1504b7d6b90537e85d612ccbdf0d8d6231ca471862925f8261343c`；combined target SHA `36b0fcc1400b04a98cdcc6b580ac14bc46df01800ebd423f157139f5e6c9a8cf`；driver SHA `6cbececeafba7a38669119155fe56a8a3adb7de287ec590c8fc6877e1e30aaa7`。pure postprocessing没有重跑Lean。

服务器 raw native文件55968185B/SHA `ee5563d146ad1ece2675d990131074d869b46411c60e1c7469255f11853d5b6b`，raw expressions1549544B/SHA `2bc946c4c0aa8cfda60c45443b87d403656a55b454b2b1bc9e5ab27cfe81071b`；完整日志、环境、raw Expr、闭包和二进制均保持server-only，没有下载到本地。没有把机器审计体积当成人读覆盖量。

最终 **CORRECT** 的范围是这份完整 S5 Source 的原文忠实性、数学证明、私有全源内核检查、实际156所属范围、完整项目递归依赖绑定及标准公理闭包。一般分布 OQ4、完整 Spectrum/OQ4 根与发布/集成仍不在本结论中。不新增rawleaf，不签发canonical/emit授权。heavy已结束并释放；本审查STOP。

---

# 附录：原 Phase A 完整报告（历史快照）

下文逐字保留当时报告。当时机械门 pending 的字段已由本报告上半 Phase B 实际核验补齐；该历史快照不被覆盖或回写。


# OQ4 S5 独立完整审查：Phase A

STATUS: CORRECT
REVIEW_SCOPE: LOCAL_STATIC_ONLY
REVIEW_CONTEXT: OQ4 lifetime context99 / fresh independent S5 reviewer
SOURCE_SHA256: 5b492c8193434dbe2db6be8cc82ca653d329a0e6b5c587aa6cf5204953e48397
SOURCE_BYTES: 56403
KERNEL_TYPE_CHECK: PENDING_PHASE_B
LEAN_EXECUTION: NOT_RUN
TRANSITIVE_AXIOM_AUDIT: NOT_RUN
DEPENDENCY_INTEGRITY_AUDIT: NOT_RUN
NEW_RAW_LEAF_INCREMENT: 0
S5_OR_SPECTRUM_OR_OQ4_ROOT_CLOSED: NOT_CLAIMED

此处 CORRECT 仅裁决授权的 Phase A：原始语义、冻结数学、完整匿名相对证明、41 个透明定义、20 个公开头，以及最终 Source 的完整静态推理一致且没有关键数学缺口。实际精化后的内核类型、依赖环境、公理闭包和服务器机械门均尚未由本审查执行或接受。收到过父实例给出的检查状态和哈希元数据；本结论由本审查自己的完整读取、独立比对和推理产生，不以已有 PASS 或其他审查结论为依据。

## 1. 完整输入与读取覆盖

全部路径以 `C:/game/shao lean/` 为工作区根，原始来源另在只读 `C:/game/shao/current/`。逐文件完整字节数、SHA256、总行数、全文或精确局部读取范围及公开头边界记录在 `input-read-manifest.json`，并嵌入 `phase-a-review.json`。FULL 表示模型实际完整读入；对上游 library 不以全文哈希冒充全文阅读。

| 核心输入 | 字节 / 行 | SHA256 | 模型读取 |
| --- | ---: | --- | --- |
| 原 `oq4/c01/spectrum01.md` | 4306 / 119 | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 1–119 全文 |
| 原 `oq4/frozen01.md` | 1491 / 20 | ea50b9fe0d742cbc9481fb126476ae2a788c7b0ec42d4e60636d757baf7cbc5a | 1–20 全文 |
| `frozen-rademacher-s5-probability-phase-v1.md` | 15006 / 235 | b79dd1cb131277acab9f156668ed1fde8aafa9c6632b821951719617b701b04d | 1–235 全文 |
| `frozen-rademacher-s5-formal-statements-v1.lean.txt` | 24193 / 471 | 1b1ad31b8147cb142f7c5bca262903abe11428cc186e93b967a5adaeb01dd6a4 | 1–471 全文 |
| 匿名 `rademacher-s5-probability-phase/proof.md` | 26160 / 519 | f212c53f79bfa219ebd99f0ad70e23ee0e9634c2c132234b8e5195012cc62235 | 1–519 全文 |
| 最终 `rademacher-s5-implementation-v1/Source.lean` | 56403 / 1122 | 5b492c8193434dbe2db6be8cc82ca653d329a0e6b5c587aa6cf5204953e48397 | 连续 1–400、401–780、781–1122，全体证明体 |
| S4 数学冻结 `frozen-rademacher-s4-probability-assembly-v1.md` | 11831 / 173 | 144e3c290ca60c174ceec0cc85b41519a82faf0eb55c09a1c54e61e1d097e00a | 1–173 全文，仅声明 |
| CP 数学冻结 `frozen-rademacher-critical-phase-v1.md` | 8147 / 117 | 4e8be7821b842a1fe7a6a143f9705fa476b05615e122fdd621d4cb1c5c88c1ce | 1–117 全文，仅声明 |
| S4 精确形式冻结 `frozen-rademacher-s4-formal-statements-v1.lean.txt` | 16426 / 378 | 0c4af1e038d7290b08daf6da9578519be7ffc913611f91fca2b833129d5fe6f1 | 1–378 全文，仅定义/空证明占位 |
| CP 精确形式冻结 `frozen-rademacher-critical-phase-formal-statements-v2.lean.txt` | 10959 / 214 | d2656efb76cbbdba2ad08bc9352b05270461e466aec8a94d09b9dca0ed60a4bc | 1–214 全文，仅定义/公开头 |

已全文读取工作区 AGENTS、SERVER、TEAM，以及 math-theorem SKILL 与 prompt-library、openai-workflow、lean-verification 三份必要参考。它们的各自哈希见清单。本阶段明确禁止服务器/Lean/Git，故没有为了技能的一般 Lean 阶梯越权进行工具链探测或编译。

一次批量输出在工具层被总长度截断；不能将该输出视为完整覆盖。因此其缺失的 CP 形式冻结及 S4 数学冻结随后分别完整重读。最终上述覆盖没有遗漏。

## 2. 原文到冻结和形式输出的逐项对应

| 原来源位置 | 冻结数学位置 | 匿名证明位置 | Source 位置与裁决 |
| --- | --- | --- | --- |
| spectrum 5–7：固定 Rademacher，真实 V=√n | 46–82、88–99 | 39–71、75–105、120–179 | 32–75、237–375：固定两点律、有限产品、真实平方能量及实际自归一化事件；PASS |
| spectrum 11–12、33–34：弱胞元/空路径/低阈值 | 82、101–107 | 108–118、177–179 | 269–313、426–447、570–611：N=0 保留；正时间桥只在 n≥1；主胞元最终取得；PASS |
| spectrum 70–77：S4 相位/三项尺度 | 109–140 | 181–307 | 377–568、614–650：同一 S4_EVENTUAL、同一全 j 截尾 S4_ALL 与中心项桥；PASS |
| spectrum 85–90：实际临界倍率指数 | 125–140 | 266–309 | 521–568、652–656：实际 log Q−E→0，Q/F→1，Q−F→0；PASS |
| spectrum 95–96：立方及立方减一 | 142–163 | 346–364 | 778–830：精确 CP 自然数子列，端点实际概率与合法尾段；PASS |
| spectrum 97–98：内部 nearest 相位 | 163、189–199 | 366–381、401–419 | 760–776、808–830、885–956：同一 floor(t+1/2)，并列向上；PASS |
| spectrum 101–104：固定 c 的 up/down/内部相位 | 165–209 | 383–439 | 730–776、832–956、1018–1050：固定自然移位、同一 CP 量；PASS |
| spectrum 93、100–104：完整聚点区间及不收敛 | 211–225 | 441–493 | 958–1118：任意 StrictMono 子列包含、每点覆盖、两序列无有限实极限；PASS |
| frozen01 3、7–9：实际 U，其他原问题作用域 | 44、233–235 | 11、25、512–519 | 49–52、237–267、所有公开量词：实际 Brownian 对象经 S4 公开桥消费；不扩大到一般分布/均匀窗口 OQ4；PASS |

原 spectrum 97–98、96 的精细根余项 O(k⁻²)、O(k⁻⁵) 明确未被冻结，也未被这里声称证明。原 spectrum 61 的更强 Brownian 相对指数 O 率没有被引为 S5 新假设。保留 frozen01 的实际 Brownian 身份及首项消费边界。

## 3. 41 个定义与 20 个公开头

独立脚本 `phase-a-static.ps1` 对冻结文本和最终 Source 执行：删除注释、归一空白，定义比较完整透明右侧，公开定理比较到 `:=` 之前。没有用证明体文字比较代替数学审查。结果：冻结 41 defs / 20 public heads；Source 41 defs / 20 public heads / 13 private helpers；61/61 相同，差异列表为空。逐项行号映射在 `static-interface-comparison.json`。

20 个公开结论逐项确认如下（冻结行 → Source 行）：

| 公开项 | 行映射 | 静态判定 |
| --- | --- | --- |
| definition_bridges | 230 → 237 | 全部真实对象和 Cluster 定义桥完整 |
| zero_time | 254 → 269 | 原零时间项完整 |
| positive_time | 262 → 293 | 正底数/sqrt/立方及 x 精确桥完整 |
| actual_path_energy | 266 → 315 | 实际有限产品律上的共同 a.e. 能量完整 |
| actual_source_event | 273 → 342 | 可测性、a.e. 事件、真实概率及 Qsource 桥完整 |
| positive_time_S4_bridges | 285 → 377 | 同一 H、δ、第三尺度、x、w、Q、QK |
| S5_DOM | 297 → 570 | 最终合法性与正侧趋零均为输出 |
| S5_S4_EVENTUAL | 313 → 614 | 原索引输出及每个固定 J 的同一全 j 尾序列 |
| S5_MAIN | 319 → 652 | 六项极限及共同合法 ε 尾段 |
| S5_CUBE_GEOMETRY | 325 → 778 | 严格自然数子列及合法减一 |
| S5_CUBE | 344 → 808 | 立方/减一/内部实际相位 |
| S5_ROUNDING | 354 → 832 | 原上下舍入和 tie-up |
| phase_index_bridges | 378 → 861 | CP 原 target/index 精确式 |
| S5_PHASE | 393 → 885 | 同一组 Ja/Jb/Jα 及 phaseOffset |
| S5_CLUSTER_BOUND_Q | 414 → 958 | 任意严格 τ，实际 Q 的全部有限极限 |
| S5_CLUSTER_BOUND_QK | 424 → 988 | 任意严格 τ，实际 QK 的全部有限极限 |
| S5_CLUSTER_REALIZE | 434 → 1018 | 每个区间 L 的同一 CP3 相位实现 |
| S5_CLUSTER | 444 → 1052 | 两条序列的完整双向集合等式 |
| S5_NOT_CONVERGENT | 452 → 1074 | 固定 c>0，无有限实极限 |
| S5_UNIT_CLUSTER | 460 → 1107 | c=1 的原区间与无有限实极限 |

Source 80 的 `attribute [elab_without_expected_type] shift` 是冻结之外唯一执行性元数据命令。shift 的定义仍是完整相同的 `{α} → (ℕ→α) → ℕ → ℕ→α` S4 别名；属性调整精化时是否先用期望类型，不定义数学对象、不增添前提或公理，也不改变已写明的移位公式。静态上这是数学不变的精化元数据。**归一文本相同不能代替实际精化后的内核类型相同**：自然数移位、实数强制转换等实际类型必须留 Phase B 验证。

额外导入仅为标准 tactic、实幂渐近及有限产品测度模块；本模块没有新 notation、宏、elab、局部假设组或把概率结论装入类型类的代码。`static-source-scan.json` 对去注释后的 Source 没有检出 sorry/admit/axiom/unsafe/native_decide；这只是一项本地文字扫描，不是公理闭包审计。

## 4. 完整推理的承重核验

### 4.1 固定域、时间与真实能量

c 一次固定且仅要求 c>0。所有指数是实数 1/3 与 −1/6。Source 293–313 先取得 n≥1 的正底数、sqrt 正性，再用 sqrt_eq_rpow 和 rpow_add 得 x√N=h，随后合法除以 √N。h³=c³N、N/h³=1/c³ 来自同一 CP positive_time，不使用自由根序列。

Source 315–340 对固定 Rademacher law 先证明单坐标只取 ±1 a.e.，通过实际 product measure 的坐标零集接口及有限 `ae_all_iff` 得到所有 Fin n 坐标共同成立。平方和因此为 n，V 是实际 energy 的 sqrt。n=0 也由空有限和/空乘积处理，既未假设 V 的身份也未换成方差能量。

Source 342–375 由连续前缀和与连续能量墙得到可测事件，在上述共同满测集上用同一个 x√N=h 替换阈值，再用 a.e. 集合相等和 measure_congr 取得真实概率相等。k=0 被真实 closedStrip 包含；正时间阈值非负使它不改变源文 k=1,…,n 的最大值事件。早期 h<1 的概率仍按原事件定义，无谱表达替换。Source 269–291 单独交付 n=0 的空事件、p=K=1，不在此处声称正时间概率对数合法。

### 4.2 S4_EVENTUAL 与同一尾移位

Source 426–455 验证 hcell 的见证就是 CP cutoff，取得原 h→∞、N/h²→∞，第三尺度在 n≥1 精确为固定正数 1/c³；据此调用已冻结的实际 S4_EVENTUAL，输入是 `(phaseFloor c, id, height c)`，没有自由 S4 概率比前提。

Source 614–650 对**每个** J≥Ncell 明确构造 TailS4Inputs：三个胞元条件对 j+J 全部成立，两项发散尺度按同一个加 J 组合保持，第三尺度全 j 等于 1/c³ 并以 J_M=0 作界。随后实际调用 S4_ALL 的三条同移位序列。w 的桥是 `(π²/4)*(1/c³)*δ = coeff*δ = E`；x、δ、Q、QK 和 ShiftedObjects 同时对齐 j+J。原索引结果通过已接受的 S4_EVENTUAL 公开返回接口取得，而非偷把 S4_ALL 的全 j 前提当成最终前提；上游返回桥的证明实现不在本阶段重审。

匿名证明 185–272 还逐步给出 j=N−J 的合法自然数返回和原阈值 J+j_pos、J+j_ε；没有截断减法损失，且全部概率量使用相同 J。这与 Source 消费 S4_EVENTUAL 的方式相容。

### 4.3 实际正性、概率对数和相位误差

Source 457–484 把实际 S4 TimeLegal/ProbabilityLegal/LogIdentities 与正时间桥、实际源事件桥合并为本模块 LegalAt。Source 521–568 取 Npos=max(Ncell,max(1,max(Jtime,Jpos)))，所有 p/K/b/Q/QK/Qsource 的正性和所有 log 恒等式在同一尾段成立，均在结论侧。

同一实际 S4 log 误差通过 n≥1 的精确桥变为 log Q−E 与 log QK−E 趋零。对任意 ε 的阈值再与 Npos 及两条 log 误差阈值取最大，故不会用 Real.log 或除零的总函数值取得概率解释。私有泛型 ratio_from_log_error 所用的正性与趋零前提，在实际调用处均来自上述证明，并非新增公开假设。

由 exp 的连续性及尾段 exp(log Q)=Q 得 Q/F→1。绝对差不能单凭相对误差得到；Source 500–519 确实消费 CP finite_phase 的同一固定 c 全局界 `0<F≤exp(coeff)`，再以 ε/exp(coeff) 控制 `F*|Q/F−1|`。该更强的全 n F 界本身由真实非负高度的弱 floor 相位推出，不限制原概率序列。匿名证明 286–307 使用其足够的尾段版本，数学完整。

### 4.4 同一 CP 严格子列及实际概率转移

Source 659–728 严格区分 CPPhaseOutputs 与 PhaseLimits。先保留同一 σ 上的 δ/E/F，再用 StrictMono 的余终性组合整列实际误差；σ(j)≥j 把同一个 Npos 带到所有实际概率与对数。PhaseOutputs 对任意固定 J 同步全部量，而不只移位相位或只移位概率。

Source 730–776 中 up 和 nearest 的原 CP 见证只追加固定 2，down 的 CP 见证已≥2；这正是原见证的输入移位，严格递增、每点胞元与全部极限同步保持，不是从目标概率极限反选新 σ。S5_PHASE 选择一组 Ja、Jb、Jα，此后 d=0/1 直接复用 down/up，内部复用 α=1−d 的 nearest 与同一 Jα。c 与 α 的见证可以依赖参数，不能依赖 ε；实现符合此要求。

Source 778–830 保留 `(j+1)^3` 与 `(j+2)^3−1`，其自然数减法、整数/实数转换及 floor=k−1 由 CP exact_below_cube 的 k≥2 域供给。nearest 透明定义是 Nat.floor(target+1/2)；公开 rounding 结果明确误差区间和半整数向上，未换任意 nearest 选择。

### 4.5 完整区间的两个方向及不收敛

Source 958–1016 处理**任意** StrictMono τ 上的有限实际极限 L。由 Q(τ)−F(τ)→0 推出 F(τ)→L，故可用 CP 已接受的确定性 factor 聚点集合给 1≤L≤exp(coeff)。QK 同理；实际合法尾域及 Q=QK 的转移另外从 LegalAt 取得。该论证没有把 CP 的确定性聚点结论误说成实际概率结论，也没有只检查构造的子列，更没有在证明 L>0 前先取 log L。

Source 1018–1050 对每个 L∈[1,exp(coeff)]，先取得 L>0、q>0 及 0≤log L≤q，令 d=log L/q。然后使用 **CP.phase_realization 的同一自然数相位子列**，保留其 δ/E/F 三项极限，再以已证实际误差同时转移 Q、QK、Qsource。这个 J 是同一 CP3 的固定见证；冻结 S5_CLUSTER_REALIZE 本来量化该见证，不要求它和 S5_PHASE 的另一存在性包装具有命题外的指定数值相等。两个方向于是给完整集合等式。

Source 1074–1105 通过 Q−F→0 与 QK−F→0 将假设的全列有限极限转成 CP.factor 的有限极限，反驳 CP 已接受的 not_convergent。它与匿名证明 491–493 显式消费实际两个不同端点的论证等价；实际比较误差已在前面证明，故不是直接把纯确定性不收敛冒充概率不收敛。q>0、exp(q)>1 单独交付。只否定单一**有限实极限**，符合冻结结论。

## 5. 风险检查与隔离边界

| 风险 | 核验结果 |
| --- | --- |
| 原固定分布被泛化/换 law | 无；law 的两点 Dirac 展开、pathLaw 和 p 都固定 |
| V=√n 被加成自由前提 | 无；共同有限乘积 a.e. 证明产生 |
| n=0 或早期 h<1 被删去 | 无；定义保留、zero_time 单独证明，最终门仅控制尾段 |
| 弱整数 δ=1 误换 strict δ=0 | 无；CP floor+1 精确复用，立方 δ=1 |
| positivity/log合法/概率极限被当前提 | 无；全部由具体实际 S4 消费和桥产生 |
| 全 j 接口误作 eventual j | 无；S4_EVENTUAL 返回与显式 TailS4Inputs/S4_ALL 分开核对 |
| δ、E、F、p、K、x、b 或 σ 各自独立截尾 | 无；同一 shift、ShiftedObjects 和 PhaseOutputs 保证同步 |
| 绝对误差遗漏 F 有界性 | 无；CP 弱相位界显式消费 |
| 只列端点或只给区间包含 | 无；任意 τ 包含及任意 L 实现两向齐全 |
| 对一般 c 假设某个正时间整数高度 | 无；舍入相位及极限端点足够 |
| 任意 nearest/tie 未覆盖 | 固定向上并列与冻结 CP 一致；不声称额外推广 |
| 隐藏强 Brownian 率、第四尺度或变化 c | 无；只消费原实际 S4 与固定 CP 输出 |
| 局部文字扫描冒充内核/依赖公理审计 | 未作此声称；Phase B 待授权 |

允许且实际读取的额外公共接口边界：

- library CP：28–57 的 18 个透明定义，以及全部 23 个公开定理的完整头；每头严格在 `:=` 前截断。23/23 与冻结 v2 归一比较相同，结果见 `cp-public-head-comparison.json`。未读 58–859 的私有推导或任一公开定理证明体。
- library S3 22–79 与 S2 11–39：透明对象别名/定义，确认 p 是原产品 closedStrip、K 是原 killedMass、x=h/√n、b 是实际 BrownianSup.probability；未读其证明。
- RademacherCosine 15–20：halfENNReal、law；另只读 law_isProbabilityMeasure 的公开实例头。
- FinitePath 18–31：Path、prefixSum、prefixSquares、energy；ClosedSurvival 26–27 的 closedStrip 与 44 起的最大值桥公开头。
- MeasurablePath：continuous_prefixSum、continuous_energyWall 两个公开头。
- KilledIteration 16–27：环境参数、iterKernel/action/mass 透明定义，另只读 killedAction_zero 头；KilledKernel 20–27 的 translation/restrict 透明定义及 killedKernel_apply 头，确认闭区间杀死且无重新归一化。
- BrownianSup 44–54、121–125：真实 pathSup、traceSup、fullStrip、可测版本 U 及实际事件 probability；另只读 traceSup_aemeasurable、measurable_U、U_ae_eq_pathSup、U_le_ae_iff_fullStrip、probability_eq_fullStrip 的公开头。U 的可测版本与真实上确界 a.e. 对齐由公开接口承担，未假设一个自由尾函数。

所有上游文件先做公开声明索引定位；索引只回显公开定义/定理第一行、namespace/variable 等声明行。用于哈希及提取头的脚本在内存扫描原文件字节，但模型输出严格限于上述透明定义及 `:=` 前的头，没有输出/阅读上游证明体。哈希是整个只读文件的指纹，不能据此声称审过其实现。

未读取作者96的 progress、receipt reasoning 或其他 S5 声明/数学审查产物。父实例另披露：作者定位标准属性时曾接收 Mathlib/Order/Defs/Unbundled.lean 五条属性示例的单行 lemma，行尾包含短证明项。本审查没有读取该 Mathlib 文件、这些短证明项或作者由此形成的推理；只将这条披露留作最终隔离/读取边界记录，未把它作为 S5 数学输入或本审查证据。

Source 19–21 的“未运行 Lean / pending”注释是原作者阶段性元数据；本 Phase A 不以该注释或父通知的运行状态认定任何机械门。没有改写它或任何目标文件。

## 6. 结论和待授权事项

Phase A 结论 **CORRECT**：完整匿名证明在锁定的实际 S4 和 CP 输出之下闭合冻结范围；最终 Source 的全部静态推理忠实实现该范围，公开定义/头没有改变，未发现需要立即停止的真实条件差异。

尚未完成且本阶段不得执行：服务器目标检查、真实精化后 61 个公共项类型/定义核验、依赖哈希与转移完整性、公理闭包/覆盖审计及相应机器收据复核。标准 shift 属性涉及的实际类型也属于下一阶段。此报告不认证上游证明实现，不签发 S5/root CLOSED，不增加 rawleaf。

只在自己的 `drafts/oq4/rademacher-s5-independent-bounded-v1/` 写入审查与审计产物；没有修改目标 Source、冻结输入、作者文件、library、缓存、公共记录或 Git。完成后 STOP，等待 Phase B 明确授权。
