# Unit 219 最终独立审查 004：最终 public2 与同对象机器证据补充

结论为 **CORRECT_FORMALLY_QUALIFIED**。资格绑定最终源码 `c0b43c654b54d7b556c9a3e312fc96411fe8d65c16df8cda5a7ac4b3e02f002b`（188078 字节、3230 LF），以及原始成功对象 `3c9135de70cb9fb82425e0c0c019c3b0177c58844a386a6d660bdbf3232f853a`（7702760 字节）。资格只覆盖 unit 219 的固定区间 `[1/2,16]` 比较及本文件五个冻结公开接口各自明示的范围。**unit 220 未关闭，C2/C12 与 fullRootOD 仍 OPEN。**

最终 source-to-statement、完整证明、实际类型、透明定义值、所有权、公理和同对象机器证据之间没有未覆盖项，也没有发现关键数学或接口缺口。本补充与旧封存的完整 source 审查共同构成最终审查；旧报告的 pending-machine 结论保持其历史含义，不修改旧报告来制造新证据。

## 独立性、授权与本次实际工作

审查者为 `/root/bounded_centered_fixed_formal_review004`，与作者 `/root/bounded_centered_fixed_formal_author003` 分离。父 C12 owner 为 `01a174b9-5b2e-7611-ba13-02580d678eb3`。本角色已读 AGENTS.md、math-theorem skill 及其 proof-review/Lean 工作流材料；未启用 math-ultra，未创建子代理。此次恢复 activation 的 SHA256 为 `2af3591719f937c2f32c281741a27f3beac50688561c94eede892099e9cdc3a4`。实际运行 ACK 已写入，activation 绑定的 21 个输入在 ACK 和最终核对时均逐个通过 SHA256、字节数检查。

此次唯一写入目录为本 `machine-supplement001/`。没有修改证明源码、旧封存审查、220、其他 owner 或共享实现；没有执行 Lean、AX、server、network、upload、Git/API，也没有发 sidebar 跨聊消息。所有机器结论来自父提供、精确绑定的既有服务器回执；审查者不将读取回执冒充自己重新执行或观察了服务器进程。

配置为 `gpt-6.1-sol/xhigh`。actualBackend、actualModel、actualEffort 无可观测遥测，分别记录为 null；usage 的 input、cachedInput、output、reasoningSubset 均为 null。配置名称不作为实际模型遥测或订阅消耗证据。

## 精确复用与唯一改变的完整证明

旧 complete-source 审查覆盖源码 `664248ff27985283f74074a24e7359b9eaf217c9b8f6026994f532c1c69071bb` 的全部 16 个完整证明、5 个透明私有定义、局部实例及 7 个 import。其报告 SHA256 为 `8461d887b3df7e4e0011d16b441973f81fd31b871a7390e2938eeef190a1d41e`，父接纳 SHA256 为 `cc842c8e1812a82fb202e5d79d84c4ae93563de20a882cc08b35400c35b88bef`，旧全零 RELEASE 为 `9d6b3324b1613922fb92b65b373d939e26da05bb1350d7da691e36e02472d9b9`。旧审查不是机器合格证据；本次补齐的机器证据绑定的是最终 c0b43c65 版本。

独立逐块字节比较见 PROOF-REUSE-CHECK.json：全部 16 个头与旧已审 source 逐字节相同，其他 15 个完整 proof body 逐字节相同，整个 preamble、5 个定义、局部实例与 7 个 import 逐字节相同。唯一改变是 `iid_actual_all_level_h0_terminal_budget` 的 body。其新完整 body SHA256 为 `3a3c49a035195874c79e6ef751d15616678ad8fa8ee02eb9c9818778a8d257b8`。因此另外 15 个证明精确复用原 complete review，未重复审查或执行已接受旧模块。

我实际完整重读了最终 public2 的整个声明和证明，源码 1553–2038 行，而非只读 55 字节补丁。改变仅将积分被积函数非正证明中的点值零函数展开，并显式标注实数零：先 `dsimp only [Pi.zero_apply]`，再分支使用 `hFs b` 或 `(le_rfl : (0 : ℝ) ≤ 0)`。它正确处理函数值与实数零的表示，不改变假设、结论、所取随机对象或积分不等式。

完整 public2 的数学链仍正确。它使用真实 `h0Future`、真实严格能量下降 cutoff 和真实终端 sourceAlive 指示量。identity 与 reveal 两侧都先有可测性、真实 L1、逐点 `[0,1]` 范围，积分的有限性不依赖 Bochner 默认值。大 H 分支的粗界与小 H 分支各自成立；后者的反向闭命中 NH、强制正值 N、有限选时分解和 exceptional 事件都保留原边界。

选定 suffix 的 transport 保留同一完整 suffix。局部 `hStopped (k) (hk : k = rt+t-t)` 将函数 F、其可测性、全局界及 section 积分条件一起放进依赖族，再经 `subst k` 得到精确维数；调用 `hStopped rt (by omega)` 不会丢失 selectedSuffix、路径长度或 section 对应关系。实际 `Phi` 是 future 减 `min(cost,1)`，所以在整个定义域逐点位于 `[-1,1]`；它不是把原始无界 U/J² 函数硬称为 boundedPhi。原始 U、J² 的 rawL1 由各自真实矩生产者提供，积分代数与 domination 所需 L1 均在使用前建立。

固定 suffix corridor 支付 `Ccorr/(r+t) * (8 Jmax² + 128 U + 2H)`。完整选时预算给出 `E W ≤ 1794 H`，exceptional 支付 `12H/n`，故终端总支付为 `(1794 Ccorr+12)H/n`。`H/n=4 delta²` 得到 `(7176 Ccorr+48)delta² ≤ (7200 Ccorr+100)delta²`。`Ccorr` 与 `Cterm=7200 Ccorr+100` 在 rho、n、x、Brownian law 之前选择；常数不依赖所审样本或目标概率。最后 iid randomReorder 的完整 map 等式将路径、permutation、cutoff、future 与终端一起运输。没有自由核、期望 cutoff 或替代终端。

## 全部实际 TYPE/FULLVALUE 的完整阅读

`actual-types-values.txt` SHA256 为 `5ac31c7a16fe6fd1ead025fca580faa90df263691dfc71bc93801456968dabb2`，612478 字节、8040 行；索引 SHA256 为 `7c3e4cc463921b0c8aaa6ec827a0423598cbb215ad2a54eaeaed374aa2a8415e`。已按完整 declaration 的索引区间小批阅读全部 **145 个实际 TYPE** 和 **9 个 non-theorem FULLVALUE**。较大的单项单独读取；原始数学 TYPE/VALUE 阅读没有截断或省略。READING-STATE.json 保存真实逐项 cursor；COVERAGE.json 对每项记录 owner、kind、行界、整个 entry hash、TYPE hash、VALUE hash（如有）、完整阅读标志及递归公理。

最终确定性核对同时比较了索引、原始 TARGET_DECL header、owned-audit、逐项阅读记录四者：145 个名字、顺序、kind、owner 和 AX 清单全部一致，无重名，无遗漏；从第 1 行至第 8040 行连续覆盖，无剩余未读 entry 或 value。索引四种截断标记的实际计数均为零。此检查只是本地证据一致性检查，不执行 Lean。

实际模块所有常量为 **145 = 136 theorem + 9 definition**，五个预定 public theorem 均在实际清单中。它与源码的 16 个 theorem、5 个 private def、1 个局部实例计数分开记录：额外常量包含编译产生的 proof/simp 辅助定理、方程定理与 matcher/splitter。不能用源码行首计数替代所有权清单。

16 个源码定理对应的实际 TYPE 均完整读过：

| 源码定理 | 实际 TYPE 序号 | 证明证据 |
| --- | ---: | --- |
| abcf_bounded_own_budget_identities | 70 | 旧完整 proof 精确复用 |
| abcf_suffix_grid_payment | 124 | 旧完整 proof 精确复用 |
| abcf_two_sign_gaussian_all_level_budget | 103 | 旧完整 proof 精确复用 |
| iid_actual_all_level_retained_negative_budget | 75 | 旧完整 proof 精确复用 |
| abcf_future_measurable_integrable | 105 | 旧完整 proof 与 amended P4 精确复用 |
| abcf_masked_future_eq_Icc | 106 | 旧完整 proof 精确复用 |
| abcf_append_future_corridor | 144 | 旧完整 proof 精确复用 |
| abcf_h0_future_reorder | 66 | 旧完整 proof 精确复用 |
| abcf_fixed_suffix_terminal_all_level | 51 | 旧完整 proof 精确复用 |
| iid_actual_all_level_h0_terminal_budget | 43 | 最终整个 proof 本次完整重读 |
| abcf_halfline_initial_all_positive | 67 | 旧完整 proof 精确复用 |
| abcf_legal_c1_fixed_segment | 39 | 旧完整 proof 精确复用 |
| abcf_fixed_absolute_comparison | 36 | 旧完整 proof 精确复用 |
| iid_actual_bounded_centered_fixed_comparison | 30 | 旧完整 proof 精确复用 |
| iid_actual_bounded_own_budget_identities | 37 | 旧完整 public forwarding proof 精确复用 |
| iid_actual_halfline_initial_all_positive | 132 | 旧完整 public forwarding proof 精确复用 |

其余 120 个实际 theorem 的完整类型均为相应生成的逻辑、序、算术、有限指标、定义方程、matcher 方程或 proof 局部推论。包括较大的 NH 展开类型、带 k/hk 的维数界及 finite-grid partition，全量阅读保留了它们的真实 binder 和前提，没有仅凭名字判断。未发现新增隐藏数学假设、其他 owner 的覆盖替代、未计入的非定理 kind 或改变结论的生成声明。

九个 non-theorem 的 TYPE 与整个 FULLVALUE 分别完整覆盖如下：

| 序号 | 定义 | 完整值的核对 |
| ---: | --- | --- |
| 1 | abcf_fixed_absolute_comparison.match_1_1 | 三种 MonitoredDomain 的 motive/cases 分支，真实生成 matcher |
| 20 | abcf_h0Future | 对同一 p.path、p.perm 的真实 energyCutoff 调用 futureAt |
| 23 | labelPermMeasurableSpace | 有限 permutation 空间的 `Top.top`，与 reveal 接口的可测空间相容 |
| 27 | abcf_suffixCubic | 原正能量/H guard、真实 first mark、T√T 分母及 D³ |
| 84 | abcf_fixed_absolute_comparison.match_1_1.splitter | 上述 matcher 本身，没有新数学内容 |
| 92 | abcf_jointBill | 同一真实 physical bill 的有限 rank 和 |
| 93 | abcf_suffixLate | 同一 guard/first mark、D^k 与真正自然数 n−t 分母 |
| 130 | abcf_futureAt | 有限 range(n+1) 的 masked sup；真实 sourceValue 减真实 terminal sourceAlive 指示量 |
| 140 | Shao.Probability.te_interior_signs.match_1.splitter | 当前模块拥有的生成别名，完整值指向已接受 SourceTerminalEnvelope 的原 matcher |

最后一项的显示名字包含 `Shao.Probability`，但实际 owner 是本目标模块；本审查照实际 owner 纳入了它，没有因命名空间过滤而漏审。所有 matcher/splitter 的完整值与类型一致，无新 axiom。

## 实际声明、物理对象和范围核对

全部 16 个实际源码 theorem TYPE 的量词、let、概率测度、可测空间、维数及数学前提与冻结头相符。P4 的 4 处显式维数消歧在实际 TYPE 中确实固定到同一 n；没有残留自由维数或通过额外假设回避 transport。两项新公开导出分别保留私有已证命题的全部范围和前提。所有五项 public 的实际类型已完整阅读，而非只验证源文本名字或前几个 binder。

固定比较仍要求同一个 centered unit-variance rho、真实 `beta=E|Z|³`、`delta=beta/sqrt(n)`、`1/2≤x≤16`、支撑 `sqrt(n)/(100x)` 与 `delta*x³≤epsilonF`。epsilonF、CF、CA 是在 law、n、x 与 Brownian probability space 之前选定的正普适常数。相对误差的固定 16 端点依靠 `Psi(16)>0`；该证明不推出 x>16 或任意 M 的组装。

own-budget 导出给出真实自身 law 的 R0/Rx 与全 prefix 预算，范围 x≥1/2；不把预算换成任意下界或目标概率。C1 的合法输入由同一真实 `Rx=delta(1+x)^3` 推出：x≥1/2 时 `1+x≤3x`，故 `Rx≤27 delta*x³≤rhoStar`。`epsilonF=min(rhoStar/27,1/8)` 同时推出 `delta≤1`，实际调用的是原 C1 第二预算域。没有遗漏原 C1 的 domain disjunction、假定 symmetry 或套用错误 law。

retained-negative 公开预算仍允许满足冻结 section 可测性及 nu≤实际 cutoff 的任意 nu；没有偷偷增添 stopping 或 independence 前提。它支付真实 retained absolute bill 与 interval 自身的 negative overshoot。h0-terminal 预算对 x≥1/2 给出同一真实 future 的 L1、可测性、范围和 Cterm delta² 支付。半直线初始公开导出保留所有 x>0、较弱 bound≤sqrt(n)、真实初始 V0 L1，以及两个符号各自 Brownian 弱命中概率恒等式；其全正范围不是由固定16比较外推。

actual boundedPhi、rawL1 与 stopped-suffix 依赖族已在新整个 public2 和实际 TYPE 中交叉核对。原 complete review 中的其余物理接口与 producer 消费核对按 exact hash 复用：原 source fidelity、216/217/218 数学、真实 marked/averaged 权重、闭 CDF、Gaussian layer cake、rank Fubini、真实 source kernel/strip/moment/C1/Brownian 接口没有变化。本次未重新审计已接受旧证明或重复旧机器检查。

严格/闭边界均保留：反向 NH 是闭命中，真实 cutoff 是正向严格下降；prefix survival 与 sourceAlive 为严格内域，final-energy strip 为闭域，最终比较为弱乘法命中。Q=0、U=0、t=0、odd/even midpoint 和 rank-zero witness 的原分支仍在；没有借无原子假设删掉等号事件或全零样本。双壁事件是两个可异时的存在命中，Brownian 端同样是两个独立存在量词；没有改成同一时刻双壁命中。全路径 Brownian 的 null-measurability 证据依赖同时对全部时间成立的 a.e. 代表，原审查的该项证据与未变 proof 一起保留。

## 同一最终源码、同一原对象的内核与递归公理证据

kernel006-start/result 的 source SHA 在前后均为 c0b43c65，native 自然 RC0，errorHeaderCount=0，输出原对象为 3c9135de/7702760B。audit001-start/result 仍绑定同一源码；audit 自然 RC0、零错误，所读 original O 的 SHA256 与 native 输出相同。类型索引与本地阅读状态也绑定相同 source/O。未将旧 RC1 候选、缺失对象、重建对象或另一源码的 AX 结果移作本版证据。

owned-audit.json SHA256 为 `9f0aeac073f5ec1c61f45b6c359af4cdcd59bed078991c9af44334da56d8b1a3`。既有审计方法遍历 environment constants，并按 `env.getModuleIdxFor?` 的实际模块 owner 选择全部目标常量，包含 private/generated。对每一项调用 `Lean.collectAxioms`，所得是递归依赖公理，而非仅扫描当前表达式中的直接 axiom 名。实际 145 项全部 PASS；每项公理集合均为 `{propext, Classical.choice, Quot.sound}` 的子集。九项 non-theorem 全为 definition，没有未提供完整值的 opaque/other kind。五项预定 public 均为实际 theorem。作为方法核对，完整读取了已建立的 OwnedAudit-public5.lean；该本地文件作为 supporting input 单独封存，不冒称它是本次重新执行的审计。

九份服务器回执及 transcript/index 均有精确输入绑定。native 的 log SHA 为 `d43289d8a9c3154a288e45faed6e7b8092fdd942057c9905a280bb4047213520`，53524B；audit log SHA 为 `54963f5da7341bef2f3a4df008283e855895c86e9993e45f0f7f87b4cc46b489`，612693B。这些日志哈希是服务器回执记录的 provenance；本地完整阅读的是提取的 612478B TYPE/VALUE transcript 与所有必要的 receipt 元数据，没有声称本地持有或全文检查未提供的 raw log/二进制 O。

两项检查的 phase SHA 均为 `f9f0f3d77821f54b15d5250f25325468033b81d154f39589cf86473ffaa4449e`，与 C12_OQ56_23 相符。命令使用 CPU44–47、c12-heavy.lock、-M8192 -j4。实际 thread records 显示 native 的 5 个 userCompute 与 audit 的 4 个 userCompute 均精确限定44–47。各自一个 `iou-sqp-*` kernelSQhelper 是同一 Tgid 的零 ticks dormant 内核 I/O helper，单独记录；不能把它的0–255 affinity误报为实际用户计算越界。aggregate memory 峰值分别163.27295684814453、163.01662063598633 GiB，低于180 GiB watchdog和200 GiB hard；RSS峰值分别847648、847592 KiB。审查者没有再次请求服务器检查。

## 最终资格与释放

最终资格同时具备：受影响的完整 proof 独立审查、未变15个 proof 的 exact-body 复用、全部 frozen heads/values 与实际 TYPE 一致性、全部实际 owner inventory、全部145TYPE/9FULLVALUE阅读、最终源码内核成功、原同一对象上的所有 owner 递归 AX 白名单通过。formalQualified=true 仅绑定上列最终 source/O 及其明确 scope。

本工作是 source mechanism 的实现与验证，保留原 source、accepted producers 与外部结果的归属；没有新增 novelty/firstness 认证。原 C1 immutablev85 的已接受状态不由本报告更改。本报告不关闭 unit220、任意固定 M 或增长区间 assembly、full positive precap overshoot、fullRootOD、C2/C12，也不恢复 separately PAUSED_BY_USER 的 OQ3。

本次本地元数据处理中出现过短函数名解析成 PowerShell alias 和错误 JSON 字段名的行政性失败，均已更正；未触及 source/Lean/server。若干行政性组合展示输出曾到输出上限，所需字段以定向解析重新读取；145TYPE/9VALUE 的完整声明阅读未截断，覆盖由逐 entry hash 与连续行界再次核对。

最终 CHECKPOINT、verdict、SOURCE/INPUT/PAYLOAD seal 和全零 RELEASE 交父读取。释放时本角色 source/proof/review/execution writer、children、heavy、inflight、server/network/upload/GitAPI、pending external 均为0，没有后台任务或未完成请求。本次完成后的下一动作是父对精确最终审查包的 intake/publication；这不构成 reviewer 在 turn 结束后继续执行的声明。
