# SourceOriginalHalflineComparison / PR327 完整独立终审

STATUS: CORRECT

JUSTIFICATION: 本精确源码证明了冻结的原 AE 可测、中心化 iid、有限且正二阶矩的 signed halfline compact comparison。全部 1217 行新源码及证明、全部 19 个实际所有者的完整 TYPE、19 个头内 literal let 与完整 head-local `letI := ⊤`、零非定理 VALUE 库存、实际模块所有权与递归公理凭据均已独立审查。未发现关键数学缺口。此结论仅覆盖以下 exact source 和陈述，不扩大为原 C1 增长窗口相对误差、C12 根或其他开放根的完成。

## 精确对象、独立性与执行边界

- PR: https://github.com/randomcat4/shao-lean/pull/327
- Head: `90adb4373112fa4dd46e3f6750c2dd51d2f3b8bd`。
- 新源: `drafts/c1-original-halfline-comparison-production/SourceOriginalHalflineComparison.lean`，1217 行，68689 B，SHA256 `ac13f6b211910d923aea74bcbb1967d533c061d103d089bb4ca8fd07d6a46cfb`。
- 服务器原对象: `/root/rivermind-data/shao-lean-20261021/outputs/common-original-halfline-comparison-v82/producer13.olean`，2190520 B，SHA256 `fbb57b7dac25a7ad6e71df1b29bb122ab990c2438e81ff798a6eb3ab808b37af`。
- 审查者: 全新非作者上下文 `/root/original_halfline_comparison_final_review`；作者 `/root/true_energy_strip_author`。审查者未编写或修订被审源、未合并，写权只在本 review 目录。
- 调度配置为 `gpt-6.1-sol / xhigh`；独立的实际模型/effort/token 遥测没有暴露，均按未测量记录；input、cached_input、output、reasoning_subset 为 null，无订阅百分比估算。
- 先读当前 AGENTS.md、math-theorem 与其验证协议，落盘实际 ACK；未启用 math-ultra、子 agent、sidebar、Goal 或 automation。全部远端操作是原文件/hash/Git/PR 的只读检查；本轮零新 Lean/AX、零旧 producer 重编、零成功检查重放。

作者 RELEASE SHA256 `0eaa67d9b0dcac2568807c5fe58b68dd3d4ea577c3e989e1a545781c5dd04b07` 明确释放源码/目标执行/生产元数据写权、零在途；其绑定的 final-receipt SHA256 `d7ea45073663dea435e99c93d2fb35b223e11c13e121ae4c1c328d144d991d9d` 与实际读取一致。审查期间没有恢复作者写权。

## 冻结、上下文和时间顺序

初始冻结 SHA256 `ececb02a2e6ce3ce71d8b6b25f56d3d884a28f9f5a93f447f7bc7e3b1908269b`，activation SHA256 `3880342d93837e4356f77fec77905c6abd9cc0bfdefb52774bcaebe0fc9583d3`。context-v2 冻结 SHA256 `52695c4d560c11e80ab636e7ebada5469bc7a5ffa52687a615527e11651301bd`，amendment01 SHA256 `54801794e5f0607119245db7cece144b155ef360deb1b7a868cde977d91d7470`。

独立字节比较确认：原冻结与 v2 冻结从 theorem 开始至陈述末端均等于最终实际源；提取的 4654 B 陈述 SHA256 是 `31b7cc2044f178acfaba76b493550481fb341fb102d7e9f8b9d5790c8565134f`。v2 的完整 theorem 前上下文与最终源相同。19 个 let 与 `letI : MeasurableSpace (LabelPerm n) := ⊤` 均保留。源是 UTF-8、无 BOM、纯 LF，没有格式修复或重冻结。

真实 ambient delta 恰为新增 `Shao.C2.InitialCompletionError` import、`Elab.async false`、`maxHeartbeats 2000000` 和 `open SourceActualLocalProfileBudget SourceSeparatedOvershoot`。新增旧模块的源 SHA256 `d2cf1fc8f6042f4ba2dc0f6ec52140a48da7c6aab2cfae59fd3dfafc0f1e7ec1`；其完整 `zero_energy_removal` 公共头另行读完。实际公共 TYPE 将 `sourceValue`、`eventCompletionKernel`、`LabelPerm`、`MonitoredDomain` 等均解析到预期原 namespace，标签测度结构实际展开为 top；没有出现新增假设或额外抽象实例参数。两个 option 不改变数学前提。

时间顺序为 activation 18:07:50 UTC → context-only amendment 18:46:04 UTC → source13 原快照 18:50:38 UTC → producer13 18:50:54 UTC → 原 audit/check13 完成约18:51 UTC → 导出/最终 receipt 18:52 UTC → commit 18:53:10 UTC → publication 18:53:58 UTC → 作者零在途观察/释放 18:54–18:55 UTC。没有以较后冻结替代成功 gate 的事实。文件 mtime 只作交叉佐证，主要信用仍为精确源绑定的记录。

一次本审查自用的初始文本提取误以为 declaration-only 冻结含 `:= by`，导致空提取比较为 false；已按真实的 namespace-end 分隔重新提取，与作者声明无关。修正后两份冻结均逐字相同，记在 freeze-and-source-validation.json，未修改任何外部工件。

## 原文陈述忠实性

完整读取只读原稿 `C:/game/shao/current/c12/main.tex` 的148–173、199–207、288–310、900–1037、1077–1148，以及 supplement.tex 的3921–4030、4535–4665相关完整段落。两份原稿哈希与 source-inputs 绑定一致。

原始对象是 n≥1、均值0、0<EX²<∞ 的 iid 实随机变量。形式头只要求各 X_i 对 mu AE 可测，独立且与同一个 rho 同分布；没有强制处处可测、额外矩、对称性、无原子或有界支持。population 逐点是原样本，Q=∑X_i²、S_n=∑X_i、W 在 Q>0 时为 S_n/√Q、Q=0 时取0。`upperMax (s • population) hn` 的定义和完整公共头确认它恰取正前缀1,…,n，s=±1。

R 是 `n ∫ z² min(|z|,1)` 对 `rho.map (z ↦ z/√(nσ²))` 的真实积分；不是任意 error 输入。结论的 x 范围正是0≤x≤1，v 是所有实数，端点条件始终 W≤v 与同一个 B_1≤v，即使 s=-1 也不翻转端点。严格生存和弱乘法 crossing 互为精确补集，保留 Q=0 和墙上等号。

原 main 的完整 compact comparison 使用绝对最大值；本项明确只独立装配单墙结论，不从双侧比较反推单侧。原文 main 981–1037 及 supplement 4535–4665 中可用于单墙的实际过冲/余项/终端预算被准确消费。x=0 时单侧正前缀严格生存可能非空；例如 n=1 的中心化 ±1 律有概率1/2满足 X_1<0。最终证明没有套用原双侧 proof 中“严格生存为空”的端点断言。

原稿 Pinelis2011 截断标量界及其 Shao 归属、JingShaoWang2003 相对尾输入、已合格反射模块的归属保留。此单元复用合格的 PR312/313 引擎，不新增外部结果公理、不作新颖性声明，也不重审历史 p54 修复。

## 全部新证明的逐段数学审查

### 1. 常数、原律与独立均匀标签（行102–188）

先取得统一 CB、CE、CG、Cs、C0，再选择 C=1+2CB+2CE+CG+3Cs+16+C0，随后才量化 Brownian law、原 law、n、s、x、v。正性由各原常数正性支付，统一性没有量词换序。

iIndepFun 与各实际 marginal map 得 population 的 canonical product law；AE population 与恒等标签的 product map 得 pairedPopulation 的积律。canonical Borel 坐标处处可测，故可合法调用既有 iid random-permutation map 定理；再通过 paired map 得同一独立标签 seed 下 shuffled 的 HasLaw。这三个是真实结论，没有任意 pushforward/law oracle 前提。逐点重排只保留 energy、完整末和及 normalized endpoint；未声称最大值逐点排列不变。

### 2. 真实反射、初值和所有 guards（行189–367）

raw geometry 支付0<R≤1与 h=4nσ²R²>0。真实 Brownian hB 分别支付 upper/lower reflection，再给实际 kernel、导数的可测性和 KernelBounds 4；既有 KernelBounds 完整结构已读，没有 interval regularity/small-Taylor 输入。

endpoint 外侧时严格 bridge 事件由 t=1 为空。x=0 的 sourceAlive 因含 rank0 而死亡，实际单位桥核也因 t=0 严格墙条件为空。x>0、Q>0 时，逐个 seed 用 bridgePath 的字面表达式做 √Q 缩放，处理末点内/外两分支，得到 source rank0=1_{Q>0}K(W)。Q≤0 分支借 energy≥0 得 Q=0，保持原 guard。逐 seed 的 V0 实际可积由 canonical 有界可测 V 与原 population law 传回。

### 3. 同一 Brownian tuple、事件和 Fubini（行368–493）

tuple=(bridgeNoise B, B1) 的实际 HasLaw 是 Q×N(0,1)。在 BridgeNoise×ℝ 上定义同一个 signed 全路径严格事件 E；连续 C(BridgeTime,ℝ) 映射与 compact BridgeTime 使该事件 Borel。已资格的 AE bridgeNoise 等式同时对所有 t 给出原 Brownian AB 与 tuple⁻¹E 的 AE 相等，未把 B0=0 或连续性提升为逐点事实。

有界指标的真实可积性和 product Fubini 给 PB(AB)=∫K dγ。对 E∩{u≤v} 同样处理，并逐 u 保留闭条件，得联合概率=∫1_{u≤v}K(u)dγ。AB、其掩码只需相应 AE/NullMeasurable 性；没有假设 PB 完备，没有把非可积 Bochner 积分默认值当概率。

### 4. 闭 CDF、lower mask 和 Q0（行494–648）

PR312 的全实闭 CDF 对 normalizedEndpoint 的真实 pushforward 给 |F_endpoint(v)-Φ(v)|≤CsR，尺度 √(nσ²)=√σ²√n 已核。K 在上墙为 antitone，在下墙为 monotone，范围[0,1]由实际事件核给出。既有 antitone 单位期望转移给一项 CsR；monotone 情形用1−f转化，积分均先证明可积。

上墙的闭截断仍 antitone；下墙用 K−H，其中 H(u)=1_{v<u}K(u) 是 monotone 单位函数，故误差≤2CsR。严格互补 `v<u` 保留原 u=v 原子，没有误作连续端点。真实 Q0 概率由 PR299 ≤16R，`zero_energy_removal` 只剥离该实际事件，得到边际/联合初值差≤(2Cs+16)R。它不是独立性或目标概率 oracle。

### 5. 原正前缀、同 κ 和 terminal E 运输（行649–770）

Interior J 与 s*y<w 精确对应。正 x 时 sourceAlive 到 n 等于重排含0最大值生存，再证明其等价于正前缀最大值生存；Q=0 单独处理。反射公式给 K(u)=1_{s*u<x}(1-exp(-2x(x-s*u)))，下墙的符号与原端点保持一致。

remainingEnergy 在 `(reorder a pi, id)` 与 `(a,pi)` 逐点相同，所以同一个闭能量 cutoff κ、sourceAlive、sourceValue 都协变。用真实 randomReorder HasLaw 将 identity-order 的 terminal discrepancy 可积性与 CE R² 整体运输到 reveal law。没有自然 iid 过滤下的停止时刻断言，也没有另造独立 κ。

### 6. 单墙 O≥0 与 B/E/G transfer（行771–1037）

所有未选、非小能量、死状态分支均为0。上墙穿越时 p=w−y∈(0,b]，下墙穿越时 b≤p=−w−y<0；由 b²≤T/2、末点内侧、T>0 推出实际因子 c=1−(b+p)(z−y)/T≥0。实际 G 上墙≤0、下墙≥0，因此两侧 `-(b-p)*c*G` 均非负。墙上等号 b=p 给0，除法均在 T>0 分支，没有边界漏项。

真实 B 给 ∫Σ|L|≤CBR；真实 E 给 ∫|Vκ−A_f|≤CER²；真实 signed analytic host G 经实际 K 识别给 |EA_f−EV0|≤CGR。所有 L/O/terminal/source 项的可积性来自完整已资格公共头，并在使用积分加减前落实。

先取 m=1 的实际 telescope：EVκ−EV0=EΣL+EΣO，故 EΣO≤CBR+CER²+CGR。随后对任意可测 |m|≤1 的同一样本函数取 telescope；O≥0 支付 |E mΣO|≤EΣO，余下终端和 L 分别按绝对预算支付，得到2CBR+2CER²+CGR。由0≤R≤1得 R²≤R。此处没有把欲证的 masked comparison 作为预算前提，没有未经证明的任意 mask 因子化。

### 7. 原空间回传、x=0 和最终补集（行1038–1217）

canonical Borel AC 经原 AE population HasLaw 传回 A 和其真实 closed-W joint。masked final integral 只在 m=1 或 m=1_{W≤v} 时使用重排 invariance；后者由真实末和/能量保持支付。所得严格生存误差为 D R，D=1+2CB+2CE+CG+2Cs+16+C0。

x=0 另用 PR315 的原正前缀严格零墙预算 ≤C0R；Brownian strict 事件只有在 B0=0 的 AE 集上为空。其 closed-endpoint 子事件按包含关系支付。不会将 source rank0 空事件与原正前缀事件混同。n=1、Q0、v<0/等于0/任意实数都在实际量词和分支内。

弱 crossing 是严格生存的点态补集，先获得 NullMeasurable 后再作 measureReal_compl。联合弱 crossing 是端点事件减严格生存联合事件；另付真实 endpoint CDF 的 CsR。因此最终 C=D+Cs 正好同时覆盖四个误差。负墙不反转端点、严格/弱边界无原子删除，零能量样本属于弱 crossing。末端证明至 namespace end 全部已读。

## 全部实际所有者、完整 TYPE/VALUE 与公理

成功原对象的 module-owner audit 用 `env.getModuleIdxFor?` 与 `env.header.moduleNames` 判所有权，遍历 env.constants；不是按名字前缀猜。完整 audit driver 已读，`Lean.collectAxioms` 递归检查每一个实际所有者，遇到白名单外公理即失败。

实际19个 = 1个public theorem + 18个generated simp theorem；源码private helper、global definition、global instance、实际非定理值均为0。完整 TYPE 文件94549 B，SHA256 `9d88f340b798915910f3e0d035c38b38311c08a0d558040260bcddaaa1b4e33f` 已以1–350、351–700、701–1050、1051–1128的连续显示逐字读完。独立解析全部19个 TYPE 并重算各自 SHA，均等于 actual-owner-index；报告 JSON 保存每个完整 TYPE 字符串和哈希。

public TYPE 保持所有原参数、所有量词、所有 head lets 的实际值、top 标签可测结构、三个 HasLaw、逐点状态、四种概率差及全部 integrability 结论。没有 hImage/hRegular/hSmall、目标 budget、任意 pushforward、反射或可积性 oracle 输入。

generated 清单精确为 `_simp_1,_simp_2,_simp_3,_simp_4,_simp_5,_simp_6,_simp_7,_simp_8,_simp_9,_simp_10,_simp_11,_simp_13,_simp_14,_simp_15,_simp_17,_simp_18,_simp_19,_simp_21`。其完整类型分别是自反严格序为假、2/3/4非零、非零乘积/幂非零、自然数后继非零、交集/空集/闭下区间/自反弱序/积集/全集/补集/非严格序互补/否定全称/集合差的逻辑正规化。全是 theorem；不是隐藏定义或新数学前提。未伪造 generated 项的具体 tactic 位置，只有 unique proof 内生成这一实际 provenance。

`all-owned-non-theorem-values.txt` 完整50 B确认为无项，SHA256 `dfb1e4e7e304217a2c0dfdc04da14c84b6102d584ff910bc1789d975bcc82d15`。头内 let/letI 并非全局 non-theorem VALUE，但其完整源码值及 public actual TYPE 内的展开已单独覆盖。theorem 的巨大 machine proof value 未要求/未打印。

所有19个的递归公理集合仅为 propext，或 propext/Classical.choice/Quot.sound；public 与 `_simp_7,_simp_19` 为后三者，其余为 propext。未出现 sorry/admit/new axiom/unsafe/native_decide；独立源码扫描也为空。没有把“编译成功”当作原文忠实性的替代。

## 原凭据、依赖信用与限制

check13 kernel_rc=0、audit_rc=0，同次原调用；本轮重新读取服务器原字节/hash，source13、原对象、原check13/log、原audit13/log、完整类型导出、实际owner index 均匹配已绑定值。原 audit13.log SHA256 `e193d8184700dab98ab19b32aa0248a8af79d15d4d6935c011ec91941609c933`；其19段完整 TYPE 与本地类型导出逐字匹配，不是摘要代替。原内核日志 SHA256 `9408b66c1958121c1a76c0ff4c0b0108e7acaa7e2db8cbf0dff99d9b9b88bd3e`，未发现 `error:` 或 `error(...)`；退出码以原记录为准。

工具链原文件为 leanprover/lean4:v4.36.0-rc1，mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`，目标 import link 仍解析到 producer13 原对象。commit blob、工作树源与 source13 SHA相同；只读 GitHub PR 查询确认 exact head 和唯一新增1217行源，PR OPEN且未合并。

失败01–12各自原source/log/receipt均再次只读验证存在且哈希一致，均kernel_rc=1、object_or_axiom_credit=false；check12 LOCK_BUSY probe 保留且不视为一次 Lean 成功。作者旧“先前haves全通过”叙述已撤回，本审查没有使用它。成功信用只来自13，没有回放失败或旧producer。

完整937行必要公共接口/定义值/ambient context已逐字读完，并补读 KernelBounds 的全部结构字段和新增旧import的 zero_energy_removal 完整头。source-inputs 绑定23份依赖源、11份上游资格、baseline view及两份原文的38项哈希均通过；作者释放及原始证据绑定的77项（含重复引用）也通过。已资格旧证明只消费其完整接口与必要值，复用现有非作者完整证明/类型/值/公理信用，未重读旧证明正文或重跑核。

非阻塞文档观察：精确源码行1的“Mathematical candidate only: no production source or Lean/AX execution”是从候选保留的旧注释，与生产/检查事实不符；不影响陈述或内核证明。本次不更改该注释，以保留已核源码字节。没有要求因该注释重审旧模块或重跑13。

最终限制：CORRECT 只为这个 exact signed halfline compact theorem；不认证完整 C1 growing relative/full I_n，不认证 C2 actual killed=image，不关闭 OQ56 根。OQ3 PAUSED_BY_USER，OQ4 只有既有独立有限范围 COMPLETE；其余原根状态保持。Root 对本报告全文消费一次后，可复用此 exact-source 完整独立审查及原服务器凭据；合并/根资格仍由 Root 决定。
