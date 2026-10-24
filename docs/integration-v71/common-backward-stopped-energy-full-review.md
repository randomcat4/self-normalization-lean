STATUS: CORRECT

独立完整终审确认，精确版本 `Shao.Probability.SourceBackwardStoppedEnergy` 的三个公开冻结头、22 个显式私有证明和全部源内局部值正确；未发现关键数学缺口、语义收窄或凭据错配。此结论只覆盖真实有限 iid 的反向停止预算，不代表终端包络、completion、平方条带、joint comparison 或 C2 根闭合。

审查者 `/root/common_backward_stopped_energy_full_review`，全新 `gpt-6.1-sol / xhigh`，不同于作者 `/root/common_one_sided_root_actual_author`；使用 math-theorem，不用 math-ultra，不使用子代理。已读 AGENTS、SERVER、TEAM 当前规则与 streamlined-acceptance-current。作者在 04:13:42 UTC 封存并释放源写权及执行权，无在途命令。本审查只写本报告及 coverage JSON，没有更改生产源、冻结、旧凭据、library、缓存或原文；没有执行 Lean、lake、AX 审计、push、PR 或 merge。

精确源及原始机械凭据已只读核对：

- source-only commit `68b38b09bb7a660a6e8ea1af29110018d69eae0f`，tree `8f437e568443c79034ece4ec06c7fdc26296cc2d`，parent 为已接受 C1 commit `1b4cc5ecd960220062952310d7916709b2e01323`；本提交仅新增本模块。
- 本地全文、服务器当前源、提交 blob、首次成功 `whole028.lean` 均为 SHA256 `5476ba61888e6e4e7177960d5418e2f1dd92c15952faa74a30420f2c18a27f54`；68,701 字节、1399 行、UTF-8/LF、无 BOM/CR。
- 第一次完整三公开头成功 `whole028` 原生 rc0；原 `outputs/common-backward-stopped-energy/whole028.olean` SHA256 `f85c2d1f488c14b89414c6b2b0099d962e049f2e52516cb310bfef1491360306`。生产对象别名仍解析到这个原对象。原日志 SHA256 `8e95368842f705149ede63636aa9a20fff122ff24e56dcbf33005c28d57744ef`，仅保留 linter/弃用及已知 Mathlib 工作区提示，无 error。
- 唯一 actual-owner 审计原生 rc0；日志 SHA256 `547672629233d3c4843dfc5df61c3f35a577472fa4173f073211a3b9ad160370`，233,534 字节、3784 行；native JSON SHA256 `3f3486f162740fd1633bd3662eb79c4dc2be0bca29bac34f16c280a75006f1fd`；审计源 SHA256 `0e39c94ca5cc0d40582e65f9ccd8f47f77a185d555d87ef5a314df0d093ea714`。
- whole-kernel-receipt SHA256 `871fe5cf1e4ec803ef02f8f1e947bdd95db978857035bd458bf5a1479574cba5`；checkpoint SHA256 `97676fbb4350cdc8f273b4992c45179ce15a7379b93d1de2d050df43066c2c3b`。checkpoint 里的旧 partial/实施范围字段为历史快照，当前完整状态以 latest_attempt、whole_kernel 和 whole receipt 为准。
- 公开冻结文本 SHA256 `b4bec7706d32ce5c2dc07aabd7539de4f84b33a369941cc82f8b8f4adc9f1768`，原 proof-candidate SHA256 `89ea68a23cebf5478f5b683245d64535fcff48c35d07923a39f9177e87fadd41`。本审查再次机械核对全部 3 public + 22 private 完整字面头与各自事先冻结文件匹配。历史 v14 无界辅助头和准备但未装配的 v17 不在最终源，不被计作已检声明。

完整读取源第 1–1399 行，包括全部声明内 let、证明、局部 have 的推导以及 46 个 statement let、26 个 proof let、1 个匿名 DecidablePred letI 的完整多行值。逐声明完整覆盖如下；头/证明哈希及 73 个 let/letI 索引均存入 coverage。

| 声明 | 源行 | 审查要点 |
| --- | --- | --- |
| sourceBackward_clipped_square_mean | 26–94 | 从真实二阶矩推出 n,R,H 正；尾部 2R·z²≤F(z) 与 nEF=R 支付 clipped mean≥1/(2n)。 |
| bse_prefixSquares_mono | 96–105 | 非负平方的有限前缀单调性。 |
| bse_reverse_sum | 107–128 | Fin.revPerm 重排与互补有限指标拆分。 |
| bse_reverse_prefixSquares | 130–134 | 真实后缀平方和恒等式。 |
| bse_reverse_prefixSum | 136–141 | 真实后缀和恒等式。 |
| bse_capped_find_data | 143–189 | Nat.find 最小性；弱命中、严格失败和 cap，包括末端 L。 |
| bse_reverse_past_factor | 191–232 | 真实有限 pi 独立族、反转单射、past/current 独立与乘积积分。 |
| bse_bounded_predictable_wald | 234–290 | 实际过去可测 indicator 的有限和；同时先证计数及停止和可积。 |
| bse_capped_find_measurable | 292–342 | 用 k<NH↔k<L∧Q_k<H 给出全部 Ioi 原像。 |
| bse_prefix_step | 344–362 | 有限滤过索引的单步插入分解。 |
| bse_clipped_prefix_bound | 364–381 | 停止前能量<H，加最后一个 clipped increment≤H。 |
| sourceBackward_capped_stopping_energy_budget | 383–550 | 真实 cH/cN、NH/N/Wald、ENH≤4nH、EN≤7nH、失败≤12H、EU=EN/n。 |
| bse_forward_displacement_control | 552–578 | S_(n-N+l)-S_(n-N)=B_N-B_(N-l)，实际 J≤2K。 |
| bse_reverse_factor_of_dep | 580–617 | 由过去依赖性以零延拓构造真实有限过去函数，未假设 stop 独立。 |
| bse_stopped_second | 619–745 | diag 用平方 factorization；i<j 的真实过去 F=D_i·1_(j<T) 消去交叉项。 |
| bse_maximal_weights | 747–840 | A 的运行最大值递推；W=sign(M_(k+1))ΔA；有限平方望远镜和与 |ΣW|≤A。 |
| bse_prefix_sum_sq_bound | 842–854 | 有限 Cauchy–Schwarz 和 card≤n，得到任意前缀平方≤n·energy。 |
| bse_integrable_energy | 856–861 | 实际 pi 坐标 eval 的二阶矩拉回与有限求和。 |
| bse_finite_max_measurable | 863–887 | 固定有限 running max 的可测递推，与 Icc sup 精确相等。 |
| bse_bounded_stopped_path_measurable | 889–974 | 对所有可测 T≤n，用固定 n 与零延拓，真实变动停时 B_T/K/J 可测。 |
| bse_stopped_max_data | 976–1033 | 先证所有平方可积，由真实路径 energy 支付；没有以随机上界当固定常数。 |
| bse_stopped_prefix_dep | 1035–1056 | 停止前缀在 min(k,T) 的实际过去依赖性，逐项处理 i<k。 |
| bse_stopped_tail_test | 1058–1131 | 每个未来 i≥k 的乘子 F·1_(i<T) 只依赖 i 之前坐标，L1 独立乘积合法。 |
| bse_stopped_l2_maximal | 1133–1300 | W_k 在 k+1 以前可测，future cancellation 后用 (2B_T−ΣW)²≥0 吸收得4。 |
| sourceBackward_stopped_second_and_maximal | 1302–1397 | 由真实 NH 特征导出 N 过去依赖，二阶矩=EN/n，backward4、forward16。 |

原文对照完整读取 `C:/game/shao/current/c12/main.tex` 1077–1149 和 `supplement.tex` 4604–4665，源哈希分别为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`、`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。归一化下实际 `n E Z²=1`，所以原 `σ²=1/n`、`h=4nσ²R²=4R²`，`m≤3H/σ²` 正是 `m≤3nH`。真实有限 pi 产品、Fin.rev、完整原始平方和、弱首达及严格失败都与原反向预算部分一致；没有把抽象 martingale/Wald/Doob、停止独立性或目标预算当公开前提。第一项不需 mean zero；第三项才明确使用 mean zero。只有有限二阶矩，没有新增三阶矩、有界支撑、对称、无原子或几乎处处正能量要求。

三个承重链均成立。首先，真实尾平方在 `z²>H` 上由 `2R≤min(|z|,1)` 控制，取消已证明为正的 R，得到 clipped mean；原零参数 budget 没有被误配成正参数截断预算。其次，`i<NH ↔ i<L ∧ Qrev_i<H` 保证 cH、cN 仅用当前增量之前的坐标。真实产品独立性给出 factorization；有限求和后得到 ENH、EN、失败概率和 EU。失败事件只推出 NH=L，没有反向把末端命中也判成失败。最后，交叉项中 `D_i 1_(j<T)` 是 j 之前的真实可积过去函数，故当前坐标均值零确实消去交叉项。

最大值证明独立核对了全部积分前提。对任意可测 T≤n，B_T²、K² 先由 `n·energy` 支付可积，J² 再由 4K² 支付。运行最大 A 与 W 的递推都对随机路径逐点定义；A_n=真实 K，`|ΣW|≤K`。W_k 只依赖前 k+1 个反向坐标，故从 k+1 起的未来增量可用 tail_test 消去。各乘积先证可积，再交换有限和与积分；由 `K²≤2ΣM_(k+1)W_k` 和 `(2B_T−ΣW)²≥0` 吸收出系数 4。这里从未把 K 或 T 当确定上界，也未假设停止事件与其增量独立。前向几何恒等式对每条路径给 J≤2K，平方积分得到系数16。候选文字的 layer-cake 路线在最终源中换成有限权重望远镜证明；结论和冻结前提完全相同，无未付接口。

全部 70 个实际 owner（3 public、22 显式 private、45 generated）完整 TYPES 均已审查，owner 由 `env.getModuleIdxFor?` 选取；每项都为 theorem，非定理 full VALUES 应覆盖数为 0。读取使用原 `pp.all/deepTerms/proofs=true` 日志：将已经完整读过、逐字相同的重复子表达式无损提取为19个文字字典，完整读取字典及每个类型所有非重复 binder/let/instance/目标和上下文；逐类型逆展开与原始仅空白规范化文本全相等。没有用首尾、结构摘要或省略号替代类型；不声称相同原始重复字节被反复逐字重读。日志的 ⋯、...、sorryAx 计数均0。45生成项均为实际算术、成员/序关系 simp 或 Nat.find 记账命题，无隐藏定义或额外假设。逐项 recursive collectAxioms 的集合均为标准 `propext / Classical.choice / Quot.sound` 的子集，完整 AX 已读。定理机器证明项按精确源、原 o、owner/name/index 与审计日志绑定，没有全文打印或因补 proof-term 哈希重跑审计。

依赖沿用已接受 v68 闭包，并由 v69/v70 的保留链延续；不重新审查旧证明或重跑旧 AX。v68 receipt SHA256 `63dde1b75b911cc4d8f47b81d19dc6838763adba762443a5f3c1a735a93a4f94`；本次 dependency-reuse SHA256 `02032845ccdd1ce2fbecbc98438e3f23f0a9669d5f07f72d66246cf011ff4f14`，其原 manifest SHA256 `92626c7d1fac232b9c8653f0d95326d8fcd64070d7618cfabe5185d0d02946fa`。9 个本地库源均等于 v68 source map 及作者绑定源，服务器9对 source/object 只读重算均一致。完整读取实际消费的 Path/prefixSum/prefixSquares/energy/truncationF/truncationBudget 值与 positivity、integrability、measurability 接口；同时核对钉死 Mathlib 中 pi 独立族、反转 precomp、有限 disjoint tuples、independent product integrability/integration、eval measure-preserving 接口及概率测度条件。旧实例闭包复用已接受资格，没有新增 project instance。

保留全部开发分母：partial001–019 有17个 rc1，partial005 和 partial015 为较早局部 rc0；whole020–027 的8个 rc1均保留源/日志且无对象。完整三头首次成功是 whole028；共25失败、2局部成功、1完整成功。不能把 partial005/015 混算为完整通过。成功后 producer replay0，完整 owner audit replay0，本审查 Lean/AX 调用0。禁止项 sorry/admit/new axiom/unsafe/native_decide 均0。版本为 Lean `v4.36.0-rc1` / Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。本审查未触碰资源配额或外部CPU0–9/80GiB工作。

本模块只消除原 S.8.10 反向 stopping/Wald/二阶/Doob 预算义务，不证明原后续 complete suffix conditioning、corridor、terminal envelope、平方条带、共同完成或联合比较。保持 p54 修复及外部结果归属；不提出新颖性声称，也不以124机制为前置。C12/OQ3/OQ4/OQ56 根组保持 OPEN。

终审完成，释放本报告和 coverage JSON 的写权及本任务执行权；无在途命令或未完成后续写入。input、cached input、output、reasoning-subset 的实际 token 数不可见，均记 null，不估订阅百分比。
