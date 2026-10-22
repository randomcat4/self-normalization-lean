# OQ4 PR154 独立验收

STATUS: CORRECT
CRITICAL_GAPS: []

验收冻结 head `457139f395ee3153bcbe85a8ba1b94f37e481b68`，tree `eb71cad17b83f4d9568332e72a11642566e506ff`。新增模块 `Shao/OQ4/RademacherS5Assembly.lean` 为 56,403 字节、1,122 行，SHA256 `5b492c8193434dbe2db6be8cc82ca653d329a0e6b5c587aa6cf5204953e48397`；读取前后哈希一致。20 个公开定理、41 个公开透明定义、156 个模块所属常量得到覆盖。

本轮是新上下文的独立来源、数学和 Lean 源码审查。完整读取原 `spectrum01.md`、原 `frozen01.md`/`verdict01.md`、S5 冻结数学及声明、冻结实现全部 1–1122 行，逐项核对实际 S3/S4 消费接口；没有读取旧独立评审推理来决定本结论。来源 `C:/game/shao/current/oq4/c01/spectrum01.md` SHA256 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`，来源 commit `35d4580b61e22e7145f47730045a09874ef93259`。

## 忠实性与前提

原始作用域是第85–104行的固定 Rademacher、弱事件 `M_n≤x_nV_n`、每个固定 `c>0` 的 `x_n=c n^(−1/6)`。实际输出为 `log Q_c(n)−q_c δ_c(n)→0`，其中 `q_c=π²/(4c³)`、`δ=floor(h)+1−h`，及全部相位和完整倍率极限点区间 `[1,exp(q_c)]`。本报告排除原96/98的细立方根率子句；排除 strict112–115 和原116的更广义务。此处的 CORRECT 不等于一般 OQ4 或整份 Spectrum 根闭合。

源码32–98行的 `root/height/phaseFloor/upperHeight/delta/E/F/coeff` 都是同一 CP 对象的透明别名；`x` 的指数是实数 `−1/6`，不是整数除法。`p` 沿 S4→S3→S2 是固定 Rademacher 产品律上的 `closedStrip` 实概率，`K` 是同律杀死质量；`b` 沿 S4→S3 接入给定真实 Brownian 过程的 `BrownianSup.probability`，并有 `P.real {U≤s}` 与完整时段 strip 的桥。`F=exp(E)` 是显式相位因子，未被当成自由 Brownian 尾函数。

所有承重公开结论只需要实际 Brownian 输入 `hB : IsBrownianReal B P`、概率测度实例和固定参数 `0<c`。S5 主概率结论、分母正性、事件识别、CP 相位、收敛及不收敛都在输出侧。分类定理中的“给定某子列有极限”或“L 属于目标区间”是所证明两个方向各自的条件，未循环承担 S5_MAIN。内部 `ratio_from_log_error` 的抽象代数接口由已经证明的 `actual_s4` 输出实际满足，没有把目标藏成外部输入。没有新添有界性、非格点、密度、矩或变化分布假设；没有声称 c 上统一门槛。

声明冻稿 SHA256 `1b1ad31b8147cb142f7c5bca262903abe11428cc186e93b967a5adaeb01dd6a4`。去除注释和空白、略去唯一 `shift` elaboration 属性后，41 个定义的数学头/值及20个公开定理头逐项相同，名称集合无差异。所有输出谓词均透明，并非附加公理。

## 完整数学与源码核对

1. **对象、能量、正时间（237–423行）。** `definition_bridges` 将全部命名接到实际事件。`zero_time` 保留 `n=0`：能量与 V 为0，自归一化空事件为全空间，`p=K=1`；没有将 `x(0)` 解释成正时间缩放。`positive_time` 在 n≥1 时先证明 N、sqrt N、c 的正性，再用 `sqrt_eq_rpow` 与正底数 `rpow_add` 严格推出 `x√N=h`、`x=h/√N`，并消费 CP 的 `h³=c³N`、`N/h³=1/c³`。
2. **同一自归一化事件（315–375行）。** `actual_path_energy` 从单坐标 Rademacher 的 a.e. ±1 与产品坐标零测集传输得到全有限坐标 a.e. 支撑，故 `energy=Σa_i²=N`、`V=√N`。`actual_source_event` 证明可测性并将上述能量桥与精确缩放代入全前缀弱事件，得到事件 a.e. 相等，继而实际测度和实概率相等及 `Qsource=Q`。包含 k=0 的前缀约定在本正阈值域与原 M_n 相容；没有在全路径上假设 V=√N。
3. **S3/S4 的实际消费（377–484、613–650行）。** `positive_time_S4_bridges` 逐项证明相同 H、δ、第三尺度、x、`w=E`、Q/QK 桥。`critical_inputs` 从 CP 的 cutoff/scales 推出最终胞元、h→∞、N/h²→∞、第三尺度最终恰为1/c³并有界。`actual_s4` 直接调用已证 `S4_EVENTUAL`。已核读该上游：它在同一 `k+K_cell` 上调用 `S4_ALL`，再以共同移位返回原列；`S4_ALL` 由 DA2 加实际 `S3_MAIN` 得到结论。S3_DOM 的 Brownian 比值趋1和最终正性来自实际 `BrownianFirstTerm` 定理，S3_MAIN 的输入没有假设该概率渐近。S5_S4_EVENTUAL 又对每个 `J≥Ncell` 显式输出同一 n=j+J 的全 j 胞元、三尺度和实际 S4_ALL，以及 δ/E/F、p/K、x、Brownian 分母、Q/QK/Qsource 的共同索引恒等式；不存在 all-j/eventual-j 偷换。
4. **主相位与合法概率对数（486–656行）。** `main_outputs_proof` 从 S4 取得两个真实 log-ratio 误差并通过 n≥1 的精确桥改写。`Npos=max Ncell (max 1 (max Jtime Jpos))` 同时支配 CP 胞元、时间和真实概率正性；`legal_of_s4` 把 S4 的 p=K>0、b>0、Q=QK>0 和实际 log 除法恒等式传回 S5，并加入已证明的 Qsource 桥。`exp(log z−E)=z/F` 只在该正性尾段使用，所以得到 Q/F→1；由 CP 的全 n 界 `0<F≤exp(q)` 乘回，严格得到 Q−F→0。QK 同理。随后输出任意 ε 的门槛≥Npos及同一合法尾段；没有把总函数 Real.log 的早期值伪装成普通概率对数。
5. **子列与相位转移（659–956行）。** `CPPhaseOutputs` 只包含确定性几何和 CP 极限。`actual_phase_limits` 将已证主误差及绝对差沿同一严格自然数 σ 复合，并由 `σ(j)≥j` 得最终同一合法概率尾域。`phase_outputs_of_cp/cp_phase_shift` 对任意额外共同 j 移位同步所有量。立方子列是 `(j+1)³`，立方减一是 `(j+2)³−1`；其自然数减法、整数/实数转换与严格递增没有遗漏。一般 c 的 up/down/nearest 正是 ceil、ceil−1、floor(target+1/2)，并列向上；up/nearest 的额外移位2同时作用于同一全部对象。S5_PHASE 选择同一组 Ja/Jb/Jα，d=0、1和内部 α=1−d 分别复用上述同一序列，不另选一个具有期望概率极限的见证。
6. **完整极限点与不收敛（958–1118行）。** 任意严格递增 τ 上 Q（或QK）有有限极限 L 时，`Q−F→0` 使同一 τ 上 F 也收敛于 L；因此 CP 的完整 cluster_sets 给出 L∈[1,exp(q)]。所有 τ 都最终落入同一合法尾域，并同时转给另一个实际倍率。反向对区间内任意 L，由 L≥1、q>0 取 `d=log L/q∈[0,1]`，用同一 CP phase_realization 的严格自然数时间序列得到两个实际倍率极限。两向共同得到完整集合等式，非仅两端点或包含关系。若全列 Q/QK 有极限，减去已证绝对误差便使 CP factor 全列收敛，与 CP.not_convergent 矛盾。c=1 的区间与两个立方端点恰为原文常数。

## 逐个公开头与显式私有证明

| 公开定理 | 源行 | 核对结果 |
|---|---:|---|
| definition_bridges | 237 | 实际固定对象与 Cluster 精确定义 |
| zero_time | 269 | 空时间、能量、事件和质量全部保留 |
| positive_time | 293 | 实数 rpow/sqrt 与正时间精确桥 |
| actual_path_energy | 315 | 产品律 a.e. Rademacher 能量 |
| actual_source_event | 342 | 可测实际自归一化弱事件相等 |
| positive_time_S4_bridges | 377 | 同一 S4 对象、常数和比值 |
| S5_DOM | 570 | 从正侧趋0、胞元和概率合法尾段 |
| S5_S4_EVENTUAL | 614 | 同一共同移位全 j 消费和返回 |
| S5_MAIN | 652 | 真实 log 相位、相对与绝对误差 |
| S5_CUBE_GEOMETRY | 778 | 两立方子列及自然数减法合法性 |
| S5_CUBE | 808 | 实际端点与内部相位概率极限 |
| S5_ROUNDING | 832 | ceil/down/nearest 及并列向上 |
| phase_index_bridges | 861 | 相位序列透明恒等式 |
| S5_PHASE | 885 | 同一组 offset 与全部 d∈[0,1] |
| S5_CLUSTER_BOUND_Q | 958 | 任意收敛实际 Q 子列的完整界 |
| S5_CLUSTER_BOUND_QK | 988 | 任意收敛实际 QK 子列的完整界 |
| S5_CLUSTER_REALIZE | 1018 | 区间每点的同一 CP 实际见证 |
| S5_CLUSTER | 1052 | Q/QK 完整双向集合等式 |
| S5_NOT_CONVERGENT | 1074 | q>0 及两个实际全列不收敛 |
| S5_UNIT_CLUSTER | 1107 | c=1 原文区间与不收敛 |

全部13个显式 private 证明逐行读过：`critical_inputs:426`、`actual_s4:449`、`legal_of_s4:457`、`ratio_from_log_error:486`、`difference_from_ratio:500`、`main_outputs_proof:521`、`cp_phase_of_data:659`、`cp_phase_shift:673`、`actual_phase_limits:685`、`phase_outputs_of_cp:720`、`up_actual_phase:730`、`down_actual_phase:749`、`nearest_actual_phase:760`。其全部角色已在上述完整链中核对，没有未展开的承重假设。

## 所属、生成项、依赖与机械证据

所属范围按原生模块归属计，不按命名空间前缀猜测。`environmentDifference=moduleOwnership=stage2=curated roster`，均为相同156项；41 defs + 115 theorems，其中20公开、13显式private、82生成。已逐项将原生的156类型及41完整定义值与发布 actual-interface 对齐，并独立算哈希与 owned ledger 比对，无差异。人工覆盖方式是全文1–1122行中的41定义与33显式证明，以及另外读取全部82生成项的实际类型；没有声称人工阅读55MB的所有递归表达式。

82生成项涵盖透明定义方程、congr_simp、数值非零 simp 辅助和自然数线性算术证明辅助；它们不提供新的目标概率假设。11个 S5 命名空间外项也全部纳入并逐个读类型：

- `Shao.OQ4.RademacherS2Assembly.K.eq_1`
- `Shao.OQ4.RademacherS3Assembly.K.eq_1`、`p.eq_1`
- `Shao.OQ4.RademacherS4Assembly.K.eq_1`、`N.eq_1`、`Q.eq_1`、`QK.eq_1`、`b.congr_simp`、`p.eq_1`
- `Shao.Probability.BrownianSup.U.congr_simp`
- `Shao.closedStrip.eq_1`

这些是原定义的展开/同余，名称位于上游命名空间并不意味着可以漏掉。JSON附完整41定义、20公开头、13私有头、82生成项名册。

递归 type/value 引用图61540项再次作只读可达性核对，无未解析引用；797个项目依赖常量、26个实际 type/value 依赖模块都可达。另6个仅导入模块单列。全部32份依赖源字节与冻结head、v38基线 `63f82bd7ea2a0fba92a4ad217c4ad27bfa3ead00` 和原生运行绑定一致，无替换上游源码。尤其 CP=`388f17e1c257d9b1fe74914866937bd9dc6ce1fb1398e72761b3f65c8464a96f`，S3=`097d3a773d48f9d94a2a5b439c00d39f6c87eb9b1c793d3b91dba6066fef369c`，S4=`803ee8488697c8f335e35a32f32fdd31ca69d521e1071eef2018af5b12f775bd`。

本审查没有运行 Lean、build 或 emit，没有修改作者模块、合并或再开子实例。静态目标源无 sorry/admit/新增 axiom/unsafe/native_decide。保存的完整原生审计使用 Lean4.36.0-rc1、Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，156所属与797项目依赖的 unsafe/partial/axiom-kind均为0，公理并集只有 `propext, Classical.choice, Quot.sound`；其机器层由 root 统一门验收。

root v39统一门现已 PASS。本轮只复核 `coordination/integration-v39/gate-result.json` 与服务器 `logs/integration-v39/result.json` 字节相同，SHA256 `a74870ea363ebb14763aaf1d336d1e0794a887ebe98b41c9b77e4659ab7ecc66`；七个实际命令退出码均0，对应日志哈希再次读盘核实。门中本模块源SHA与冻结完全相同；全库277生产模块、1875公开定理、3180含生成命名空间定理、5470所属常量，271旧源/1048旧对象复用且不变。没有重复成功的 Lean 检查。此机器层仅认证当前编码；本报告另行完成其上述源义忠实性审查。

关键原生证据哈希：actual-owned markdown=`c238f118c54250ed2cccb00b2bc8f8d2f47e25f36f9699d8202b8ce32389bd65`；发布 actual-interface=`9f6e12970f116b4a2760d81e2250292737f8379d45c159f881f2ab90f17eb379`；native audit=`ee5563d146ad1ece2675d990131074d869b46411c60e1c7469255f11853d5b6b`；raw-expressions=`2bc946c4c0aa8cfda60c45443b87d403656a55b454b2b1bc9e5ab27cfe81071b`。完整依赖和证据绑定见配套JSON。

源码18–22行“未运行 Lean/pending”的历史注释仍保存在冻结字节中；当前检查状态应以上述绑定同一源SHA的实际收据及root门为准。该注释不改变声明或证明，不构成数学缺口。

## 未完成范围与接受边界

- 原96的 `k³−1` 立方根余项 `O(k⁻⁵)`、原98的内部相位余项 `O(k⁻²)` 未由本模块形式化完成；后续本地数学/声明/SourceReady状态不冒充服务器 Lean 通过。
- 原112–115严格事件的 ceil 分类、整数 δ=0、严格完美立方倍率及一般严格事件仍在本验收范围外，不能因弱S5通过而报闭合。
- 原116更广阈值变动及量词下的 `O(n/h³)` 对数概率变化完整义务保留待单独冻结/认证。
- 一般分布、变化 c、其他格陪集、uniform-x OQ4、完整 Spectrum/OQ4 根与共享energy9/10保持 OPEN。新增原始叶为0，不报原题完成百分比。本审查不作新颖性或历史首次裁决。

可接受的是：冻结模块对实际 Rademacher 弱事件的 S5 概率相位装配、同一 CP 子列、完整倍率极限点及不收敛；没有关键缺口。
