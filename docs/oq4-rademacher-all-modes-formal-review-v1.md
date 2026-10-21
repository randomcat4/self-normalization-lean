# RademacherAllModes 独立最终形式审查 v1

STATUS: CORRECT
LEAN_STATUS: LEAN_FULLY_CHECKED
FROZEN_SCOPE: D1 + D2（F₁ 未化简有限谱）
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

结论：固定 canonical source 忠实实现冻结 D1/D2；实际 canonical 无产物检查、完整原 source 镜像检查、direct-target 导入、actual-all41 导入和18项展开契约均通过。source 的17个当前 owned 声明完整进入实际导入环境；其中1个生成声明与旧847重合，故 distinct-new=16、actual union=863。重名项没有被过滤，旧 owner 和完整旧记录保持。所有拟认证声明的传递公理只含 propext、Classical.choice、Quot.sound。

本结论仅关闭此薄模块的冻结 D1/D2。它不证明 cot 系数化简、S1、低高度分支、S2–S5、一般分布 OQ4，也不关闭 Spectrum 或 root。

## 1. 固定输入、角色边界和证据位置

审查者在 PREP 后保持隔离，收到 lead 明确 AUTHOR_CANONICAL_READY 后才读取新 canonical。未读取其他 review 推理、作者过程、intake/candidate 或作者私有 Source；没有把作者 receipt、ledger 或工具当成正确性依据。匿名数学 proof 本轮不需要，也未读取。审查使用 canonical 实际证明、冻结接口、原始来源及必要已认证透明定义/公开签名。第7节准确披露一次旧接口提取边界失误，不能将本轮描述成零旧证明体访问。

已读 AGENTS.md、SERVER.md、coordination/TEAM.md 与 math-theorem 的 prompt/openai/lean 指引。所有 shell workdir 均为 C:/game/shao lean；所有 Lean 仅在指定服务器、单进程、taskset 0-3、无 -o 执行。没有 Git mutation、cache/source/common/root/pins 修改，也没有恢复其他参与者的更改。

| 输入 | 固定值 |
|---|---|
| 工作树 | /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4 |
| branch / HEAD | feat/oq4-all-modes / c8112257ac213cd488ae24ab73100fab36837802 |
| canonical source | Shao/OQ4/RademacherAllModes.lean，7720B，SHA256 04cd5a52a40398586908a42682724c357daf0e0c8bbf25a049bbd620d27ee8aa |
| 唯一新 olean | .lake/build/lib/lean/Shao/OQ4/RademacherAllModes.olean，183592B，SHA256 93ac5657481fb7555620730e3ceaf9adcacc9ba0979451541dd4e6cc3cd017cf |
| 冻结接口 | frozen-rademacher-all-modes-v1.md，6845B，SHA256 dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10 |
| 原始来源 | C:/game/shao/current/oq4/c01/spectrum01.md，4306B，SHA256 b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b |
| canonical-release-base / base-receipt | 均为 SHA256 5ccce5c8b2f357933f674c1c6410a0300dca3c8ce77d371af155e25ab888dca5 |
| 92项保护 map | SHA256 cf3b164c60adf590af9749d6cdf894f11031c76ed316820111f433bd2858b76f |
| 97项旧产物 map | SHA256 cd1493d4e5058103c8281d2b4652ceb997f9db0608a5ebb3ce71dd28dfedb5a1 |

实际工具链：Lean 4.36.0-rc1，commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e；Lake 5.0.0-src+c9afcdd；mathlib 807d3836b165983210ee2ecf3cd28f239436949c。

原 PREP 报告703ac95b5cffc13989a54c16115357fe6a1d5dd58eafa5f830b0df955ebb89f9 / 7877B 已由 lead 原字节归档到 drafts/oq4/rademacher-all-modes/prep-formal-review-v1.md。最终报告在本原路径扩展。

全部自有服务器证据位于 repro_outputs/oq4-rademacher-all-modes-independent-v1。原始日志、完整 Expr、完整定义体、原始登记 JSON 和二进制均只留服务器。可分发的独立 curated receipt 为：

/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-all-modes-independent-v1/independent-final-curated-receipt.json

该 receipt 为27736B，SHA256 c4c79662471f4e1dd91f12ee390795d0286971187c43448fbb29154fa0d49d71，含输入、实际命令/receipt、全部17项元数据和记录 hash、重名核对、scope、语义结论、守恒与失败披露；不含 raw Expr 或定义体。

## 2. 实际 Lean 检查

| 检查 | 结果 | 时间 |
|---|---|---|
| direct canonical：lake env lean Shao/OQ4/RademacherAllModes.lean | exit0，无产物 | 4.10s |
| 完整原 source actual-mainModule 镜像，-R final-mirror-v1 | exit0；mainModule 恰 Shao.OQ4.RademacherAllModes | 9.26s |
| direct-target actual import + 必要 Lean 审计 import | exit0 | 8.90s |
| 旧40 + target 的 actual-all41 import + 必要 Lean import | exit0 | 9.82s |
| ExpandedContractsV2.lean，18项展开契约 | exit0，无警告/错误 | 4.06s |

镜像构造没有删行、改数学字节、改原 imports、prepend 旧40 或 import 自己的 olean。它仅在完整7720B原 source 前加 import Lean，后加 AuditTailV4；原 source 从偏移12起连续逐字节相同。三个原 import 仍为 RademacherFiniteBasis、RademacherIteration、KilledPathLaw。actual mainModule 由真实 -R 参数验证，未靠字符串改名模拟。

审计尾在运行时遍历所有 getModuleIdxFor?=none 的常量，不做 name/namespace 筛选；import 审计以实际 owner OR namespace 捕获所有 private/generated/namespace外常量。审计自身产生的当前 owned 常量数为0。PREP 镜像 smoke 曾实际覆盖 namespace 外、private、非空 universe 参数、private instance 和 inactive scoped instance；深度256的 Expr Repr 探针具有256个 Expr.app、无省略号，不依赖猜测 pp.maxDepth 或 AttributeKind 的 Repr。

## 3. 原始记录逐项 exact 与真实重名

每条记录包含 raw name、kind、完整 universe 参数及其原始表示、完整 Expr type、传递公理、每个 definition/opaque 的完整 body、安全字段、实例活跃标记/优先级/属性种类。比较不展开或读取 theorem proof body来冒充定义体。source/direct/all41 的记录只对 owner/current-owned 这两个来源位置字段作明确转换，其余逐字段 exact。

| 实测范围 | 常量 | definition | 说明 |
|---|---:|---:|---|
| 固定旧40 actual import | 847 | 98 | 74个 private 原名；225项 universe 参数非空 |
| 当前完整 source owned | 17 | 1 | 16 theorem；17项 universe 参数实际均为空 |
| direct-target imported target owner | 17 | 1 | 与 source17 原名和规范化记录全量相同 |
| actual-all41 target owner OR target namespace | 16 | 1 | distinct-new，含私有及其他 namespace 的生成项 |
| actual-all41 全集合 | 863 | 99 | 精确为旧847与 source17的真实集合并集 |

source17包含8个命名公开 theorem、4个 private theorem、1个公开 definition 和4个生成 theorem。其中生成的 RademacherFiniteBasis.coefficient.eq_1 与 RademacherFiniteBasis.vector.eq_1 仍由 target 实际拥有；它们没有因 namespace 不属于 target 而遗漏。survivalCoefficient.eq_1 同样完整比较。

唯一真实重名为 Shao.OQ4.killedAction.congr_simp。其 raw name/kind/universe/full Expr type/三公理依赖/实例字段及其他非 owner 记录与旧847、directtarget 和 all41 完全相同；规范化完整记录 SHA256 为58563d2b26d57907ccb57b6a5d95c3335cfefd20cecc0bbb97ca432473190bd4。source 中它是当前 owned，directtarget 中 owner 是 RademacherAllModes；actual-all41 中 owner 仍为旧 Shao.OQ4.KernelRecurrence，旧完整记录不变。该项保留在全部 source17核对和 union 核对中，没有被滤去或计成两个 distinct 声明。

source17全部出现在 actual-all41。所有旧847记录及98个完整定义体逐项保持。结果文件 comparison-v2-exact.json 的 status=EXACT_MATCH，errors=[]。旧847全记录规范化 SHA256 仍为 d7d022fd1c4eab733163eebdb7259a5cd535888c9fb0c0037d43b67a9318f721。

比较器V2另对真实审计数据作内存篡改自检：重名项 type、重名生成项 universe 参数及新 definition body 任一篡改均被拒绝，恢复后再次 EXACT_MATCH。该过程没有改 canonical source 或任何数学文件。

## 4. 完整实例登记与公理审计

实例比较覆盖活跃表、erased 集、各实际导入模块的完整 global/scoped 导出条目、当前模块新条目，以及条目的原名、完整 val Expr、keys、priority、synthOrder、attribute kind。不同 import 范围的全局数量没有互相冒充一致性证据。

| 明确审计范围 | 实际 OQ4 imported modules | 活跃登记 | 含登记模块 / 导出条目 |
|---|---:|---:|---:|
| 原 source 三 imports + 必要 Lean；主模块不计在 header imports | 8 | 24838 | 2658 / 25270 |
| direct-target 一 import + 必要 Lean | 9 | 24838 | 2658 / 25270 |
| 旧40 imports + 必要 Lean | 40 | 25020 | 2697 / 25453 |
| 全41 imports + 必要 Lean | 41 | 25020 | 2697 / 25453 |

source/direct 同范围的活跃和完整登记 exact；old40/all41 同范围的活跃和完整旧登记 exact，erased 集也一致。actual-all41 模块集合精确为固定旧40加 target，无缺漏或额外 OQ4 模块。source/direct 的实际模块集合关系也逐项核对。

新注册实例实际为0，新的活跃实例实际为0，17项 source-owned 的 instance 标记均为false；不是预设0。审计不创建实例或额外常量。source 原文对 sorry/admit/axiom/unsafe/native_decide 的词项命中均为0；所有 source、direct 和 all41 拟认证常量的传递公理并集只含 propext、Classical.choice、Quot.sound，unsafe和axiom声明数均为0。

## 5. 来源 → 冻结 D1/D2 → 实际 statement/proof

### 固定对象与量词

直接检查已认证透明定义：states=整数 Icc(-m,m)，modes=自然数 Icc(1,2m+1)，H=(m:ℝ)+1，theta=(j:ℝ)*pi/(2H)，mu=cos(theta)，phi(w)=sin(theta*(w+H))，vector(r)=phi(r:ℝ)。实际 law 是(1/2)δ₁+(1/2)δ₋₁，现有内部 IsProbabilityMeasure 实例由展开契约实际 inferInstance 验证。

killedKernel 是 translationKernel 对 closed Set.Icc(-h,h) 的 restrict，killedIterKernel 是这个真实核的自然数幂；killedAction 是真实核积分，killedMass 是该作用于常数一的值。没有引入替代递归、自由特征值或新矩阵幂。所有公开 D1/D2 定理完整保留 m≥1、m≤h<m+1、整数 r∈states、自然 n；D1 还量化每个 j∈modes。无 n>0、奇数 j、正/非零 mu、正生存、无周期或奇偶配对前提。

### D1：真正可积性与全部有限幂

canonical第32行 killedIterKernel_integrable 提供真正 Integrable。证明使用实际 phi 的可测性和全实数域 |sin|≤1，调用既有有限 killed kernel 的可积性接口；它不从 totalized integral 的等式反推可积性。

第39行的一步网格身份把真实 grid 的整数见证转成 states membership，调用已认证的全部模态 killedKernel_integral，所得正是实际一步 killedAction。第51行 killedAction_eq_pow 从真实 killedAction_zero 起步；后继通过实际 semigroup，把一步身份只在 killedIterKernel_ae_grid 支持的几乎处处网格上代换，然后线性提出 mu 并用自然数 pow_succ。该推理没有除以 mu，也没有取 |mu|，所以零、负谱和周期消去都保留。第80行 integral 形式由 killedAction 的原定义得到。

展开契约实际通过：字面 sin/cos 公式、真实 (killedKernel law h)^n、字面有限集、原整数起点，分别检查 Integrable、积分幂等式和 action/积分同一性，包含全部自然时间0。

### D2：仅 F₁ 重建到实际质量与概率

第15/18行 survivalCoefficient 明确为 coefficient m j (fun _=>1)，并给出(1/H)乘原 states 上的计数和。它不是1/(2m+1)平均，也不是条件生存分布。

第87行 constant_reconstruction_ae 只对 F₁ 使用已认证 reconstruction。实际有限幂核由已认证 ae_grid 给出整数网格支持，故在每个支持点把 B2(F₁) 变成常数一的几乎处处重建。第101行质量证明先把 killedMass 展开成真实常数一积分，再用该 ae 等式，使用每个加权 phi 的 genuine Integrable 调用 integral_finsetSum，最后用 D1。这些步骤没有要求 mass>0，没有除 mass，零质量仍保持同一等式。

第125行把结果连接到真实 measure.real Set.univ。第134行连接 n步 Rademacher乘积律下 shiftedClosedSurvival：正时间1≤k≤n的弱事件 |r+prefixSum|≤h。第144行只在零起点连接原 closedStrip（包含k=0）；代码显式由 m≤h 和 m≥0 得0≤h，再使用有该条件的旧概率桥，并验证0∈states。没有暗中删除 h≥0 或用 strict strip。

展开契约实际核验了完整字面计数谱和及唯一1/H、真实核质量、独立用旧公开接口重建的 ae-grid F₁、shifted路径事件和原closedStrip事件。没有只靠 prettyprint 或名称相同下结论。

### 边界

h=m 的弱端点通过实际 closed kernel 与专门展开契约保留±m；m≤h<m+1 和整数±1步长给实际吸收点±(m+1)。modes 包含中心 j=m+1 的零特征值和其后的负特征值，最后 j=2m+1 仍属完整模式集，且公式使用原 signed mu^n。

n=0的实际核等于δ_(r:ℝ)已通过定义展开契约；0^0=1单独核验，D2的零步谱和恢复1。没有先杀死零步起点，也没有删除合法整数起点条件。所有结论保持在冻结的 m≥1 与整数起点范围内，没有扩展到m=0、0≤h<1分支或其他非整数coset。

18项 ExpandedContractsV2 全部实际通过；它们是语义检查补强，最终正确性仍由原 source、全部实际声明和证明逐项审查共同支持。

## 6. 守恒、产物与结束状态

最终实际文件扫描：OQ4源码精确旧40加target共41个；保护源码/配置范围为旧132加target共133项，全部固定。旧40还在PREP逐个匹配 immutable c8112257 HEAD blob。旧847/98定义体与完整registry保持。

实际整个 .lake/build 文件映射精确等于旧97 map加上述唯一新olean，共98个，路径和每项SHA全部exact。canonical source与sole olean在所有审查前后分别保持04cd…e8aa和93ac…17cf；不是仅计数相同。最终保护JSON与审查前保护JSON完全相同，HEAD仍c8112257。

reviewer own emit=0，live owned Lean processes=0，自有binary/private编译产物=0。所有检查进程已退出。没有新增 .olean/.ilean/trace/cache产物，没有Git/cache写入。final-full-tree-conservation.json 和 final-protection-before/after.json 为服务器原始证据。

## 7. 全部工具失败与独立性披露

PREP保留：API探针的 Lean.instanceExtension 命名失败（真实为Lean.Meta.instanceExtension）、显式 PHashMap.toList 查询失败（实际投影调用可用）、远端rg缺失、ModuleIdx被误当单构造器、liftIO命名遮蔽，以及非必要 ReducibilityHints 缺少Repr。相应失败源/log/receipt仍在；最终AuditTailV4实际通过，没有改变数学字节。

最终接口提取V1在透明 coefficient 定义末尾没有识别同一行 @[simp] theorem 边界，导致仅旧 RademacherFiniteBasis.theta_one 与 mu_one 两条简短j=1兼容证明体意外可见。已立即向lead披露，lead允许继续并要求准确记录。未发现更大访问范围；这两条旧证明不构成全部j的D1或F₁的D2证据。本轮不能声称零旧证明体访问。旧固定源码上的原工具输出已按原筛选规则重建保留于 interface-extraction-v1.stdout.log；失误说明在 interface-extraction-failure-and-fix.json。严格V2修复了属性感知声明边界，并按括号深度在顶层 := 之前截取公开签名；interfaces-v2.md不含旧theorem证明体。核心D1/D2另由完整canonical审查与18项展开契约核验。

PREP比较器V1实际运行后因假设 source-new 与 old不相交而报1项名称集合MISMATCH；comparison-v1-overlap-mismatch.json及日志保留。V2没有过滤重名，而是核对真实交集、逐项exact和旧owner保持，最终EXACT_MATCH并通过篡改拒绝自检。这是审计工具集合模型修正，不是数学修订。

ExpandedContractsV1的三处审查者手写sin展开括号存在语法错误；V2仅修复自有契约文件括号，18项全部通过。V1源和失败stdout/stderr/receipt保留，canonical source从未被修改。

不存在尚未关闭的D1/D2关键缺口；结论为 CORRECT / LEAN_FULLY_CHECKED，且仅限本冻结叶。
