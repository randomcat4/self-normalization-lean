# 两个相邻单元的独立最终审查

审稿人：OQ4 context214；实际模型/推理强度：gpt-6.1-sol/xhigh；全新作者外上下文。本人没有参与两个实现，没有修改实现、冻结文本、旧收据或共享文件。审查采用 math-theorem；未使用 math-ultra。

**A：RademacherRealStrictBoundary — STATUS: CORRECT。**

**B：RademacherBrownianBoundaryShift — STATUS: CORRECT。**

这两个结论只认证下述冻结的有限事件桥和实际布朗边界平移。没有认证一般严格临界相位渐近、极限点集合、一般增量律或原 OQ4 闭合。所有原根组仍为 **OPEN**。

## 1. 精确认证版本与读取范围

| 项目 | A | B |
|---|---|---|
| 最终源码 | rademacher-real-strict-boundary-v1/attempt003/Source.lean | rademacher-brownian-boundary-shift-v1/attempt002/Source.lean |
| 完整源码读取 | 277 LF，12781 字节，全证明体 | 108 LF，4961 字节，全证明体 |
| Source SHA256 | `009ec0792ffdb48ff38be1f402c71c5c3892d5ae35a9227fbcaca16d6565b9c2` | `a1afd98a0f645623b736a1a5b88f4974e3e955cf0b38c02f5153776c1e24d1ac` |
| 完整声明冻结 SHA256 | `0c0a6b1520bc4f0421073ac9076e2fc6aab957408ea78d3040a07c883298a300` | `186e57fcdd1815ee65001b92da2b3bf86ad7cab261d5aa50688372e673dd0802` |
| Combined SHA256 | `99068b2dd2f616e540c873eaead5416ab7d9f54b652ba411d55a1d2cc6af8e3d` | `15307f7eb6d27510930221600fb1b0524f8c79fdaf902e58835781684e717da2` |
| 服务器执行收据 SHA256 | `b7d17ff4d40f0e6fd2d6ad662c8f4b39409b603727774ce0b7f27aaf4022117a` | `f7a5c080f05b73159c3adc1f6b96c790052d15a5039efe2040226250b525601f` |

完整阅读了两个 frozen-interface.lean.txt、freeze.md、lead-freeze.json、最终 Source.lean、全部实际 owned 的完整显式类型，以及所有实际 owned 非定理的完整值。不是只看声明摘要或作者计数。A 的数学建议第3节另外完整读过，其建议不是本结论的证明依据。

原源 C:/game/shao/current/oq4/c01/spectrum01.md 第1—4节全文已读；本次直接对应第4节，源 SHA256 为 `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b`。第2—3节的完整渐近和极限点主张不由本次两个单元独立闭合。

通过本地只读字节比较，逐一删去最终源码的证明体后，保留下来的全部前导设置、命名空间、声明头和定义完整值，分别与冻结全文精确相等。未运行 Lean 解析器。两份源码均为 UTF-8 无 BOM、仅 LF；没有额外顶层源声明，没有 sorry/admit/new axiom/unsafe/native_decide。

## 2. A 的独立数学核查

### 2.1 确定事件和标量桥

第12行的定义真实使用 `sum i in range r, X (i+1) omega`，只检查 `1 <= r <= n`。`X 0` 不参与；它不是自归一化事件，也没有把一个自由概率函数命名为实际概率。

第33—50行：由 h>0 得 C=Nat.ceil h>=1。先以该条件调用 Nat.cast_sub，才把自然数前驱的 cast 写成 C-1；没有把截断减法直接视为实数减法。Nat.lt_ceil 与自然数相邻关系给 m=C-1<h<=C。对任意整数 z，明确把实数绝对值改写为 Int.natAbs z 的自然数 cast，得到

`|(z:Real)| < h <-> natAbs z < C <-> natAbs z <= C-1 <-> |(z:Real)| <= (m:Real)`。

第51—69行：对具有所有 r<=N 整数前缀的路径逐个应用该标量桥。严格事件没有零前缀；闭条带多出的 r=0 由 prefixSum=0 和 m>=0 单独处理。反向只读取正前缀，没有漏掉 N=0。

第70—83行：actual_path_support 的实际完整类型给同一全测集上全部整数前缀。只在该集上应用确定性身份，随后 measure_congr 和 ENNReal.toReal 给真实概率相等。没有声称 Shao.Path N 中全部实路径集合相等。

### 2.2 原空间与几乎处处传输

第105—132行的指标双射是 Fin n 中 i.val<r 与 range r。r<=n 正好保证反向构造 Fin n 的上界，逐项函数值为 X(i+1)，r=0 是同一个空和。因此 strictEvent 的逆像身份是逐点确定性身份，不依赖 iid 或可测性。

第133—169行使用已接受 sourcePath_identDistrib 的完整实际类型：任意可测空间上的概率测度、正下标独立函数族和固定 Rademacher IdentDistrib。没有完备测度、Measurable X_i、N>=1 或额外矩前提。

原空间 AE 身份并非仅由概率相等推出。源码先构造两个 canonical 可测事件的对称差 D，证明 pathLaw D=0，再对可测 D 使用 IdentDistrib.measure_mem_eq 得 μ(F^-1 D)=0。measure_eq_zero_iff_ae_notMem 将其准确变为几乎处处不属于坏集，结合两个真实前缀事件的逆像语义得到所需 AE 等价。该步骤不要求原始逆像本身处处可测，也没有把外测度为一误当作补集零测度。

第165行概率身份对 strictEvent 直接使用同分布，不借用刚得出的另一个事件概率定义。随后与 canonical 桥相接。

### 2.3 非整数与边界攻击

第194—209行：严格到弱直接取 le；r=0 由 h>0 处理。反向若整数前缀绝对值等于 h，则 h 等于整数 |z|，与完整非整数假设矛盾。第210—273行重新以可测坏集传输该 AE 身份，再以 measure_congr 得两个原空间真实集合的概率相等。

核查的退化情形如下：N=0 时无正前缀，严格事件为全集，闭半径 m>=0 也只检查零前缀；0<h<1 和 h=1 时 C=1、m=0，N>=1 的 Rademacher 首步使两事件概率均为零；N=1、h>1 时首步满足两事件；整数 h=K>=1 使用 K-1，不误用 K；非整数 h>0 时严格 h 与弱 h 仅在整数支持上等价。例 N=1、h=1 的严格概率零、弱 h 概率一，说明端点没有被抹去。任意实路径 v(0)=1/2、h=3/4 不满足全路径集合身份，实际定理正确保留了整数前缀条件/AE 限定。

h<=0 不在冻结范围；本报告没有外推完整合取结论。A 不给全 h>0 的概率正性、对数或渐近结论。

### 2.4 A 的实际 owned 全覆盖

以下12项完整显式类型均逐项读完。唯一非定理完整值也已读完并与冻结定义对照。

| 实际 owned 后缀 | 核查内容 |
|---|---|
| sourceDeterministicStrictEvent | 上述真实有限正前缀和事件的完整定义值 |
| ceil_boundary_bridge | 全部七层合取、一般整数前缀路径条件、canonical AE 及真实概率身份 |
| source_ceil_boundary_bridge | 全部 ΩX/μ/X/iid/同分布量词、逐点逆像、原空间 AE、两个真实概率身份 |
| noninteger_boundary | 完整非整数条件及 canonical/original 五项结论 |
| ceil_boundary_bridge._proof_1_1 | C>=1 下 C-1<C 的否定导出 False |
| ceil_boundary_bridge._proof_1_2 | C>=1 下 natAbs z<C 与 natAbs z<=C-1 等价的否定导出 False |
| ceil_boundary_bridge._proof_1_3 | r!=0 下否定 1<=r 导出 False |
| noninteger_boundary._proof_1_1 | 同一正自然数推理，完整 n/r 参数已读 |
| noninteger_boundary._simp_1_2 | 集合并成员命题与析取的完整 Prop 等式 |
| noninteger_boundary._simp_1_3 | 集合差成员命题与合取否定的完整 Prop 等式 |
| source_ceil_boundary_bridge._simp_1_1 | 同上并成员化简，完整多态类型 |
| source_ceil_boundary_bridge._simp_1_2 | 同上集合差化简，完整多态类型 |

实际分类是 public4、generated8、definition1、theorem11，无显式 private 或源实例。生成项没有隐藏的数学前提或更强假设。

## 3. B 的独立数学核查

第13—35行的实际类型量化真实 B:NNReal->ΩB->Real、概率测度 P、IsBrownianReal B P 证据，以及两个各自趋零、最终正的确定序列 x,y。结论分别是共同尾部两个真实概率及其比值为正、实际对数比减去精确指数修正趋零、实际比值除以指数修正趋一。无自由尾函数，无 x/y->1 或修正指数收敛前提。

第36—47行只在证明体内令 b 为真实 BrownianSup.probability、f 为真实 firstTerm。f(s)=(4/pi) exp(-(pi^2/8)/s^2) 对所有实 s 按 Lean 全函数语义严格为正；log f(s)=log(4/pi)-(pi^2/8)/s^2 精确成立。这里连 s=0 的全函数表达也合法，后续概率渐近仅在最终正尾部使用。

第48—60行完整使用 actual_brownian_firstTerm 的 ε-δ 类型。对任意最终正且趋零的 z，z<δ 最终成立，与最终正性相交后得到 b(z)/f(z)->1。没有偷用正侧外的估计，也没有要求两个序列有共同速率。

第61—72行从 actual_brownian_eventually_positive 取同一个 δ，对 x,y 分别取得尾部小于 δ，再交四个尾部条件；b(x)>0、b(y)>0 以及 b(y)/b(x)>0 都有实际证明。

第73—95行在1处用 log 连续性得 log(b(y)/f(y))-log(b(x)/f(x))->0。共同正尾部满足每次 Real.log_div 的两个非零条件。代入两个 log f 精确值后，符号和方向为

`log(b(y)/b(x)) - (pi^2/8)*(1/x^2 - 1/y^2)`

`= log(b(y)/f(y)) - log(b(x)/f(x))`。

指数的方向已独立核对，没有把 x、y 对调。第96—105行先对上述误差应用 exp 连续性，再在共同正尾部用 exp(log q)=q、exp(a-d)=exp(a)/exp(d)，得到所要求的概率比除以 exp(d) 趋一。全过程不需要 d 有极限或有界，也不依赖全序列概率处处正。

边界核查：允许 x=y；允许 x/y 趋零或无穷；允许 d 发散或振荡；有限个非正值不影响结论；分母指数始终正。若删除最终正前提，负阈值的实际概率可为零，所以源码正确保留了该前提。B 不直接给格点谱、严格相位或自归一化结论。

B 唯一实际 owned `actual_brownian_boundary_shift` 的完整显式类型已逐行读完；实际为1个公开定理、0个生成项、0个非定理，无额外完整值待审。首败001到最终002仅在既有 body-local simpa 加入 Function.comp_def，冻结头部和数学假设未改。

## 4. 旧接口的完整语义覆盖与证据复用

A 的16个直接项目接口的完整实际类型、所有非定理完整值均已读完：RademacherS5Assembly.p/pathLaw/V；Shao.Path/prefixSum/closedStrip/energy/prefixSum_zero；RademacherCosine.law；RademacherStrictCube.strictP/strictEvent/strictSelfNormalizedEvent/actual_path_support/measurable_events；RademacherOriginalIIDTransport.sourcePath_identDistrib；OriginalIIDWindow.sourcePath。p 的 S5->S4->S3->S2 完整别名链另外读到真实有限乘积测度的 closedStrip 概率；law 的 halfENNReal 完整值为1/2。没有把 p 当作抽象谱函数。

B 的6个直接项目接口完整类型均已读完：actual_brownian_firstTerm、actual_brownian_eventually_positive、firstTerm、firstTerm._proof_1、firstTerm._proof_2、probability；两个非定理 firstTerm/probability 完整实际值已读完。另完整读取 library 中 U、traceSup、pathSup、rationalTime、probability 的定义链，以及 U_ae_eq_pathSup、U_le_ae_iff_fullStrip、probability_eq_fullStrip 的完整类型。U 是真实过程有理时刻绝对值上确界的可测版本，几乎处处等于 [0,1] 连续路径绝对值上确界；概率为 P.real {U<=s}，不是任意尾函数。

额外读取了承重的实际 Mathlib 接口：Nat.one_le_ceil_iff/lt_ceil/le_ceil/cast_sub/cast_le、Int.cast_abs、Finset.sum_bij；IdentDistrib.measure_mem_eq、measure_eq_zero_iff_ae_notMem、measure_congr；Measure.real、ae、iIndepFun；Metric.tendsto_atTop、Tendsto/eventually/comp/congr'/sub、eventually_lt_nhds；Real.log/exp 完整值及本证明使用的 log_mul/log_div/log_exp/exp_log/exp_sub/正性/连续性类型。使用点的非零、正性、指标界和可测集合前提均满足。基础库的既有证明资格复用，没有声称人工重审所有库递归证明。

A 的直接旧模块 source `230ebf25...`、成功对象 `930fa403fa9e927b4a48f047b10e06f4fc5510a7ae60e0fdd5a7e4b4b86ae105` 与 context211 已接受 CORRECT 收据的完整 source/object/stat 字段相合；当前 direct-input-reuse 的 before/after stat 相等。B 的三个 Brownian 源 pin 与 v71 PASS 源清单逐项相合，B2 对象 stat 也与 context211 当时合格的 BrownianFirstTerm 导入记录完全相同。按 streamlined-acceptance 复用这些资格，不重审旧证明、不重编、不读或重哈希旧对象。

## 5. 内核、公理、完整图与对象绑定

完整阅读成熟 audit-suffix.lean 的245行，并阅读 B 相对 A 的全部差异。审计的 difference 是整个源环境相对导入环境的差，不按声明命名空间筛选；moduleOwnership 和 foldStage2 分别求出并强制等于 difference。对每个实际 owned 调用 collectAxioms，拒绝 unsafe/partial/新 axiom；全部类型和值引用递归进入依赖图，opaque 值显式索取；递归图的任意 axiom-kind 也只许白名单。项目依赖按实际模块归属分类，直接旧接口全类型和非定理值导出。

本人重新比对本地 native/graph/per-root-axioms 的每个实际 owned 名称、完整类型、定义值、逐项公理集和类型/值引用，没有仅复制计数。两个单元各18份紧凑 manifest 文件的 SHA256/字节数全部独立匹配。Combined 精确为 Source 加一个 LF 加 audit suffix。完整结果见 independent-evidence-manifest.json。

服务器仅运行一次有界只读 Python 查询：读取已经保存的成功审计 JSON、校验保存图内部的可达性与引用完整性，读取当前成功对象 stat，并哈希实际被编译的当前 Combined 源码。没有重新读取任何对象内容，没有 Lean/解析器/构建/新 native walk，也没有下载原始图、日志或二进制。结果见 server-readonly-verification.json。

| 证据 | A | B |
|---|---|---|
| 首次成功 Lean PID/退出 | 857189 / 0，已回收 | 857674 / 0，已回收 |
| 实际用时 | 8.728193741291761 秒 | 16.18925354629755 秒 |
| 实际 owned/public/generated | 12 / 4 / 8 | 1 / 1 / 0 |
| 保存的完整类型和值递归图 | 21830，全节点可达、引用无缺失 | 61042，全节点可达、引用无缺失 |
| 项目声明/模块/项目导入 | 34 / 12 / 98 | 493 / 20 / 26 |
| 直接外部接口（含标准库） | 288，名称恰等于全部 owned 的外部直接引用 | 286，同左 |
| 内核选项 | skipKernelTC=false、autoImplicit=false、trustLevel=1025 | 同左 |
| 对象 SHA256（复用首次记录） | `50306e1e8c0190c9c53b3106fd722800c29167d29361f7cd99913e174c4a18ef` | `df930c2872285474275cc8c651ae0b908f356a09031eb259d7b8bc29f32924fa` |
| 当前成功对象精确 stat | dev64947、inode4860591、size329504、mtime_ns1792821466879326565 | dev64947、inode4860758、size195920、mtime_ns1792821619306904697 |

两个对象的当前 stat 都与 first-successful-object/execution-receipt/manifest 的原记录精确相等。所有 mtime_ns 都由 Python 整数保真读取和写出，没有经过 JavaScript Number。实际被编译的 Combined 哈希与本地当前 Combined、执行收据完全一致。

两个保存图的全部 axiom-kind 声明、每个实际 owned 的递归公理集均只包含 `propext`、`Classical.choice`、`Quot.sound`。所有图节点 safe 且 total。固定工具链 leanprover/lean4:v4.36.0-rc1、mathlib 807d3836b165983210ee2ecf3cd28f239436949c；成功命令 -M8192 -j4、CPU18–21、OQ4 单重命令锁。首败记录保留，A 的001/002及 B 的001均不是接受证据，自动生成 sorryAx 的失败输出没有混入最终合格公理集。

非阻断的显示标签遗留：A 的 owned-interface 首行仍是旧 sparse-critical-denominator 通用标签；B 的最终 logInfo 仍含 ORIGINAL_STRICT_BOUNDARY 字样。这些标签未用作对象身份依据。实际 mainModule 强制守卫、声明名、源哈希、对象路径和完整图均绑定正确当前单元。

## 6. 残余范围与交接

在上述精确版本和声明范围内没有未关闭的关键证明、语义或证据缺口。仍需后继单元把真实 Rademacher 自归一化严格事件与 h_n 的确定边界事件相接，并把弱谱在 a_n=ceil(h_n)-1 的结论与本次布朗平移配合，独立证明一般严格相位及误差趋零。特别是旧 S4_ALL 要求 m<=h'<m+1，整数 h_n=K 时不能用 m=K-1、h'=K 强行调用。

本审查不发 PR、不合并、不编辑 status/REGISTRY。唯一写目录为本目录。审查结束后释放该目录写权；pendingOperations=0、pendingTools=0、pendingLean=0、pendingServer=0。没有后台执行承诺。输入/缓存输入/输出/推理子集用量均未知，记录为 null，不估算订阅百分比。
