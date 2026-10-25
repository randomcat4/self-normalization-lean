独立完整审查结论：**CORRECT**，仅适用于 PR370 的 `Shao.Probability.SourceCircularWitnessMoment` 这一 M producer 的下述精确源码和声明。审查者为全新非作者上下文 `/root/circular_witness_moment_final_review`，按指定配置 gpt-6.1-sol / xhigh 使用 math-theorem；没有调用 math-ultra、再委派上下文、修改生产源码或运行新的 Lean / 公理检查。实际模型遥测、输入、缓存输入、输出、推理子集用量无法取得，均记 null。

这次结论来自完整阅读原文、全部 2,068 行 Lean 源码、十三个证明体、全部 83 个实际模块所有者的完整展开 TYPE，以及原审计程序、完整相关回执和成功检查日志。不是对作者摘要、名称清单或旧“qualified”标签的复核。逐个声明的实际名称、模块索引、类型字节范围、类型哈希、读取分块、来源位置和独立语义判断记录于 `coverage.json`。本报告不将 M 的成立扩展成 C2、C12 或 OQ56 根定理完成；survival、wallstrip 及原文下游交换/记录机制仍未由本 producer 支付。OQ3 的单独暂停和原 C1 immutablev85 已完成状态均不受本报告改变。

**精确对象。** 审查源码为 `drafts/c2-circular-witness-moment-production/SourceCircularWitnessMoment.lean`，97,715 字节、UTF-8、LF、无 BOM，SHA256 为 `838e7f719f54ef5a1085d45af2ea379ddf56353ae0c264d0db6ce0b3f1692667`。PR370 head 为 `d5a3871b4df360e7a5e6399c4eb3c60f754bb6a6`，tree 为 `823b07e4060e24ab9915caf48e3ce49d570e46e4`，提交 parent 为 `440b026e8caba7f76e6bb1cb7e9be6c3e641de16`。只读服务器核对了原生 Git commit/tree 的物理 SHA1、提交中的源码 blob、工作树源码和干净状态；相对 parent 只新增这一文件，共 2,068 行。读取 PR 时其状态为 OPEN，head 相同，远端 main 已前进，读到的 baseRefOid 为 `b4cbb754ddaaeeff036f676fd680c313d56a143b`。本审查没有合并、改写或发布任何内容。

作者的封印链未被改动。`RELEASE.json` SHA256 为 `dfeb95453c89317fa352da121c7aa4dd85ae9043b9c15d5cbe572144343ec7bb`，`final-receipt.json` 为 `3ec838871ae6dc1d2d95dd1f5fded22f3c7e09784445c587195f5594a66f3b7c`，`binding-manifest.json` 为 `8ce6df5a86d0a757d95526dbb14670dcc06d3fd8d4038fc1d4c1f8aef33b731b`。独立脚本逐一核对 283 个 payload 的字节数与哈希，加 manifest、final receipt、RELEASE 共 286 个封印文件。作者已释放源码和执行权，inFlight 为空；本审查只写自己的审查目录。

**原文到实际声明。** 唯读原文 `C:/game/shao/current/c12/supplement.tex` 的 SHA256 为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。完整阅读了 5197–5252、5295–5350、5535–5550 三段。5197–5252 中的循环见证是对真实循环弧的 `S_N - 2 × 弧和` 取最大值，含空弧、整弧，并约定 N=0 时为零；同段 small-moment 结论的主二次系数是 .5010005。5295–5350 的加权集中、记录与交换论证及 .503 / .506 预算，5535–5550 的 ballot、较低命中和好能量/权重条件，只用来辨别本 producer 的消费边界，未记为本模块已证结果。原文 5197–5217 的其他循环不变性、Lipschitz、record 身份也没有被这一概率矩定理自动一并宣称完成。

公开 Lean 定理先量化 `∃ C : ℝ, 1 ≤ C`，再量化概率律 ρ、B、N、θ。ρ 是实数 Borel 概率测度，输入仅为 B>0、ρ 几乎处处 |z|≤B、真实积分 ∫z=0、∫z²=1。β 是字面 `∫ |z|³ ∂ρ`；样本测度是字面 `Measure.pi (fun _ : Fin N => ρ)`。L 是字面的所有真实模 N 循环弧的有限上确界，N=0 分支显式为零。其输出为真实 `Measurable L`，并在 `0 ≤ θ` 且 `θ * B ≤ 1/10` 的闭域上同时给出真实 `Integrable (fun a => exp (θ * L a)) P` 和

\[
 \int e^{\theta L_N}\,d\rho^N
 \le C(1+N\theta^2)
 \exp\!\left(\frac{1002001}{2000000}N\theta^2
                 +C N\theta^3\beta\right).
\]

`1002001/2000000 = .5010005` 是精确有理数，不是小数近似。实际 TYPE 中的全部实例、隐式参数、let 代入及嵌套合取均已逐字阅读，确认没有 HasLaw、任意 filtration、目标 moment、survival 或 concentration oracle 作为额外前提。可积性也不是用“不可积时 Bochner 积分为零”来取得数值界。

**冻结与许可。** 当前全部十三个头和 41 个字面 let 与 Root 冻结文本精确相等：原九个 private 共 31 lets、公开头 3 lets，后来增加 canonical martingale 4 lets、circle-prefix 0 lets、adjacent-windows 3 lets。独立比较还确认原九个数学头在 context V3 中未变，公开 V1、V2、V3 数学头相同；上下文增加 import 没有改变前提或结论。

原批次 Root 冻结回执时间 06:27:33.296706 UTC，保留其独立观察“正式源码不存在”；作者于 06:30:42.819577 观察后，06:30:42.820577 首次写入的 source01 哈希与档案一致。canonical-martingale 的 Root 冻结 07:03:43.446560，含 07:03:15.331639 实际源码中新名称不存在的观察；作者观察 07:09:34.716858，首次 body 档案 07:10:42.747098，原 source06 字节哈希相符。circle-prefix 与 adjacent-windows 的 Root 冻结分别在 07:09:58.576558 和 07:43:08.908352，其回执明确保留当时作者 body-zero 的自述；对应作者观察在 07:14:28.561061 和 07:44:15.688472，仍记 bodyWritten=false，原首次 draft 哈希均绑定。后两条是 Root 冻结加作者 body-zero 记录，报告没有把它们改称独立机器观测，也没有使用 mtime 证明先后。

`cwm_linear_tilt_product_density` 消费已接受的私有 `er_pi_tilted`，有精确许可 `coordination/circular-witness-moment-context-v3-private-consumption.json`，SHA256 `fd57429b5754a2cd5174c18ab59919b3adf9a99790f4ce9ca3f2d34c88f57c01`。授权源是 `EndpointRelativeError.lean` SHA256 `e9624ff50b79c8e41b749e4b6851870129797a38c692b809a90e81cda8699223`，原对象 SHA256 `d151025f575332bba21c3fe1dbf50bc30fca5715dce069692c515d2f32398804`，本次只读核对服务器对象和原已接受审计日志，并完整读取实际私有 TYPE、直接消费的原证明及许可。实现通过 `Lean.mkPrivateNameCore` 和 `Lean.mkIdent` 按正式模块名构造私有名字，没有在源码中硬编码字面私有 `.0` 名字。该私有 theorem 是一般有限乘积指数倾斜的等式，不是 M 或 survival 结果；当前使用满足真实逐坐标 exp 可积前提。许可于密度 body 之前被观察，首次密度源档案的精确哈希也已核实。

**十三个证明体的独立判断。** 下列行号均指本次精确源码；每项都同时核对了原文所需语义、源码证明和最终实际 TYPE。

1. `cwm_log_mgf_taylor`，19–142。先选与律、B、参数均无关的 C≥1。用已接受 bounded quadratic tilt 接口的真实密度/矩可积性，在 s=0 时获得所需原律矩；由单位二阶矩与三阶矩不等式得到 β≥1，由 |X|≤B 得 β≤B，从而 B≥1。`|t|B≤3/5` 保证所有 Taylor 输入合法，得到正 normalizer、Jensen 型 c(t)≥1 和 `|c(t)-1-t²/2|` 的三阶控制。令 u=c−1≥0，以 `u-u²≤log c≤u` 和 u 的二次界吸收 log 的余项；t⁴ 通过 |t|≤.6 与 β≥1 归入 |t|³β。这里没有新增高阶矩假设，最终是绝对 log 误差界，能在正负参数使用。

2. `cwm_canonical_exponential_martingale`，143–324。对任意真实有界概率律 ν、q，不要求 ν 中心化。c 是其正指数母函数，P 是 ν 的真实有限乘积，S k 是所有 i<k 的坐标集，Z k 是这些坐标上 `exp(q a_i)/c` 的乘积。证明构造的是坐标限制映射 comap 的真实 prefix filtration；可测/强适应、所有 k 的可积、非负和真实积分一均在证明体中建立。下一坐标与既有坐标集合不交的原生独立性给出所有前缀可测集合上的 set-integral 相等，再由原生 martingale 构造定理得到鞅。k≥N 时 S 饱和，证明实际处理了停住后的所有自然数索引；N=0 也是空乘积一。没有传入任意 filtration 或任意已知鞅。

3. `cwm_finite_exponential_maximum`，325–509。输入为 0<r<q、实际有界 ν。对 H=maxWithZero 的所有 0≤k≤N 前缀，若 H≥u，指数鞅在某 k 达到 `exp(q u-D)`，其中 `D=N max(log c,0)`。使用 pinned mathlib 的非负 submartingale 闭阈值 maximal inequality，及终值的真实积分一，将闭尾控制为 `exp(D-q u)`。再用可测闭尾层积分得到 `E exp(rH) ≤ 1 + r/(q-r) exp D`。在层积分前已由 AE 有界 H≤NB 证明 exp(rH) 真正可积，积分转换不依赖默认零值。采用闭事件 `{u≤H}` 的接口，对原子概率律也合法；r<q 明确保证尾积分收敛。

4. `cwm_circular_arc_prefix_formula`，510–564。N>0 时对每个 i:Fin N、k:Fin(N+1) 的真实模 N 弧，分别证明 i+k≤N 的普通前缀差和跨 N 接缝的首尾和。有限索引双射与周期延拓处理模运算；k=0、k=N、i+k=N 的边界均在量化域内。没有删掉空弧、整弧或接缝等号。

5. `cwm_path_extrema_geometry`，565–869。L 是真实循环弧见证；A、R 分别是有序前缀上升与回落的有限上确界。证明逐项建立可测性、非负和 sumabs 上界，再建立 `L=max(S_N+2R, 2A-S_N)` 和 `R(-a)=A(a)`。从弧到两种前缀差的一侧界与从实际极值对到普通弧/补弧的反向界均已支付，补弧的 u=0、v=N 和包裹索引单列处理。有限集合非空及有界有真实见证；N=0 分支直接化为零。这一几何等式正是后续反射合并的同一路径桥梁，没有把 L 替换成较易估计的其他对象。

6. `cwm_linear_tilt_product_density`，870–982。ν 是实际 `ρ.tilted (θ*id)`，不是额外给定的新律。利用许可的有限乘积倾斜等式，证明 ρ^N 按 θS_N 倾斜等于 ν^N；指数 partition function 确实是 c(θ)^N。对任意原律下 genuine Integrable 的 g，AE 密度在有界支持上受常数控制，因而 g 在倾斜律下以及 g·exp(θS_N) 在原律下均可积，得到真实密度积分恒等式。证明显式使用 c>0/c^N≠0，有限产品和空产品也覆盖。前提没有提供欲证 M 或 drawdown 矩。

7. `cwm_tilt_future_negative_maximum`，983–1100。对 θ>0，实际倾斜律的负向最大值以 r=2θ、q=2.001θ 使用有限最大值引理。负向 normalizer 等于 `c(-1.001θ)/c(θ)`；原律中心化和单位二阶矩只在原 c 的 Taylor 界中使用，绝未假定倾斜后漂移为零。精确二次差 `((1.001)^2-1)/2=2001/2000000=.0010005`；三阶误差吸收为 4Kθ³β，正部 `max(log cn,0)` 被合法上界。`r/(q-r)=2000` 归入统一常数。原 θB≤.1 确保正负 Taylor 参数均在 .6 域内。

8. `cwm_tilt_short_block_range`，1101–1284。对块长满足 Nθ²≤1.01，实际倾斜路径的局部 range 用 H(a)+H(−a) 控制。以 r=4θ、q=5θ 分别估计正负最大值，对应原律参数 6θ 和 −4θ，闭 θB≤.1 正好满足所需 .6 Taylor 域，等号未排除。log-ratio 的二次项上界 18θ²、三阶项上界 217Kθ³β，再由 θβ≤θB≤.1 和块长条件成为统一常数。Young 不等式把 exp(2θ(H+ + H−)) 控制在两个 4θ 指数之和的一半，不要求正负最大值独立；可积性由这一真实支配给出。

9. `cwm_drawdown_block_pointwise`，1285–1408。m>0 时 count=(N+m−1)/m 是实际截断时间块数，块起点 im、终点 min((i+1)m,N)。从 R 的一个实际极值对 u≤v 出发，选择 `min(u,N−1)/m` 所在块，分 v 在块内和块终点之后两种情况，得到 R≤localRange+future，因此 exp(2θR) 被所有块对应指数乘积的和控制。u=N、最后不足 m 的块、闭端点、θ=0 都由量化/分支或非负性处理。这里是逐点几何，不以独立性偷换。

10. `cwm_iid_adjacent_windows`，1409–1519。对任意 lo≤mid≤N，窗口 W1_j=a_(lo+j)、W2_j=a_(mid+j) 的真实 map law 分别是 ν^(mid−lo)、ν^(N−mid)。通过坐标注入、有限乘积坐标独立和两个互不相交索引集合，证明真实 IndepFun，再逐个合法 k 证明窗口前缀和等于原路径前缀差。没有作为输入假设窗口有某个 law 或独立性。空窗和 N=0 允许，所有 subtype/Fin 索引的生成算术义务均在实际 TYPE 覆盖中。

11. `cwm_tilt_drawdown_moment`，1520–1802。θ>0 时取 m=ceil(1/θ²)，证明 1≤mθ²≤1.01；由 β≥1≤B 得 θ≤.1。实际每一块的 localRange 由 W1 的正负最大值支配，future 由 W2 的负向最大值支配。上一步真实 map law 和相邻窗独立性使每一项的积分分解；两因子可积和乘积可积均单独建立，然后消费短块界和未来界。future 长度≤N 的指数预算合法单调上推。count≤1+Nθ² 由 count·m≤N+m 和 mθ²≥1 得到，确实支付原文的多项式因子。N=0 被显式独立处理。R 的指数在使用积分不等式之前已有有界支持可积证明。

12. `cwm_first_exponential_piece`，1803–1932。原律下 g=exp(2θR) 先有 genuine Integrable；密度等式将 `exp(θS_N+2θR)` 的积分写成 c(θ)^N 倍实际倾斜 drawdown 矩。log c 的 1/2 主项和 drawdown 的 2001/2000000 主项精确相加为 1002001/2000000，两个非负三阶误差统一吸收入新的常数；常数在 law/B/N/θ 前固定。θ=0 单列常数函数，不使用 θ>0 引理或除 θ。输出同时有真实可积性和界。

13. `actual_circular_witness_small_parameter_moment`，1933–2066。对原律反射 pushforward，证明有界支持、中心化、单位二阶矩和 β 不变；真实负路径的 product map 等式将反射第一片段搬回原 ρ^N。借 `R(-a)=A(a)` 和几何 `L=max(S+2R,2A−S)`，exp(θL) 被两个第一片段指数之和支配。两片段都已可积，故目标也 genuine Integrable，然后积分相加并选 C=2C0；该 C 与律、B、N、θ 无关。最终公开头仍是实际字面 L，不是仅某一个有限片段恒等式。

**全部实际 TYPE、VALUE 和传递公理。** 原完整类型文本 799,417 字节，SHA256 `960d2bbaced3bf0d3e65e979cea2b78532b0f853c450a1907784c603906a2f62`；其中 83 个纯 full_type 合计 781,882 字节。按原 UTF-8 字节、行边界切成 39 个连续分块，全部逐字送入并完整阅读，未替换实例、复用模板、抽样或按相同类型去重。曾经合并读取 chunks 3/4 以及 17/18/19 时有工具输出截断，已分别重新完整阅读 3、4、18；最终 0–38 无缺口。coverage 中逐项保留原文本的半开字节范围、SHA256 和相交 chunk，另有连续覆盖和原 JSON/TXT 重构的确定性校验。

实际 owner 集来自 `env.constants.toList` 加真实 `env.getModuleIdxFor?` / `env.header.moduleNames` 判定，未按命名空间前缀过滤。独立核对 owner-index、owned-audit、83 条原 audit log TYPE 和导出 JSON/TXT 的集合、kind、模块索引及字面类型全部相同：1 public、12 source private、70 generated，合计 83，全部 theorem。70 个生成项的每个实际 TYPE 均完整阅读，逐项映射到相应前缀索引、补弧、窗口注入、分块端点或有限集 simp 的实际源码义务；不是仅列其名字。完整 owner 索引中非 theorem 为零，所以不存在被省略的非定理 VALUE；审计代码若遇到非 theorem 会打印实际 VALUE 或失败，原完整日志也无 DEFINITION_VALUE 分支。

完整读取原 `SourceCircularWitnessMomentOwnedAudit01.lean`，确认其对每个实际模块所有者调用 `Lean.collectAxioms` 作递归公理收集，并在 whitelist 外立即失败；输出设置 pp.all / pp.deepTerms / pp.proofs，具有足够 pp.maxSteps/maxRecDepth，实际输出无省略符。83 项实际传递公理集均包含于且仅允许 `propext`、`Classical.choice`、`Quot.sound`；本模块源码未出现 sorry/admit、新 axiom、unsafe、native_decide，也未增加全局 def/abbrev/instance/opaque。数学证明没有通过 Lean 元编程插入未核验命题：唯一名字解析操作得到已接受私有 theorem，最终实际 proof term 仍受原 kernel 及递归 AX 约束。

**复用的服务器证据。** 原 whole23 的 source23 与当前源码哈希相同；producer23.olean 6,324,848 字节，SHA256 `c0347fab9269733944e77d612dcdecae186edb18cc9ed465822a6b281f5f0c10`，工作树目标对象也是同一哈希。原 kernel 日志 SHA256 `10be202c513defefd8fd5e2f0c29d3117c5e38c131c481f5100855b5aecd037f`，audit 日志 SHA256 `9cfb582b3507a1ed5d0f96b4084ba92105624924bc986fae53f8715e8413ae91`。本次只读服务器核对了这些原文件、原核查脚本、JSON、rc 和运行状态。kernel-rc23 与 audit-rc23 的字节都为 `0\n`。成功 kernel 日志完整阅读，无 error，含非致命 lint/deprecation 提示。原脚本整体最终退出 kernelrc，因此没有把脚本 rc0 自动当成 AX0，而是独立核实保存的 auditrc0 及全部 audit 内容。

原调用在同一个 root-heavy.lock 内以 CPU40–43、`-M8192 -j4` 编译 source23，再将当次成功对象无覆盖地放入 import 目标并进行全 owner AX。运行状态为 COMPLETED；原 23 次实际 kernel 尝试中的自然失败、部分成功以及锁 busy75 记录全部留在生产封印中，只有 whole23 的全源码成功计入本结论；没有将旧 partial 或 whole22 的 rc1 记为完整证明。审查没有重放失败、未知请求或成功检查。

版本为 Lean v4.36.0-rc1、mathlib commit `807d3836b165983210ee2ecf3cd28f239436949c`。五个直接项目依赖 `FinitePath`、`MeasurablePath`、`BoundedQuadraticTilt`、`AuxiliaryEnergyCentered`、`EndpointRelativeError` 的服务器源码和本地 curated 源均与已接受 v91 receipt 中精确 source map 相同；v91 receipt SHA256 `a9082daa66f1675e5643e75e623531d5f493b868785fc7f85a3c7aa1a310ba85`。完整阅读了当前消费的关键接口及其必要定义/直接证明上下文，包含有界 tilt/Taylor、三阶矩下界、真实 prefix/maxWithZero、finite-product tilt，以及原生 maximal inequality、layer-cake、实际坐标独立、相邻窗 map/积分乘积和 martingale 构造。其他已接受旧模块的完整证明审查按精确哈希复用。

成功日志中的 mathlib local-changes 提示不能单独当作 pin 改变或证明通过依据。对应 Root 的原 cache 回执明确只有 OptionalStopping 缺失对象被补齐，2730 个 pinned closure sources 未变、35477 个旧 artifacts 未变、旧 producer 重编译为零、没有 full mathlib rebuild。本次只读核实 pinned OptionalStopping 源 SHA256 `e058839e6396834220f8caea0a36fb8ae7fb09331e0ebaa2607b8388191b0dcd`、对象 SHA256 `e3d36f3fe3f06c0496a95a1577c44415d368f3d579db913ba1ff57e56f1775aa`、原 preflight 和 compile02 receipt 的物理哈希。也记录了七个消费的原生 mathlib 源哈希；未复制 10MB preflight 或二进制到协作区。只读额外接口抽取曾因 named argument `(m := ...)` 提前截断，已改为完整字面 ambient/header 行 300–330 阅读并修正自己的工件；这不涉及数学源或原证据改变。

**边界和限定。** 闭 θB≤.1、原子律、N=0、θ=0、空/整循环弧、最后短块、空相邻窗和倾斜后非零漂移均有上述具体证明路径。没有要求原律连续、无原子、对称或 tilt 后中心化；反射是证明中的 pushforward，而不是输入的对称性假设。β 是真实三阶绝对矩，单位二阶矩和有界支持保证其 finite 及 1≤β≤B。所有主常数先于 law/B/N/θ，短块选择只依赖 θ，不改变最终统一量化顺序。

本精确版本的原文 M producer 已获得完整独立数学/Lean 源到声明审查，且复用的原 kernel 与所有实际 owner 递归公理证据有效。未发现需改源码的数学错误、声明偷换、未覆盖的实际 TYPE/VALUE、超 whitelist 公理或阻断性证据缺口。最终判断为 CORRECT。Root 后续接受与集成仍应核对这些精确哈希、接口交互和本报告范围；源码/proof/依赖如发生数学改变，只对受影响证据重新门控。本审查不执行集成、不改原根 OPEN 状态、不解除 OQ3 暂停。
