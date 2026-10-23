STATUS: CORRECT

Shao.Probability.SourceLindleyRegulatorFirstMoment 的两条冻结公开声明、全部 338 行最终源码/证明，以及实际归属该模块的 27 个定理均通过本次独立完整最终审查。没有关键缺口，没有隐含前提变更。此结论只覆盖实际循环调节量和一阶矩，不关闭二阶矩、生存概率、能量倾斜或原 C1/C2。

审查者 /root/common_regulator_first_review，fresh gpt-6.1-sol / xhigh，从未编写本模块。遵循 math-theorem、AGENTS.md 与 streamlined-acceptance-current.md。仅写本 MD 和同名 JSON；本轮 Lean 命令与公理审计命令均为零，复用精确成功的作者服务器证据。

## 精确版本与冻结声明

- 单文件提交：ea081d727abfd0c0171943da924d464ba9d0b56b；树 b2dc0b6af92b3d1602fb2cfb99f0624689c438df。
- 源码 SHA256：c2dcdb409763ba20386e064e6a8ed612bf060677da80442c727289ffc7ab3108；15591 字节，338 个 LF，UTF-8 无 BOM、无 CR。
- 本地草稿、服务器工作文件、提交 blob 与 kernel-006.source.sha256 完全相同。提交只改变 Shao/Probability/SourceLindleyRegulatorFirstMoment.lean；工作树的其他未跟踪文件不属于本次提交。
- freeze SHA256：2740f24a4b11b7ff1b641c8fb0042448534880ff3cc609f557104ad1fabb3232；candidate：da384cb9b713b16ca9490237cc5284d9cd1416d2bd09bf6233a2bbdbb06a2b2b；contract：ae38511098aa540d3ab3f16cf14f88d4623e660627eb9055b1c3a36a454b9ec3。
- 作者 receipt SHA256：570c15dcb2a21f2ad90e3b9f896576c9911c7c284da96f4564628e681ce0b544；writerReleased 与 heavyExecutionReleased 均为 true。

完整逐字比较了 candidate 与最终两条公开声明，二者完全相同。令 N=n+1、P=pi(ν)、μ=∫a dν、V=Varν(id)。第一条对所有 n≥0 和真实 Path(N) 证明所有 Fin(N) 循环旋转的真实末次 lindleyRegulator 之和等于 max(-prefixSum a N,0)。第二条只假设 ν 为实数概率测度和 ∫a² 可积，证明真实末调节量的 L1、N·E U=E max(-S_N,0)，以及 E U≤sqrt(V)/sqrt(N)+|μ|。没有中心、对称、正方差或隐藏尾界假设。JSON 保存两条完整声明及逐 owner 类型哈希。

## 来源到陈述

完整读取原 supplement.tex LF2137–2184（整文件 SHA256 b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd）、完整合同及完整冻结文本。实际被完成的是 LF2139–2174 的循环恒等式与第一矩界；LF2176 起的第二矩论证已读但不属于本结果。

实际 Path 是 Fin N→ℝ，prefixSum 是前 N 项之和。消费的 Lindley 递推为 W_0=0、W_(k+1)=max(0,W_k+a_k)，实际 regulator 为 max(-(W_i+a_i),0)，不是独立支配变量。lindleyDelta 的真实定义也以此 regulator 作反射位移，未被改写。用 k+j 的 Fin 加法正好得到来源的循环旋转；0 基索引与来源 1 基索引只相差记号。n=0 是源时间 i=1；任意 i≥1 都由 n=i-1 覆盖，没有遗漏首步。零总和、重复增量、相等前缀最小值均保留。

## 完整证明审查

L24–126 的每个私有辅助证明均已逐行核对。prefix_step 正确分解有限前缀；state_nonneg 与 state_ge_sum 使用实际递推。state_cons 归纳证明 W(x,a_tail)=max(x+tailSum,W(tail))；当完整和≤0时，该最大值的总和分支不超过非负尾状态，于是 state_remove_first 可以删首。state_prefix 只消费已接受真实前缀接口。rotate_total 用真正的 Equiv.addRight；rotate_tail 逐坐标验证相邻循环的尾与前缀，空 Fin n 分支显式处理。regulator_balance 是真实递推的代数恒等式，包含 W+a=0。

L129–178 的循环定理分支完整。总和≥0 时，每个循环的 W_(N-1)+a_last≥S_N≥0，因此每项 U=0，总和为零。总和<0 时，设 W_j 为循环 j 的末状态，删首与 rotate_tail 给出循环 j 的末状态等于循环 j+1 的前 N-1 状态。因此实际递推给出 U_(j+1)=W_(j+1)-W_j-a_j。对真正循环置换 j↦j+1 求和，所有 W 项相消，剩下 -S_N。没有选择最小点，也没有排除 ties；N=1 的循环仍成立。

L180–200 的可测性和支配界证明了实际 U 可测且 0≤U≤|a_last|。L202–336 的概率证明先从唯一矩假设得到 ν 下 id∈L2，再通过真实乘积测度评价映射得到每个坐标的 L2、真实同法则与独立性。U 的 L1 由绝对末坐标支配实际支付，随后才使用旋转的同法则得到每一旋转的 L1、相同期望和有限求和积分交换。所用 Equiv.addRight j 是实际坐标置换；iid_observable_identDistrib_perm 的全部可测、独立、相同边际条件均由 canonical product law 提供，因此这里确实实现了该循环映射的测度不变性，而非假设某个替代耦合。

随后实际 S_N 的 L2、均值 Nμ 与方差 NV 均从真实坐标和得到。核对了固定 mathlib 的 variance_sum_pi 完整接口：概率边际及各坐标 L2 正是这里已证明的条件。variance_eq_integral 与 variance_eq_sub 的可测/L2 条件也齐备。对 |S_N-Nμ| 用方差非负得到 (E|S_N-Nμ|)²≤NV，进而 E|S_N-Nμ|≤sqrt(NV)，这是有效的实数 Cauchy–Schwarz 论证。负部亦由 |S_N| 支配获得真实 L1，再逐点支付 |Nμ|=N|μ|。最后只除以正的 N 和 sqrt(N)；sqrt(NV)=sqrt(N)sqrt(V) 得到冻结的常数 1 界。未除以 V 或 sqrt(V)，所以 V=0 保留。非零均值和非对称分布完整保留。

## 服务器证据复用与旧接口

服务器 workspaces/common-centered-characteristic-v44 的 HEAD、tree、源码、目标 .olean/.ilean 与 receipt 完全匹配。kernel-006、owned-types、owned-audit 的退出文件均为 0。已完整审查 receipt 中三个原始执行字符串：Lean 在 flock 与 taskset 下执行，没有管道掩盖状态；紧随命令的 rc=$? 保存并返回状态。kernel 日志只有已接受稀疏共享 mathlib 视图的 local-change warning，没有错误。既有 kernel-001…005 开发失败保留，未当作成功证据，也未重跑任何成功项。

| 证据 | SHA256 |
|---|---|
| kernel-006.log | fba92798401e89109ac7d84c8cea11527992a1f6b153b3c1d2aada0eebf025a2 |
| owned-types.log | cf6c58d8c7fea92355f7ff6823a7376b111946cb76cf233f2a8239ea7d4a9931 |
| owned-audit.log | ac7c401218921ccbe39b0d31676f9455ceb629b6a58853d0ce7d99282d7f85b9 |
| owned-audit.json | d9bd22742212fc79c9bfc8c78ebdff9409e72edb4f96337d267e249c122730ba |
| 目标 .olean | 614998314b71f96ba81982605e12742a889cad3447c9e22ec3ef89ffdbeeec06 |
| 目标 .ilean | ae9e4cd6271c63a85d94a3206b9fd59b2d7c0e39a075e3b05cafff5d58df973a |

实际 Lean pin 为 leanprover/lean4:v4.36.0-rc1，manifest 与实际 mathlib HEAD 均为 807d3836b165983210ee2ecf3cd28f239436949c；packages 解析到既有 shared-v34/packages。既有命令使用 root-heavy.lock、CPU10–13、-M8192、-j4、autoImplicit=false。

只核对旧输入完整消费接口与精确哈希，未重审其旧证明或重编译。FinitePath、Lindley、LindleyTelescoping、FiniteIID、FiniteIIDMoments、MeasurablePath 六个源码与接受 v51 的 source map 相同；这六个当前 .olean 也逐一与 integration-bearing-v51 的已接受对象相同。v51 receipt SHA256 为 1a963ea31c6f42708d96531fa183e007064fd29e21289866346d2694d0b6abdb。全部源码/对象哈希保存在 JSON。

## 全部实际 owner 结论

完整读取 pp.all 导出的 27 个实际类型，类型导出名字集合与 getModuleIdxFor? 选出的全部 owned audit 名字集合严格相同；无截断、无新 definition。完整审查 collectAxioms 递归审计器与每条实际结果。所有 owner 均只依赖 propext、Classical.choice、Quot.sound 的子集。生成的 Shao.lindleyState.eq_1/eq_2 虽不是新增手写声明，其实际模块归属在此，也已包含，不能漏计。两条手写公开 theorem、12 条手写 private theorem、11 条 private 生成证明、2 条非私有递推生成 theorem 合计 27。下表 P 表示 _private.Shao.Probability.SourceLindleyRegulatorFirstMoment.0.Shao.Probability.；A 表示全部三项白名单公理，B 表示 propext 与 Quot.sound。

| 实际 owner（P 前缀如上） | 结论 | 公理 |
|---|---|---|
| Pstate_cons._proof_1 | CORRECT | B |
| Shao.lindleyState.eq_2 | CORRECT | A |
| Pprefix_step._simp_1_3 | CORRECT | A |
| Pprefix_step | CORRECT | A |
| Pregulator_bounds | CORRECT | A |
| Protate_tail._proof_1_1 | CORRECT | B |
| Protate_tail._proof_1 | CORRECT | B |
| Protate_tail | CORRECT | A |
| Pstate_remove_first | CORRECT | A |
| Shao.Probability.iid_lindleyRegulator_last_first_moment | CORRECT | A |
| Pstate_cons._proof_1_3 | CORRECT | B |
| Pstate_nonneg | CORRECT | A |
| Pstate_ge_sum._proof_1_1 | CORRECT | B |
| Shao.Probability.lindleyRegulator_cyclic_sum | CORRECT | A |
| Pmeasurable_state_actual | CORRECT | A |
| Pmeasurable_regulator_actual | CORRECT | A |
| Pstate_ge_sum._proof_1_2 | CORRECT | B |
| Pstate_ge_sum | CORRECT | A |
| Pstate_cons | CORRECT | A |
| Pstate_cons._proof_1_4 | CORRECT | B |
| Pmeasurable_state_actual._proof_1_1 | CORRECT | B |
| Shao.lindleyState.eq_1 | CORRECT | A |
| Protate_total | CORRECT | A |
| Pprefix_step._simp_1_1 | CORRECT | A |
| Pstate_prefix | CORRECT | A |
| Pregulator_balance | CORRECT | A |
| Pprefix_step._simp_1_2 | CORRECT | A |

每个 owner 的完整名字、实际类型 SHA256、同一源码 SHA256、递归公理、完整阅读标记与独立理由均逐条写入同名 JSON。生成证明逐条核对为有限集合成员等价、合法索引算术或真实递推方程，没有隐藏数学前提。源码禁止构造扫描为空：无 sorry/admit/新 axiom/unsafe/native_decide。

本结果是原文第一矩论证的忠实形式化，不作新颖性主张。原始二阶矩界需要的 source-law survival/concentration、能量倾斜及其矩/漂移支付、完整 regulator lemma 与原 C1/C2 仍 OPEN。审查任务已完成，审查者释放槽位；根整合可以复用本精确版本审查与既有成功服务器证据，仅对实际未覆盖的交互风险补查。
