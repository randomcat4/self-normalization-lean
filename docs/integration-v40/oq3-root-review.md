# v40 OQ3 原始根 A 独立验收

STATUS: CORRECT

critical_gaps: []

审查者：`/root/v40_oq3_root_accept`。仅拥有本报告及同名 JSON；未改作者源码、旧模块或旧票，未运行 Lean、合并或创建子实例。服务器操作通过 `tools/server.py` 只读且限 CPU10–13；未触 CPU0–9/80GiB 外部工作。

## 1. 结论与可正式关闭的范围

建议 root 正式接受 PR161 并将 **root-contract/R1 中完整 A：一个固定实数 iid 律、固定 x0 的真正联合非格点鞍点余项反例** 标为 CLOSED。此建议基于原始题目、完整新源码和所有实际所属类型的独立语义/证明核查，并已绑定统一 v40 PASS 门，不只依据聚合接口数或先前 CORRECT 标签。

精确结论：存在一次选定的有界中心化概率律 P、同一 q/w、固定 x0=√q/4∈(0,1/2)，P(X>0)>0，P 的全部质量位于 1≤|X|≤4+√10；原 P 的 (X,X²) 真正联合非格点且有逃向无穷的频率使特征函数模趋 1；其实际全域 logMGF 有指定梯度和完整 Hessian，Hessian 正定，指定正则鞍点是全正能量弱尾域上 EReal Legendre 率的唯一全局极小点；λ0、λ1、vCorr 都严格为正。对同一 P 的真实有限产品概率及实际自归一化比值尾事件，存在严格递增正样本量列，使 √n(Cn−vCorr⁻¹)>J；且标准 `Asymptotics.IsBigO atTop` 的 n⁻¹/² 余项命题为假。

本票正式关闭的是上述 **R1/root-contract 所冻结的修正常数 vCorr 版本的完整固定 x 反例**。它不是 ICM 印刷常数 v 与 vCorr 相等的证明，也不是整个 OQ3 的所有部分完成。B/C/D、随 x 变化的一致展开及最弱条件问题不因本票关闭。

## 2. 冻结版本与来源

| 对象 | 精确绑定 |
| --- | --- |
| PR | https://github.com/randomcat4/shao-lean/pull/161 |
| 作者 head / tree | `293d3394546eaec284d39b86ed1f6449af7f70c8` / `104e9e1c3e49cec5372ff5eef9d8c0937591210a` |
| parent | v39 accepted head `59a531b89eff7c11e4fc53583067f2cd3b53a517`，直接父提交；tree `43577d0d66de8325a756c9ac25e43e53809c3525` |
| 新源码 | `Shao/OQ3/SourceCounterexampleRoot.lean`，209 行/11189 字节，SHA256 `13b3da0fa68dd12ffdc8357dae609629d8a95219d4e205417e92899493f37a59` |
| scope | `69ed5bbb5bccadc3b552c75f09b090f775164d4eb0fe9eaa8a1cf0f65f59308b` |
| 原文 | `supplemental/icm2010/icm01.txt`，SHA256 `9024791b6e01b2254a3e9baca54d555a1591ed58d30a9de93cf1a9cf2f5d882d` |
| R1 | `current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` |
| 根契约 | `drafts/oq3/root-contract.md`，SHA256 `a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a` |

原文按 **LF** 计行：8926–8949 定义实际 K、鞍点、Λ0/Λ1/Δ；8951–8967 为 Theorem 3.1、(3.3)/(3.4)；8968–8978 为 Open Question 3、(3.5) 和随 x 一致性问题。`str.splitlines()` 还切分 PDF 换页控制字符，会把 Theorem 3.1/OQ3 定位为 9126/9143，不能混用该口径。根契约旧 LF 定位正确。

R1 §§1–4 给精确补偿构造、同 q 的逆倾斜原律、全尾域极小性、联合非格点和逃逸共振；§§5–8、(19)/(20)/(25)–(31) 给固定阶段全层常数、正 h^(3/2) 差距和选见证后再选未来质量的同律传递。已从这些原源核验 A 的量词，而非先从作者报告推定 A 的范围。

## 3. 新根逐项证明核查

### 同一个实际 P，所有必要性质均生产

源码67–144的公开定理无 caller 前提。外层一次 `∃ q w`，先输出 1<q<103/100、每个 w_i>0 和同一 w 的四个真实 `HasSum` 约束，再定义 P=`originalMeasure sourceEll w`。样本量 n 只出现在该量化之后的同一 `Measure.pi (fun _ : Fin n => P)` 中。

145–163只调用一次存在生产者 `exists_source_fixed_law_not_isBigO` 取得最终 q/w/P，然后将同一个 q/w 和 hm 传给两个普遍 canonical 定理。未在率、Hessian、尾概率或子列处重新选择律；未假定正率、唯一极小、LLT、余项失败或 hcont。

`sourceEll=log(31/30)`；`fixedAtom` 使用基点 (-1,1,4+√10,2) 和新增原子 4+√(10−2^−(j+1))，是 R1 从 j≥1 开始的零基重索引。四特征为 (1,X²−4X,X exp(−ell Y),X²)，Y=8X−X²，目标 (1,0,0,q)。`originalMeasure` 是倾斜原子律的真实逆倾斜，`originalMeasure_centered` 用第三约束给 EPX=0；不是将倾斜律 π 错当作原律 P。

### canonical 全域和全正尾域唯一极小

已重审 `BivariateLegendre` 完整定义及两个证明、`SourceCanonicalRate` 完整99行、`SourceGlobalExponentialTests` 完整证明。`bivariateMGFDomain` 是真正 `Integrable exp` 的集合，`bivariateLegendreRate` 是其上所有实际实值对偶函数的 EReal 上确界，没有用不可积函数的总化积分、`toReal` 或局部候选率代替全域率。

`source_saddle_exponential_value_bound` 证明每个实参数的指数可积、分割函数正及候选点对偶值统一上界，并由 (8ell,−ell) 达到该界。`exists_source_tail_exponential_separator` 对每个 c>0、a≥√q√c/4 且不等于 (q/4,q) 的点给严格更大的实际对偶测试：c<1、c>1+H 单独分离；可行 c 区间用 R=√c/√q，R=1 时直接用 a>q/4，R≠1 时用 Bernoulli 指数测试及严格熵差。p=0/1 端点包含在闭区间中，尾域内部的大 a 由非负额外项覆盖。

故根的 Dtail 是 **所有 c>0 的弱尾域**，包括不在实际凸支撑中的点；非候选点率允许为 EReal.top。没有缩到局部邻域或边界，也未偷纳 c=0。此集合不是整个 R² 中的闭集；“弱尾”只指保留 ≥。

### 实际梯度、完整 Hessian、正定和同一尺度

已重审 `SourceCanonicalSaddle` 完整171行，及 `SourceLogPartitionDerivatives`/`SourceGeometricScale` 承重证明。lift 保留任意 Fin2 参数的两个坐标；先建立整个 K 函数与原 P 的字面 log 积分相等，再传递一阶导数与 `fderiv` 的导数，因此不是只在 theta0 值相等后错误运输导数。

参数积分求导通过有界支撑与紧参数球上的实际可积支配完成；归一化矩通过 `originalMeasure_retilt` 与同一 π 的矩相等。完整双线性 Hessian 是同一 `parabolaCovariance (atomicMeasure w)`，包括交叉项。正定来自真实正基点原子上的中心二次型积分严格正，不以 det>0 单独冒充正定。

v=(1,2a0/x0²)=(1,8)，λ1=σ²/detΔ−32ell/q；正 det、正曲率和正 vCorr 已生产。`correctedInverseScale sourceEll q (atomicMeasure w)=vCorr⁻¹` 的平方根/逆矩阵代数使用同一 q/w/Δ，λ0 则等于同一 `saddleRate`。新源码176–177的 `change` 只折叠 definitionally identical 局部名字，没有增减数学假设。

### 实际 iid 比值尾事件与全 n 系数身份

17–24：有限坐标和、平方和、sqrt、除法均可测，故所有 n（含0）的字面 ratio Tail 为 Borel 集。

26–45：从 P 下 AE 1≤|X| 经每个坐标的产品边缘和有限 `ae_all_iff` 得所有坐标同时成立，再逐点证明 energy≥n。只有 n>0 才推出 AE 正能量，没有把零能量约定隐去。

47–65：在正能量 AE 集及 n>0 上，分母 √n√energy>0；用 `le_div_iff₀` 和 `sqrt_mul` 双向得到 `sourceTail q n =ᵐ[nu n] Tail n`。没有平方丢失 Sn 正号；无需额外 q>0 前提。

184–195：上述一般私有引理全部由实际 P 的 hP/hb 消去输入。n>0 时使用事件 AE 相等和 λ0=saddleRate 得真实概率身份；n=0 时两系数的 √0 前因子都为0，单独处理，未对零分母消约。结论是 **所有 n** 的整个 `normalizedTailCoefficient = C` 函数身份。

### 固定律对角构造、严格单调见证与标准非 Big-O

关键旧链已重审：`StageSourceAsymptotic` 将真实 finite-stage conditional weak convergence 兑现到全层极限；`SourceFixedLawRemainder` 的新私有有限见证调用的是这个无 hcont 版本，不是仍带 hcont 的旧 `StageSourceWitness` 辅助接口。固定 J 后的 phase-return 子列、全正负层常数和正 h^(3/2) gap 给任意大的有限阶段见证；没有三角阵统一 LLT 假设。

`SourceTransferBudgets` 先为每个已经选定的有限前缀与 n 选正 cap；随后 `exists_witness_first_positive_mass_with_tail_caps` 构造同一个严格正可和 r。`SourceFixedLawRemainder` 用真实产品换测度/未来尾差界及尺度连续性，在同一最终 w 上生产“任意 K,N 后仍有正 n≥N 且缩放余项>K”。再由 `SourceFixedLawCounterexample.increasing_remainder_witnesses` 递归选严格递增 nseq，且每个 J 的差距>J。该重选只选样本量，没有重选概率律。

`SourceRemainderNotBigO` 私有证明把标准范数型 IsBigO 界沿 Tendsto nseq 拉回，选 J>max(B,N)，先证 √n>0 后消逆，得到缩放有符号余项≤B，与 >J 矛盾。没有将有界子列或非标准口头 Big-O 当结论。新根204–206通过全函数 hcoeff 和同一 hscaleeq 原样运输见证与 `¬IsBigO`。

## 4. 全部 actual private/generated 类型

已完整实读实际 TYPE 清单112行/8756字节，SHA256 `8230b32559957991ac6e97c965528f7a3b06bc3dc7e3b1b4972596f6e6a8edc7`；无省略号。公开根及所有 let/量词与源码67–144逐义一致。

| 实际所属常量 | 核查 |
| --- | --- |
| private `ratio_tail_measurable` | 任意实阈值/所有 n 的可测集；完整17–24证明正确 |
| private `product_energy_pos_ae` | 任意概率 mu、AE abs(X)≥1、正 n ⇒ 真实 product AE 正 energy；完整26–45证明正确 |
| private `sourceTail_ae_ratio` | 任意 q/正 n/任意 nu/AE 正 energy ⇒ AE 事件等价；完整47–65证明正确 |
| public `exists_fixed_jointNonlattice_saddleExpansion_counterexample` | 无 caller 前提，完整 A 合取及实际概率归一化；完整67–206证明正确 |
| generated `normalizedTailCoefficient.eq_1` | 旧定义的无条件精确展开；实际 owner 是新模块，已纳入，不按名字排除 |

共1 public、3 private、1 generated，0新定义。每项实际 audit 公理集均为 `[propext, Classical.choice, Quot.sound]`。未见 sorry/admit/新增 axiom/unsafe/native_decide 或逻辑捷径。

## 5. v39 依赖和 v40 机械证据绑定

74 项正式前置字典逐项与 PR161 冻结 git blob、只读 library 文件及 accepted v39 receipt 的 `source_files_sha256` 比较，三者差异均为0。v39 receipt SHA256：`dfea5cdd6b37f0509af4cd9412e0188e5de8f28934d8970cfdf908f61af9b2c3`。重点三项：CanonicalRate `fc492cbacca9a8df208b9a20ea47d7e84e71c1c48e1f87448adbd925f5378d92`；CanonicalSaddle `24200d85b6c4d13862ab166da8c7e6221ef87601216a125d5e8dc3260d0a7941`；RemainderNotBigO `620bd072fc799b1684a5d54b1912d3abb5c26833a20d680d354185bc9eea633f`。本票只重审根完成所需关键证明链，没有重复全库机器门。

作者已有 build02 exit0，360字节日志 SHA256 `0b2a95876f2658cddda1d6c2d3c19bf60e5b1273d6bbfeaf09e0812df1e63331`，实际只有一条 style.haveILetI 提示，不能说空日志。已有 audit SHA256 `fcb8711223a24e11d77139d059c1d1151eb20faa4ff260d0c442eed7662f931e`，5所属声明/5定理及白名单 PASS。已只读核对原始日志哈希与 owner/公理块；未重编。

统一 v40 结果 local `coordination/integration-v40/gate-result.json` 与 server `logs/integration-v40/result.json` 同 SHA256：`e64b378bc563d4fae8a2e1493280624e3c748e25686105426c15c5be11b65542`。只读核对七份日志均 exit0、实际哈希与结果一致；build 含本新模块及总入口的顺序成功，public1882、含生成 namespace theorem3190、所属常量5507、覆盖生产模块281。277份基线源与1054对象复用绑定保持不变。

组装 head `723f9eed6927b7cb8f1ed60a1db9542eb0cb7875` 中 PR161 精确 head 是祖先，本新源码 SHA 与独立审查字节相同。工具链 Lean4.36.0-rc1/mathlib807d3836固定；root 门 CPU10–13、8192MiB/j4。机器门由 root 运行，本票没有新 Lean 命令；不把读取已有 PASS 说成 reviewer 自行重编。

## 6. 不影响 A 关闭的范围边界

- 一般任意 rho 的 KL 恒等式与数据处理路线 R1(9)/(10)未在此根中逐字形式化；实际全域指数分离测试已证明 A 所需的唯一率极小性，是充分的替代证明路线。
- 精确 ζ(−1/2) 系数及 O(h²) 展开 R1(24)不是本票所需。已接受链给同一真实全层常数严格正、统一的 h^(3/2) 下界，足以完成(25)–(31)对角反例；不把该下界说成精确 ζ 展开。O(h) 抵消没有被误说成 O(h) 障碍。
- 可选(14a)“违反每个多项式弱 Cramér 界”加强不在根结论中，主反例不依赖它。
- 全邻域 C∞/均值映射局部逆/局部率逆图等额外正则结构不是被冻结完整 A 最后接口的未消除前提。本票不凭 A 把这些辅助任务算完；同批 PR163 的独立范围由其专票决定。
- B 的 Song/胞重建/边界 Laplace/显式远区概率桥，C 的完整标准化倾斜族稳定性组装，D 的幅值丢番图存在性/十六原子 β=3/8/小 x 正则鞍点合并见证，都不由 PR161 证明。PR159 的局部进展也不能自动关闭完整 C。
- 未声称最弱修复、β端点最优、历史首次、所有 x 的一致展开、字面 ICM 印刷常数修复或整个 OQ3 全部关闭。

**root_closure_recommendation：CLOSE A（完整且恰为 root-contract/R1 的固定同律、固定 x0、corrected vCorr、自归一化尾概率余项反例）；B/C/D 保持 OPEN。没有妨碍该 A 关闭的 critical gap。**
