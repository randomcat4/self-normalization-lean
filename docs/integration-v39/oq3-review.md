# v39 OQ3 独立数学与 Lean 源码验收

STATUS: CORRECT

审查者：`/root/v39_oq3_accept`。时间：2026-10-22 21:49 UTC。结论限于 PR153、PR156、PR158 的三个冻结增量。未发现关键缺口；`critical_gaps=[]`。不据此宣告原始 OQ3 A/B/C/D 全部或其中某根已经关闭。

本轮先读 AGENTS.md、SERVER.md、TEAM.md 和 math-theorem 验证流程，再独立从原始题面、冻结声明和实际证明重建推理。只拥有本报告及相邻 JSON；没有改作者模块、合并或启动 Lean，也没有创建子实例。已有服务器成功检查只读复用，v39 组装编译、公理和完整覆盖由 root 统一判定。

## 1. 冻结版本与来源

| PR | 精确 head | parent | tree | 新生产源码 SHA256 |
|---|---|---|---|---|
| 153 | `9170a40f3e9a6d519a987c2a0ceaade85136cd36` | `5a82f9e0587a93fc413f83f22713f7e6ec1d8ec5` | `d31116c0ddf1fde5db454dbd77167a021c1bf74e` | `620bd072fc799b1684a5d54b1912d3abb5c26833a20d680d354185bc9eea633f` |
| 156 | `7dcf60695c046d0d89e96b92ccd25604e444cfe9` | `ffdedd610d0af501c3dd4672cf7f78d80eee543c` | `0acb4f35dc49de4f27250df50bfd32838eb51d01` | `fc492cbacca9a8df208b9a20ea47d7e84e71c1c48e1f87448adbd925f5378d92` |
| 158 | `2e563432d9e21e01dce9e591c575071aafa83d9d` | `7dcf60695c046d0d89e96b92ccd25604e444cfe9` | `f2a6538df51518a3236174b2cbf37093fb45015c` | `24200d85b6c4d13862ab166da8c7e6221ef87601216a125d5e8dc3260d0a7941` |

分别完整审读 `SourceRemainderNotBigO.lean` 83 行、`SourceCanonicalRate.lean` 99 行、`SourceCanonicalSaddle.lean` 171 行。服务器只读 `git show` 核实三提交各为新增一个生产模块加五份交付文件，源码字节、scope 完整公开签名、收据均一致；没有其他生产修改。PR156 从 v38 接受点分支，PR158 直接接 PR156；没有把 PR153 误说成 PR156 的祖先。

原始来源实读：

- `supplemental/icm2010/icm01.txt` SHA256 `9024791b6e01b2254a3e9baca54d555a1591ed58d30a9de93cf1a9cf2f5d882d`，按换行符分行的 8926–8978：Theorem 3.1 的二维特征函数绝对幂可积条件 (3.3)，以及 Open Question 3 的固定 x 误差 O(n^-1/2) 与另一个 x 变化的一致性问题。
- R1 `current/oq3/proofs/r1/report.md` SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，重点 §§1–8、(6)、(9)–(14)、(19)–(20)、(25)–(31)。
- R2 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`；RP SHA256 `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`；`root-contract.md` 用于精确区分 A/B/C/D 和尾域约定。

原 ICM 印刷常数与已冻结源的修正常数有差异；本验收严格使用 root-contract、R1、R2/RP 的 `v_corr`。三个增量没有证明随 x 变化的一致展开，也没有宣称最弱弱 Cramér 条件或历史首次。

## 2. PR153：同一最终律的标准 Landau 否定

公开声明：`Shao.OQ3.exists_source_fixed_law_not_isBigO`。无公开定义。它存在量化一次 q、w；q∈(1,103/100)，全部权重严格正，完整四条真实 HasSum 约束保留；随后 P 固定为 `originalMeasure sourceEll w`，x0 固定为 √q/4。保留概率、中心化、1≤|X|≤4+√10 的 AE 界、正半轴正质量、真正二维联合非格点、显式逃逸共振及其模趋一、正率和正尺度；同一律上存在 StrictMono 且趋于无穷的正自然数见证，并对每个 J 有严格缩放差 >J。新结论是标准 `¬Asymptotics.IsBigO atTop`，对象确为实际归一化概率余项、比较函数确为 `(sqrt n)⁻¹`。

私有引理 `not_isBigO_inv_sqrt_of_scaled_witness` 的全部源码及实际 TYPE 已读。假定标准大 O 后，`hO.bound` 给实常数 B 及最终范数界；沿真正 Tendsto 的 nseq 拉回，取得索引阈值 N。选 J>max(B,N)，由 nseq J>0 先得 sqrt(nseq J)>0。实数范数即绝对值且正逆平方根的绝对值可消，得到 f(nseq J)≤|f(nseq J)|≤B/sqrt(nseq J)。乘正根并合法约分得 sqrt(nseq J)f(nseq J)≤B，与 B<J<该缩放差矛盾。无需 f 单调、f 最终非负、B 预先正或 nseq 的值等于 J；n=0 不在约分使用点。

主证明只拆解一次已接受的 `exists_source_fixed_law_counterexample`，原样保留其 q/w/P、nseq 和所有性质，再将同一实际余项交给私有引理。没有为否定结论重新取律，也没有在公开前提里输入失败结论。

重要生产链已核：`SourceFixedLawCounterexample` 的见证由 `SourceFixedLawRemainder` 的“任意晚、任意大”结论递归选择，后继时间至少上一时间+1；递增性与趋于无穷不是假设。后者从实际有限阶段无条件极限、实际正 h^(3/2) 差及转移预算产生 hW，再先选合法前缀的 chooseN 后构造唯一正可和 r。它没有将 hcont/hW 作为最终调用者假设。原源精确 ζ(-1/2) 渐近并未由此宣称已证；此前严格正 h^(3/2) 充分下界足以供此真实反例使用。

`normalizedTailCoefficient` 的定义是 `sqrt(2*pi*n)*exp(n*saddleRate)*P^n.real(sourceTail q n)`；P^n 是同一 P 的真实有限乘积律，非自由数列。`sourceTail` 是正能量及 `x0*sqrt(n*energy)≤sum`，保留正尾符号，非仅平方事件。其与显式自归一化比值事件的最终 AE 等式仍属 A 最后组装范围。

裁决：CORRECT。原始概率律、四约束、递增见证、标准绝对误差 Landau 否定语义均忠实，无偷加目标假设。

## 3. PR156：同 q/w/P 的完整正能量域规范 Legendre 最小值

公开声明：`Shao.OQ3.source_canonical_rate_unique_minimizer`。输入仅 q∈(1,103/100)、w≥0 和完整四条 HasSum。hm0 实际导出 HasSum w 1 与 P 概率；概率实例位于 letI 证明中，不是额外 caller 前提。P 是原逆倾斜律，W(x)=(x,x²)。

尾域严格为 `D={(a,c) | c>0 ∧ (sqrt q/4)*sqrt c≤a}`。弱不等式边界及所有不可实现矩点均保留；没有只比较可行矩集或局部邻域，没有纳入 c=0，更没有将此集合误认为全 R² 闭集。

定义与重要依赖完整核对：

- `bivariateMGFDomain` 就是真指数的 Integrable 集合；`bivariateLogMGF` 仅在此域的 subtype 上取真实积分的 log；`bivariateLegendreRate` 是该完整域上有限实测试值嵌入 EReal 后的 iSup。未用域外总化积分或 `toReal`。
- `source_saddle_exponential_value_bound` 对全部实 s,t 给实际 Integrable、严格正配分、候选测试上界及 theta0=(8ell,-ell) 的精确达到。其源码先由有界性证明可积，再用逆倾斜 log 恒等式与 exp≥1+h 的积分证明中心测试上界；无输入极小性。
- `exists_source_tail_exponential_separator` 对每个 c>0 的非候选尾点给实际可积严格测试。源码覆盖 c<1、c>1+H 的不可实现点；区间内以 R=sqrt(c/q) 分类，R=1 而 a>q/4 直接严格分离，R≠1 用 Bernoulli 测试。0≤p≤1 的两个端点由有限实测试单独实现，不假定端点熵最大值由有限参数达到。
- 真实 energy MGF 的 Bernoulli 上界来自 exp 的凸弦比较；`binaryRelativeEntropy_source_gap` 给严格 `(7/200)*(R-1)^2` 下界，sourceEll*q<7/200。相关实际源码/前提不含原全局率极小结论或一般 rho KL(9)/(10)。

新证明用 all(s,t) 的 Integrable 先证明 domK=univ，然后构造带真实成员证明的 theta0。所有域内 log 与 literal log 定义相同；其严格正积分由规范 spec 给出。q>0 和 sqrt(q)^2=q 证明 (q/4,q)∈D。每个 z≠候选给坐标差，正确实例化上述严格分离器，之后才调用一般 `bivariateLegendreRate_unique_minimizer_of_tests`。

一般接口的源码也已读：候选的上界和达到给 EReal iSup 等于有限 L；任一非候选点有一个有限严格测试，故其 EReal 率严格大于 L。其他点允许率为 +∞；不以所有点有限作为隐藏前提。其推理足以给全 D 比较及等号当且仅当候选，完全不依赖局部凸性代替全局论证。

裁决：CORRECT。完整 c>0 域、真实 domK/K/EReal、有限候选率及全局唯一极小性均已实际产出；没有另选 q/w/P，无偷加最小性或 KL 假设。非负权版本不额外声称每个如此输入的率严格为正，严格正率由 PR158 对正权版本生产。

## 4. PR158：规范 ambient K 的实际 Hessian、正定性与尺度

公开声明：`Shao.OQ3.source_canonical_saddle_hessian_and_scale`。只在同 q 范围、同 w 的全部严格正权及完整四约束下使用 PR156。没有 caller 导数、正定矩阵或尺度等式假设。

`lift` 对所有 Fin2 实参数逐点保持 pair 坐标；由 domK=univ 构造。K 定义为同 P 的 canonical logMGF 经 lift，随后先证明整个函数 K 等于 literal log 积分的函数 hK。两个 HasFDerivAt 都是在这个整体函数等式下转移，第二项确是 `HasFDerivAt (fun theta => fderiv ℝ K theta)`；不是仅在 theta0 比数值，也不是对子类型任意求导。

`SourceLogPartitionDerivatives` 的实际源已审：有界支持和参数闭球给连续积分导数的共同支配，正配分使除法、log 求导有效；在 theta0 真正反倾斜回 `atomicMeasure w`，真实一至四阶积分给梯度 (q/4,q) 和完整协方差矩阵。Hessian 连续双线性表示展开为 `Σij D_ij u_i v_j`，坐标次序保持 (X,X²)，D01=D10。

D 精确是 `parabolaCovariance (atomicMeasure w)`，不是 P 的未倾斜协方差或自由正定替代。新证明通过 hm0 建 atomic 概率实例，w>0 与真实 singleton 身份给四个基点正质量。对 u≠0，Fin2 穷尽推出 u0≠0 或 u1≠0。`centered_parabola_integral_pos` 使真实中心多项式平方积分严格正；其底层源在基点 -1、1、2 上排除非零二次多项式为同一常数。用实际积分等式、D 对称与有限和展开得到对所有非零 u 的 `u·Du>0`。这严格强于只证明 detD>0。

由 q>0 得 x0²=q/16，并合法清分母生产 q=a0²/x0²、s0=-2a0t0/x0²、t0<0。theta0 与 PR156 的 thetaStar 先以 Subtype.ext 识别，然后真实测试值 lambda0=saddleRate；`saddleRate_pos` 的严格凸 exp 证明利用两个正质量、不同 Y 值的基点给 lambda0>0，未预设此结论。

几何尺度使用同一个 D：v=(1,8)，`v·D⁻¹v=Var_pi(Y)/detD`，所以 lambda1=Var_pi(Y)/detD-32ell/q。此前已接受几何模块的实际逆矩阵展开、横向方差界和 sourceEll<1/30 给 detD、lambda1 正性。正确正根乘法给

`vCorr=(-t0)*sqrt(detD)*sqrt(lambda1)>0`，

`correctedInverseScale=(sourceEll*sqrt(Var_pi(Y)-(32ell/q)*detD))⁻¹=vCorr⁻¹`。

所有分母与根的正性先得到，未依赖零倒数的全定义行为。该尺度与 PR153 用的同 q/w 的尺度完全一致。

裁决：CORRECT。实际规范 K、完整二阶、同 D 严格正定、真实鞍点关系和尺度均已绑定；没有声称全参数邻域 C²、均值映射局部逆或标准化 WC 已完成。

## 5. 全部新模块所属声明

三个生产模块合计 13 个所属声明，全部为 theorem：3 公开、1 authored private、9 generated，0 def，0 axiom。逐个实际 TYPE 及全部续行已读，不能按 namespace 代替模块 owner。

- PR153：公开目标加 `_private.Shao.OQ3.SourceRemainderNotBigO.0.Shao.OQ3.not_isBigO_inv_sqrt_of_scaled_witness`，无生成声明。
- PR156：仅公开目标，0 private、0 generated。
- PR158：公开目标及以下九项。`_simp_1_3/4/5` 分别为非零 2/3/4 与 0 相等的命题等于 False；`_simp_1_6` 为无零因子情形非零积不等于零；`_simp_1_7` 为 IsReduced 的非零自然幂不等于零；`_simp_1_8` 为 GroupWithZero 的非零整数幂不等于零；`_simp_1_9` 为 CharZero 下自然数后继 cast 非零。另有实际 owner 属本模块的 `Shao.Probability.bivariateLegendreRate.congr_simp`（测度/W/z 相等时相应值相等）和 `Shao.Probability.bivariateLogMGF.congr_simp`（域参数相等时值相等）。这些只是各自假设下的逻辑/代数或 congruence，没有新增 OQ3 数学假设或目标结论。

三份新 Audit.lean 全源已读：它们以 `getModuleIdxFor?` 的实际模块 owner 枚举常量，不漏跨 namespace 生成项，检查 theorem 目标、拒绝新 axiom、逐声明 `collectAxioms` 并核白名单。机器覆盖和传递公理的最终票仍归 root 的 v39 统一门；本轮只复用已有记录。

实际 TYPE 清单 SHA256：PR153 `b1a33ab434168929e1d76ee9b3a81ed203512bf589bb884337f320fdf5ec4220`；PR156 `ad697138682ba7011ac982c0aa2d91dec33c889cc97294573b9c878ff84852d6`；PR158 `44761c849e7db83f4698362a93d8a8d68fa1805071bff76b73e5a64b73c5a655`。本地已读清单与服务器原件哈希相同。

## 6. 证据与复核限度

67/13/25 个正式项目依赖分别逐项绑定各 frozen head 的 git 源、署名 receipt 和本地只读源码，缺失 0、哈希差异 0；不据此声称逐行重审了所有旧模块。重要已接受依赖的数学接口及上列承重实现已经另行阅读。新源全文无 sorry/admit、新 axiom、unsafe、native_decide 或证明设置弱化。

| 项 | PR153 | PR156 | PR158 |
|---|---|---|---|
| author receipt SHA256 | `c57191588b792ed11d7590092f7dff12924cb617ec7606bad737a4fc914a6c61` | `670a4854c3bc5c7e5373e0356bafd6a1c439288e55e9a8fc44fb762590112939` | `0d20d7daf0dda654e48baf1eab18b48feffaff687f254a30106acd825cc02104` |
| 已有成功 build | build-01，空 log | build-02，一条实例写法提示 | build-01，六条样式提示 |
| build log SHA256 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | `ce4cbd4ec47005a0d924acceac601f98e2a34626d98b5d9f74fb4f91a32748fa` | `37a061bb7b717aac10835e80298aac8802f89c1be827d05f55d990b63f18fcd8` |
| Audit log SHA256 | `1c79fd089b9afccb3040b2d1907c89777e24a46ec71d5242e8902ad295e442a3` | `6373f2d127ac31a5683d3cf7b8765f643aa626fcc25606af45b63c9204886ced` | `1c49550b55ad2158fddcd7cba7a77b98f90ea46a786fe4245fda93a69b1dc7e3` |

上述成功 log 已按服务器原始字节核 SHA；署名 exit 0、标准白名单与实际 TYPE 一致。PR156 v1 的 import-only 失败 log `260cc7c835654100a3cb9b99dd704774a04f9d735d2f06db59e5a0809565dbd6` 保留；v2 仅以同 Shao 包根的只读符号链接视图修复导入，公开 TYPE/proof 未改，成功源只改 scope 注释 hash。没有把失败记为成功或重编不变成功目标。

钉死 Lean `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。三源与 root 组装目录 `workspaces/integration-bearing-v39/verification/frozen-v39.json` 一致。

完稿前收到 root 统一 gate **PASS**，并做了只读证据绑定，没有重复 Lean。服务器 `logs/integration-v39/result.json` 与本地 `coordination/integration-v39/gate-result.json` 字节哈希同为 `a74870ea363ebb14763aaf1d336d1e0794a887ebe98b41c9b77e4659ab7ecc66`；其中七个命令 exit 0，七份现存 log 的哈希逐一相符。组装 head `1d1de3c48fe65170dab2ac09acd4ab580384a919` 含三冻结 head 为祖先；冻结源码无差异。实际覆盖 277 模块、1875 公开定理、3180 含生成项命名空间定理、5470 所属常量；271 旧源和 1048 旧对象复用证据保持不变。此机器结果归 root，数学/源语义验收归本独立报告。

## 7. 原始 A/B/C/D 的未闭合范围

- **A，固定律反例：OPEN（最后组装）**。本批已提供同一源律的标准否定、全 c>0 规范率最小性、实际 Hessian/正定/尺度。最终原根声明仍须一次取 PR153 的同 q/w/P，再实例化 PR156/158，输出同一个存在量词下全部根性质；补真实 P^n 下 n>0 的 AE 正能量与显式 `S_n/V_n` 尾事件等价、同 lambda0/vCorr 的概率系数重写，并完成该根源的独立审核与统一机器门。本批没有这个组装定理。一般 rho KL(9)/(10)、精确 ζ 系数(24)、可选超多项式近共振(14a)仍未整体形式化；已接受的直接指数测试和严格正 h^(3/2) 下界足以替代相应反例用途，不把这些路线差异混称 A 目标失败。
- **B，一种充分修复：OPEN**。还需真正均值映射邻域逆及谱/矩/标准化 WC 一致性、Song s=8 外部定理的无新公理形式化、逐胞振荡与绝对误差、可测胞重建、边界 Laplace 及余项、显式远域概率估计的组合。有界特例从率极小性到远域 Cramér 概率界仍另需证明；无界版保留原显式概率假设。beta<2/5 只是充分条件，端点及最优边界未证。
- **C，有界稳定性：OPEN**。本批不改变旧有测度支配与余弦积分部分。基点 WC 到真实紧倾斜族 norm 界/精确 m²c/2，以及后续矩阵标准化和完整稳定性接口尚未由这三个 PR 交付。另一个 PR 之外的新候选/作者门不能计入本批接受；无界单点自动稳定不成立且没有被声称。
- **D，严格弱于 strong nonlattice 的抛物线见证：OPEN**。八正幅值与七平方差同时 AE 丢番图选择、Borel–Cantelli/Fubini 满测存在性、十六对称抛物线原子的 beta=3/8 定量相位缺口、Dirichlet 逃逸近共振与充分小固定 x 的正则全局鞍点仍需组合证明。R1 本批律的近共振不替代 D 的不同有限支撑定量 WC 见证。

综上，接受这三个冻结增量的完整数学和 Lean statement/source 忠实性；`critical_gaps=[]`。原根闭合状态与 v39 最终机器结果由各自明确门决定，不能以新增辅助声明数量推算。
