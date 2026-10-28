# KB368 / KC369 / KD370 独立完整联合终审

STATUS: CORRECT
QUALIFICATION_RECOMMENDATION: CORRECT_EXACT_LOCAL_SCOPE，按 KB368 → KC369 → KD370 依次资格化。

本报告仅裁决以下冻结的新单元。三份最终源、五条公开声明、九条独立导入环境中的实际所有者 TYPE、全部十五个证明局部 let 值、三份完整 Audit 程序及现有全部 native/AX 日志均已完整阅读并核对；没有发现关键数学缺口。机械层复用作者已有精确源绑定的服务器内核与全部实际所有者递归公理回执。本审者没有执行 Lean/native/AX、构建旧生产者、上传或下载对象/日志、修改源/冻结/映射/资格/状态或发布。

## 1. 身份、边界与输入封存

独立审者及本报告唯一 writer：`/root/oq3_kb368_kc369_final_review`；父作者/sole OQ3 owner 为 `01a16c48-80ee-7520-a9d9-faeeb6d05c78`，与本审者分离。Root 为 `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`。本审者已实际运行 ACK，并完整读取 math-theorem 主技能、prompt-library、openai-workflow、lean-verification；遵守当前显式恢复 phase40。历史 OQ3 暂停已由人类恢复撤销，本审者没有取得任何执行资源或源写权。

规定模型/推理：`gpt-6.1-sol / xhigh / fresh`。实际运行模型、实际 effort、inputTokens、cachedInputTokens、outputTokens、reasoningSubsetTokens 本工具界面均不可见，全部记录为 `null`；不把规定配置冒充观测，不估算订阅百分比分配。

| 单元 | input map SHA256 | 行数 | scope SHA256 |
|---|---|---:|---|
| KB368 | d5d75dd03e981cc34a458692639bb2e37a789b66165800a40f8bb6b5c52af836 | 27 | bb1dfe9754a8e9f97ae1f3894a0e32513dc11b4e91908ecdd4603f6629b0d259 |
| KC369 | 41dbc8468092fc41531c425270d74d2d23062c1187f2bcd11473ae6adf79c0b2 | 30 | cb8f1f30225bbe2a39079fc7958e7443b0fcfd3e07b9c8f436237d8f394d9f07 |
| KD370 | 8ded8384b90648515574c5ab4b1c7ec13ac2e60ec7f2e93c5b838129818e3508 | 24 | 1968d26dbb27746e5adb9acb2bd1d1ebcd339c611d769d5bd83c3ef99f55f63b |

开审及最终读回后均逐条计算全部 81 个 map row 的实际 SHA256/bytes，并核验三份 map 自身、scope 哈希、soleReportWriter 与 jointFinalReport。三份 map 均不改写：KB/KC 预列的两单元是同一联合报告的子范围；KD map 明确扩展为本次三个单元的完整联合范围，且三份指向同一审者及 `u22kb-proof-review.md`。报告外全部冻结输入保持原字节。

| 单元 | 最终 source SHA256 | bytes / LF / CR / BOM | frozen declaration SHA256 |
|---|---|---|---|
| KB | 9e526278b01d912ec4c981c0eb700bcd4edfc0bebc11704bf637103978f37899 | 4594 / 90 / 0 / false | a6e0111b36ecb53a5b162d93255462a56f902fd8dd72834f724a496510eda625 |
| KC | bcf54b06a346508d69f865e4bb785c685eb7c643588cb34530e3288f628999b3 | 3563 / 75 / 0 / false | 883fc57542b00f1e401501d3379444d948e6aa1bcacdbccbefb676aa2dc5d16d |
| KD | d9d40d3fb394aed773e71b49740bbf26d40bd26d81c765a58383a71c38b7259f | 6074 / 119 / 0 / false | 8b8dae5fe2e307051eeed0367e2ce994c34d30e3d2a05816ad4855301b862ad7 |

对五条最终 theorem，从名称到 `:= by` 的完整声明与冻结文本去空白比较全部相同；同时逐 binder/量词/目标人工核对其完整实际 TYPE。没有声明级 let；证明局部 let 不能因此省略，详见各节。最终三源全文搜索 `sorry/admit/axiom/unsafe/native_decide/implemented_by` 均为零。

## 2. 原始来源、实际率对象及承重证据

只读原始来源为 `C:/game/shao/current/oq3/proofs/r2/report.md`，实际 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。完整读了所需行 47–67（并读了定义行 38–45、有限正幅值对称律的上下文行 375–491）。原始尾域精确为 `D_level={(a,q):q>0, a≥level sqrt q}`。原文要求正尾的唯一全局正则鞍点、负第二倾斜参数、切向曲率及其邻域外率间隙；本次三个辅助单元不能代替这些要求。

已全文读取 `library/Shao/Probability/BivariateLegendre.lean`（SHA256 `d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58`）中的真实定义和 test 接口。`bivariateMGFDomain` 是实际指数可积参数集；`bivariateLogMGF` 为该域上真实积分的对数；`bivariateLegendreRate` 为所有实际参数 tests 的 EReal 上确界，允许 `+∞`。以下记该同一率为 I，K(p)=log∫exp(p₁x+p₂x²)dmu，m=(∫x dmu,∫x² dmu)。没有改成熵、代理率或预设有限的实函数。

承重旧证据按精确哈希复用，未重审已接受旧证明或重跑其检查。25 项 bearing 文件/qualification/review/receipt/TYPE/manifest 绑定核验全部成功；accepted manifest 的完整 U22l、U22c row 与 bearing 中复制的精确 row 逐字段相等。U22c 归档 row 的 `docs/oq3-u22/u22c-proof-review.md` 在本地以同内容文件 `drafts/oq3/u22c-proof-review.md` 保存，实际 SHA256/bytes 相同；没有把不存在的相对归档目录当成本地已读路径。

- U22l OpenDomainLegendre 源 `941c08552f300af2c85e2df7f55399b69c4468bca467fe88b8a303a6a3c74bc3`；accepted standardization manifest `bd3b06c93481e2890b807208806b3e202dd34040386f038793686d954c03102f`；完整旧独审 `u22kl-proof-review.md` SHA `3e9951f16c042ddfe6291fa1d94f601c8131506416a586d40c2839e676c0b094`。本次完整读了被用的两个实际 TYPE、其全部声明级 let 值，并读其源以明确 chart 的 e 为 OpenPartialHomeomorph。零参数 rate-attainment 不要求协方差非奇异；compact mean chart 要求实际倾斜协方差 det≠0，给完整均值闭球及同一实际 I 的实值等式。
- U22c OpenDomainFrechetCumulants 源 `b5d48b414adbc80f7db44f37cc2b2b423d44263c54e8547a5a356768a116df72`；accepted milestone manifest `14fe897f27f1d74d09b7862f79b61eac0a7b98c1e1109ae5b805ce33e5ad7a9b`；完整独审 SHA `9ce863de680d5b8972933cc0a93e01cbfca0da7905570404dcb3697949a4a87f`，27855B/151LF。完整读实际导数接口的 nu/means/K/D/pr0/pr1/row0/row1/gradient/hessian 值：投影 `.2.2.2.2.1` 精确给 `HasFDerivAt K gradient theta`。取 theta=0、tilted_const 后 gradient 就是实际 m 的线性泛函，未引用错误的 hessian 或依赖 hdet。
- U15a TiltedMeasureDomination 源 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`；完整旧独审 SHA `7db85ddbb0f713ebb01cd54639a2834c51c22fe8242081b6d9533d8feaa21636` 及 accepted handoff `9f7d5d029a6eed0a0c7a00ded22e2e7b0db4f5132d682d1bbc1ab3d5b85438d9` 已 hash 绑定。本次读实际 `quadratic_exp_integrable_of_ae_abs_le` 完整接口；它仅用概率性、0≤M、AE |x|≤M，允许任意实 u,v。
- JW363 qualification `89b1162cf7317c1df142f1888efc51daf08e173336a80d22fae9941f6b01887b`；源 `9510b16dfeafa0c257890a78520277eb8a5ad2d2a1bcc44ce75076061688fc59`；首原对象 `8f570c7978b2b352daa7d5db380b167e87591e24d650df90cd163079015b633b`；完整旧独审 `u22jv-proof-review.md` SHA `1bb57df191b4ff864e0bdc1a07c9e384977557456657b421ac4795ca3ac0f8fa`。本次完整读 compact_sublevels 实际 TYPE，以及同一已资格化联合范围内 JV 的 full-domain/rectangle separation 完整实际接口。JW 给任意有限实阈值的整平面紧子水平集；不需要正 lower。
- BI ParabolaCellRateAnchor 源 `a6c6546788a6069c38bdc7545cc670252734236f67aa7c9e0892f0924de5842e`；独审 `615f58cc598db96cfc2408971b046219bb493e1c39d75acf29f1aac50ae2b50e`；accepted manifest `d7668a9fb28e96776e8ab9620403553f9a2ba3118e9c6b984199d42218da9fd4`。完整读其实际 `bivariate_legendre_rate_lower_semicontinuous` TYPE，适用于任意 NeZero mu、任意 W，故适用于当前真实二次率。
- JY365 qualification `3af9e09a8d3e1d1398634d59532b2a6bd01b3c7d6e51ef1b1da2a85efe837db0`；源 `e39dd81451cb3496ec26039721388c256ee13318a8a95193e458aaa39fb9eaa2`；首原对象 `7c9b451db6afa4bdd863129093b8451bf775003637d60413b89d1446422ce5a4`；完整旧独审 `u22jx-proof-review.md` SHA `d3a1ff82305b0683cf56e851f5bed2764549fc8062fb69ff4d616f6074a6ca3c`。本次完整读 finite-test global-minimum 实际 TYPE：它从显式 feasible w 及 Iw≤实 L，产生原尾域的真正全局极小点，而非只在新加紧集上极小。

只读远端复核七个直接依赖的实际 source、accepted-source-view 对象 hash、解析目标均与已封存 server-dependency-binding 相等。OpenDomainLegendre、OpenDomainFrechetCumulants、TiltedMeasureDomination、BI 的旧 retained artifact 首原来源仍为 UNKNOWN/null；本报告不升级其 provenance。前三者 retained hash 分别为 `fd7c4ddacc183c4bd93030bed4c5b57c677965668fe192abd51d9126150f2a6e`、`6059967b10abffa9967d6fd1fa9cfc5542dda3d7afb5e03439cc6d932a67c6b9`、`f8cc665a94eedcef80779b4611a152577a8712b909528cad0f1d1da78e5b2ace`；BI retained 为 `08153875d627ddbc82a6f02f138a44c57d5fb9a3f8d39b257e22a2fc71327c6f`。

## 3. KB368 完整源到陈述/证明审查

五个证明局部 let 全部读全并核对：K 是实际 log-partition；m 是实际一、二阶矩；G=m₁·fst+m₂·snd；对任意被测试 z，Q=z₁·fst+z₂·snd，F(p)=Q(p)−K(p)。它们都位于证明内部，没有把所需结论装入 statement 假设，也没有遗留非定理模块 VALUE。

第一个公开结论对任意有界概率 mu、任意整平面 z 同时证明 I(z)≥0、I(z)=0 当且仅当 z=m、以及 z≠m 时 I(z)>0。没有协方差非奇异、中心化或正能量下界假设；退化 Dirac 律也在范围内，离开其均值的率可以为 +∞。

1. 源 24–32 用已接受有界二次指数可积性得到每个 p 的实际域成员，进而域=univ，故 0 是内点。没有把局部域错当成整域，也没有在不属于域的参数上取 test。
2. 源 33–41 明确使用实际 tilted_const 将零倾斜律化为 mu。Frechet 接口给 DK(0)=G，Legendre attained 接口给 I(m)=0；此处不调用只在非奇异协方差下成立的逆映射。概率性使 K(0)=log1=0，实际矩的可积性由有界性/accepted interior cumulants 保证，不依赖非可积 Bochner 积分的默认值。
3. 源 42–46 取实际参数 p=0 的 test=0，得整平面 I≥0；值域为 EReal，无需预设 I 有限。
4. 核心源 47–67：若 I(z)≤0，则每个实际 p 的实 test p·z−K(p)≤0。EReal→ℝ 的 exact_mod_cast 只施于有限 real test 与零之间的保序嵌入，未取 I(z).toReal。由于 F(0)=0，0 是 F 的全局最大点，从而是局部最大点。F 的导数为 Q−G，Fermat 强制该整个连续线性映射为零；分别作用于 (1,0)、(0,1) 得 z₁=m₁、z₂=m₂。已读钉死 mathlib `IsLocalMax.hasFDerivAt_eq_zero` 的完整使用条件，确为无约束实 Banach 空间局部极值，不需要额外 tangent cone 假设。
5. 源 68–73 把上一步用于零值正向及“非严格正则≤0”的反证，另一向由 I(m)=0；EReal 线性序足以覆盖 +∞，没有声称非均值点率为有限实数。

第二个公开结论源 75–87，增加且仅增加中心化、level>0、z₂>0 与原尾不等式。sqrt(z₂)>0，因此 z₁≥level sqrt(z₂)>0，而实际均值第一坐标为零，故 z≠m，第一结论立即给 I(z)>0。没有把“均值是全平面唯一零点”偷换为“正 level 尾域唯一极小点”；也没有使用 lower>0 或 hdet。

KB 裁决：CORRECT。它提供真实零集及所有中心化正尾点的严格正率；有限最小值须另由已有全局极小值接口与本次 KD 的可行测试共同保证。

## 4. KC369 完整源到陈述/证明审查

三个证明局部 let 全部核对：I 为同一实际率，m 为同一矩均值，C={I≤1}∩{r≤dist(·,m)}。两条公开声明仍仅假设有界概率及 r>0，无中心化、协方差、正能量假设。

源 19–25 从 AE |x|≤M 得 0≤x²≤M²，取 JW 的 lower=0、upper=M²、L=1，得到整平面 {I≤1} 紧。源 26–30 用 BI 的实际 EReal LSC 得 {I≤1} 闭，连续距离使闭球外条件闭；交集 C 是上述紧集的闭子集。这一步没有把闭尾域 q>0 错当作闭集，C 根本不含尾域约束。

非空分支源 31–52：EReal LSC 在非空紧 C 上达到最小，得到 z0∈C。由 r>0、r≤dist(z0,m)，若 z0=m 则 r≤0，矛盾；最终源显式暴露 typed `r≤dist z0 m` 后再化简，方向 `hr.not_ge` 正确。于是先资格化的 KB 给 0<I(z0)。钉死 mathlib `EReal.exists_between_coe_real` 允许从这条严格不等式选有限实 g 满足 0<g<I(z0)，包括一般端点为 +∞ 的情形。gap=min(1,g)>0。任意整平面 z 满足 r≤dist(z,m)：若 I(z)≤1，则 z∈C，gap≤g<I(z0)≤I(z)；否则 I(z)>1≥gap。两分支的 real→EReal 嵌入方向一致。

空分支源 53–56：C 空意味着所有球外点 I(z)>1，故统一取 gap=1。没有遗漏“所有球外点率为 +∞”、球外无有限支持点或 C 恰为空等边界。gap 总是有限正实数，率不要求有限。

第二声明源 58–72 先取同一个 gap，令 delta=gap/2>0。若 I(z)≤delta 且 dist(z,m)≥r，则 gap≤I(z)≤gap/2<gap 矛盾，故严格 dist<r。量词为每一 r>0 先选 delta，再覆盖整平面所有低率点，包含闭子水平的等号边界。

KC 裁决：在本报告先接受 KB 的前提下 CORRECT。这个 gap 以实际均值 m 为中心；它不是原文所需的正尾唯一鞍点邻域外 gap，不能据此宣称尾域唯一性或原文第 4 假设已闭合。

## 5. KD370 完整源到陈述/证明审查

七个证明局部 let 全部读全：q=∫x²dmu、m=(0,q)、K 为同一实际 log-partition、I 为同一实际率、L(z)=e.symm(z)·z−K(e.symm(z))、epsilon=min(1,min(R,rho)/(sqrt(q)+1))、w=(level sqrt(q),q)。e/R 是旧 chart 产生的局部逆与正闭球半径；delta 是已先资格化 KC 产生的正实低率阈值；rho 是 L 在 m 连续所产生的正邻域半径。即使 e.symm 在 target 外被实现为总函数，证明只在其 target 内使用逆映射与实际 I=L 等式。

冻结陈述精确假设 mu 概率、AE |x|≤M 且 M≥0、AE lower≤x²≤upper 且 lower>0、实际均值为零、基准 parabolaCovariance(mu).det≠0、r>0。结论先选一个 0<epsilon≤1，再对所有 0<level<epsilon 产生 z∈原始 D_level，0<I(z)<+∞，z 对所有原始 D_level 点全局最小，并对整平面所有满足 I(y)≤I(z) 的 y 给 dist(y,(0,q))<r。公开 TYPE 的量词顺序、全平面最后量词和原尾全局量词均与冻结源相符。

1. 源 34–42 由 AE 有界构造 x² 的真实可积性。概率性给 ∫lower=lower，integral_mono_ae 得 q≥lower>0。这里 lower 的严格正性确实使用；不能将本定理悄悄推广到可能有任意近零能量的任意有界律。
2. 源 43–60 用已接受 JV 的实际 full-domain 得 0 内点；零倾斜恰为 mu，故原 hdet 正好满足旧 chart 对零倾斜协方差的条件。he 在 0 的等式给 e(0)=m，0∈e.source 使左逆 e.symm(m)=0 合法。没有先验把逆定义在整个平面。
3. 源 61–75 用 chart 保证 closedBall(m,R)⊆e.target，R>0 确保 m 在 open target。故 inverse 在 m 连续；accepted Frechet 保证 K 在 0 连续，通过 e.symm(m)=0 合成得 L 在 m 连续且 L(m)=0。最初编译失败只在 ContinuousAt.comp 多传一个点 m；最终合法形式 `hKsymm.comp hcont` 不改变上述数学内容。
4. 源 76–89 先为给定 r 取 KC 的 delta>0，再由 L 连续且 L(m)=0 得一个 rho>0，使 dist(z,m)<rho 蕴含 L(z)<delta。epsilon 的分母 sqrt(q)+1>0，R,rho>0，故 epsilon>0，且 epsilon≤1。它在 intro level 之前固定。level<epsilon 蕴含 level(sqrt(q)+1)<min(R,rho)；level>0 使 level sqrt(q)<min(R,rho)。无需暗加 level 与 r/图半径有关的未写条件。
5. 源 90–108 取明确 w=(level sqrt(q),q)。q>0，w 正好满足原尾边界等式。Lean 的乘积空间距离使用 max 度量，完整 `Prod.dist_eq` 展开确给 dist(w,m)=level sqrt(q)；这里没有误用欧氏范数公式。上一步保证 w 同时在 chart 的闭 R 球和连续性开 rho 球。chart 的完整 actual-rate 等式在 w 给 I(w)=(L(w):EReal)<delta，因而 I(w)≤delta 且有限。使用的 hrest 投影确为实际 I 等式，不是仅均值逆关系。
6. 源 109–114 把同一 mu/M/lower/upper、level、L=delta、上述明确 w 传给 JY。可行性参数 `(le_refl _)` 正是 level sqrt(q)≤level sqrt(q)。得到 z₂>0、原尾不等式、I(z)≤delta 及对所有原尾 y 的全局最小性质。KB 第二结论给 I(z)>0，实 delta<top 给 I(z)<top；不是只在人为闭球或有限截断尾集上的最小。
7. 源 115–116 对任意整平面 y，只要求 I(y)≤I(z)，则 I(y)≤delta，KC 立即给 dist(y,actual m)<r；hmean 只把实际 m 第一坐标替为零。最后一项没有 y∈尾域前提，因此其结论覆盖所有原尾全局极小点：任何另一极小点 y 也有 I(y)≤I(z)。这提供统一定位而未证明唯一性。

KD 裁决：依次先接受 KB、KC 后 CORRECT。无隐藏 theta 参数选择、无曲率或倾斜符号假设、无把存在某个 level 弱化为全部小 level 的量词变换。hdet 和 AE 正能量下界是显式冻结前提，本报告不删减或重新解释。

## 6. 全部实际 TYPE、生成声明和新交互

三份 `u22kb/kc/kd-actual-types.txt` 均全文读过，没有用结构摘要代替完整 binder、let、实例或目标。精确 SHA256 依次为 `2b44ed4ddef216487b7d41cadee19d06534956606bd5af6a19a758dccae0be6c`（2686B/47LF）、`7dab67acff7fa6cb900edea3149faa76fb41b1e3263877ba8c1570c4f8bff9bf`（1145B/26LF）、`0faa5b6c75161bc9f89579d565e6c46ac796e8aef8c3a24a59b584a9a5fc66b8`（2033B/33LF）。全部 9 个 standalone owner 记录均为 theorem，所需模块非 theorem VALUE 为 0；十五个 proof-local let 已单独覆盖。本报告以这些 hash 绑定全文，不重复粘贴 TYPE 附录。

KB 独立导入环境的完整六项为两条公开数学 theorem、一个本地生成 `_simp_1_4`、三个 shared namespace 生成 theorem。具体 shared 名为 `bivariateLogMGF.eq_1`、`bivariateLegendreRate.congr_simp`、`bivariateLogMGF.congr_simp`；本地 simp 的完整类型是任意 AddGroup 中 `(a-b=0)=(a=b)`，仅依赖 propext。三个 shared 类型分别为真实 logMGF 定义展开、mu/W/z 同余、同一域元素 theta 的同余，均未增强数学前提。KC 两项、KD 一项正是本报告的另外三条公开 theorem。没有因 namespace 不属于 Shao.OQ3 而漏审 KB 的生成声明。

已实际重新计算完整 `DECL/TYPE/AXIOMS/KIND` block：KB 的 `bivariateLegendreRate.congr_simp` 与旧 BY、IV、qualified JZ 的每块均为 438B、SHA `54727f0b65c228a4fd0424c7d165d9486e33dd982ad87722163cd3b29451dbdf`；KB 的 `bivariateLogMGF.eq_1` 与 qualified JZ 均为 421B、SHA `62684fb34437b71615072b27d09f97a25103039cf43e2aaacb9dfa97a2c7199a`。没有只比较名称或截断首行。

完整读取已有 `u22kb-legacy-import-check.lean`、record 与远端 `legacy-import.log`，没有重跑。该新交互程序 coimport BY/IV/JZ/KB，检查三 shared 全名实际 owner，检查五个具体数学目标仍存在，结果 RC0、`KB_BY_IV_JZ_COIMPORT PASS`、`OLD_AXIOM_COLLECTIONS 0`。log SHA `c88caed5b9b1c8f4f722df6efd02bb2ce264d657a041624242fd60bda8112f6e`，1408B。实际 owner 分别为 BY 的 PhysicalWindowRateFloor、JZ 的 BoundedCenteredParabolaSmallPositiveMinimum、KB 的 BoundedParabolaLegendreZeroSet；KB 首原对象保持不变，new/old producer builds=0。

这些证据消除本批具体旧新 coimport 的 uncovered risk，但不是全库无重名的证明。Root whole-current-owner 集成必须仍按完整名称去重，特别包括 `bivariateLogMGF.congr_simp`，不能把 standalone 的 6+2+1 直接称为全局新增 9 名。本报告不认证任何全局 new-name count，也不重复 qualified JZ/KA 旧证明审查。

## 7. 服务器内核、失败历史及全部递归 AX 证据

服务器路径三者均为 `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22{kb,kc,kd}-20261028`。本审者只读 glob 了每个目录的所有 `build-*.log`，然后完整读取 audit.log，另读 interaction log；没有照 KC/KD 旧 whole-logs 模板只读 build-01。远端 source-01/02/03 历史、当前源、工作树对象、accepted-source-view 解析目标/hash 均以只读方式核对，全部与回执相等。

| 单元/attempt | source SHA256 | RC | 完整 build log SHA256 / bytes |
|---|---|---:|---|
| KB001 | 9e526278b01d912ec4c981c0eb700bcd4edfc0bebc11704bf637103978f37899 | 0 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 / 133 |
| KC001 | 5232b5b5b376d28d8b373ff10b485423753ded4e817d1ddfadb5cccfbff98165 | 1 | 9dce2019e71633684a0706b7d0f33814093b35049ad533e7f623dddc63f3f3f3 / 638 |
| KC002 | 95b4e4977c087ea81efb4290753cf4f9ab8698356e35bf1a11e4c8e8e8f4f50b | 1 | 18649721c6cb4b6db04609544501b44b0dbcf0f6c0f1f4d000012b15eac21729 / 348 |
| KC003 | bcf54b06a346508d69f865e4bb785c685eb7c643588cb34530e3288f628999b3 | 0 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 / 133 |
| KD001 | d7737dc0fa4260fc6c7cb8fc7fcf12c297f18e10d08c1a3628199dbe095e7b63 | 1 | e92cab0f47be9b89109c1192261e70766bbba262bdb8e8af94861b31b2b847b0 / 406 |
| KD002 | d9d40d3fb394aed773e71b49740bbf26d40bd26d81c765a58383a71c38b7259f | 0 | fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626 / 133 |

KC001 的完整错误是 `hr.not_le` 不存在，兼有 dist_self unused-simp；KC002 是 literal set membership 未暴露成 r≤dist，因而 expected r≤0 的类型不合；最终差分仅为显式 typed h、正确 hr.not_ge 和实际需要的 dist_self 化简。KD001 是 ContinuousAt.comp 多传 m，最终仅删除该实参。均逐差分核对，五条冻结声明未动、数学推理未变；失败源和失败日志保留。三份成功日志仅含同一条 mathlib repository local changes 警告，所以其日志 hash 相同；这不把不同 source-bound 成功当成同一次执行。

| 单元 | 首次成功原对象 SHA256 / bytes | Audit 程序 SHA256 | 同原对象 audit.log SHA256 / bytes | TYPE / VALUE / public |
|---|---|---|---|---|
| KB | fad09a7f0ce32aae84bcf4f6d15cfc56cbb4e32e7e5314e3d424d46511de2898 / 183232 | f484c5d06b234ef03b57b0bbb624d789e7b05d315ccf8b6c5aca227e48bc4875 | 653687fe84776288908eb61515b91b4b8e8a9ddf941655b72db5740033eb5af3 / 2938 | 6 / 0 / 2 |
| KC | 48708a06cd60b86185be48252a145aab9e04d825b98ad0a634c1bdc3c4821da5 / 100832 | 278dd831985a69e592684071322e4b1e1e55292b526b2b778868864ca657b3a9 | 75afff81244788f6d97d0a7b0d4f26e9f539a8740c4a2c0c219a55892d07fdde / 1397 | 2 / 0 / 2 |
| KD | 3bf53bd70a5ba3dbf13e41ff8077a14bf69e2e6ed3ade7d23ba22955feb8af2f / 297040 | c70ee5687828f09dcebccdee6e8170288810cf55c7111d9a1e2baa2da908fbc0 | 60f20edf2e574404f8e58abe36ddb4304f9fe7bce496c1b7ebcbae7350947a67 / 2285 | 1 / 0 / 1 |

三份完整 Audit 都遍历 env.constants 并以 `getModuleIdxFor?` 比较真实模块 owner，未按 public namespace 筛选；每一项调用 Lean.collectAxioms，拒绝新 axiom 和 whitelist 外的传递公理，验证 frozen target kind/count，若出现 defnInfo 则检查 safe 并输出完整 VALUE。实际 allCount=theoremCount 分别 6/2/1，无 opaque 或 defnInfo 遗漏；所有传递公理仅为 `propext, Classical.choice, Quot.sound`（本地 simp 仅 propext）。三者 audit RC 均 0、各自 AXIOM_GATE PASS，并由 audit request 的 before/after 对象 hash 断言与当前只读对象复核绑定到同一首原对象。没有把另一版本成功或仅 target 的公理检查冒充 all-owner。

实际工作树 `lean-toolchain` 只读为 `leanprover/lean4:v4.36.0-rc1`；mathlib HEAD 只读为 `807d3836b165983210ee2ecf3cd28f239436949c`。已从该 pinned commit 全文读所用 Fermat/实数介入 EReal 的相关完整接口，且两实际工作文件与 pinned git-show 字节相同；保留 repository local changes 警告，不据它声称全仓无本地修改。作者回执均为 server-only `-M8192 -j4 -DautoImplicit=false`、phase40、CPU36–39,44–47、现有 c12-heavy.lock；memory 回执保存 raw 和 cache-aware admission，不改变资源政策。本审者没有持锁或执行 heavy。

机械裁决是精确局部冻结目标的已有 `LEAN_FULLY_CHECKED` 证据通过，并完成本报告的 source-to-statement 语义核验；它不表示原始 D 或 full OQ3 被 Lean 完整证明。

## 8. 适用性、贡献边界与最终释放

对原文有限正幅值对称律，这三项的一般 bounded-law 接口是适用的承重步骤：有限正幅值带来有界及正能量下界，中心化与实际 covariance det 非零仍须由该具体 law 的既有构造证据满足。它们不自动替原文 witness 省掉这些证明，也没有 formal consumer 把全部原文条件自动打包。KB 的严格正率本身不需 hdet；KD 得到小 level 的严格正、有限、全原尾全局最小值和全低率子水平局部化。KC 的整平面均值外 gap 与 KD 的均值邻域定位不可标成正尾唯一鞍点外 far gap。

当前明确未闭合：正 level 全局极小点唯一性、正则边界鞍点的参数识别、theta₂<0、正切向曲率、围绕该唯一正尾鞍点的原文远区率间隙，以及原始 D/full OQ3 全部结论。原始 D/full OQ3 状态均保持 OPEN。本报告没有认证新颖性或论文核心贡献；这里使用的是可明确检查的 Legendre/Fermat/紧性与局部逆映射论证，在项目同一实际率对象中闭合辅助依赖，不能包装成已解决原始开放根命题。

最终建议：先以本报告接受 KB368 的精确源及已有首原对象/AX；再接受消费该接口的 KC369；最后接受消费两者的 KD370。三个 CORRECT 均指冻结 scope，没有关键缺口或要求改数学前提的修订。qualification、manifest、status 和 Root 集成由父 owner 处理，本审者只交付本报告。

完成操作：最终修改后本审者全文读回本报告，重新核验全部 81 map rows、三 map/scopes/source/freeze 字节；报告为 UTF-8、LF、无 BOM/CR。报告自身 SHA256/bytes/LF 在本审者完成消息中给出，以免自包含哈希循环。随后释放本报告唯一 writer，状态 `COMPLETED_STOPPED`；heavy=0，inflight=0，pending=0，uncertain=0，children=0，`NO_NEXT_TASK`。本终审没有持久继续机制或未完成后台任务。
