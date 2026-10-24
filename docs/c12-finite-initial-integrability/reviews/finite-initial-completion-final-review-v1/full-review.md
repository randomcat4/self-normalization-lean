# 实际有限路径初始完成：独立最终审查

STATUS: CORRECT

两个模块共八个完整源证明、十五个实际模块所属完整类型、两个非定理完整值以及十五个递归公理结果已全部审查，未发现关键缺口。`Shao.C2.FiniteInitialCompletion` 的四个公开声明，以及随后追加的 `Shao.C2.TruncatedScalarBudget` 的四个公开声明和两个透明定义，均与各自实现前冻结的完整声明一致；各自原成功内核、全所属公理审计和全部收据工件均已按精确字节复核。本结论只接受以下局部依赖，不关闭 C1/C2 或其他原根。

审查者 `/root/finite_initial_completion_final_review` 未参与被审源码写作，使用全新 gpt-6.1-sol/xhigh 上下文、math-theorem 与中文输出规范，没有使用 math-ultra 或再委派。模型/努力等级依据本次显式委派配置；上下文不暴露独立运行遥测，输入、缓存输入、输出、推理子集四项用量均记为 null。唯一写目录是本报告目录；生产源、冻结、旧证据、library、共享实现和版本锁均未修改。

## 精确范围与绑定

源 SHA256 为 `137372daf442c41cdd5d31d8f49b2fabf9b7aad82a0f41a9d6ab686e2474712b`（4930 字节）；原成功对象及当前对象均为 `ef563f8a7afddff2d1f12a9ecaa3b39330aad3ff5df7bc58e04e4b678b5fcd3b`（171728 字节）。冻结 SHA256 为 `0da2db8aaa1a18d91d2c9af7bc7cd5af81477f588867b4fa09dacc694b3ecb9e`；作者收据 SHA256 为 `8a738481446214e824b2ce2e29eacc069feb87e1c57a4a5543f912db394587a7`。

完整实际类型文件为 17814 字节、SHA256 `960d2498c64d68042f29843ff4f69be680cff491a8133836358cf860ccc0ae42`；定义值文件确实为空。四个源定理及四个生成 simp 定理构成全部八个实际所属。OwnedAudit 使用 `env.getModuleIdxFor?` 和实际模块索引全选，然后逐个递归 `Lean.collectAxioms`，没有按命名空间或公开名筛选。全部结果只含 propext、Classical.choice、Quot.sound 的子集。源码是 UTF-8、无 BOM、LF，未发现 sorry、admit、新 axiom、unsafe 或 native_decide。

## 原文到形式陈述

完整读取只读来源 `C:/game/shao/current/c12/main.tex` 1038–1076 行（cn:initial）与 `supplement.tex` 3914–4025 行（S.8.2、S.8.4 的定义、估计和证明上下文）。两源文件 SHA256 分别为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` 与 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。

本单元的输入是实际有限路径归一化端点的闭分布函数与标准正态闭分布函数的显式一致差界 δ≥0。它没有把目标路径误差或零能量概率界放入前提，也没有把真实能量替换为方差、中心化能量或任意抽象非负变量。`Path n = Fin n → ℝ` 配以实数 Borel 结构的乘积；`energy z = ∑ i, (z i)^2`；`prefixSum z n = ∑ i, z i`；`normalizedEndpoint z` 在 energy=0 时明确为0，否则是最终和除以真实能量平方根。上述定义、`energy_nonneg`、`measurable_energy`、`measurable_normalizedEndpoint` 和零能量端点定理的完整源接口均已读取。可测性实际沿有限和、平方、平方根、除法以及零能量可测分支建立。

方法偏离是明确且合法的：原 cn:zero 从截断平方和 U 的期望/方差和 Chebyshev 不等式独立推出 16R；本单元在已经明确给定的标量 CDF 输入下，用无原子参考律的闭/开 CDF 差界推出零点原子≤2δ，再由真实零能量事件包含于端点零事件得到 P(Q=0)≤2δ。此路线不冒充独立的 16R 证明，不提高矩条件，也不消除尚未形式化的标量 δ≤CR 输入。原文 Pinelis2011 式(1.10)、定义(1.7)复述 Shao 截断标量界的归属保留。

P 可为任意 `Path n` 上的概率律，因此结果涵盖 iid 产品律；本单元没有使用独立、同分布或中心化隐藏前提。那些条件属于未来标量估计实例的适用性。所有自然数 n（含0）、所有实数 a、v、全时刻严格区间生存及闭阈值 `≤v` 都保留。n=0 时端点恒0，输入 CDF 界本身限制 δ，不会凭空给出任意小误差。a≤0 的严格生存为空，与完成函数定义一致。

## 四个源证明和全部生成声明

1. `atom_le_two_cdf`，10–36 行：`lower_set_discrepancy` 给出 Iio x 的差界；显式 hρx 使参考律的 Iio/Iic 实质量相等。Iic x∩Iio x=Iio x，Iic x\\Iio x={x}；概率测度有限性满足 `measureReal_inter_add_sdiff` 的前提。闭 CDF 差的上界和开 CDF 差的下界相减，精确给出 μ.real{x}≤2δ。没有对 μ 无原子作假设，也没有错误地把 μ 的开闭 CDF 相等。
2. `normalized_energy_zero_le_cdf`，38–64 行：可测的真实 W 的推前 μ=P.map W 为概率律；HasLaw 的可测闭集质量身份把原域输入精确转为 μ(Iic x) 的输入。Mathlib `nullSingletonClass_gaussianReal` 只要求方差参数非零，参数1满足条件，因此标准正态0点无原子。HasLaw 的可测单点质量身份给 P(W=0)=μ{0}，真实 `normalizedEndpoint_of_energy_eq_zero` 给 {energy=0}⊆{W=0}，概率有限性允许实测度单调性，结论为2δ。
3. `finite_initial_marginal_error_of_cdf`，66–81 行：把 P、真实 W、真实 energy、W 的几乎处处可测性、energy 可测性和处处非负性代入已合格的 `InitialCompletionError.initial_marginal_error_of_cdf`。该精确接口给出的是真实布朗运动严格生存概率与实际零能量删去积分之间的界 2δ+P(Q=0)。用本模块第二定理支付零能量项，线性算术给4δ。没有使用不可积积分的默认值；可积性由所复用的合格接口建立。
4. `finite_initial_joint_error_of_cdf`，83–100 行：同样代入已合格闭阈值联合接口，保留积分中的 `normalizedEndpoint≤v` 分支及目标中的 `B 1≤v`，再支付零能量项。没有额外耦合条件，B、PB 可在另一概率空间上；最终概率仍是同一 B、PB 的全时刻生存且闭端点事件。

四个生成 simp 定理的完整实际泛化类型也已逐个读取：集合差成员的合取等式、Iic 成员与≤的命题等式、Iio 成员与<的命题等式，以及单点成员与相等的命题等式。它们关联第一条源证明的集合恒等式；没有私有、生成所属或非定理值遗漏。全部八个实际类型原样阅读，没有用类型摘要替代。

## 依赖接口与证据复用

复用已合格的完整独立审查：endpoint-cdf-transfer 的报告 SHA256 `7f07295d860e5b27e68b01e1ca000f2e57a749d3e220b2888171188e77fd453d`，standard-bridge-law 的 `7eb667d7e53782be5eee0aff695d1965acda9d7db8d8a931c8e74d37760d5461`，initial-brownian-identity 的 `99413ee8c1e05d15bbbda14ecb30a27178b7481a2919d6294725f1018ed2667d`；BridgeDomination 的接口另按其原合格 bridge-permutation 报告 `568c781dac68a0ecb79e401897d30ceaa70dead2966fa77f47f9972406b29ed2` 逐项绑定。模型、全新上下文、独立性和对应完整覆盖已核对；未重审旧模块的完整证明。

实际消费的 `lower_set_discrepancy`、两条 InitialCompletionError 误差接口及 BridgeTime、BridgeNoise、bridgePath、strictInterval、intervalCompletion、bridgeLaw 共九个完整实际类型、六个完整透明值均已读，并与旧报告 `allOwnedCoverage` 的精确类型/值哈希一致。桥的时间域是闭单位区间，桥噪声是两端为0的连续路径；桥路径是 (1−t)y+tz+√Tg(t)，区间完成是全时刻严格上下壁交事件的真实概率。实际 strictUpper/strictLower 源定义和 bridgeNoise/pinPath 的源定义亦已读，以确定输入确实是同一布朗桥完成机制。

仅上述依赖重复子表达式使用旧报告的无损字典。字典及编码文本均完整阅读，脚本验证递归展开后逐字节等于原始完整文本，并逐项匹配旧合格哈希；未声称重复读取所有重复原始字节。新模块全部八个类型直接原样读取。

服务器六个已合格依赖模块的当前源/对象对全部精确匹配原合格证据。五个旧模块 MeasurablePath、Normalization、Events、FinitePath、TwoSided 的本地只读库源、当前源/对象，以及已接受 v71 的精确映射均一致。原映射在 `logs/integration-v71/baseline-reuse.json`，SHA256 `2d21a615db45ce0d85388bfdabfd9b5579b23db197065739fe2e791481342419`；该映射实际含551源、1328对象，本审查只核对这五行，并核对 `workspaces/integration-bearing-v71` 中对应接受源/对象字节。初次在 outputs 等常用路径未定位到映射的只读记录保留，随后只补此精确定位核验。

Mathlib 的实际 `Iio_ae_eq_Iic'`、`measureReal_inter_add_sdiff`、`nullSingletonClass_gaussianReal` 定义条件已在固定版本源中核对，分别满足参考点无原子、有限测度及 Iio 可测、方差1非零的使用要求。

## 服务器证据、Git 变化与释放

工具链 `leanprover/lean4:v4.36.0-rc1`，Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，包视图 shared-v34；工作树 `workspaces/c12-bridge-domination-v71`。作者 attempt003 内核退出码0、全所属审计退出码0。所有收据工件的字节数/哈希相符；原审计日志与完整类型文件的八块内容逐块精确对应，定义值块确为0。保留 attempt001 缺失旧对象、attempt002 Iio 参数推断失败的原源码/日志；只有原成功 attempt003 被复用。成功日志中的 mathlib 既有修改提示及两个 letI 风格建议不构成证明缺口，没有为消除提示重编。

首次证据只读观察时分支为 `author/c12-brownian-bridge-law-v71`、HEAD `b56cc6506b5352786c0c28f70cff68e522481a11`。lead 发布旧六模块 PR257 后，仅 Git 行政状态变化；最后观察于 `2026-10-24T06:02:24.777934+00:00`，分支为 `author/c12-finite-initial-v71`，HEAD 为 `01c4cb2b0092402bf89556fe2c75cd861ab7bfaf`，被审源仍为唯一此路径的未跟踪文件，源/对象哈希保持不变。没有将 HEAD 变化误当作数学变化或重跑旧门。

本审查 Lean 调用0次、producer 重编0次、heavy 命令0次；最后只读观察 C12 无 Lean/lake 进程、c12-heavy.lock 无持有者。只读观察脚本第一次因 lslocks 返回空 path 引发 TypeError 的响应已保留，仅修复该观察器并重做失败观察，未影响任何证明源或旧收据。审查者无在途操作，报告写入/执行权限释放给 lead；未曾取得生产写权限。

接受的局部结论是：实际有限路径端点闭 CDF 输入 δ 推出真实能量零事件概率≤2δ，并推出实际初始布朗边际/闭阈值联合完成误差≤4δ。独立原 cn:zero 的16R证明、外部截断标量 δ≤CR、三域/telescope、terminal/overshoot、核商与光滑性、C1/C2 根结论仍 OPEN；OQ3 保持用户暂停。下一源依赖由 lead 继续冻结和调度，本报告完成不表示总任务停止或持续运行机制。

## 同一独立上下文追加：真实截断标量预算

lead 在本上下文审查有限路径单元期间独立冻结并实现 `Shao.C2.TruncatedScalarBudget`，随后才交给本审查者。新增四个源定理证明、七个实际所属完整类型、两个完整透明值及全部递归公理均已完整审查；先前有限路径证明未重审。合计十五实际所属为十三定理、两定义，其中八个公开源定理、五个生成定理。

新增源 SHA256 `16dce108e7050358da813e5ae7b5cdd9c4559d71146236b44a4a2a1b4b4525e3`（3882 字节），原 attempt001 与当前对象 SHA256 均为 `0c91831c76b49b99212ebfae5f553135ed233c877da65541e45db21bb295f9e7`；冻结为 `649e219551fbe95afad51077188e1004bacb6a63626f5143dfde8a4ad184967d`，收据为 `fc024b69c88df976ea9282e5b3eba9b9cb0a6295818dd62e70d037f106102c57`。七个完整类型文本为21515字节（SHA256 `c6dcd426def357cc183b39fc40e8da924b844821f7733f0697e34074279795f8`），两完整值为3858字节（SHA256 `c4a86bd6373a63615effb78abdf71edb23ba9cca8eca9fcc5a9580c8c7718e5c`）。新增类型/值均直接原样完整阅读，未使用摘要或省略。

两个实际透明定义精确为 γ₂=n∫z²1{|z|>1/2}dν 与 γ₃=n∫|z|³1{|z|≤1/2}dν。严格大截断、闭小截断覆盖边界，10.2 精确写成51/5，真实预算 R₀=`truncationBudget ν n 0`。旧 `truncationF` 的完整透明定义是 z²min(|z|,1)，旧 `truncationBudget` 的完整透明定义是 n∫F((1+t)z)dν；消费的 nonneg、decomposition、scale_one_le 以及两截断可积性声明的完整参数/类型已读取。旧源显式设置 autoImplicit=false，涉及的测度、n、平方可积、t/c 和阈值条件均未隐藏。旧证明按 v71 接受证据复用，没有重新证明或重编。

1. `scalar_gammas_nonneg`：两个被积函数处处非负，n≥0，积分非负给出两个量非负。本辅助声明对任意测度成立；后续预算推导仍明确要求平方可积，没有用不可积积分的默认值支付实际标量误差。
2. `scalar_gamma_sum_le_budget`：给旧分解 t=1，条件 −1<1 成立，得到 R₁=8γ₃+4γ₂。给旧放缩 t=0、c=2，1≤2 成立，其上界是 R₁≤8R₀。γ₃≥0 使4(γ₂+γ₃)≤8γ₃+4γ₂，故 γ₂+γ₃≤2R₀。h2 保证尾平方积分以及小截断三次积分真实可积；没有要求全局三阶矩。
3. `scalar_weighted_error_le_budget`：51/5≤25、γ₂≥0 给(51/5)γ₂+25γ₃≤25(γ₂+γ₃)≤50R₀。证明没有把51/5误写成整数除法，也没有遗漏非负性或变更预算。
4. `iid_initial_errors_of_truncated_scalar_input`：完整声明显式保留概率律ν、n>0、平方可积、均值0、n∫z²=1；P 的实际依赖 let/have 绑定精确为 `Measure.pi (fun _ : Fin n => ν)`。有限产品概率实例满足先前有限路径接口。令 δ=50R₀，预算非负保证 δ≥0；显式 hScalar 加第三定理给同一真实 W、同一 P 的闭 CDF 差≤δ，然后分别消费本上下文已经完整审查的两条4δ界，得实际边际/闭阈值联合误差≤200R₀。所有 a、v 实数、真实 energy、零能量删去分支、闭阈值及同一 B、PB 的目标事件均保持。hn、hmean、hnorm 在代数传递中不使用，但确实保留在最终实际类型中；它们记录外部输入的标准化中心 iid 范围，不能删去后声称证明了外部定理。

新增唯一生成定理 `scalarGamma2._proof_1` 的完整实际类型是 `Nat.AtLeastTwo (1+1)`，供两个有理截断常数的数值实例使用；它是定理而非遗漏的非定理值。OwnedAudit 同样按实际模块所有权选择七个常量，5定理/2定义，逐个递归公理均仅在标准白名单内。两个完整透明值中出现的该生成定理引用已覆盖。

条件化范围必须明确：hScalar 是同一实际 iid 端点 W 的外部一维闭 CDF 界 `(51/5)γ₂+25γ₃`。它是显式定理前提，不是新增公理、已形式化的 Shao 标量定理或目标初始路径概率界。来源 supplement 3943–3953、4011–4016 的 Pinelis2011(1.10)/(1.7)复述 Shao 的归属原样保留。本单元形式化了预算支付和条件式实际 iid 装配，未证明外部标量界、未独立完成原16R零能量论证，也未要求更高矩。

两个新增旧依赖 TruncationIntegrals 和 Basic.TruncationBudget 的本地库源、当前源/对象、原 v71 baseline-reuse 精确两行及 `integration-bearing-v71` 对应接受源/对象均相符；仅两个既有只读叶链接被复用。有限路径依赖源/对象仍与先前已审版本精确相同。未重编旧 producer，未重复先前有限路径成功门。

新增原 attempt001 内核、公理审计均退出码0；收据全部工件精确匹配。原成功审计日志与七个完整类型块、两个完整值块逐块相同。新增成功日志保留 mathlib 既有修改提示及 hn/hmean/hnorm 未用参数建议；没有为消除建议修改冻结声明或重编。最后新增证据只读观察仍为 `author/c12-finite-initial-v71`、HEAD `01c4cb2b0092402bf89556fe2c75cd861ab7bfaf`，C12 无 Lean/lake 进程、无锁持有者，审查者无在途操作。

两模块合计 Lean 调用0次、旧 producer 重编0次、heavy 命令0次。报告写入/执行权限释放给 lead。新增可接受局部结论是：平方可积给 γ₂+γ₃≤2R₀ 与加权误差≤50R₀；在明确外部 hScalar 前提下，实际标准化中心 iid 的两条初始完成误差≤200R₀。外部标量证明、原独立16R、terminal/overshoot 和 C1/C2 原根仍 OPEN。

逐所属覆盖、全部字节绑定、依赖接口哈希、服务器响应及释放状态见同目录 `full-review.json`。
