# U16b 完整独立证明、来源与类型审查

STATUS: CORRECT

唯一审查 lease 1。只拥有本报告及服务器 run 对应 proof-review.md；不修改作者源码、scope、旧票、共同文件或缓存，不 spawn、Lean/probe/构建/复编。并非独占代码库，保留他人编辑。承认此前声明审查上下文存在；本次重新仅提取实际公开定义完整体和定理完整类型，独立翻译先落盘，尚未读取实际证明或本次机械证据。

## 第一阶段：actual 公开定义体和完整类型盲译

实际输入 PositiveLayerTail.lean SHA256 `ebcef2d9ada2df9973a16ab8f1c9806c304dbaf1d01731c9de5ffcfd9d12172a`，4600 字节、96 行。本阶段只读一个定义完整体及一个定理完整类型。

`positiveNormalLayerTerm`：对任意实数测度 mu、实数 q/ell/h/theta、自然数 n/k，定义实数 sqrt(n)·exp(−ell·h·(k+1−theta)) 乘真实 n 重 Measure.pi(Fin n→mu) 对事件 normalDeviation(q,z)=h(k+1−theta) 的 real 质量。没有改变已有 Path、normalDeviation 或 mu；定义自身无概率或正性门，故证明必须由定理门保证 .real 对真实有限概率的含义。n=0 的 sqrt0 系数为0，未设置约掉 sqrt n 的定义。

`exists_stage_positive_layer_tail_bound`：给定真实实数概率 mu、固定自然阶段 J、实中心 q/a、ell>0；同一 mu 几乎处处 |x|≤4+sqrt10，真实 E(normalValue)=q、EX=a，真实 normalVariance(mu)>0 与 parabolaCovariance(mu).det>0；同一实际有限阶段支撑为 stageAtom(Fin4⊕FinJ)、新增点 addedAtom(j.val)，且每个活跃原子有严格正的 mu.real 单点质量。在这些输入之后，∃一个实 C>0，使对自然 n 最终成立：对所有 theta∈闭区间[0,1]，实际 k↦positiveNormalLayerTerm(mu,q,ell,dyadicMesh J,theta,n,k) 是真正 Summable，且对全部自然 K，真实移位尾和 ∑'k term(K+k)≤C·exp(−ell·dyadicMesh J)^K/(1−exp(−ell·dyadicMesh J))。

C 和同一个最终 n 阈值都在所有 theta 与所有 K 之前；没有 theta 相位相容、d 有界或 n≥1 的额外结论门。J=0 合法；theta=1、k=0 允许零层，theta=0 从 h 开始，K=0 即全和。需真非负实际项、rho∈(0,1)、分母>0，并在比较实 tsum 之前建立左右两侧可和。不得从不可和实 tsum 总化为0或 ENNReal.toReal_top 获得尾界，也不能逐 theta/K 改阈值。

本盲译先落盘，随后才读冻结 scope/R1、全部实际 proof/locals 与实际库，之后全部 actual TYPE，最后作者 receipt/真实机械事实。这里只审固定 mu/J 的正层权重尾，不把结论提升为紧倾斜族、完整负层支配或 LLT。根 A/B/C/D、完整负层支配、完整 LLT 与 hW 均 OPEN。

## 第二阶段：冻结类型、真实来源和继承接口

盲译先落盘后，读取完整冻结 scope、此前声明票、真实 R1 与全部实际96行实现。scope SHA256 `6fd7a6124bf672404f31d658f01250987f9bcdef69020cbb47e5a388cc9527f5`，statement SHA256 `80d04a156e6c5128dfae47d463cac8206b3d94599048d0c3cbbefa158f80a797`。本次独立提取 actual 定义完整体与定理完整类型，去空白后均与冻结 fence 完全相同，没有新增门、改测度、改层位置或改量词。

真实 R1 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次直接复核389–403及411–429行。390–392行给正层所用标准 scalar sup_d 质量 C/sqrt n；400–403行真实层网格是 h(ℤ−theta_nJ)，theta_nJ={nq/h}；421行是似然 exp(−ell d)；428–429行明确正层截尾由几何似然权重完成。因此当前正层权重和界来源充分，但不包含负层(17)、整个(19)极限或 LLT。scope 范围概括到428时，对应句子实际延续到429，本票保留此精确说明而不改冻结历史。

actual U16a 源 `NormalLayerMassBound.lean` SHA256 `66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1` 的206–218行完整类型已重新在指定服务器读取。它对同一真实 mu,J,q,a 和全部本单元 hb/hq/ha/hS/hD/hrange/hpos 给 ∃C>0、最终 n、然后∀d:ℝ 的真实产品层 real 质量界，恰好是36–37行消费的门。U16a 完整独立票 `2ad0fb6fbfeb948653bc1e8cf6ac854395b896fed7fa281defcb8c29aca3cb6f` 已接受，不重复其成功构建。本单元未借条件律补定义、仅可达层渐近或 bounded d 结果来代替这个全实 d 的统一门。

真实统计量仍是 Path n 上 ∑Y−nq、Y=normalValue=8x−x²，h=dyadicMesh J=(2^J)⁻¹；mu 是给定的实际有限活跃 stage 原子律，不另构造任意 q/a 概率。probability pi 是同一 mu 的实际 Fin n 产品，finite measure 实例使其每层质量有限，.real 是真实有限概率，不是 top.toReal 伪零。正协方差与有限活跃原子条件经既有完整链传入 U16a，不在本单元重复假定任意 det>0 就足够。全部承重闭包的实际哈希留最后机械阶段核对。

## 第三阶段：全部96行 actual proof 与每个局部辅助

以下数学审查先于 Audit TYPE 和作者 receipt/绿灯读取，并先落盘。

第1–13行保持冻结 imports、namespace、open/open scoped 和 noncomputable 环境。第15–18行完整定义正是盲译的三因子实乘法：sqrt n、真实 exp 权重、真实 Pi 的 real 层质量；无 authored private 定义或 theorem。是否存在编译生成 owned 项，留待实际 TYPE 盘点，不从源码行数推测。

第36–37行先以全部同源输入从 U16a 一次性取 C,hC,hbound。第38行实际 hmesh>0 对所有自然 J 有效（J=0 时 h=1）。第39–44行 rho=exp(−ell h)，exp_pos 给 rho>0；hell 与 hmesh 给 ell h>0，exp_lt_one_iff 得 rho<1；abs_of_pos 得 |rho|<1，再显式建立 hden:0<1−rho。由此真实几何级数可和。hden 后续不需被当作除法约分前提消费，但它已严格记录输出闭式的非零正分母，不是未经门控的 totalized inverse。

第45行选择同一个 C>0；第46行仅 filter_upwards [hbound] 确定 n,hn 后，第47行才引入任意 theta∈[0,1]。所以最终 n 事件在全部 theta 之前，且下文第74行才引入 K。无逐 theta 或 K 另选阈值，没有从一个固定层的界偷换成对所有层统一的界。

第48–51行 hnonneg(k) 展开 actual 定义，以 sqrt_nonneg、exp_pos.le 和 ENNReal.toReal_nonneg 证明真正的实际加权项非负。虽然后一个引理对任意 ENNReal 可用，本类型中真实 Pi 已是有限概率，因此其含义不依赖无穷质量转0。这里没有发生积分/Fubini/概率互换，也不需要将一个有限实项当作已可和。

第52–68行 hmajor(k) 逐项独立有效。第54–59行先把 rho^k 用 Real.exp_nat_mul 改写成 exp((k:ℝ)(−ell h))，再用真实 exp_le_exp.mpr。实际 hh=ell*h*(1−theta)≥0 来自 htheta.2，nlinarith 恰好给 −ell·h·(k+1−theta)≤(k:ℝ)(−ell h)，指数方向正确，没有负号反转。第62–64行 ring 仅重排乘法，将真实项写成 exp(−ell d)·[sqrt n·真实层质量]；第65–66行把 hn 在实际 d=h(k+1−theta) 实例化并乘严格正指数。第67行使用 hC.le 将 hexp 乘 C≥0，第68行交换成 C rho^k。没有除质量、除 sqrt n、或假定 d>0；htheta.1 对源正层语义合法而在上界推理中冗余。

第69行先证明大项 k↦C rho^k 的 Summable；第70–72行随后用实际非负比较门得到实际层项的真 Summable，第73行把它作为结论第一分量。这里未先使用 tsum、未用不可和 tsum=0；不存在把实级数与 ENNReal 无条件可和混同的情况。

第74–85行处理任意 K：hmajorShift(k) 直接用 hmajor(K+k)，然后 pow_add/ring 得 (C rho^K)rho^k。它保持目标的 K+k，没有套错库常用 k+K 的移位语义，也无需调用 summable_nat_add_iff。第81–82行先由真实几何可和得移位大项可和；第83–85行再以 hnonneg(K+k) 和 hmajorShift 比较，得到实际移位小项真可和。两侧 summability 均已先于最终 tsum 比较明确建立。

第86–93行 hsumShift.tsum_le_tsum 实际消费逐项≤和两侧 Summable；随后 hsumrho.tsum_mul_left _ 从真正几何可和提常数。最后先 rw 真正 tsum_geometric_of_abs_lt_one habs，得 (C rho^K)(1−rho)⁻¹，再 rfl 仅展开 rho 和实除法的乘逆定义，准确得到 C exp(−ell h)^K/(1−exp(−ell h))。没有非法约分、没有丢 K 次幂或错一个 rho 因子。正的 hden 确保这个闭式在数学上是有限正分母几何和。

边界逐一检查：theta=1、k=0 时 d=0、exp0=1=rho^0，实际 hmajor 等号边界允许；theta=0 首层 d=h，本界故意只用更松的 C rho^k，未错误重复添加 d0 项。K=0 时 pow0=1、尾等全和；J=0 时 rho=exp(−ell)仍在(0,1)，四基点活跃门不消失。n=0 定义项为0；本定理只输出最终 n，但证明中无任何 sqrt n 除法或 n>0 消去，原 hbound 未改阈值即可。theta 不需与 nq/h 匹配：U16a 已为全部实 d 提供真界，离网格层本来真实为0。ell>0 不能省略或代入0后还声称分母>0；本类型保留了严格门。

本单元仅建立固定 mu/J 的正层权重可和与统一 theta/K 几何尾界。未调用切向事件/条件 Lévy、LLT、实际完整源层和极限；没有将此结果提升为 J/ell/紧倾斜参数族共同常数。全部96行、每个 let/have/calc/filter 辅助均已逐步核对，数学阶段结论 CORRECT。

## 第四阶段：实际固定库语义

在指定服务器只读实际库相应完整声明与门，没有 Lean/API probe。

- SpecificLimits.Normed SHA256 `eee44dfd62feb67bdf3ccc6cf57e8e101f38a7408dbb9c6347e0978ce2010d41`493–497行，summable_geometric_of_abs_lt_one 与 tsum_geometric_of_abs_lt_one 的门正是 |rho|<1，后者真和为 (1−rho)⁻¹。
- InfiniteSum.ENNReal SHA256 `88ef56c969006630d0066b7af2c74e75dd060608f3c42f0ef288ad1c6da908cc`532–537行，实际 `Summable.of_nonneg_of_le` 参数 f,g 都是实数函数；需 g≥0、g≤f、Summable f 后才得 Summable g。第72、85行两次调用均实际提供全部三门。
- InfiniteSum.Ring SHA256 `bba1f8897f3b78060d4893ee3b47f8edf6f533d2adca7909305d0a42ee50c087`43–44行 Summable.mul_left 及53–55行 Summable.tsum_mul_left，在ℝ真实拓扑环/T2/标准求和滤子 NeBot 下适用；使用的是带真实可和门的等式。
- InfiniteSum.Order SHA256 `526aed3d15913b1d7ad9de9f28fc26ac9ab023942b0d80cbc72323a293817b01`132–135行 to_additive 生成 Summable.tsum_le_tsum，必须有逐项≤与左右两个 Summable；第88行全部消费，没有套 ENNReal 无可和门版本。
- Complex.Exponential SHA256 `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`234–235行实际 Real.exp_nat_mul，317–318行 exp_le_exp、337行 exp_lt_one_iff，正好支撑自然幂转换、指数方向和 rho<1。
- Constructions.Pi SHA256 `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`303–313行给真正有限 n 产品有限/概率实例；Measure.Real SHA256 `1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d`40–53、65–66行表明有限质量下 .real 和原 ENNReal 概率匹配，非 top.toReal。实际同一概率与 normalDeviation 可测层解释沿既有接受链保持。

这些真实库文件及公开导入路径已在本单元声明票独立静态检查，本次重新核对实际消费的精确门。源码没有私有库 API 依赖或额外可积性互换。数学阶段先保存完毕之后，才读全部 actual owned TYPE；作者机械证据仍留最后。

## 第五阶段：所有 actual owned TYPE 完整核对

上述全部数学审查先落盘后，从真实服务器现有 Audit.log 只过滤 DECL/TYPE 和所有长续行；此阶段尚未读 AXIOMS/PASS/receipt。实际两项为：

1. `Shao.OQ3.exists_stage_positive_layer_tail_bound`，实际第2–21行完整类型全部读取。mu 真概率、固定 J/q/a/ell、ell>0、同一 hb/hq/ha/hS/hD/hrange/hpos 全在 ∃C 前；之后 C>0、最终 n、再∀theta∈Icc0 1，结论同时给真 Summable 和∀K 的真实 K+k 尾和界。精确指数、dyadicMesh、rho 的 K 次幂与分母均与 actual/frozen 类型相同。没有漏掉长续行中的概率门或把可和性/全量词挪成额外假设。
2. `Shao.OQ3.positiveNormalLayerTerm`，实际第24行完整 TYPE 是 `Measure ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℕ → ℝ`，与 mu,q,ell,h,theta,n,k 七参数的完整 actual 定义一致，没有隐藏 IsProbabilityMeasure 或阶段限制。实际定义体已逐字独立审查，不仅凭此箭头 TYPE 推断定义语义。

实际输出只有该公开定理和公开定义；没有另列 authored private、generated theorem 或定义方程常量。此 inventory 取自真实输出，不因先前预计数量而省略检查；最后机械阶段再核 Audit 的所有权覆盖与计数。当前全部 actual TYPE 阶段结论 CORRECT，之后才读取作者 receipt 与真实机械证据。

## 第六阶段：最后读取的真实机械证据与完整绑定

数学和全部 actual TYPE 先完成并落盘后，才读取本地 U16b-receipt.json、真实远端 receipt、Audit.lean 与 AXIOMS/PASS、现有 build/olean、版本与闭包。此机械阶段没有执行任何 Lean/API probe/构建/复编，也没有下载完整原始日志。作者门与本票独立数学判断分离。

- 本地 actual、服务器 worktree `Shao/OQ3/PositiveLayerTail.lean` 与 run 源快照均为 SHA256 `ebcef2d9ada2df9973a16ab8f1c9806c304dbaf1d01731c9de5ffcfd9d12172a`，4600字节/96行。真实源无 CR、尾空白或 sorry/admit/axiom/unsafe/implemented_by/extern；完整定义体与完整类型已由本审查独立去空白比较冻结文本，两项均相同。scope 两端 `6fd7a6124bf672404f31d658f01250987f9bcdef69020cbb47e5a388cc9527f5`，声明票两端 `80d04a156e6c5128dfae47d463cac8206b3d94599048d0c3cbbefa158f80a797`，均绑定本次冻结输入。
- 本地与实际远端 receipt 均5818字节，SHA256 `332d6c64caac11572a0f1f4c2358be1d2b5dda5b686c895943082a3dfe1adb83`。其中 pending 与 No U16b commit/PR 是 author-check 时的历史状态，不替代本票最终状态。
- 真实 build-01.log 为0字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。exit0 和实际 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/PositiveLayerTail.olean Shao/OQ3/PositiveLayerTail.lean` 命令由作者保留回执记录；空文件本身不独立证明退出码。实际目标 olean 存在，188848字节，SHA256 `1d00d2c8a6adf494b6339ea2d81449e4cca732c254802bca46fb59c5307a8c09`，未复跑成功命令。
- 真实 Audit.lean 为1637字节/36行，SHA256 `b2270afddc56dac70b9e31cb72f6d0070a43f1e22968da104f77ce511a7d85f5`，全文核读：导入真实目标、核冻结 theorem 的 isTheorem 和正层定义的 defnInfo，再遍历正层定义/目标的完整 stem 与整个 `_private.Shao.OQ3.PositiveLayerTail` 前缀。对每个 owned 项拒绝 isAxiom，并用 Lean.collectAxioms 检查全部传递依赖，白名单仅 propext/Classical.choice/Quot.sound，覆盖不是仅一条公开定理。
- 真实 Audit.log 为1667字节/29行，SHA256 `58cac053abc51a7b405f50a7469a3735ff7d7260a08afb2e15c83cd952b46f86`。所有权枚举实际2 owned：1 def、1 theorem、1 frozen target，没有额外 private/generated owned 项；两项实际 AXIOMS 都是 `[propext, Classical.choice, Quot.sound]`，真实 `U16B_AXIOM_GATE PASS`。全部 actual TYPE 已在上一阶段连长续行核读，非由计数或 PASS 代替类型检查。
- 实际 branch `feat/oq3-positive-layer-tail`，HEAD `115ce0f27cd1c89330a232688c4ce060196d29a2`，git status 仅 `?? Shao/OQ3/PositiveLayerTail.lean`。真实 toolchain 是 `leanprover/lean4:v4.36.0-rc1`，lean-toolchain SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；manifest pin 与实际 mathlib HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。

从真实目标源重新递归解析实际 Shao import，得到恰好25项前置，路径集合与 receipt 完全一致；每份实际源 SHA256 均逐项 MATCH，全部25份既有 olean 均实际存在。实际 run/prerequisite-hashes.json SHA256 `db1bc6ba04abd3a4c74bdeda87ba89d933d18730a931d2c02684cb3f852fb4cc`，其内容亦程序核对与 receipt 完全相同。各项实际核对值如下（共同前缀 Shao/ 省略）：

| 实际前置源码 | SHA256 |
| --- | --- |
| Basic/FinitePath.lean | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| OQ3/AtomProjection.lean | `0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22` |
| OQ3/AtomicMeasure.lean | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| OQ3/CentralFourierIntegral.lean | `4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93` |
| OQ3/FiniteConstraints.lean | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| OQ3/FiniteFarArc.lean | `3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71` |
| OQ3/FiniteNormalSpan.lean | `0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de` |
| OQ3/FiniteStageMeasure.lean | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| OQ3/FundamentalFourierAsymptotic.lean | `aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1` |
| OQ3/InverseTilt.lean | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| OQ3/JointNonlattice.lean | `51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559` |
| OQ3/NormalLayerConditionalLaw.lean | `94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a` |
| OQ3/NormalLayerFourier.lean | `063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3` |
| OQ3/NormalLayerMassBound.lean | `66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1` |
| OQ3/NormalTangentDomination.lean | `b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90` |
| OQ3/NormalTangentGaussian.lean | `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39` |
| OQ3/NormalTangentMoments.lean | `8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1` |
| OQ3/NormalTangentPowerLimit.lean | `819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457` |
| OQ3/PositiveRate.lean | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| OQ3/RegularCovariance.lean | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| OQ3/ResonanceArithmetic.lean | `cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b` |
| OQ3/SampleBoundary.lean | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` |
| OQ3/SourceStarter.lean | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| OQ3/SummableAtoms.lean | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| Probability/FiniteIID.lean | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: actual 完整定义体和唯一公开定理完整类型与冻结声明及真实 R1 正层权重截尾相符；全部96行证明、所有局部辅助和实际固定库门已独立逐步核对。代码先取得全实层共享的实际概率质量界，在所有 theta/K 前选择同一正 C 和最终 n 事件；ell>0、dyadicMesh J>0 真实给0<rho<1及正分母；实际加权项非负，原项和移位项都在实 tsum 比较之前得到真可和。移位通过 K+k 直接大项和 pow_add，闭式精确，theta1/J0/K0/n0与不可达层无漏洞。全部两项 actual TYPE、全部 owned 传递公理白名单、真实25源闭包和 source/receipt/Audit/build/pins绑定一致，没有发现需要修改的声明、数学、来源、类型或机械缺口。

本票接受固定真实阶段 mu/J 的正层权重可和与 theta/K 统一几何尾界；不声称负层 Chernoff、率二次下界、紧倾斜族统一常数、完整层支配/完整(19)、完整 LLT、条件 Lévy、hW、WC、KL、全局最小化、最优性或新颖性。根 A/B/C/D、完整负层支配、完整 LLT 与 hW 均保持 OPEN。整个审查只写本报告及其授权远端副本，没有修改实现/scope/旧票/共同文件/缓存，未 spawn 或复编。
