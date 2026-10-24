# PR341 独立完整数学、语义与 Lean 证据审查

STATUS: CORRECT

本结论只绑定 `Shao.Probability.SourceOriginalLawNonresidualReturn` 的最终 876 行源：SHA256 `c74962d88fbbe6cd89f61cd0cc3454491af0a5433c4792d51b465239caa5f9e7`，46299 字节；PR341 head `c71d6d01f974881b3744e601b76e5ad60ee5bbdb`，tree `91c3d4ccc639ea6ea34f031d857d16de6c98c402`，blob `67b75baa96b2da22bafc5633c3017103355941be`。它证明原 AE iid 家族在同一原域 I_n 上、x≥1 且原 R_n(x)≥cstar exp(-3x²) 时，实际同路径两弱墙事件与实际 Brownian 两弱墙事件之差为 O(C(cstar)R_n(x)Ψ(x))。criticalGaps 为空。

这不是 residual 比较、完整 g:double、全 C2 或 C12 根闭合。C1 已有另行验收的完整原题结果，未在本报告重审或追加信用；C2/C12/OQ56 保持 OPEN，OQ3 保持 PAUSED_BY_USER。

## 独立性、运行与不可变绑定

本审查者是作者之外的 fresh 最终验证上下文，仅写指定 `drafts/c2-original-law-nonresidual-return-final-review/`。先写实际 runtime-ack，再核验作者 RELEASE，之后才完整审读证明。使用 math-theorem 的独立验缝角色；没有启用 math-ultra、创建其他上下文、聊天、Goal 或日程，没有更改源、冻结头、作者凭据、Git、共享缓存或旧证据，没有执行 Lean、AX、build 或 smoke。

作者 RELEASE SHA256 `43978d5d3bf7c32c17028bb361b83ba654bf94d2836308fed664543f84e643af`，receipt SHA256 `372df6c907bc66ceb932d211c37badc1b9b10564daa26bda5c5ef407b54bbeb5`。两份服务器原件与本地逐字哈希相同；sourceWriterReleased、targetExecutionReleased 均为 true，inflightTools 与 targetLeanProcessesObserved 均为空。作者实际只读释放观测为 2026-10-24T21:42:04.908631Z。本审查者在服务器 21:46:34.007478Z 再观测目标 Lean 进程为空，native Git 工作区干净。

请求配置为 gpt-6.1-sol / xhigh。工具未曝光实际模型、实际 effort 或 token telemetry，因此 actualModel、actualEffort、input、cachedInput、output、reasoningSubset 均分别为 null。没有推算订阅百分比。

## 完整读取与冻结一致性

最终源码逐行完整读取 1–876；全部实际 owner 类型胶囊逐行完整读取 1–603（51980 字节，SHA256 `9d63fab97c6edc5352f21153ce6e34b9d75af5664e16dce769d2fcf46f6e4c76`）；候选完整数学证明、候选头、107 行 proof-candidate.md、unpaid-interface.md、源范围与 517 行消费接口/必要值胶囊完整读取。胶囊中 358 个带原行号的项目源行与真实对应源逐字匹配。此材料用于定位及作用域审查，不替代最终证明。

完整原文读取：main.tex 149–245、310–355、1153–1270、1402–1559；supplement.tex 4682–4767、5758–5796。main SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`；supplement SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。只读原文未修改。

完整冻结上下文相同：imports、autoImplicit=false、Elab.async=false、maxHeartbeats=5000000、noncomputable section、namespace、opens 均逐字保留。公开头 SHA256 `2cefacfd4fbf9051b609877a52091f00453b8853ddc4e0a649eb5dd25ab32824`，私有头 SHA256 `7fb482842dea235c37266fc9b17fac91e07423bfac4d9e24317a1df72ff6c4e4`；本审查者直接从最终源提取完整头并与冻结原件比较，逐字相同。公开 11 个 literal lets 为 sigmaSq、sigma、scale、nu、Ln、Rn、I、population、rawEnergy、D、DB；私有 3 个为 R、P、DB。唯一私有头已由 amendment01 在正文写入前冻结，其 SHA256 为 `8eb4cce8b18ec0e6b28beae4d6a8cdaf5695ec423c53196b094690780e065669`。

最终源开头的三行候选历史注释仍写“PR333 pending/no private”。这是已被资格与 amendment01 明确取代的历史注释，不是实际声明、所有权或当前验收状态；不据此扩大或缩小数学头。源是真正 UTF-8、无 BOM、LF，无 CR；没有 sorry/admit/new axiom/unsafe/native_decide，0 新 source definition、0 source instance、1 private theorem。

## 原文到声明的忠实性

main 149–197 的原律是实值 iid、零均值、正有限二阶矩、2<p≤3 的有限 p 绝对矩。公开头保持全部这些条件；有限 family X:Fin n→Ω→ℝ 以每坐标 AE 可测、iIndepFun 和与原 rho 的 IdentDistrib 表达真实联合 iid。没有提升为处处可测、增加完备空间、对称性、无原子、密度、第三矩或目标概率/可积性 oracle。

sigmaSq、sigma、scale 和 nu 分别是原二阶矩、其正平方根、sigma√n、原 rho 经 z↦z/scale 的实际推前。Ln 的分母严格是 sigma^p n^((p−2)/2)，Rn(t)=n∫F((1+t)z)dnu，F(z)=z² min(|z|,1)。I 逐字是 {t≥0 : t≤Ln^(−1/p) 或 Rn(t)≤rhoStar}；给定 rhoStar∈(0,1/16] 没被改为另一个较小存在常数。声明同时返回原 rho 积分的 Rn 身份。

D 的两号使用同一 population、同一 rawEnergy=∑X_i²。upperMax/lowerMax 的真实值只取正前缀 1…n；没有引入空前缀或把两号放到独立样本。DB 的两号同样使用同一 B、同一 omega，量化 BridgeTime=[0,1] 的全部实时间；它是实际 IsBrownianReal 概率事件，不是任意解析函数 d。PR333 的已资格头进一步识别 PB(DB)=4Ψ−H，恰合 main 1153–1164 的 d(x)。

原题 crossing 始终是弱乘法不等式，strict survival 是其精确补集。最终源没有把弱墙换成严格墙，也不去除 cutoff 等号原子。原 Q=0 时两墙均为 0≤0，因此全零样本仍属于 D；scale 的正比例恒等式也覆盖它。证明中仅除以已证正的常数 scale、V、sqrt V、a、delta、q，未除以样本能量。

main 1178–1189 的全 growing 目标比本头强。本头准确给出它的 nonresidual 原律子范围，且显式保留任意固定 cstar>0。C 在 rhoStar、p、所有概率空间/Brownian、mu/rho、n、x 之前选取，只依赖 cstar。原文 main 1403–1424 的 full centered 比较并未被当作输入；本源只消费 PR333 无辅助 nonresidual 条件的两项界。

## 完整证明复核：私有头 19–722

**19–89：量词、常数和真实 Brownian。** 固定 cstar>0 后，先选普适 coarse 常数 Cc 与 marked-discard 常数 Cb，再定义 K=√(2π)、C0=2K+2e+2、eps=1/1024、eta=eps³/2²⁰、A0=512C0 e²+512K+Cb/eps³、B0=e(C0+2)+2。Ccompact=e¹²/(cstar Ψ(2))、Clarge=(Cc+2)/eta、Csmall=A0+2KB0/cstar，C=1+Ccompact+Clarge+Csmall，所有分母严格正。C 已在 Brownian/law/n/x 进入上下文前构造。PR333 实际头给 d≥0、d≤2Ψ(x)、d≤2exp(−9x²/2)≤2exp(−4x²)。两概率的绝对差≤二者之和；这一步只需非负性。

**90–137：完整非小预算分支。** 1≤x≤2 时两真实概率均在 [0,1]，差≤1；原 nonresidual 给 R≥cstar e⁻¹²，而 Ψ(x)≥Ψ(2)>0，故 Ccompact 付清。x>2 且 R≥eta 时，D⊆upperCrossing，原 coarse 头给 P(D)≤CcΨ(x)，加 d≤2Ψ(x) 后由 Clarge 付清。x=1、x=2、R=eta 都在非严格分支内。任何小 n 在满足声明前提时也在这三个完备分支之一，不额外排除。

**138–241：真实闭截断、非零均值、方差和 affine 推前。** 小支有 0<R<eta≤eps³/8。rhoA=cond nu{|z|≤eps/a}，a=1+x，是真概率律，有界支持与一至四阶真可积性由 sourceTruncation_law_data 返回。m=∫z drhoA 没被置零；d0=n|m|、g=n∫|z|³、V=n∫(z−m)²。已接受的 paid_moments/variance_bounds 给 d0≤2R/(eps²a)、g≤2R/a³、V∈[1/2,4/3] 和 n∫|z−m|³≤8g。

源码 168–178 真正构造 Integrable(z−m)、Integrable((z−m)²) 并用 integrable 的减法算中心均值为 0；没有以总化积分的默认 0 代替期望。sV=√V>0，zeta=map((z−m)/sV)rhoA；square/cube 推前前分别构造 hf2/hf3，再由 integrable_map_measure 得 zeta 二、三阶真可积。integral_map 的实际函数被明确指定，推得均值 0、n∫z² dzeta=1 及 delta=(n∫|z−m|³)/sV³。sV³≥1/4、g 界给 delta≤64R/a³。后续能量头另返回 delta>0，才对 delta 作正分母运算。

**242–338：支持、joint map、位移和样本量。** |m|≤eps/a 来自真可积的绝对均值界，故 zeta-AE |z|≤4eps/a。PA=pi(rhoA) 经逐坐标 affine T 实际推前为 PZ=pi(zeta)，由 Measure.pi_map_pi 支付，映后真概率保证所需 SigmaFinite；不是新 HasLaw 前提。Cpath A=A−m、E={Q_C≥V/2} 均可测。hs=3d0、y=x−hs；数值 eta 给 a hs≤1/8、hs≤1/a、y≥1、y≤x、|y−x|≤1/a、8x hs≤1。条件支持使 ∫A²≤(eps/a)²，而 n∫A²≥3/4，因此 x≤√n/2。这些都是已证数值后果，不是加强输入。

**339–462：实际能量的同路径包含。** Cauchy–Schwarz 先得 |∑A_i|≤√n√Q_A，平方展开 Q_C=Q_A−2m∑A_i+nm²，再用有符号项的绝对值上界，得 √Q_C≤√Q_A+√n|m|。所有平方比较两边非负，故不会发生负数开方或错误逆向。每个 k 的真实前缀差是 card(U)m，card(U)≤n，故绝对差≤d0。E 上 √Q_C≥1/2，且 x√n|m|≤d0/2，于是 hs√Q_C≥d0+x√n|m|。因此 y√Q_C≤x√Q_A−d0；分别取原正墙与负墙的正前缀命中点，推出同一个 Cpath 的两墙命中。没有将随机能量墙作为自然滤过停时。正比例 Cpath/sV 保持 D，含能量 0，且 T 的 joint map 搬运整个交事件概率。这里只需要右侧包含；无需未付的 full Brownian threshold Lipschitz 或双向 centered sandwich。

**463–544：低能量项真正按 Gaussian 尺度支付。** finite_iid_energy_lower_tail 在 zeta、真 square/cube、n second=1、kappa=1/2 给 delta>0 及 PZ{Q≤1/2}≤exp(−1/(64delta²))。E 的补集经 T 包含于这个闭下尾事件；严格补集被包含在弱界内，未遗漏等号。令 q=512R∈(0,1/32]。delta≤64R/a³ 推得 1/(64delta²)≥a⁶/(16q²)；a≥1、x≤a、32q≤a、q²≤1/16 分别给 8x²q²≤a²/2、16aq≤a²/2，故 a⁶/(16q²)≥x²/2+a/q。exp(−a/q)≤q/a 与下 Mills φ(x)/a≤Ψ(x) 遂给 PA(Eᶜ)≤512KRΨ(x)。这里没有把“很小”作为证明；全部固定常数的数值不等式都在最终源内。

**545–620：辅助 centered 律仅用无下界的两项界。** 事件包含与 Eᶜ 费用给 PA(D(x))≤PZ(D(y))+PA(Eᶜ)。uY=delta(1+y)³≤512R≤1/20000，且 zeta-AE |z|≤4eps/a≤1/(4y)，真实均值与 n second 条件已付。调用 PR333 的 cstar=1 参数后，只取 hComp(hUySmall).1，即 |PZ(D(y))−d(y)|≤C0 uY Ψ(y)+C0 e^(−4y²)；从未调用需要辅助 uY≥exp(−3y²) 的第二项。再加实际 d(y)≤2e^(−4y²)，并用 |y−x|≤1/a 的 tail 比较及 8x hs≤1 得 Ψ(y)≤e²Ψ(x)、e^(−4y²)≤e·e^(−4x²)。因此 PA(D(x))≤(512C0 e²+512K)RΨ(x)+e(C0+2)e^(−4x²)。

**621–680：闭条件 product 与原律 marked 账。** N 是所有实际坐标的闭保留事件，Borel 性由真实有限坐标表达式构造。P=pi(nu) 的坐标 iid 及实际 law 被明确证明；sourceTruncation_conditioned_sample 返回 map samplePath(cond P N)=pi(rhoA)，其中 samplePath(eval)=id，故 cond P N=PA。cond_mul_eq_inter 给 px PA(D)=P(N∩D)，measureReal_inter_add_sdiff 给真实完整 mixture，px≤1 与 PA(D)≥0 用于上界。D∩Nᶜ⊆upperCrossing∩Nᶜ，原 marked-bad 头在同一 x、同一 eps、u=x 调用，给 (Cb/eps³)RΨ(x)；未改用纯删除概率 O(R)，未评价邻近原律阈值是否属于 I。回到原 P 后得到 |P(D)−d|≤A0RΨ+B0e^(−4x²)。

**681–722：只在原律使用 nonresidual。** 下 Mills 与 (1+x)e^(−x²/2)≤2 给 e^(−x²)≤2KΨ(x)。原 hnon：cstar e^(−3x²)≤R，乘 e^(−x²) 后给 e^(−4x²)≤(R/cstar)e^(−x²)。因此最后余项≤2KB0/cstar·RΨ，恰由 Csmall 付清。这个吸收发生在原律 mixture 之后。候选 unpaid-interface 的有限支持反例正确说明“原 R 下界⇒辅助 centered u 下界”无效；最终源没有使用该错误推论。

## 完整证明复核：公开头 724–874

**724–804：原域和数值 guards。** 从私有头取同一个 C 后才引入 rhoStar/p/Brownian/原律。original_raw_normalization_data 返回 sigma>0、nu 真概率、nu 真 square/p 可积、均值 0、n second=1、Ln=n∫|z|^p 与整路径正尺度推前。若 x 在 I 的 moment 分支，原 moment-domain 头直接给 x⁶≤n 和 n∫F(xz)≤1。若在 budget 分支，原 sample-size 头给 (1+x)⁶≤n；F 的非负尺度单调性和两端真可积性给 n∫F(xz)≤Rn(x)≤rhoStar≤1/16≤1。完整给定 I 保持不变，closed moment endpoint 不丢失。私有头随后用原 hnon 调用。

**805–834：AE iid 的完整联合律和真指示可积。** population AE 可测；iIndepFun.map_fun_eq_pi_map 和每个实际 IdentDistrib.map_eq 得 map population mu=pi(rho)。使用整个 path 的 IdentDistrib，非仅边缘律。E=doubleCrossing Borel，population⁻¹E=D 逐点成立，故 D nullmeasurable，无需原空间完备或 X 处处可测。E 的指示函数在真实概率 Praw 下 Integrable；经 IdentDistrib.comp 与 integrable_iff 得原 D 的指示函数真正 Bochner 可积，并用真实 joint-law 事件概率恒等式给 mu.real D=Praw.real E。没有依赖积分总化的空洞 0。

**835–874：正尺度、Rn 原积分、Brownian 可测性及完成。** scale>0，T a=a/scale 的整路径推前为 Pnorm。energy_smul、sqrt(c²Q)=c√Q（c>0）、两号 positive-prefix max_smul 逐点给 T⁻¹E=E，连 Q=0 也成立；因此 Pnorm(E)=Praw(E)。Rn raw-law 身份用实际 nu map 与连续 F 的 integral_map，左右被积函数都因原/normalized 真 square 可积且 F(w)≤w² 而真可积：原一侧等价 F(((1+x)/scale)z)，可直接由已有 integrable_truncationF_mul 得到。此身份不是用默认零积分蒙混。DB 的 nullmeasurability 来自实际 Brownian 头，x≥1 确保其 x>0 条件。最后联合概率等式将私有结果精确搬回原 D，完成所有五个输出。

## 六个实际 module owner：逐一类型、证明关联和递归公理

所属审计按 Lean 环境 `getModuleIdxFor?` 的精确 defining module 选择所有常量，不按 namespace 前缀裁切。实际 6 个全是 theorem；因此 0 个非定理 VALUE 是由实际 kind 计数推导的，不是预先假定。完整 pp.all 类型逐字收于 full-review.json 的 actualType 字段，包含所有 binder、universe 和实例展开；以下给其完整数学含义与证明关联。

1. **公开 `…original_iid_nonresidual_double_crossing_comparison`**：实际类型胶囊 11–397，完整 source 头 724–765；空间 universe 为 Ω:Type u_1、ΩB:Type u_2，分别有 MeasurableSpace 实例；PB、mu、rho 分别有真实概率实例，Real 的 Borel/范数/积分/序等实例在 pp.all 中全部固定展开。全体其余 binder、11 lets 与五输出见本报告嵌入的完整冻结头。证明体 766–874；递归 AX 精确为 [propext, Classical.choice, Quot.sound]。没有额外隐含假设。
2. **私有 `_private.Shao.Probability.SourceOriginalLawNonresidualReturn.0.Shao.Probability.SourceOriginalLawNonresidualReturn.olr_normalized_nonresidual_return`**：实际类型 401–583，source 头 19–38、证明 39–722；ΩB:Type u_1 及其 MeasurableSpace、PB/nu 的概率实例明确，完整三个 lets 与 normalized guard 前提见嵌入头。递归 AX 精确为 [propext, Classical.choice, Quot.sound]。公开结果实际调用它，不是未使用的旁支。
3. **该私有名后缀 `_simp_2`**：实际类型 595–603：∀ {ι:Type u_1} {R:Type u_4} [NonUnitalNonAssocSemiring R] (s:Finset ι) (f:ι→R) (a:R)，(∑i∈s,a*f i)=a*(∑i∈s,f i)。它是完整有限左分配恒等式，关联 source 352–363 的 Q_C 平方和展开/反向 Finset.mul_sum 化简。递归 AX=[propext, Quot.sound]；不是额外概率或矩前提。
4. **后缀 `_simp_4`**：实际类型 589–592：∀ {α:Type u} {ι:Sort v} {x:α} {s:ι→Set α}，(x∈⋂i,s i)=(∀i,x∈s i)，两边为 Prop 的 Eq。关联 source 623–631 的 N 与坐标闭集交表示，propext 把 iff 转为等式。递归 AX=[propext]。
5. **后缀 `_simp_5`**：实际类型 585–587：∀ {α:Type u} {β:Type v} {f:α→β} {s:Set β} {a:α}，(a∈f⁻¹s)=(f a∈s)，为 Prop 的 Eq。关联 source 629–631 的 eval preimage/保留事件表示；递归 AX=[propext]。
6. **后缀 `_simp_7`**：实际类型 2–7：∀ {G:Type u_1} [Semigroup G] (a b c:G)，a*(b*c)=(a*b)*c。它是逆向结合律化简，关联 source 688 的 `←mul_assoc` 等标量归一化步骤，不增加交换性或随机前提。递归 AX=[]。

四个 generated 声明也由同一整文件 producer006 内核对象产生并在唯一所属审计中逐一出现。没有把 private-only 编译或单独 public-name #print 当作完整覆盖。全部六行逐名与 coverage-index、owned-audit 和实际类型转录一致。没有需要补充的非定理 definition/opaque/instance VALUE。

## 依赖复用与相互作用

已接受 v84 的 source map 实际有 753 个 Shao/ production 源及 11 个入口/脚本/配置；当前 v85 有 771 个 production 源及相同类别的 11 个其他源，不能把 764/782 个 map 总条目称为 production 模块数。v85 receipt SHA256 `bee6010790734dfc41f2819b76948946a7dec1ac6bd08a5139c8accf1e493fdd`，main 按 Root 当前接受状态为 `86510732060ac7272069fe9fd203636a94107eb5`。16 份实际消费的已接受项目源同时与 v84/v85 的 source-hash map 完全一致。本审查还按 v84 的 753 个实际 source-map 键验证本目标工作区对应旧对象都解析到原接受对象，753/753，无失败；目标工作区总 755 个 project olean reference=753 旧项+PR333+本目标。

承重接口已完整读：SourceTruncationBridge 的 conditional law/paid moments/variance，SourceClockBridge 的 exact conditioned sample，OriginalGaussianTail 的 normalized coarse，OriginalCDFPullback 的 same-law marked discard，SourceMomentDomain 的 normalization/domain guards，TruncationSampleSize 的 unchanged-domain sample bound，QuadraticEnergyLowerTail 的真实 iid Laplace 下尾，GaussianTail 的 tail/下 Mills/local comparison，以及 FinitePath、Events、TwoSided、MeasurablePath、TruncationIntegrals、TruncationBudget、FiniteIID、BridgeDomination 的必要完整值、头与上下文。真实 pinned Mathlib 的 joint iid map、IdentDistrib、cond、pi_map_pi 头/必要值与四源哈希也核对；额外读了 integrable_iff 与 cond_mul_eq_inter 完整必要头。

PR333 SourceNonresidualBrownian 已有独立完整审查及 Root 资格，资格 SHA256 `90331f1b54169b31465534f5a5fc894b7e90ee42aefd50a2c5817dd9a0796e2a`。其精确 source `e6de66f3b78a8607842ad71608e0bbce53751f2b69b3e6b973c7f125d8361b23`、原 producer006 object `1c43222adcc43fb0503a38b5b797d1124332c47d8199952a2b6b04fe19d26a0c` 在服务器直接复核。本目标导入路径解析到这个原对象。其旧独审 MD hash `e86348a4c1982ea5864e37c742683ae648add9891e0dc4dfbc4fa78df33203c2` 与 JSON hash `978651c1954904fcf9a4471e322d562f206fc65d7e01815722262e97614ca46d` 作为已接受证据复用；没有重新委托其完整旧证明审查或执行旧 Lean/AX。

另外四个直接 import 的 source/object 逐一实物哈希一致且 import reference 解析到原 v84 对象：SourceTruncationBridge object `3a23c563b69b9316b50d14f3b008ad26575d4c547602f4abd13e9c1718295c7a`；OriginalCDFPullback `5e5060b82bb52b278e9c1ffda3d1875420bd41f74a2e01c3091f0de6c7e84745`；SourceMomentDomain `8f7ccf7d80680f86f52df88e6b239f5d35f51530202422e371dc2f2d3c6ce776`；QuadraticEnergyLowerTail `6a42ffb03b5e1a755fff036877956bff3b11b6162d1ad4df687143879bed9912`。没有不匹配接口、额外假设或交互缺口。

SourceFullYReflection、SourceDesmoothing、SourceOneSidedRelativeError 只属候选读过但未消费的材料；本头没有从这些旧接口取得未付的 C2/residual 信用。旧数学证明/内核/AX 复用范围严格为 unchanged source/object 对应的已资格项。

## 原服务器内核、公理、失败与发布证据

所有原证据留在 `/root/rivermind-data/shao-lean-20261021/outputs/common-original-law-nonresidual-return-v85/`。本审查通过 tools/transport_client.py 只读原件；没有把二进制、完整日志、环境或缓存下载到工作区。必要类型从已存在的文本胶囊重构原审计日志，其余原日志全部完整阅读。

唯一整文件成功是 attempt006，exit 0、28.222693482413888s，source c74962…f9e7；原 producer006.olean 3859536 字节，SHA256 `de0c64d39df68b1746d38878b1906b6e77335e845a4a75ae6c6681d05ebb9baf`。最终工作区 source、attempt006.source.lean、HEAD blob 解码字节三者哈希相同，目标 import olean 与原 producer006 解析到同一文件，哈希相同。

原实际命令为 `flock -E 75 -n /root/rivermind-data/shao-lean-20261021/locks/root-heavy.lock bash -c <body>`；body 依次 source 固定 activate.sh、cd 专用 worktree、`exec taskset -c 10-13 lake env lean -M8192 -j4 -o <outputs>/producer006.olean Shao/Probability/SourceOriginalLawNonresidualReturn.lean`。私有 worktree 为 `workspaces/common-original-law-nonresidual-return-v85`。真实 pins 为 leanprover/lean4:v4.36.0-rc1、mathlib 807d3836b165983210ee2ecf3cd28f239436949c；使用已接受 shared-v34 package view。原 log SHA256 `e967b6f0a4257a13c3ae3146aac7507c23fed5b06e5aaff93460b44f515df798`，171 行全部读完。只有 letI 风格、deprecated simp 名、unused/unreachable tactic 与 ring 建议等提示，无 error；ring 建议不是 kernel 失败。

唯一 all-owner audit 是 owned-audit-command001，exit 0、5.82132607139647s，在同一锁/CPU/8192MiB/j4 下 `lake env lean … OwnedAudit.lean`，导入前述同一原目标对象。audit driver 的 SHA256 `e71fd96fe74b4afb7a52f2a6dc81e7ebfc7a9ac4526e26186ef1b8fe4d779f41`，完整驱动已读；它遍历所有常量，精确 module owner 选择，递归 Lean.collectAxioms，遇到 whitelist 外公理即失败。它输出 6 constants/1 public/6 theorems/0 definitions。审计 JSON SHA256 `70ce35abf9d42a41f0c5cdce186129925b67026d2a1623dd8e13e30ef66afd88`；原日志 SHA256 `283a72e8f03542509e6a9cde77136757d6d34115366987f762e80187892b947d`，606 行。服务器 difflib 精确确认：原 log 1–2 是 package warning，3–605 逐行等于已完整读的 603 行实际类型转录，606 是终结覆盖计数；三部分全部已读，非节选抽查。

完整失败分母如下，原 source snapshot 和 log 哈希均在 full-review.json 记录并在服务器核验：

| 操作 | 范围 | rc/Lean 次数 | 实际结果与最终修复 |
|---|---|---|---|
| 001 | private-only | 1 / 1 | square integrability 展开、显式 integral_map 函数、support measurable set、delta 代数和 Cpath 可测性 elaboration 失败；最终源作显式展开与正分母推导。957 行全日志完整读，后半按前半精确相等块重构。 |
| 002 | private-only | 1 / 1 | support/drift/cast 代数及 heartbeat 超时。传输 operation_timeout 只关闭通道，原远端执行继续，后来同一次执行自然 rc1；未发信号、未不确定重放。最终改为有界 `linarith only` 与明确 calc。666 行全日志由完整001的精确相等块及所有新增原文重构阅读。 |
| 003 | private-only 准备探测 | 75 / 0 | 实际发现 Root heavy 锁已有 owner，日志 2 行明确 ZERO LEAN。不是失败内核，也不是 private 成功。 |
| 004 | whole public/private | 1 / 1 | measureReal_mono 参数名、add_le_add 方向、Ln 改写、indicator 函数等式未闭合；最终 proof-only 修复。555 行全日志精确重构阅读。 |
| 005 | whole public/private | 1 / 1 | hMarked 的局部 lets/upperCrossing 未展开导致类型化简不对齐；最终增加精确 simp 展开，不改数学。129 行全读。 |
| 006 | whole public/private | 0 / 1 | 唯一整文件成功，171 行全读；随后一次完整 owner audit。 |

因此实际 5 次 kernel 调用=4 失败+1 whole PASS，private-only successful=0；另有1 busy零Lean、1 all-owner audit。attempt002 的 transport failure 从未算数学失败结果本身或 quota 结论，恢复后真实 rc1 才进入分母。原始日志/receipts 一致支持该分母；“未发信号/无重放”的负面事实还依赖保存 chronology/transport-interruption 记录，本报告不声称拥有操作系统全历史审计。服务器 snapshot diff 显示所有六版上下文与私有冻结头相同；公开头在004–006均相同，001–003不存在公开定理。最终格式与冻结头没有因修复改变。

本地 artifact-index 的全部35项哈希已复核一致。服务器 native Git HEAD/tree/blob/工作树/单一 changed-source 与 immutable publication/native records 一致，PR仅添加此源。源版本与服务器对象/receipt/audit 已物理绑定。没有为了本审查重放已成功检查。

## 证据限制与交付边界

本次机械资格来自已经实际完成、源哈希绑定的原整文件内核与递归所属审计；本审查者没有第二次编译。这符合当前 streamlined acceptance，不削弱实际内核或独立完整审查要求。package 日志保留“mathlib repository has local changes”的既有警告：未把它隐去，也未声称 package checkout 干净；所用 pinned commit、四个本单元必要 Mathlib 源哈希、旧接受对象 reference 和直接 import 原对象全部核实，旧资格照原精确版本复用。本报告没有重新做 full mathlib 或全部753旧 proof 的审查。

发布绑定依据服务器 native Git 与保存的 PR API 原证据；本审查没有重新访问实时 GitHub，所以不把 immutable draft/merged 字段当成未来实时状态。Root 合入时仍应绑定此 exact head/source 并检查实际 aggregate interactions；目前未发现新的冲突或需重复旧 proof 审查的具体风险。

CORRECT 的数学范围严格为本报告完整冻结头，不包含 residual 原 R<cstar exp(−3x²)、全 I_n 的 double 比较、完整两侧 relative theorem、m:C 增长窗口或 killed/image/interval regularity 专线。已完成的是一个实质 original-law nonresidual 返回依赖。新颖性/论文总价值不在本次源绑定正确性认证范围。

## 完整冻结上下文与头

下面的上下文及两个头从已哈希、逐字匹配的最终源原样提取；完整 expanded actualType 已逐 owner 保存在机器 JSON，避免用简写隐藏实例或 universe。

```lean
/- Mathematical candidate only: no production bodies or Lean/AX execution.
   PR333 exact source is a pending independent-review dependency.
   One public head; no new definitions, instances, global or private helpers. -/
import Shao.Probability.SourceNonresidualBrownian
import Shao.Probability.SourceTruncationBridge
import Shao.Probability.OriginalCDFPullback
import Shao.Probability.SourceMomentDomain
import Shao.Probability.QuadraticEnergyLowerTail

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceOriginalLawNonresidualReturn
open MeasureTheory ProbabilityTheory
open Shao.C2.BridgeDomination
open scoped BigOperators NNReal


private theorem olr_normalized_nonresidual_return :
    ∀ cstar : ℝ, 0 < cstar → ∃ C : ℝ, 0 < C ∧
      ∀ {ΩB : Type*} [MeasurableSpace ΩB]
        (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
        IsBrownianReal B PB →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu]
          (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 →
          (n : ℝ) * (∫ z : ℝ, z ^ 2 ∂nu) = 1 →
          ∀ x : ℝ, 1 ≤ x → x ^ 6 ≤ (n : ℝ) →
            (n : ℝ) * (∫ z : ℝ, Shao.truncationF (x * z) ∂nu) ≤ 1 →
            let R : ℝ := Shao.truncationBudget nu n x
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
            let DB : Set ΩB := {omega |
              (∃ t : BridgeTime, x ≤ B ⟨(t : ℝ), t.property.1⟩ omega) ∧
              ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
            cstar * Real.exp (-3 * x ^ 2) ≤ R →
            |P.real (Shao.C2.doubleCrossing hn x) - PB.real DB| ≤
              C * R * Shao.standardNormalTail x

theorem original_iid_nonresidual_double_crossing_comparison :
    ∀ cstar : ℝ, 0 < cstar → ∃ C : ℝ, 0 < C ∧
      ∀ rhoStar : ℝ, 0 < rhoStar → rhoStar ≤ 1 / 16 →
        ∀ p : ℝ, 2 < p → p ≤ 3 →
          ∀ {Ω ΩB : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩB]
            (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB) [IsProbabilityMeasure PB],
            IsBrownianReal B PB →
            ∀ (mu : Measure Ω) (rho : Measure ℝ)
              [IsProbabilityMeasure mu] [IsProbabilityMeasure rho]
              (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ),
              (∀ i, AEMeasurable (X i) mu) →
              iIndepFun X mu →
              (∀ i, IdentDistrib (X i) (id : ℝ → ℝ) mu rho) →
              Integrable (fun z : ℝ => z ^ 2) rho →
              (∫ z : ℝ, z ∂rho) = 0 →
              0 < (∫ z : ℝ, z ^ 2 ∂rho) →
              Integrable (fun z : ℝ => Real.rpow |z| p) rho →
              let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂rho
              let sigma : ℝ := Real.sqrt sigmaSq
              let scale : ℝ := sigma * Real.sqrt (n : ℝ)
              let nu : Measure ℝ := Measure.map (fun z : ℝ => z / scale) rho
              let Ln : ℝ := (∫ z : ℝ, Real.rpow |z| p ∂rho) /
                (Real.rpow sigma p * Real.rpow (n : ℝ) ((p - 2) / 2))
              let Rn : ℝ → ℝ := fun t => Shao.truncationBudget nu n t
              let I : Set ℝ := {t | 0 ≤ t ∧
                (t ≤ Real.rpow Ln (-1 / p) ∨ Rn t ≤ rhoStar)}
              let population : Ω → Shao.Path n := Shao.Probability.samplePath X
              let rawEnergy : Ω → ℝ := fun omega => ∑ i : Fin n, (X i omega) ^ 2
              ∀ x : ℝ, 1 ≤ x → x ∈ I →
                cstar * Real.exp (-3 * x ^ 2) ≤ Rn x →
                let D : Set Ω := {omega |
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.upperMax (population omega) hn ∧
                  x * Real.sqrt (rawEnergy omega) ≤ Shao.lowerMax (population omega) hn}
                let DB : Set ΩB := {omega |
                  (∃ t : BridgeTime, x ≤ B ⟨(t : ℝ), t.property.1⟩ omega) ∧
                  ∃ t : BridgeTime, B ⟨(t : ℝ), t.property.1⟩ omega ≤ -x}
                Rn x = (n : ℝ) * (∫ z : ℝ,
                  Shao.truncationF ((1 + x) * z / scale) ∂rho) ∧
                NullMeasurableSet D mu ∧
                Integrable (D.indicator (fun _ : Ω => (1 : ℝ))) mu ∧
                NullMeasurableSet DB PB ∧
                |mu.real D - PB.real DB| ≤ C * Rn x * Shao.standardNormalTail x

end Shao.Probability.SourceOriginalLawNonresidualReturn
```
