# PR344 独立完整终审

STATUS: CORRECT

本结论仅认证下面锁定的 `SourceActualRegularPhysicalRatio.lean`：公开的真实区间核减上半线核的一阶空间导数比，以及实现它的唯一私有远像尾引理。没有发现数学、陈述忠实性或本次证据绑定缺口。C2/C12/OQ56 仍 OPEN；OQ3 仍 PAUSED_BY_USER；C1 的原范围闭合来自其他已接受单元。

审查者是本轮新鲜、非作者的独立上下文 `/root/actual_regular_physical_ratio_final_review`，不是 root 或 `/root/permutation_reveal_candidate`。只写本目录，没有修订源码、作者证据、旧审查或共享文件，没有合并。按指定配置请求 gpt-6.1-sol/xhigh；工具未提供可独立证实的实际模型和 effort，二者记录 null。输入、缓存输入、输出、推理子集用量也均未暴露，分别为 null，没有作订阅百分比分摊。

## 1. 锁定对象与完整阅读范围

- PR：<https://github.com/randomcat4/shao-lean/pull/344>。
- head：`7bae0e244f82b1143cdf3669c4e28232d9e8cad1`；tree：`64f09c64b980bdc24b03ca254706a825e52b6a66`；blob：`e264d37451ce5cd0aa27cba0f7a800954b98aab6`。
- 全部 466 行、24208 字节源码 SHA256：`30ea7da3bd4924271c05e1eeb308aaa1502d9b098a9e9a0f883623b4699f3457`。本地字节、服务器源、成功命令源快照和 Git blob 的 SHA256 相同；本地重新按 Git blob 格式算出的 SHA1 也与上述 blob 相同。UTF-8、无 BOM、无 CR。
- 原成功对象 `outputs/common-actual-regular-physical-ratio-v86/producer007.olean` SHA256：`88d83140e3f2088da3bb4d6e3f2dc59d7c5df843a2f28a2dc7f07ad1c96bd995`。实际导入位置解析到此对象，哈希相同。
- 作者 receipt SHA256：`b9cf759cd2d59e1cf5b6b34b0d7b4ec581c0f1c3e6b69682658073b00a4f7d72`；作者 RELEASE：`e9119e5fd282dc632e903812d7ed0ee63367b69a51c168d2610ec694b0b0f96e`；checkpoint：`c94c1a19fbf72a2ff87d70a7569aedcf5ea28bcf43cbda3fd6f260b090860a0f`。

实际完整读过：全部新源码及两个 proof body；公开、私有完整冻结文件及其共同 context；原 supplement 4192–4231、4755–4825（核心目标 4778–4808）；候选完整数学证明；40 个必要旧接口/值的完整片段，以及正式体实际额外消费的 `int_abs_ge_one` 完整头；12 个实际所属声明的全部 `pp.all` TYPE 和各自递归公理列表；整个现成 owner-index/collectAxioms 驱动。JSON 附件逐声明保存完整 TYPE，而不是仅给公开头或省略生成项。

旧生产者完整证明及旧完整独审沿用已接受资格，不重复读、编译或审计。11 个必要旧源码和既有独审引用已实际重新核哈希；其源码哈希同时属于已接受 v85 和 v86。新模块不属于 v85/v86，故本报告没有把 PR344 冒充为已合入 v86。

## 2. 先冻结的原陈述与源到语义

公开冻结 SHA256 `5597cb1e38bbeb09f9f06e23fbd7b15489f257dbc9f40a669e1c6c4ec47b1b93`；production activation SHA256 `f5e344998821d2d3ab3f01217289a38d6edb69e5b56af8ad77bb953530652870`，时间 2026-10-24 21:59:36Z。私有冻结 SHA256 `6fa89747ff425bcb2920af0d0c2f96175d3c899a7d96ef191f9a567606b4b110`，冻结回执 SHA256 `63aadd3e2aa037b18243b058c51f5700e8a693fc00596a36625981f6c95af94b`，时间 22:06:35Z。首次 kernel 尝试是 22:11:08Z，早于证明体检查的冻结顺序成立。源码抽出的两个完整声明头、共同 import/options/namespace/open context 和七个 head lets 均逐字与冻结文件相同。

公开四个 let 是 Q、u、dI、dU；私有三个 let 是 E、F、G。没有以证明内同名函数替代公开对象，也没有额外全局定义或实例。公开量词是先存在统一 C>0，然后任意 Ω、可测结构、Brownian 过程 B、概率测度 PB、Brownian 证明以及全部实参数。C 的实际见证在引入所有参数前取 2048。

原 supplement SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。4194–4201 定义的是固定墙下的严格 Brownian bridge 生存概率，4221–4222 明确微分时保持墙和终点固定。正式头的 `deriv (fun w => ... a w T z) y` 恰是这个导数：只变起点 w，固定 a、T、z 和同一 Q。

`Q=bridgeLaw B PB` 的完整必要定义是同一个 B 的连续单位时间路径，经 `pinPath` 去掉端点后推前所得测度；`bridgePath y T z g t=(1-t)y+tz+sqrt(T)g(t)`。`intervalCompletion Q`、`upperCompletion Q` 分别是 Q 对全部 t∈[0,1] 的严格双墙、严格上墙事件的实概率。它们不是任意满足所需估计的解析核，也不是为结论另选的分布。

原条件 `y=a-u, 0<u≤|b|≤sqrt(T/2)` 在 T>0 下等价于头中 `let u:=a-y; 0<u; u≤|b|; b²≤T/2`。原 x≥16、a≥x√T、|z|<a 和位移闭界逐项保留；正时间是原桥核的定义域条件。结论正好是原文的 `0≤f_y^I-f_y^+≤C exp(-a²/T)(-f_y^+)`，没有引入概率估计、梯度比、可积性或已求和结论的 oracle。

## 3. 私有证明逐段核对（16–241）

**16–29，完整合同。** 对任意实 A,U,V，仅假定 A≥16、0≤U≤1、V≥0、U+V≤13A/8。E、F、G 的三个 literal 定义完整固定。结论同时给真实非零整数项 `H(m)=if m=0 then 0 else G(m,V)` 的 Summable 和其无条件总和绝对值上界 `1856 V exp(-11 A²/8)`。Summable 不是输入。

**30–59，非负主控与几何总和。** A>0、A²≥16、V≤13A/8 均由合同得出。令 L=928V exp(-11A²/8)≥0、q=exp(-1)>0。由 exp(1)≥2 和 q exp(1)=1 得 q≤1/2<1；真正的几何 HasSum 给 `Σ(n≥0) q^(n+1)=q/(1-q)≤1`。指数与自然幂的改写完整处理了 n+1，而不是误取 n=0 首项 1。

**60–104，全闭段指数下界。** 固定 m≠0，k=|m|≥1，S=k²A²≥1。`int_abs_ge_one` 的实际完整头正是这里需要的非零整数事实。在任意 t∈[0,V] 上，U+t≥0 且 U+t≤13A/8，|U-t|≤U+t。两项都满足

`E_m(t), F_{-m}(t) ≥ 8S-4kA(U+t) ≥ (8k²-13k/2)A² ≥ 3S/2`。

F 项额外的 2Ut≥0 未被丢错符号；末步差为 `(13/2)k(k-1)A²≥0`。这是一条对整个积分/均值段的界，不是把最终位移条件只用于 t=V 后冒推整段。

**105–122，实际有限函数求导。** 逐项普通链式法则得到

`G'_m(t)=16m²A² exp(-E_m(t)) + [-2+(4mA+2t)(4mA+2U)] exp(-F_{-m}(t))`。

E 对 t 的导数为 -4mA，F_{-m} 对 t 的导数为 4mA+2U；减去第二项再求导的两个符号都正确。该导数在所有实 t 成立，没有要求整个无限级数具有未经证明的混合导数。

**123–169，系数与导数界。** t≤V≤13A/8、k≥1、A≥16 给 `|4mA+2t|≤8kA`；U≤1 给 `|4mA+2U|≤5kA`。故乘积绝对值≤40S，加入常数 2 后≤42S（用 S≥1）。指数下界和非负系数乘法于是给 `|G'_m(t)|≤58S exp(-3S/2)`。对所有负 m 同样适用；没有把 m 当作正数。

**170–180，零迹与有限均值定理。** E_m(0)=F_{-m}(0)=8m²A²+4mAU，所以 G_m(0)=0 严格代数成立。对这个完整光滑实函数使用段上的导数范数定理，得 `|G_m(V)|≤58 V S exp(-3S/2)`。所需段内导数和界均由上两段供应，V∈[0,V] 用 V≥0 支付。V=0 时结果为 0≤0；无需假定概率核在 z=a 的导数。

**181–205，吸收多项式和可和尾。** exp(S/16)≥S/16 给 `S exp(-3S/2)≤16 exp(-23S/16)`。准确因式分解 `23k²-22-k=(k-1)(23k+22)≥0`，结合 A²≥16 得 `23k²A²/16≥11A²/8+k`。所以每项满足 `|G_m(V)|≤L exp(-|m|)`，L 的系数正是 58×16=928。

**206–241，正负整数全覆盖与真实 Summable。** 正整数参数 n+1 和负整数参数 -(n+1) 各被 `L q^(n+1)` 主控；两个参数均非零。分别得到两边 Summable，再以包含任意零项的标准整数拆分重组成整个 H。零项 H(0)=0；两侧总和绝对值各≤L。两侧都实际出现，最后系数是 2L=1856V exp(-11A²/8)。每次 tsum 加减、取范数上界都先有所需的 Summable；不存在利用不可和 tsum 的默认零值证明目标的情形。

## 4. 公开证明逐段核对（243–464）

**243–299，全部域条件由原前提推出。** 先选 C=2048。取 s=√T>0，A=a/s，U=(a-y)/s，V=(a-z)/s，s²=T。由 a≥xs、x≥16 得 A≥x≥16、a>0。由 u≤|b|、b²≤T/2 得 U²≤1/2，进而 0≤U≤1、u≤s。于是 -a<y<a；|z|<a 给 V>0。恒等式 V-U=(y-z)/s 与原位移界给 V-U≤3x/2。故 `U+V≤2+3x/2≤13A/8`（x≥16）。这些步骤保留所有允许的等号，未另加 |y|<a 或归一化位移前提。

**300–330，两个真实导数。** 已接受的 `sourceIntervalCompletion_spatial_hasDerivAt` 在 a>0、|y|<a、|z|<a、T>0 下提供真实区间概率导数；正时间下 `sourceIntervalCompletion` 的完整定义归约为 `intervalCompletion`。所以 dI 等于真实 interval image candidate 的一阶导数。上半线则在 y 的开邻域 w<a 上应用已接受 `bridge_upper_formula`，与真实 `upperCompletion Q a w T z` 局部相等后合法求导，得到

`dU=-(2V/s) exp(-2UV)`。

V>0、s>0 因而 -dU>0。正式上界证明没有除以 -dU，故不存在隐含的分母约定；这条严格正性也说明原比值解释成立。

**331–341，符号。** 两个真函数可导。已接受 `upper_deficit_antitone`（终点取 z'=z）使真实差 `upperCompletion-intervalCompletion` 在起点全线上反单调。其导数 dU-dI≤0，故 dI-dU≥0。这里使用的是差的已证反单调性和已支付可导性，没有从单纯的概率集合包含关系直接推导导数比较。

**342–368，旧级数接口条件。** 将已经满足的 A,U,V 合同交给私有引理。分别取 `PA=spatialImageA 1 a z T y`、`PC=spatialImageB 1 a z T y`。旧 `image_spatial_summable` 给两个完整整数族的 Summable，`intervalImageCandidate_iteratedDeriv_eq_intSeries` 在 j=1 给 `dI=Σ(PA_m-PC_m)`。旧接口允许 |z|≤a、|y|≤a 的地方由严格内点取弱界；需要严格 |y|<a 的导数合同由前段已证的 hy 支付。

**369–398，指数和导数系数的全部代数。** 代入 a=sA、y=s(A-U)、z=s(A-V)、T=s²，得到

`imageA(a,y,z,m)/T=E_m(V)`，

`imageB(a,y,z,-m-1)/T=F_{-m}(V)`。

完整 image 定义和其 y 导数头已读：imageA=8m²a²+4ma(z-y)，y 导数 -4ma；imageB=2(y+(2l+1)a)(z+(2l+1)a)，y 导数 2(z+(2l+1)a)。链式法则给 PA 系数 +4ma/T、PC 系数 -2(z+(2l+1)a)/T。因此 `s(PA_m-PC_{-m-1})=G_m(V)`。尤其第二族是 -m-1，F 的下标是 -m；没有漏掉平移 1，也没有把 B_0 或 B_{-1} 丢失。

**399–417，整数双射重索引。** e(m)=-m-1 是其自身逆，两个逆恒等式都已证。PC∘e 的 Summable 来自 PC 的 Summable 和 e 的单射；tsum 不变来自 e 的双射。先合法拆开两族的 tsum，再只对 PC 重索引，然后组合、提取常数 s，逐项用上段恒等式，严格得到 `s dI=Σ_m G_m(V)`。无条件绝对可和的整数总和没有重排次序问题。

**418–441，精确抽出上墙首项。** J 仅在 m=0 非零，H 正是私有引理的删零族，G=J+H。有限支撑 J 的 HasSum 与 H 的 Summable 允许相加。直接代数给 `G_0(V)=-2V exp(-2UV)=s dU`，故 `s(dI-dU)=ΣH`。私有界于是给 `s(dI-dU)≤1856V exp(-11A²/8)`。这是完整实际导数级数中的抵消，不是有限几项近似。

**442–464，较粗充分指数比较与最终常数。** 用 0≤U≤1、V≥0、V≤13A/8 得 `2UV≤13A/4≤A²/4`，最后一步仅需 A≥13，已有 A≥16。因此

`exp(-11A²/8)≤exp(-A²)exp(-2UV)`。

再以 1856≤4096、V≥0 和 dU 的准确公式，得到

`s(dI-dU)≤4096V exp(-A²)exp(-2UV)=s·2048 exp(-A²)(-dU)`。

只约去已证正数 s，并代入 A²=a²/T，即得原公开头的两边结论。候选及原文的更强 `2UV≤3A²/16` 没有被冒称为正式体已证结果；正式体使用较粗的 A²/4，仍有足够的指数余量，既不改变头也不改变 C=2048。

## 5. 边界、接口相互作用与原范围

x=16、a=x√T、u=|b|、b²=T/2、|z-y|=3x√T/2 均包含。b 的符号任意；b=0 与 u>0 不相容，是原假设本身排除的情形。u 或 V 可任意接近 0，尾界先带有 V 因子，之后只约正 s，统一常数不依赖离墙距离。私有引理另外覆盖 U=0、V=0；公开头维持 u>0 和 |z|<a。

这里没有宣称 T=0、墙上/墙外端点导数、large-step、实际 retained/reveal 积分预算、完整 residual 概率账或 C2 根闭合。终端迹仅为显式 G_m(0)=0，不是对端点概率函数额外加导数前提。B 的 rare-suffix/inverse-moment/record 装配与 C12 的旧 image/PDE 生产者归属不变。

11 个消费源码的精确已接受版本无变化；本次消费的 40 个完整旧头/值片段在实际 curated source 中逐段字面存在。额外的 `int_abs_ge_one` 已从同一已资格 source 读完整头；候选消费清单未列出这个简单算术接口，不影响正式体或旧模块资格。新模块名及公开名在当前 library/Shao 源中没有既有出现；新源不改实例、记号、共享定义、根 import 或已有模块。源码首注释仍带候选阶段措辞；正式 proof body 与已绑定执行事实以本报告和 receipts 为准，这个旧注释不参与任何数学假设。

## 6. 全部实际所属 TYPE / VALUE / AX 审核

现成驱动从 `env.getModuleIdxFor?` 取定义模块，精确等于目标模块才入库存；不是 namespace 前缀筛选。对每个实际 owner 调用递归 `Lean.collectAxioms`；所有新实际常量均 `.thmInfo`。实际库存为 **12 theorem、0 其他 kind**，即 1 公开源定理、1 私有源定理、10 生成定理。故需要完整读取的非定理 VALUE 库存为空；0 来自实际 kind，不是从“作者没有写 def”猜出。

每个完整 TYPE 与每个递归 AX 列表已在 JSON 中逐一保存并核对；下面写出各自数学意义。P=`propext`，C=`Classical.choice`，Q=`Quot.sound`。

| 实际声明（公共前缀省写；私有前缀在 JSON 保留） | 完整 TYPE 的意义 | 递归 AX |
|---|---|---|
| `actual_bridge_first_upper_gradient_ratio` | 原统一 C>0 的同桥真实空间梯度差界，全部原参数和四个 literal lets 保留 | P,C,Q |
| 私有 `arp_far_image_sum_bound` | 全实 A/U/V 合同下，三个 literal lets 的删零整数尾 Summable 且绝对总和≤1856V exp(-11A²/8) | P,C,Q |
| 公共定理 `._simp_1` | 有 Zero、字面 2 和 NeZero 2 的任意类型中，命题 2=0 等于 False | P |
| `._simp_2` | 同上，字面 3 | P |
| `._simp_3` | 同上，字面 4 | P |
| `._simp_4` | 有 Mul/Zero/NoZeroDivisors 的任意类型中，a≠0、b≠0 推出命题 ab=0 等于 False | P |
| `._simp_5` | reduced MonoidWithZero 中，a≠0、任意自然 n 时，命题 a^n=0 等于 False | P |
| `._simp_6` | GroupWithZero 中，a≠0、任意整数 n 时，命题 a^n=0 等于 False | P,C,Q |
| `._simp_7` | CharZero AddMonoidWithOne 中，任意自然 n 的强制转换 n+1=0 命题等于 False | P |
| 公共定理 `._proof_7` | 对任意整数 m，否认 -(-m-1)-1=m 导致 False；即重索引 involution 的双重否定证明 | P,Q |
| 私有尾定理 `._proof_1` | 对任意自然 n，整数 (n:ℤ)+1=0 导致 False | P,Q |
| 私有尾定理 `._proof_2` | 对任意自然 n，整数 -((n:ℤ)+1)=0 导致 False | P,Q |

这些生成 TYPE 的泛型 typeclass 前提不是新概率假设，均为 proof 内的代数化简、非零性或整数索引事实。没有未审查的私有 definition、opaque value、实例、构造器或跨 namespace owner。全部新源码扫描没有 sorry/admit/axiom/unsafe/native_decide，递归公理集合完全位于 P/C/Q 白名单。

## 7. 机械证据、Git、资源与失败分母

author 的唯一 whole 成功是 attempt007（14.9394905 秒、退出 0），源与原对象如第 1 节。唯一 all-owner audit（5.8098168 秒、退出 0）导入这个原对象；原 log SHA256 `f1ce057383b4983b004406f30b1a568c5a19b09c6e91f79130024d16544927ed`，report SHA256 `e27e49f8c317cd7086fe539888a220589ad5c46de3884dc2ea6c34cac1f1ba4d`，完整 TYPE 文本 SHA256 `89196246cc1837725e2f32d8e26a19f4598cab8b8a184efec381bc481f7cf365`。服务器只读验证确认完整 TYPE 文本原样连续包含于原 audit log，12 个 DECL、12 个 TYPE、0 个非定理 VALUE，结尾实际报告 12 PUBLIC1 THEOREMS12 DEFINITIONS0，两个成功 log 均无 error。

原命令的完整 argv 及 source/object/driver/log 绑定保留在 `full-review.json`。两次成功命令都用既定 `flock -E 75 -n .../root-heavy.lock`，激活后进入单独 worktree，`taskset -c 10-13 lake env lean -M8192 -j4`；producer 用 `-o producer007.olean`，audit 用 `OwnedAudit.lean`。无弱化内核设置，maxHeartbeats 仅是已冻结 elaboration 预算。没有占用 CPU0–9 或修改外部任务。

现有正式记录的 001/002 partial 失败、003/004/006 whole 失败全部保留；005 锁忙、退出75、0次 Lean；007 唯一 whole 成功。总共 6 次 kernel 调用、5 次失败、0 次 partial 成功、1 次 whole 成功、1 次 audit。失败没有成功信用，也未要求重跑。author RELEASE 明确释放源写权和目标执行权。

本审查实际在服务器只读重核了目标 source/object/log/audit/TYPE/driver、四个直接依赖的 source 和原导入对象、Git head/tree/blob、干净状态、source-only diff，以及当前目标进程空。观测 UTC 为 2026-10-24T22:27:49.239554Z。Lean 仍钉死 v4.36.0-rc1，mathlib 807d3836b165983210ee2ecf3cd28f239436949c，packages 解析到 shared-v34；lean-toolchain、lakefile.toml、lake-manifest.json 字节与已接受 base 完全相同。

第一次只读核对因试图读取已从干净 worktree 清走的 `OwnedAudit.lean` 而退出；请求和响应原样保留。本审查随后改核输出目录中已经封存的同哈希 driver，目标 `.olean` 原导入路径和完整 audit log 也均验证通过；没有重放 kernel/audit。这是一次只读文件位置检查失败，不是 Lean 失败，也不构成缺少原审计源。正常流程清掉 untracked driver 与 Git clean 相容。

本审查新增 Lean/kernel/AX/build/smoke 调用均为 **0**；旧 producer 重编译、旧独审/公理重放、缓存写入、Git 写入均为 **0**。86 次本地证据哈希检查和后续 accepted-interface/原文核对的逐项结果在本目录封存。

## 8. 裁决与交接

冻结公开头在原文的完整 regular first-upper 正时间域内成立；唯一私有辅助引理的原冻结合同也成立。全部 466 行 proof、12 个实际完整 TYPE、实际 0 VALUE 库存和每 owner 递归公理已覆盖。最终 **CORRECT**，无需作者修复。

完整机器可读记录为 `full-review.json`；本地物理绑定、旧接口消费验证、服务器原对象只读绑定及失败原响应均留在本目录。`RELEASE.json` 和 `evidence-manifest.json` 记录本审查最终文件哈希和零在途状态。本审查不授予 merge 权，不把普通回合结束表述为持续运行；Root 可复用本次精确版本的完整独审与原 server receipt 做资格/集成判断。
