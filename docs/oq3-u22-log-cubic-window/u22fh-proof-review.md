# FH245 独立完整终审：同一规范样本律的对数三次截断远频率

STATUS: CORRECT

JUSTIFICATION: 最终 529 LF 源码完整证明冻结的两项新增结论：同一实际倾斜样本像律在 sqrt(n)*RA<r≤n³log(n) 上的一致超多项式逐点衰减，以及所有自然权 k、所有实缩放指数 q 的真实加权远区可积性、积分非负性和严格小量。原 FF243 全部数据包、单个 E、75 个旧陈述 let 原样保留；新增 beta<2/5 在实现前已明确冻结。完整源码、整段证明、85 个声明 let、全部 770 LF 实际类型及四个承重依赖的完整公共接口/全部实际类型均已核对，未发现关键数学、语义或证据绑定缺口。

QUALIFICATION_RECOMMENDATION: QUALIFY_FH245_EXACT_SOURCE_WITH_REUSED_FIRST_NATIVE_AND_ALL_OWNED_AXIOMS。父实例须完整读取本报告 ENTIRE 并绑定最终字节后记录 qualification；本报告不自行发布、集成、改变所有权或宣称 OQ3 原根闭合。

## 角色、权限与完整阅读范围

评审上下文 `/root/oq3_fh245_final_review` 为全新独立非作者上下文。唯一写入文件为本报告；没有修订冻结命题或证明，没有创建子实例、侧栏聊天或向其他聊天发消息，没有服务器连接、Lean/AX 执行、上传、Git/API、计划或 Goal，也没有使用 math-ultra。

完整读取 math-theorem 技能及 prompt-library、openai-workflow、discovery-system、lean-verification 四份参考文件，应用中文输出与 Windows UTF-8 防护规则；执行环境实际为 PowerShell7.6.5，控制台和 Shell 输出编码均 UTF-8。读取 SERVER、TEAM 的有关执行/审计边界、streamlined-acceptance-current，并核对 REGISTRY 当前权威字段。协调5为 `01a17d3c-6dfd-7cc0-94ed-35d758a423a5`；OQ3 唯一所有者为 `01a16c48-80ee-7520-a9d9-faeeb6d05c78`。明确人类恢复文件 `coordination/resource-reallocation-20261027/OQ3-RESUMPTION-PHASE-40.json` 的本地 SHA256 为 `2b69e1eb2251724f2236bd8176623e7445a794dbb12a4f17a346885469fba480`，与当前权威绑定一致；本审查没有从该恢复取得执行权限，也不把 ACTIVE 租约当作运行观察。

先完整读取 366 LF 冻结声明，再完整读取最终源码 1–529 行和整段证明 378–526 行。全部 770 LF 实际导出分连续块逐行读取；仅移去每行行首缩进以避免长缩进造成显示截断，没有删去数学内容，没有用摘要或重复子表达式字典替代本次类型阅读。完整读取 28 LF scope、15 LF freeze-retained-FF、4 LF new-far-conclusions、47 LF Audit、186 LF receipt、103 LF audit-record、83 LF build-history、76 LF bearing、113 LF qualified-dependency、48 LF server-dependency 和 10 LF own-firstO 绑定。

承重接口完整读取：FF243 冻结334 LF、全部659 LF/1 TYPE/0 VALUE；FG244 冻结70 LF、全部84 LF/4 TYPE/0 VALUE；BV155 源104 LF（包含两个完整公共声明）及全部29 LF/3 TYPE/0 VALUE；DB187 完整公共声明和全部15 LF/1 TYPE/0 VALUE。FF/FG 和旧 BV/DB 的完整旧证明资格、独立终审与机器成功按精确版本复用；本次没有重新进行旧完整证明资格审判或重跑旧成功检查。旧 FF/FG 报告只读取与接口覆盖、资格、历史标签及来源限制有关段落，没有声称本次重新读完两份旧报告。

只读原来源 `C:/game/shao/current/oq3/proofs/r2/report.md` 的完整1–158和493–523行、完整226 LF `proofs/r2/repair01.md`、完整58 LF `verdict.md`。未写入原来源或历史目录。

## 精确版本和本地字节绑定

下表 SHA256 均在本审查中从本地原始字节重算；表列文件 CR 均为0，行数指 LF 数。远端对象和远端日志哈希另列为原收据中的保存值，不冒称在本机重算。

| FH245 工件 | 字节 / LF | SHA256 |
| --- | --- | --- |
| two-hundred-forty-fifth-unit-scope.md | 1832 / 28 | `631afb1d73f21dd77764ec32477063509e6db936ca6166632575bb17f5c20d4d` |
| u22fh-frozen-declaration.lean.txt | 24075 / 366 | `2f62043b96a7ea38e73e21d0ec745d15c43f7901b870259bc6e5b05d521e378f` |
| u22fh-source.lean | 31815 / 529 | `d4e1622225a07f756d633a7da8b697254525ae6585b5b744bb9cbb596ab2a6f7` |
| u22fh-actual-types.txt | 78085 / 770 | `a9345e6ea0717e635950096ac0358035d1a0c7d14607faed906ac10993a6d8bb` |
| u22fh-Audit.lean | 2047 / 47 | `2f45aaa0da9d473c7b3f7762e16b64e6a87834f2c387e7fc9b075a290596691c` |
| u22fh-receipt.json | 5510 / 186 | `4baea3628b466a8faa89cb20f315e6398b3ec0468e78c166cee7c239efaa3f95` |
| u22fh-audit-record.json | 3056 / 103 | `1fe0f437462b40597207d147df9c163391a4cab2cd65918d8abec208d8c01e1a` |
| u22fh-build-history.json | 2270 / 83 | `afbd4dabd034f89c64deff531edc0ea8ca403c65179907e64fe84811e66a41b2` |
| u22fh-freeze-retained-FF-binding.json | 643 / 15 | `824583245da1b0cebc54f04d4bbbe58a7e64fc591500d4825fde5483e7eabed0` |
| u22fh-new-far-conclusions.json | 2109 / 4 | `f2766405846cae17d7efd073d222a9c56551fce11b5345cc614f79584b9e3180` |
| u22fh-bearing-dependency-binding.json | 3930 / 76 | `b8d9801a06a496e0bc22b22cc76b1676f1572184bf3fb32e8dc1271443fc806f` |
| u22fh-qualified-dependency-binding.json | 6108 / 113 | `8015996123a38407cbda34dbe7b1a85e6e4f4845ead92aee205aec61cae0cb56` |
| u22fh-server-dependency-binding.json | 2616 / 48 | `841454c184d431f5ad7b8b33703fa81bfadbaf8b2f94553501fd37409381f4e6` |
| u22fh-own-firstO-view-binding.json | 597 / 10 | `946a7217d45155258318a6f4d37235216cca1a41368865b94cb63a81e6526619` |

本地确定性比较确认：最终源码 theorem 到 `:= by` 的整个声明与冻结文本逐字相同（仅比较时去末尾换行）；FF 的旧声明仅作已列出的定理重命名、明确新增 hbetaUpper、给末尾 Gaussian 包加括号及追加合取，即与 FH 的保留前缀逐字相同。并非仅凭 let 个数推断保留。声明中的 let 总数75→85；源码中未出现 `sorry`、`admit`、`axiom`、`unsafe`、`native_decide` 词项。

## 陈述忠实性与全部85个 let

mu 为实际概率测度，Theta 可为空，为实际二元矩母函数定义域内部的紧集。det 正性和整族原始联合特征函数的弱 Cramér 条件均保留。新增假设恰为 `beta<2/5`，并仍有 `0≤beta`、`0<c`、`0≤R`；冻结绑定明确记载 implementation=NOT_STARTED_AT_FREEZE。它是为真实对数截断显式限制适用范围，既未假装 FF 原本已含此条件，也没有偷偷加入结论性误差、独立性、一致性或积分前提。

tilt 是真正的 mu 指数倾斜；D、s、t、A 是同一协方差的既有白化构造。means 是该 tilt 的实际一、二阶均值；Y、laws、Phi 均由同一 A/means/tilt 定义。整个存在量词只选择一次 lo、hi、E；hE 的逐点 A 作用与 Y 坐标身份、算子界、全部矩/局部展开/累积量/高斯多项式包以及 L/U/cA/RA 都属于这同一组数据。新增结论没有另选 E、rho 或概率律。

全部陈述 let 的逐项覆盖如下，行号为 FH 冻结文件；相同名字在不同合取中各按其实际绑定作用域完整检查，没有把同名当作自动同对象。

| 冻结行范围与内容 | 该组 let 名字 | 数量 / 累计 |
| --- | --- | --- |
| 14–28 规范族 | tilt,D,s,t,A,means,Y,laws,Phi | 9 / 9 |
| 50–53 白化常数 | L,U,cA,RA | 4 / 13 |
| 85–90 对数 Taylor | P | 1 / 14 |
| 93–99 四阶对数式 | Q | 1 / 15 |
| 102–127 实际样本四阶对数 | Qsample,M,T,rho,Qn | 5 / 20 |
| 130–150 四阶指数比较 | Qsample,M,T,rho,Qn | 5 / 25 |
| 153–176 四阶多项式 | Qsample,M,T,rho,Pn | 5 / 30 |
| 178–185 真实三、四阶累积量 | X | 1 / 31 |
| 187–189 全阶一致累积量 | X | 1 / 32 |
| 192–196 八阶对数 | X,kappa,Q8 | 3 / 35 |
| 199–224 实际样本八阶对数 | Qsample,M,T,rho,X,kappa,Qn8 | 7 / 42 |
| 227–247 八阶指数比较 | Qsample,M,T,rho,X,kappa,Qn8 | 7 / 49 |
| 250–276 六阶多项式误差 | Qsample,M,T,rho,X,kappa,a,Pn | 8 / 57 |
| 278–311 局部加权积分 | envelope,Qsample,M,T,rho,X,kappa,a,Pn,small,weight,error | 12 / 69 |
| 312–335 全局 Gaussian 多项式及尾积分 | X,kappa,a,Pn,tail,f | 6 / 75 |
| 340–348 新远频逐点结论 | Qsample,M,T,rho | 4 / 79 |
| 351–366 新加权远频积分 | Qsample,M,T,rho,far,f | 6 / 85 |

末端 Gaussian 包的括号在新合取之前闭合；其存在 C 和任意 delta/k/q/epsilon 的旧量词范围没有意外吞入新结论。新逐点结论为所有实 q 和 epsilon>0，先选择 N≥1，再量化所有 n≥N、p:Theta、xi/eta 及两个真实频率限制，返回该 rho 的概率性与 `n^q*‖CF_rho‖<epsilon`。新积分结论为所有自然 k、实 q、epsilon>0，先选择 N，再量化 n/p；far 使用严格下界 `sqrt(n)*RA<r` 和闭上界 `r≤n³log n`，f 是 r^k 乘同一 rho 的实际复特征积分范数。结果含真正 IntegrableOn、普通 Lebesgue 实积分非负性及严格缩放小量，未以不可积时积分的默认值替代可积性。

## 新证明逐段核对

源码379–387：由精确合格 FF243 取得 lo/hi/E 和全部旧合取，逐个原样返回。FF 所需 hbeta、hc、hR、hdet、hWC 与当前假设相同；只新增的 hbetaUpper 用于新远区证明。没有从最终原概率展开或待证整窗误差反推任何局部引理。

源码388–409：局部 RA 与冻结的 R/L 定义相同。调用 FG244 的真实对数三次截断一致定理，使用 `beta,c*U^(-beta),R/L,q,epsilon`；hbetaUpper、hcA、hRA 精确满足全部条件。FG 给出的 N 在任意 pairlaw 及频率之前取定，因此后续按 p 构造实际 pairlaw 不破坏一致量词；N≥1 和 hn 推出 n≥1。

源码410–418：nu 就是实际 tilt p。`interior_subset (hTheta p.property)` 给出原测度下 `exp(p₁*x+p₂*x²)` 可积，由 `isProbabilityMeasure_tilted hf` 导出 nu 的概率性，未把它额外假定。pairlaw 定义为该 nu 经 `x↦E p((x,x²)−means p)` 的像。BV155 完整接口用于同一 n、同一均值对和同一 E：同时给 pairlaw 的概率性、实际样本 Q.map T 的概率性、逐样本归一化等式和全局归一化 IID 和的测度身份。源中取出的 hnormalized 是最后的全测度等式，不是仅在小频率上成立的特征函数身份。

源码419–445：Y 的两个坐标由固定矩阵与多项式构成，通过有限坐标分解证明可测。BV 的第二条接口用 `(hE p).2.2.2` 的真实逐点 Y 身份，给 `pairlaw=(laws p).map (v↦(v0,v1))`。坐标映射和 Fourier 核连续，`MeasureTheory.integral_map` 将 pairlaw 的真实积分改写成原 Phi p u v；这一步并未替换实际概率模型。hpoint 的最后合取正是同一个 cA/RA 的白化弱 Cramér 界，按实际元组位置取得 hWCp 后构造 FG 要求的 hWClaw。概率律上的核绝对值为1，且所用依赖完整接口/合格证据提供真实特征积分；没有把非可积默认零视为衰减来源。

源码446–450：先返回 BV 的实际 hrhoprob，再展开 let 并用 BV 的全局测度等式 hnormalized，将目标实际样本 rho 改写成 pairlaw 的归一化 IID 和像律。调用已先取阈值的 hbound，真实 hfreq、hcutoff 原样传递。没有把原本 n³ 界错用于 n³log n，也没有假设 pair 内两坐标独立；独立性来自 BV/FG 接口中真正的 n 个相同 pairlaw 的积测度。

源码451–480：固定任意 k、q、epsilon>0，令 m=4*(k+2)，先以指数 q+m 和容差 epsilon/8 调用 hfar 取 N。随后才引入 n、p，并定义同一 nu、Q、M、T、rho、far 和 f。`Shao.Path n` 与 `Fin n→ℝ` 是既有同一定义，样本能量仍为 Shao.energy。horderSix 中概率性在所有频率条件之前已经成立；由它导出 hrho，故即使 far 为空，也不依赖在 far 中选择频率来证明概率性。n≥1 给正实底数，a=n^q、b=n^m、a*b 均严格为正，包含负 q。

源码481–499：取 epsCF=(epsilon/8)/(a*b)>0。正底数实幂加法与自然幂身份给 `n^(q+m)=a*b`，没有把 q 限制为自然数或非负数。far 中每点的两项定义限制正好供 hFn；由 `(a*b)*‖CF_rho‖<epsilon/8` 除以正数，得到所需 `‖CF_rho‖≤epsCF`。这里只将严格点界放宽一次为 DB 的非严格点界，不会丢失最后严格结论。far 的可测性由连续半径函数的严格下界开集与闭上界闭集相交获得。

源码500–512：`log n≤n−1≤n` 对正底数成立；乘非负 n³ 得 far 半径≤n⁴。n⁴ 仅作为 DB187 积分体积半径 K；hCF 仍只针对真实 far 集，来自 n³log n 上的 hFn。没有在 n⁴ 处调用弱 Cramér 指数账、没有把 beta<2/5 偷换为对四次截断足够的条件。DB 的完整条件逐一满足：真实概率 rho、可测 far、K≥0、epsCF≥0、radial bound、同一实际 CF 点界和任意自然 k。其结论给真实可积性、积分非负性及 `integral≤4*K^(k+2)*epsCF`，体积常数4和欧氏半径与当前对象一致。

源码513–526：`((n^4)^(k+2))=n^(4*(k+2))=b` 是自然幂乘法身份。利用 a,b 非零，严格代数化简 `a*(4*b*epsCF)=epsilon/2`；左乘积分界时 a>0，方向保持。最后 epsilon/2<epsilon 给冻结目标的严格不等式。全部 hpow、hwindow、hrate、hb/ha/hab 及最终 calc 已核对；没有缺失的 n 因子、权次数或量词依赖。

## 边界与退化情况

Theta 为空时 p:Theta 的结论为空量词；上游 FF 返回的正 lo/hi 和其余包按精确合格声明复用，未加非空假设。beta=0 为此辅助接口允许的边界，FG 的正预算仍有效；原始充分修复的严格0<beta<2/5不因此扩大。beta=2/5 被明确排除。cA>0、RA≥0 使用原包，R=0 仍合法；严格远频下界排除原点。xi/eta 可为任意正、零、负实数，未丢坐标轴。

n=0 被 N≥1 排除；n=1 时 log1=0，而 sqrt(n)*RA≥0，far 为空，不出现除零或虚假的非空见证。逐点结论只在两个频率条件成立时要求概率性，积分结论的概率性则另从 horderSix 无条件获得。真实 lower 边界取严格不等号，上边界保留等号；未擅自删去边界。k=0 合法，保留零次幂；任意实 q（含负数）的 n^q 始终为正。epsilon 的严格正性足以给所有除法、容差与最终严格余量。没有额外非格点性、分量独立性、误差包络或整窗假设。

## 全实际类型、拥有者和机器凭据

770 LF 导出恰含唯一 DECL/TYPE/KIND theorem：`Shao.OQ3.compact_open_domain_six_order_log_cubic_far_frequency`；0 非定理 VALUE、0 新私有/生成声明。全部前提、嵌套存在量词、85 个 let、单个 E、Gaussian 末端括号以及新两项量词与完整冻结/源码吻合。类型末尾 AXIOMS 为 `[propext, Classical.choice, Quot.sound]`。

完整 Audit 遍历环境全部常量，以 `getModuleIdxFor?` 的真实模块拥有者等于 `Shao.OQ3.CompactOpenDomainSixOrderLogCubicFarFrequency` 筛选，不用命名空间或公开目标名单限制实际拥有者集合。对每个拥有者拒绝新 axiom 并执行递归 collectAxioms，只允许既定三项公理；打印全部 TYPE，遇到 defnInfo 会打印 VALUE，同时检查目标存在、定理种类和 frozen count。保存结果 all_owned=all_theorems=public_theorems=1、non_theorem_values=0，与实际导出和源码一致；无隐藏定义值待补读。

原 build-history 只有首次 native001：最终精确源31815 B/529 LF，2026-10-27T18:24:00.609318+00:00 记录自然 RC0，46.508016403764486秒。原生日志保存 SHA256 `573a0f46e57a90a29c18904c7e95617979d6efe69efa96a894ff5cf1572219ad`，2014 B。没有本单元失败源码、失败 native 或成功检查重放。交接说明保留6条风格警告；本审查没有读取远端原始日志正文，不声称已消除或逐条复核警告。

首次原始对象 SHA256 `ce9f5bf71e29b19b20bd5e62070dac8716053f3af68efac369af0d3b9c11795c`，2501112 B；own-firstO 把本模块 accepted-source-view 链接指向分线原 build 对象，记录 new_own_firstO_links=1、old_entry_changes=0、shared_cache_writes=0、binary_copies=0。随后同一首次对象全部实际拥有者 TYPE/递归AX 审计在2026-10-27T18:25:19.398338+00:00记录自然 RC0，6.068696968257427秒；原审计日志 SHA256 `19c561f77f02922a2aaeb5a68f0f21cd5a66ef28f267d2c3f42a47625dddc80c`，78337 B。

standalone build-history 与 receipt 的完整历史内容一致，audit-record 的全部共同核心字段与 receipt 一致。本次确定性比较共55项，全部通过，包含 FF/FG 精确 qualification 对象、各 source/review/receipt/TYPE 和 source/type/firstO 内部绑定、BV/DB 清单与选定行/发布载荷及 FH 机器核心一致性；另核对原来源、恢复文件、声明保留和所有本地核心工件字节。

本地 `library/lean-toolchain` 为 `leanprover/lean4:v4.36.0-rc1`，SERVER/恢复规则钉死 mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 和 shared-v34。保存 native/AX 使用 phase40 的 CPU36–39,44–47、既有 c12-heavy.lock、-M8192 -j4。内存记录140GiB项目/60GiB系统保留、180GiB聚合看门/200GiB硬限，无 RLIMIT_AS、cacheMutation 或 OOM；helper 的 phase39 文本是沿用的准入公式标签，不取代明确 phase40 与 CPU 字段。这里复用既有精确机器检查，不执行本地 Lean。

交接另说明完成前曾观察 PID1409426、CPU36–39,44–47、RSS3606676kB；这是分线交接中的观察说明，本评审没有亲自观察该远程进程，也没有在本机重算远端对象/原日志。保存的成功、全拥有者公理、首次对象与本次完整语义审查相容；不能把作者收据或交接观察写成审查者的新远程实测。

## 合格依赖、完整接口与来源限制

FF243 `CompactOpenDomainSixOrderGaussianPolynomialTail`：源 `32b80b9ba9602eb7507125ad705083b664842fcb2bcaba7a2a6345ce14df2e9a`，24052 B/379 LF；冻结 `448b23d47af07b2a7a8411dee457ac7e8ede85649dc205ac49fcc9b9c0dbba1a`，21978 B/334 LF；全部类型 `6231e24a678f2f1c5bcde19586b66cc12f4b7b2f2d3e532694134aa2a3bdec8c`，64963 B/659 LF，75 lets。全部公共数据包/类型已读，旧完整证明和成功证据复用；第一原始对象 `e873b79047415475a1419b455b5866ff3ac6597d362244611a97b0a12081fc4f`。

FF 合格完整独立报告 SHA256 `752b1cc6a4a14152350d8c8b6e7f278c8b9e28cddba654f39eccd498ac557a97`，158 LF；receipt `66aee60cc964667c6699d097754ec95ff69ec21aaaefeafcef5cf04e3d78a6ed`；qualification `8773fecc293c41ca230bcff43ea7b7e71aaf8e1bbff14b0cff2e8392aa1f3ca7`。qualification 于2026-10-27T18:25:38.315149+00:00记 COMPLETE_QUALIFIED、parentFullReportRead=true、reviewerCompletedStopped=true；独立评审 `/root/oq3_ff243_final_review`。本地哈希和 FH qualified-binding 对象逐字段匹配。

FG244 `NormalizedIIDPairLogCubicCutoff`：源 `43bcd522e1271ae8589336ab94e2a4683b9db02a52a893946cb36f18661ed72a`，8035 B/155 LF；冻结 `f335e2f33cfb810086b75c344daea00b95fa6bad7a27f78cebf5094c24dad53c`，3899 B/70 LF；全部类型 `1d7035493fba09fa11ce5b2ca404fa5772093a68834638d4650202ce70b7653d`，4414 B/84 LF，4 TYPE/9 lets。四个完整接口均已读：正预算实截断指数界、所有 law 的一致实截断衰减、覆盖 n³log n 的 d>3 正预算、真实对数截断一致衰减。FH 实际使用最后一条，所有参数/概率性/弱 Cramér 条件已由实际模型导出。

FG 第一原始对象 `db7cd62dab71c634a94159e51e06c2b23f6ec67921f44e0b55be5a9b13332a8d`；合格完整独立报告 `f6fd40348a2b617288b15f185c4bdf3d25d4cc60cb0177175d59ec1c739b8e93`，131 LF；receipt `7c00084f1086cee2e3b93bedffe74d736f53b4d5bd840889f15b0ac8d3b5bb0b`；qualification `eaa40c95a5d3ec5ad6acd2347c2e2bb55bc5241f94c7f9cee1d343e9c7028b26`。2026-10-27T18:33:45.826303+00:00 qualification 为 COMPLETE_QUALIFIED、parentFullReportRead=true、reviewerCompletedStopped=true；独立评审 `/root/oq3_fg244_final_review`。本地哈希和 FH qualified-binding 对象逐字段匹配；FG 的旧失败和恢复记录随已合格版本保留，不重放、不把它们当本 FH 的新尝试。

BV155 `ParabolaIIDStandardizedLaw`：源 `3c44e20c9003e0b743829a5ad46ee56f12f72c9cc8fbaa6bea61c5cbb3c526b7`，5128 B/104 LF；全部类型 `bc48a04f9d3e6f45d210b3014512005be3efeee740b98a2c90dbdb6adb1f9c49`，1560 B/29 LF。两个公开接口和生成的 `_proof_1_1 : ∀ n,1≤n→n=0→False` 全部已读；没有额外概率、矩、独立性或一致性隐藏前提。清单 `publication-u22-bn-bv/docs/oq3-u22-compact-physical-whitening/manifest.json` SHA256 `6b172b2276958a6d47c629c1c7fc8b81712bd29beb65d249a510999a7e42b1e0` 的 bv 行精确匹配绑定；源/范围/receipt/review 发布载荷哈希均匹配。旧 receipt `cc96202bba1795effea51e1ab5ed75c31eef7d0a179e92050b1c0283b7d41133` 与完整独立报告 `0ede4b14deb562e06696b2ac0c56d63b430f41c48b21063626a4870e69090c56`（108 LF、complete_parent_read=true）复用。

DB187 `PairCharacteristicBoundedIntegral`：源 `2725a98d4509855878f0841af0fd34d1668b50431a4f21f0c8090392e781b101`，4277 B/88 LF；全部类型 `64e32ec6d6acadef3c9c6a477c47af2063d272b2f95c4d6f9e1c4799a65c1014`，927 B/15 LF。完整接口为实际概率 rho、可测 D、非负 K/epsilon、D 上真实半径/实际 CF 上界，推出所有自然 k 的可积性/非负普通积分/4*K^(k+2)*epsilon 界；没有假设可积性。清单 `publication-u22-cy-df/docs/oq3-u22-weighted-gaussian-window/manifest.json` SHA256 `2be2c6f747a30630ecfd5578dbc2d59fc5ce0e0de65da563ae9d81e708108f90` 的 DB187 行精确匹配绑定；发布源/receipt/review/实际类型哈希均匹配，发布 `scope-u22db.md` 哈希也为行内 `20868bfe4b979e8591549306aae2053c2490a4560915a49d2a4afea2b95726f0`。旧 receipt `b70125f756d5563a3ea84a50fc6fe43ae9279a379706798ea905327f8def2b66` 和完整独立报告 `71c2257883a23e390e5ab734f3138f03d07e914c10562fedfd7bd779aadc208c`（101 LF、parent_complete_read=true）复用。

BV/DB 旧 receipt 历史待审标签由同源合格清单中的完整独立终审补齐。BV 原首次完整成功为attempt03，原全归属审计RC0；DB 为attempt02，原全归属审计RC0。两者旧 receipt 都没有自身首次对象哈希字段。FH server-binding 中 BV 当前保留对象为 `5ac5eba2999d340b7d7c35c62ed7fa811aa5200f8edb540fcedc91944865d3b6`、mtime2026-10-23T17:14:32.110071+00:00；DB 为 `cae165e66e87a0aeaa01bd09bdb081e1590d2db7467ad29cff922f32252da283`、mtime2026-10-23T23:02:02.588364+00:00；两者 exactFirstOriginalO=null、currentObservationNotRetroactiveArchivedHash=true。它们是后来保留对象的观察记录，不能追溯倒填为旧回执曾归档的 first-original-O。

FF 继承的 CI168/CY184/DE190、FG 继承的 CE164/CF165 的相同旧 own-object 哈希未归档限制继续保留。旧完整证明/审查/TYPE/递归AX通过精确未变的 FF/FG 合格链复用；本报告没有增加旧二进制来源保证。FH native 当时的 bearing/server 保留 FF/FG 待审历史标签；后来的 qualified-binding 明确二者在本次终审前已 COMPLETE_QUALIFIED、allBearingDependenciesQualifiedBeforeFinalReview=true、changedSourceOrObjectSinceFHKernel=false。源和 firstO 身份与历史记录相同；不擦写历史 pending、不为补齐资格重放成功检查。

## 原始题意、归属和保留开放范围

原 r2/report 本地 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`，repair01 `9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`，verdict `fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5`，均已本地核对。原报告139–156及518–519的真正截断为 n³log n；旧 DF 的 n³ 工作与之不同。本次 FH 用已经合格的 FG 对数截断桥和 BV 实际样本传输，确实补上同一实际规范模型的远弧逐点与加权积分，不是仅证明一个抽象新律的界。

原始正向命题仍是一种充分修复，严格要求0<beta<2/5、正则鞍点/几何和显式远区局部化；本模块 beta≥0 的辅助适用范围不能扩大原根范围或声称端点、最优性、最弱条件。真正联合非格点不足的已接受反例、远频率近共振障碍、p54修复以及 `v_corr=-hat_t0*sqrt(det Delta)*sqrt(Lambda1)` 均保留。

repair01/verdict 已明确将均匀律弱 Cramér Edgeworth 输入归于 Song 的 uniform-in-law 定理取 s=8；原 report 的 Angst–Poly 对角一致化叙述不在本报告中重新认证为最终归属。本模块不重证 Song 的全部外部定理、不隐去外部归属，也不进行新颖性、优先性或历史首次认证。

尚开放：同一实际模型的中频、六阶整窗口实际 CF−Pn 加权误差与组装、Fourier反演/Hermite身份、振荡/平滑/去平滑、尾域外部概率、B–D 和原 OQ3 根。FI 在其他位置的新源码或机器尝试不是本报告证据；不从本 CORRECT 推断其通过。C1/C2/OQ4/OQ56 原根状态也不由本报告认证。

GAPS: 在上述精确冻结声明、完整新源码/证明、全部85 let、唯一完整实际 TYPE、零 VALUE、承重完整接口和既有精确机器证据范围内未发现关键缺口。保留的原始下游义务与旧对象归档限制没有被本审查消除。

## 用量、最终绑定与权限释放

父实例完整读取本报告 ENTIRE 后绑定最终 SHA256，并将本独立完整审查与精确 native001/同一首次对象全部实际拥有者AX收据共同记录 qualification。无需因上下文变化自动再审旧完整证明或重跑已经成功的检查；实际数学改动只使受影响的证据失效。

prescribed/configured model=`gpt-6.1-sol`，effort=`xhigh`；实际提供方型号/推理强度证明和运行用量分项未向本上下文暴露，actual_model=null，actual_effort=null，input_tokens=null，cached_input_tokens=null，output_tokens=null，reasoning_subset_tokens=null。null 表示不可用，不表示零；没有编造购买积分、订阅百分比或配额分摊。

COMPLETED_STOPPED。本报告唯一写者权限及本次评审权限全部释放；children=0，heavy=0，inflight=0，pending=0，uncertain=0。没有待续写、待执行请求或对任何其他文件的写入权。
