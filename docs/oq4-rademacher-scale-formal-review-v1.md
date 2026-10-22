# DA2 最终独立完整审查 v1

STATUS: CORRECT
MATHEMATICAL_PROOF: CORRECT_RELATIVE_TO_CERTIFIED_SCALAR_DA1
SOURCE_TO_STATEMENT: PASS
FULL_SOURCE_KERNEL: PASS
ALL_OWNED_CONSTANTS: PASS
ACTUAL_PROJECT_DEPENDENCIES: PASS
NEW_RAW_LEAF_COUNT: 0
OQ4_ROOTS_STATUS: OPEN

本次独立审查确认：固定匿名数学证明和最终 Source 完整证明了冻结 DA2.0–DA2.4；实际公开 eta3、DA2、DA2_subcritical 与精确冻结相符。自己的实际 -R 完整 Source 检查成功；两种不作命名空间筛选的实际所属常量枚举同为 22 项，全部安全性及传递公理检查通过。无数学或形式缺口，无需修改 Source。

## 独立性与读取范围

沿用此前只读声明的独立上下文。本次先完整阅读匿名证明和最终 Source，完成数学及逐条 Source 推理审查后，才运行自己的必要 native 检查。未读作者 PublicInterface、author-receipt、server-receipt、作者运行日志/推理或既有数学独立审查推理。既有 Scalar/DA1 只按真实认证源码/类型承接，不重复认证其证明。数学冻结和匿名证明中的 DA1 pending 均为历史状态，未据此另设前提或重开上游认证。

| 完整读取输入 | 字节数 | SHA256 | 完整行范围 |
| --- | ---: | --- | --- |
| 原 spectrum01.md | 4306 | b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b | 1–119 |
| frozen-rademacher-scale-assembly-v1.md | 5248 | 9e7f840f25038e4ef55ba561eaca112802a6b373849722898f6d6a550ca9e946 | 1–82 |
| frozen-rademacher-scale-formal-statements-v1.md | 4962 | 5a52198e9dd8cc4d28b0598ecac1c6e176d2d5544a82e4ee570d769b80664fd2 | 1–129 |
| rademacher-scale-assembly/proof.md | 13172 | 641db80d6d5986135bebfb5992131956f84dfbcf3b684b6755881d5ea33ce199 | 1–372 |
| rademacher-scale-assembly-formal/Source.lean | 11989 | 00ccea34800e199a9edf712523e1e440eccbafeffa625e8fafb78253a5fd1dce | 1–294 |
| library/Shao/OQ4/RademacherScalarBounds.lean | 11062 | 12670bd33a813849156b245cad28f5efb783a55919f8a0743fcf3fb9fbff329f | 1–283 |
| library/Shao/OQ4/RademacherLatticeShift.lean | 13125 | 5c5ffa545a9e26ba2a33ebba27ffa64aaa708eaeeea0f56c84aacd8f194aebf7 | 1–293 |

原文绝对路径为 C:/game/shao/current/oq4/c01/spectrum01.md；其余文件均在 C:/game/shao lean 下，前四个冻结/证明/Source 工件在 drafts/oq4 下。上述各完整读取均覆盖字节 1 至表列字节数，无截断替代。已有 AGENTS.md、SERVER.md、coordination/TEAM.md、数学定理技能及指定参考文件的完整读取仍有效。stable-base-v1.json 在本地和服务器均完整解析，44662 字节，SHA256 ce7ac34ff90b8c79f7e32698fc0b19943722145cb7011185cbaa7c5f935ecf0a；只使用其有界哈希基线，不读作者推理。

前轮为确认真实 U1 类型而读取的 RademacherSpectralTail.lean 范围明确为 1–45、515–565 行，非全文件审阅；它不是本次 Source 的实际项目依赖，也未扩大本次证明范围。复用/参考的既有材料仅为通用元数据收集工具代码，没有读取 S2 Source 或 S2 审查推理。

## 原文到数学冻结及实际公开声明

原文 11–12 行的弱胞元 m=floor(h)、H=m+1，由全 k 的 1≤m、m≤h<m+1 精确表示；没有自由 H 或严格事件边界。原文 70–81 行的三个尺度和确定性残差是本次采用部分。原文 S3/S4 中真实概率及 Brownian 的 o(1) 不属于 DA2 的声明或证明。

Source 第 14 行 eta3 的定义行与精确冻结逐字符相同。DA2 第 60–122 行及 DA2_subcritical 第 257–276 行在仅归一化空白后，与精确冻结中的两个完整头相同，归一化头 SHA256 分别为：

- DA2：417f7b1f6b172e965b121591facf0bd6399db053e980d5da5b06ce26cd5e0627。
- DA2_subcritical：18bc724014d5e5b57786d2b947aaf66c9f46d3da9961a492329bd5dfd4382310。

实际编译后的三项公开类型及 eta3 值由自己的内核元数据完整输出在 actual-public-interface.json/md；逐项人工核对结果与上述冻结头一致。实际 H/u/a/rho/lambda 均解析到 Shao.OQ4.RademacherScalarBounds，delta 解析到 Shao.OQ4.RademacherLatticeShift。实际 eta3 值为自然数时间的实数转换除以实际阈值的三次幂。

| 冻结输出 | 匿名证明覆盖 | Source 覆盖 | 独立核对 |
| --- | --- | --- | --- |
| DA2.0（数学冻结 51 行） | 91–135 行 | 123–135、246–255 行 | 全 k 合法性、h≥1、H≥2、0<delta≤1、H=h+delta、弱整数端点 delta=1、全部显示分母非零、sin(u)/a/rho/πa/4 正性及 rho<1 完整；没有移到假设侧。 |
| DA2.1（53–57 行） | 137–204 行 | 136–186 行 | H→∞、H/h→1、N/H²→∞、最终 H²≤N 和最终自然数正时间全部证明；自然数起点先于后续 k 选择。 |
| DA2.2（59–63 行） | 206–288 行 | 187–224 行及 23–58 行 | N/h⁴→0、1/H²→0、最终 0≤N/H³≤M' 及 N/h³−N/H³→0 全部证明；M'=M、K'=K 合法且固定。 |
| DA2.3（65–68 行） | 290–328 行 | 225–245 行 | 真实固定 DA1 直接给完整残差的绝对值界；系数 π²/4、eta3(n,h) 和 delta 均准确。没有拆分相消的发散项取极限。 |
| DA2.4（70–72 行） | 330–364 行 | 277–292 行 | 全域及三个原尺度保留，只额外使用实际 eta3→0。位移项通过 0<delta≤1 消失，无相位收敛假设；输出恰为无位移的确定性三项表达。 |

所有序列仍为任意 m,n:ℕ→ℕ、h:ℕ→ℝ。不要求单调、奇偶、注入子列或所有 n k>0；早期 n k=0 完整允许。固定正实界 M 及起点只要求最终三次尺度上界，未加强为 eta3 收敛。次临界定理仍保留冻结中的 hscale3。原时间索引直接由 n k=k 取回；有限前缀仅最终进入胞元的后继应用未被冒充为已经完成。

## 匿名证明与每段形式证明的独立核查

1. Source 16–21 行的私有 zero_of_abs_le 正确把绝对值的最终夹逼转为趋零。g 本身趋零和最终绝对值上界足够，不需要另加错误的全项界。它只是数学证明多处绝对值夹逼的封装。
2. Source 23–58 行的 cube_gap_bound 与匿名证明 (30)–(31) 完全对应。h、H 正且 h≤H，N≥0；h/H∈[0,1] 给括号上界 3。恒等式 B·delta/H·(1+h/H+(h/H)²) 精确，delta/H≤1/H≤1/h，故差在 [0,3N/h⁴]。所有乘法不等式的符号条件都已由胞元合法性和自然数时间推出，n=0 时仍成立。
3. Source 123–159 行先得到全项胞元几何、H≤2h，再由 h→∞ 得 H→∞、1/h→0、delta/h→0 和 H/h→1。没有假设 delta 自身收敛，也没有循环使用待证输出。
4. Source 160–186 行用 H²≤4h² 和 N≥0 得 N/H²≥(N/h²)/4。对任意实阈值 b 使用 hscale2 的阈值 4b 即足够；b 为负也没有漏洞。之后用阈值 1 得最终 H²≤N，由 H²>0 推出实数时间正，再准确转换为自然数 0<n。
5. Source 187–215 行从 hscale3 取一次 M,K。N/h⁴=eta3(n,h)/h 只在 k≥K 后受 M/h 控制，夹逼合法；H→∞ 给 1/H²→0。三次尺度 H 分母的上下界由 N≥0、0<h≤H 得到，沿用同一固定 M,K，不把最终条件变为全项条件。
6. Source 216–224 行用前述有限参数三次幂差界与 N/h⁴→0 证明差趋零；没有对两个可能不收敛的三次尺度分别取极限。
7. Source 225–243 行实际解构已认证 Shao.OQ4.RademacherLatticeShift.DA1 的存在常数。该常数在上游已先于 m,h,n 量化，不是新输入；忽略其正性不影响当前夹逼，因为实际绝对值界已提供所需最终上界。展开真实 lambda、eta3、delta 后，hDA1 的左侧就是目标残差；右侧由 h4 与 hHinv2 趋零。没有使用自由 Taylor 估计、自由 C_log 或逐序列误差假设。
8. Source 244–255 行按冻结的合取结构装配全部输出。新增一次分母/H³ 非零及正弦正性均由真实上游全项正性推出；整数端点正确消费 delta_at_left。
9. Source 277–292 行的 .2.2.2 正确取出 DA2 的最后残差结论。c=π²/4≥0、B≥0、0<delta≤1 给 |cBdelta|≤cB；新增实际 B→0 足以使位移项消失。最后是每项恒等式 (F−shift)+shift=F，不是把两个各自发散的主项直接相加取极限。

匿名证明所有量词、零时间、正分母、实对数正参数、最终界及符号条件均闭合。没有发现新增、删减或重解释冻结前提。

## 自有完整 Source 检查与字节绑定

服务器工作树为 /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4，分支 feat/oq4-scale-assembly，HEAD e1c3ca0ca2a3c52e3e4a600a3062542ca2a6a21d；前后均相同。独立输出根为其 repro_outputs/oq4-rademacher-scale-independent-bounded-v1。

成功 attempt-v2 使用自己的 actual-R/Shao/OQ4/RademacherScaleAssembly.lean，主模块元数据确为 Shao.OQ4.RademacherScaleAssembly，没有 self import。组合文件只由 import Lean 前缀、连续原字节 Source、run_cmd 元数据后缀构成；后缀没有预先加入 named Source-owned helper。

| 片段 | 字节数 | SHA256 |
| --- | ---: | --- |
| import Lean 加换行前缀 | 12 | f9d646b1e1b6498ec413286e9310c564c992f6fd6479ae9cc9e9cdd29058ab78 |
| 连续原 Source | 11989 | 00ccea34800e199a9edf712523e1e440eccbafeffa625e8fafb78253a5fd1dce |
| attempt-v2 元数据后缀 | 3616 | 62c0d9bd4e4b471be3c0d0e934289b9d825fcbc157af9621534ce3a35eee8378 |
| 成功组合文件 | 15617 | f5b3f0eb8c108c411d1099e9ced11728fb9c54263f07c4fc4bdea9617e45c482 |

Source 的零基字节区间严格为 [12,12001)，提取字节与固定原文件相同。先 activate，再 cd 工作树；所有服务器命令限制 CPU18–21，没有接触外部 CPU0–9/80GiB 工作负载，没有设置 RLIMIT_AS/ulimit-v。实际检查命令使用 taskset -c 18-21 lake env lean -M8192 -j4 -DautoImplicit=false -R 自有 actual-R 自有主文件，不带 -o。

attempt-v1 的审计后缀显示选项使用了本版不存在的 Options.setNat，导致后缀两处错误。固定 Source 只有 linter 警告，没有证明错误；该失败完整保留，未修改 Source。attempt-v2 仅修自有显示选项为本版 Options.set，完整命令退出码 0，耗时 7.057 秒；成功后未重跑 Lean。剩余警告仅是 Source 中冗余的 tactic 序列，未关闭检查或更改证明设置。

工具链为 Lean 4.36.0-rc1，commit c9afcddf514a6772bd4d649f7cfc04eff0b9f15e；Lake 5.0.0-src+c9afcdd。实际环境报告 trustLevel=1025，未传入 trust 覆盖选项。成功完整日志为 attempt-v2/lean-full-source.log，1643 字节，SHA256 49dca03d1be626dab400023848ac424bb9593d0076c17f5acd120d1f469fc1b9；原始日志及两个 attempt、raw Expr 全留服务器。

## 全部实际所属常量与公理

在强制取得 env.constants 后，收集所有 getModuleIdxFor?=none 的常量；另独立收集 getLocalConstantInfos(skipTheoremSubDecls=false)。两种未过滤名称数组完全相同，均为 22 项，没有以命名空间范围代替 owner 范围。

22 项包含公开三项、两个显式私有引理和 17 项自动生成定理；共 1 个 definition、21 个 theorem，其中 private 9 项。按 raw/user 命名空间过滤只会得到 20 项，另外两项是：

- Shao.OQ4.RademacherLatticeShift.delta.eq_1。
- Shao.OQ4.RademacherScalarBounds.lambda.eq_1。

这两项虽然位于其它命名空间，实际 owner 仍为当前模块，已经逐项保留审计。完整 22 项名称、kind、owner、moduleIndex、private、unsafe、partial、axiomKind 及每项传递公理列在 owned-axioms.json，没有遗漏生成或私有常量。

所有 22 项 unsafe=false、partial=false、axiomKind=false；所有传递公理集合均为 {propext, Classical.choice, Quot.sound} 的子集。Source 文本也没有 sorry、admit、新 axiom、unsafe、partial 或 native_decide。实际公开三项均只依赖标准三公理。不存在新公理、占位证明或检查绕过。

成功原始元数据为 attempt-v2/metadata-raw.json，1585366 字节，SHA256 ecfc6bd7bcdb8327be40cb23bceff02f58990a0046c37d410d80227cf6f60495，仅保留在服务器。本地接口只保留完整可读类型/eta3 值及 raw Expr 的哈希，不复制原始表达式。

## 实际依赖、固定版本与旧工件

实际 header 共枚举 5171 个导入模块，逐个解析实际 object 路径。全部项目导入恰为以下 6 个；没有未绑定项目模块，全部 source 与实际解析到的 olean 均属于稳定基线，并在检查前后相同。

| 实际项目模块 | Source SHA256 | 实际 olean SHA256 |
| --- | --- | --- |
| Shao.OQ4.CosineCoefficients | 8fa6f094c330a8006c5664f8912cafd035524cc461df95e81446d2384a46c104 | 20aca8e472d615990dd6aa70299db5c984880dda7154bebadc80452e73340498 |
| Shao.OQ4.KilledCosine | 054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8 | 2fb05117fe25dd40d5ff2c39f510935807ae5fa1d1814bb1a909f5c63fb172c8 |
| Shao.OQ4.KilledKernel | f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f | ddc29558bc0e1e5f2422145aa0baf0095e1c718f2b40afc4f7668478a4a012f0 |
| Shao.OQ4.RademacherCosine | c0ba478f9ed6b5aa75d7010d70835b37065a92e9878c65b086d3c3ff24e7f861 | bbef5afc3922ee9fbfaaf6b1bc1d579b7ec762862e795e7a78165064bfb5aea3 |
| Shao.OQ4.RademacherScalarBounds | 12670bd33a813849156b245cad28f5efb783a55919f8a0743fcf3fb9fbff329f | eca40068036732752546d5280ce828ded6e42eeeb3c347c2d84a964617ad5380 |
| Shao.OQ4.RademacherLatticeShift | 5c5ffa545a9e26ba2a33ebba27ffa64aaa708eaeeea0f56c84aacd8f194aebf7 | d9c46a2facae5e2de6e120155c34be20782e8cd406b1a6bca97359fb7c0cf570 |

固定 old47、protected92、HEAD139、build104 各组均在两个 attempt 前后与稳定基线全量相等。S2 Source 的 1229ec6631165367e1b3fcef50fbe15c3dd8d73b0688de348c5659693c93e3c9 和唯一 olean 的 091f45acfe96cb19635b1b89fa4ea0591b9ee1823925d79f0ec815aee80c74d9 保持不变。

lean-toolchain、lakefile.toml、lake-manifest.json 前后相同。实际 mathlib HEAD 与 manifest 均为 807d3836b165983210ee2ecf3cd28f239436949c，实际原共享 mathlib 工作树 tracked clean；未接入 root 的新 overlay。非项目 5165 个实际导入只固定版本及实际使用解析边界；完整 header/path 清单留服务器，不声称全 cache 前后哈希冻结。没有把 root 新 Brownian/Xi 工件计入本次依赖或本次结果。

canonical Shao/OQ4/RademacherScaleAssembly.lean 与 canonical .olean 检查前后均 ABSENT；自有输出根也没有任何 .olean。没有写缓存、共享源码/配置、Git、canonical 文件或任何 olean。旧工件核对和实际依赖路径表见 actual-dependencies.json。

## 最终裁决与范围

STATUS: CORRECT
KERNEL: PASS
ALL_OWNED: PASS
DEPENDENCIES: PASS
GAPS: []
MINIMAL_REPAIR: NONE

认证范围恰为原固定弱胞元上的确定性派生装配 DA2.0–DA2.4，以及实际 eta3/DA2/DA2_subcritical 的完整 Source。公开增量仍为一个透明定义和两个定理。新增原始来源叶为 0。

没有认证真实路径概率、S1/Pair/U1 本身、Brownian 基准、概率对数或概率倍率趋一；实际 S2/S3/S4/S5、Brownian、Spectrum 与 OQ4 根结论均保持 OPEN。本轮已完成，STOP；释放 lane 唯一 heavy 租约。
