STATUS: CORRECT
JUSTIFICATION: 对冻结的 EC214 完整公共声明、92 行完整新源及证明、39 行实际 TYPE/AX 输出进行了独立逐段核对。以同一实际 law/Phi 和真三、四阶投影矩，将合格 DY210 的真实 CF 到四阶指数误差与合格 EB213 的指数到二阶 Edgeworth 多项式误差相加，构造统一正共同半径和常数，所得完整冻结结论成立。未发现新增或偷换前提、未覆盖分支、表达式不一致或非白名单公理。此裁决仅限本地频率区的二阶 CF 多项式，不是原 OQ3 根定理的闭合。

审查者：`/root/oq3_ec214_final_review`，新鲜、独立、非作者上下文；父实例指定模型 `gpt-6.1-sol`、推理强度 `xhigh`。使用 math-theorem 验缝协议，未使用 math-ultra。审查期间只写本报告；未修改任何 Lean 源、冻结声明、旧审查、资格或收据，未访问服务器、运行 Lean/AX、派生子实例或发送跨聊天工具消息。模型用量的分项计数本审查不可得，未估算或冒报。

审查日期：2026-10-27。AGENTS.md 最新 OQ3 显式恢复条款和 `ROOT_OQ56_OQ3_40` 生效；本报告是该授权下的新单元独立终审，不复活历史暂停，也不增加执行权限。

## 1. 精确输入、字节与证据边界

以下是本次本地直接计算的 SHA256。源和各输入保留原字节；新源为 UTF-8、4829 字节、92 个 LF、0 个 CR。

| 文件 | SHA256 | 本轮覆盖 |
| --- | --- | --- |
| `u22ec-source.lean` | `cf827236f02813a2e2e3fd269dd4c08081e83d8e454c4754c50a3a7b2c93c568` | 全 92 行，全部声明及证明 |
| `u22ec-frozen-declaration.lean.txt` | `31bf59416764ccdcfab0751e93a62f2968ac7d75573b42966a45460402c1515a` | 全 42 行，完整公共头和四个 let 值 |
| `two-hundred-fourteenth-unit-scope.md` | `f87b78be6da074af302a4a6c09cf7e566f346ad053108dee0f20b3dfffed95b4` | 全 19 行，范围契约 |
| `u22ec-actual-types.txt` | `2341870220fd79a4062ba1926c4bdfb06f4285ae2ace6e0ad834243a2b410af8` | 全 39 行，1 TYPE、0 VALUE、1 递归 AX 记录 |
| `u22ec-receipt.json` | `6e64543a10fdd2ea52ed51877099bfb799d0568f6944f49ba135f6b0047169c5` | 全文，原成功及失败记录 |
| `u22ec-Audit.lean` | `7d7ce952aff7286d5eaf4774f527385e18b4642fc50d0c4801b78c768f9eecbf` | 全 47 行，实际 owner 枚举和递归公理检查 |
| `u22ec-audit-record.json` | `fae0e5b4ebf36a070d59a8fa8772dcbf9ec7244a2c64b4018307fa8ca8462d21` | 全文，与 receipt 的对应字段一致 |
| `u22ec-build-history.json` | `c55469519393d51ab6bf15decee10658ecdb39cf1951e5ca43b8f01e4b00bc0a` | 全文，与 receipt.build_history 精确相符 |

直接提取新源从 theorem 起至 `:= by` 前的完整声明，与冻结文件逐字符比较相同（只按其约定补回末尾 LF）；没有签名漂移。新源禁用项扫描 `sorry/admit/axiom/unsafe/native_decide` 命中数为 0；完整人工阅读亦未见这些绕过。审查没有把扫描或编译当作数学语义审查的替代。

服务器机械证据直接复用已有源绑定 receipt，未重新执行。下列 O 和日志摘要是已提供、与当前源绑定的服务器证据，不冒称由本审查在服务器重新求得：

- Native02：当前 `cf827236…c568`、4829B/92LF，2026-10-27T14:19:17.668176+00:00，RC0，6.7627486400306225 秒；成功日志 SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`，133B。
- 首次成功原对象 O：SHA256 `12ed844bb50231791409ab62c422459f6bbb6c638f645782deb0cd5d1372abe6`，309480B。后续 AX 使用该同一原对象，不是重编 producer。
- 同 O 的完整实际 owner 递归 AX：RC0，5.782158086076379 秒，2026-10-27T14:19:47.419238+00:00；审计日志 SHA256 `960405ac5c969e67aaf45f3a9222402b6d59efb4c24deb66fa84473df6d42dba`，3197B。
- Native01 保留为 RC1，旧源 SHA256 `a432e36beeb6d93363c158b950e6c2dbe4baadcae6df1176c52c0b78f3cc4878`，4712B/90LF；失败日志 SHA256 `b0241b2bc6e1ae79d287f9d2f2a5ca77ab5dd2d7cf0dc52d95ee8d33536d6f0c`，418B。父实例说明该失败为 `norm_sub_le` arity；当前 L79–82 已明确写出差分相加等式并调用 `norm_add_le`。失败源码及全日志仍留服务器 `runs/oq3/u22ec-20261027`，本审查未下载、删除或重跑它们。
- 当前源的机械成功发生在服务器钉死 Lean `leanprover/lean4:v4.36.0-rc1` / mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 项目流程中。receipt 记录 CPU36–39、44–47，`-M8192 -j4` 和 phase40；其 memory helper 的历史 `phase` 标签为 phase39 的共享内存公式，不构成数学前提或另一条资源授权。

## 2. 只复用已合格依赖，并完整核对消费接口

本审查完整阅读 DY210 的冻结接口 40 行及实际类型文件 62 行、EB213 的冻结接口 39 行及实际类型文件 41 行，尤其完整读出被消费公共定理的所有 binder、let 值和目标。旧证明及旧终审全文没有再读、没有重新认证；它们的既有完整独立审查资格通过精确哈希核对复用。

DY210 最终资格来自 `coordination/handoffs/20261024/oq3-handoff.json` 的 `qualified_unit_exact_evidence` 中 `unit=DY210`，记录为 `COMPLETE_QUALIFIED`，原先作者 receipt 的历史 pending 状态没有被误作最终资格。该 handoff 文件本轮 SHA256 为 `b384f7df697f09c404497d28affb6780be966193a6dd2834b4b2333fead0469e`。

| DY210 绑定 | 精确值 |
| --- | --- |
| 模块 | `Shao.OQ3.StandardizedPairQuarticExponentialError` |
| 源 | `57e43c1a18d2dda37d06b57429c1888591d8ad49bd16a58f4c6c186cba1521c7`，8024B/166LF |
| 冻结接口 | `c7ead76a7d4d5857772b686ad762b82085d3f4644ef4e19e0582a246148e8462` |
| 实际类型 | `23db6e5160c4a56724553aeab7e0846d7a4550f0f45b902f15cbc8ab530bbdd3`，62LF |
| 原 O | `dcb7cb878156e5300498210b0f3082275d497a6cd604e98d144b906866f879cb`，519536B |
| receipt | `f7b8931269242fcf048b75ac81b93560b5b404e59820940e067d4024e6bed40e` |
| 合格旧独审 | `2a77aa48c873a9050048b74bd3f074971b2ace70f156f94629ceaf90d6f299a9`，117LF，独审者 `/root/oq3_u22dy_full_review` 已完成停止 |

这些本地源、接口、类型、receipt、旧审查文件的哈希均与资格记录相符。DY210 的实际公共类型 L6–35 包含同一 law 的概率、L2、零均值、协方差 I 及真实统一径向 3/4/5 矩前提，字面 Phi 和 Qn，两个误差/模界共用的正 C、正 delta≤1；所有量词在 C/delta 之后。其8个实际定理所有者的资格及标准三项递归公理记录复用，不重做旧证明审查。

EB213 最终资格来自完整读取的 `u22eb-qualification.json`：SHA256 `96926fad21853135ecd5c76ac90745300b187117a41b4c42b7c98a744f99c181`，`COMPLETE_QUALIFIED`，父实例已完整读终审且独审者已停止。其具体绑定如下。

| EB213 绑定 | 精确值 |
| --- | --- |
| 模块 | `Shao.OQ3.PairMomentEdgeworthExponentialError` |
| 源 | `0db2e043da2169510061ea6863a28289b1b3ff79ea414467e90d568193c1c8d2`，11519B/248LF |
| 冻结接口 | `9a4606e638838e502ab669fe74dc57bb53f48cb56533ad7a1794d95f62d25f65` |
| 实际类型 | `5cb17f101e49f768a4b00662cc2d9f7c7e3107c6062d48693f0480b39a5d1500`，41LF、3 TYPE/0 VALUE |
| 首次原 O | `9171846c823c6d71daf10eb19df5c1d55575392735e44beb756b65896def8ce2` |
| receipt | `17fd28cf932e2cf7f299b2124be4b7935e0155191e5661552dc4ef7092958542` |
| 合格旧独审 | `2ccd130dd0dbc3af69f5ff449afebd3ae937e6969d4b6291757f3f5e04744ab0`，171LF，独审者 `/root/oq3_eb213_final_review` 已完成停止 |

EB213 本地源、冻结接口、实际类型、receipt 和旧终审哈希均匹配。该已合格独审的 CORRECT 和 parentFullReportRead 由资格记录及父实例任务绑定复用，本审查没有重读其171行证明终审或248行旧证明。被冻结 EC scope 中“EB213, not yet qualified”是冻结时的历史状态；当前精确 EB 资格已就绪，不能把该历史括注解释为调用尚未合格依赖。

被实际调用的 EB 公共头完整为：任意同一 `law : ι → Measure (Fin 2 → ℝ)`、实 M3/M4、真实径向三四阶矩的可积性及统一积分上界，定义字面 m3、m4、Qn、Pn，给出统一正 C、正 delta≤1 后对所有 n≥1/i/u/v 的指数到多项式误差；没有额外概率、Gaussian、任意系数或 coherence 前提。新源 L55 正好传入当前 law/M3/M4/hI3/hM3/hI4/hM4，没有漏项或改 law。EB 的另一个公共引理保障这些真实投影矩的可积性；此处使用它已合格的语义后果，没有把全积分的默认值当作实际矩。

## 3. 原始数学来源与本单元的精确范围

本轮完整读取只读 `C:/game/shao/current/oq3/proofs/r2/report.md` 的 L1–158（结论及第1、2节全部）和 L493–510（前提、边界、误差 verdict 相关范围）。文件 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`，20102B/523LF；没有写该来源或其历史。

原报告 L41–60 以真实倾斜律、真实均值/协方差和标准化变量为对象，L83–92 给出 `Y_theta=Delta(theta)^(-1/2)(W-m(theta))` 和归一化 iid 和。新声明以任意真实标准化二维概率族为输入，保持该标准化特征函数层的正确一般接口，没有把 Phi 换为抽象误差、任意 Gaussian 或预设展开。

原报告 L99–115 明确把完整八阶 weak-Cramér 结果归于 Angst–Poly 正式发表版 Theorem 4.3，L128–137 的 `Q^(6)` 包含直到 `n^-3` 的二维 Edgeworth 符号测度；L139–157 还需要紧中频和远频控制。EC214 只产出局部频率的 `n^-1/2` 与 `n^-1` 两级修正，多项式中的 m3² 项虽是六次频率项，不等于完成原 `Q^(6)` 的六阶展开。它没有给测试函数/符号测度误差、Fourier 反演或原尾概率。

原报告 L13、L103–104、L153–156、L505–506 的严格 `0<beta<2/5`（上界绝不含端点）保持为原来源范围；本局部定理不需要 beta，不能因此扩大原定理范围。原报告的固定 x、正则鞍点/率间隙、外部定理归属及 `V_n=0 => S_n/V_n=0` 约定亦未被本局部证明消去或改写。已有 p54 修复和外部来源归属均未触及，未作新的根范围或新颖性主张。

因此 full order-six Edgeworth、全频区/反演、解析 CGF 及其导数、原 B/D 和 SAME single E/真实 rho 消费者均继续 OPEN；本报告不替这些待办盖章，也不把旧 A 反例证据重解释为其他根完成。

## 4. 新源完整公共头和四个声明 let 的语义审查

新源 L1–6 只导入上述两模块、进入 `Shao.OQ3` 命名空间、打开 MeasureTheory 并声明 noncomputable section；没有另加公理或别名来遮蔽目标。L91–92 正常闭合 section/namespace。

L8–28 的唯一公共头量化任意 universe 的索引类型、同一真实二维测度族；hprob 是每个 law i 的概率性；hL2 对两个坐标都要求 MemLp2；hmean 对两个真实坐标积分均为0；hcov 对每一 j/k 给出真实 covariance 的单位矩阵。M3/M4/M5 是实数，L17–28 逐阶同时要求真实非负径向 3/4/5 次函数可积和积分≤对应统一常数。这些与 DY210 一项不差。它没有把实际矩替换成任意张量或只写一个结论性误差前提；也未额外要求指标类型非空、有限或可数。空族情形由合格输入接口原有全称形式覆盖。

L29–31 的 `Phi i u v = ∫ exp(((u*y0+v*y1):ℝ):ℂ * I) d(law i)` 是正号 i 相位的真实特征函数。L32–33 和 L34–35 分别是同一实际 law 下 `∫(u*y0+v*y1)^3` 与 `∫(u*y0+v*y1)^4`；所有 u/v 都是相同频率，不存在换律、换相位或额外矩参数。

令 `S=u²+v²`，`s=√n`。L36–40 的第四个 let 完整为

`Pn = exp(-S/2) * (1 - I*m3/(6*s) + (((m4 - 3*S²)/24 - m3²/72):ℂ)/n)`。

这里 `3*S²` 在 m4 的积分外，只减一次；没有变成 `∫(projection^4-3*S²)` 或把 m4/m3 换成界。`-m3²/(72*n)` 的负号、72 和 n 次数正确：以 `a=-I*m3/(6*s)` 作形式校验，`a²/2=-m3²/(72*n)`；四阶累积量校正正是 `(m4-3*S²)/(24*n)`，cubic 的 `-I` 与正相位 CF 一致。这项校验说明 Pn 的意义，完整误差并非用形式级数代替证明，而来自已合格 EB213。

L41–49 的量词先存在同一正 C、正 delta≤1，再依次量化全部 n≥1、i、实 u/v。唯一频率条件是闭球 `sqrt(S)≤delta*sqrt(n)`。结论同时保留真正 CF 的 `‖Phi(u/√n,v/√n)^n‖≤exp(-S/4)` 和对 Pn 的 `C*(r5+r7+r8+r9)/(n*sqrt(n))*exp(-S/8)`。没有宣称所有频率、CDF、真实 rho 或样本空间构造；也没有把 Gaussian 衰减当作新输入假设。

## 5. 新源全部证明步骤与 proof let 覆盖

L50 引入四个声明 let，它们是定义性展开，不是新假设。L51–53 使用合格 DY210，传入完整原 hprob/hL2/hmean/hcov 和真实 3/4/5 矩前提，得到 `CD,dD,hCD,hdD,hdD1,hD`。L54–55 使用合格 EB213，传入同一 law 及原真实 3/4 矩条件，得到 `CE,dE,hCE,hdE,hdE1,hE`。两处都在所有 n/i/u/v 引入之前选出统一常数和半径。

用于三角拼接的中间量在两依赖中都是

`Qn = -S/2 - I*m3/(6*sqrt(n)) + (m4-3*S²)/(24*n)`。

DY210 冻结 L25–31/实际 TYPE L21–24 直接写出真实积分；EB213 冻结 L24–27/实际 TYPE L9–11 用其字面 m3/m4。将这两个声明 let 展开后，与新源 L67–69 的 proof let Qn 完全相同，复数强制转换和分母位置亦相同；EB 的 Pn 则与新声明 L36–40 相同。因而 L85 的 `add_le_add hDuv.2 hEuv` 没有利用未经证明的同律/coherence 等式，只有这些定义的约化。

L56–57 明确取 `C=CD+CE`、`delta=min dD dE`。`add_pos hCD hCE` 保证 C>0；`lt_min hdD hdE` 保证共同半径>0；`min_le_left` 与 hdD1 传递给 delta≤1。dE≤1 虽可用但不是必需，未因此少证任何目标。

L58–62 才引入任意 n、hn:1≤n、i、u、v 和局部频率条件。由 `sqrt(n)≥0`，分别把 `min dD dE≤dD/dE` 右乘 sqrt(n)，再与 huv 传递，正确得到 DY 和 EB 各自的频率条件。不要求 u/v 非零，半径边界用≤而非严格不等号，未缩小范围。L63 直接保留 hDuv.1 的真正 CF 模界，无需把指数 Qn 的模界冒充 CF 模界。

L64–69 的全部四个 proof let 均已阅读：`r=sqrt(S)`；`s=sqrt(n)`；`G=Real.exp(-S/8)`；Qn 如上。它们仅给同一表达式起局部名字，无独立所有者或隐藏前提。L70 的 hn0 由自然数 `0<1≤n` 经实数强制转换获得 `0<(n:ℝ)`；L71 得 hs:0<s；L72 得 hden:0<(n:ℝ)*s；L73 得 hr:0≤r。故在 n≥1 的全部结论区域中除法分母确为正，n=0 并未被错误消去后重新纳入结论。

L74–77 的 hpoly 恰是

`CD*r^5 + CE*(r^7+r^8+r^9) ≤ (CD+CE)*(r^5+r^7+r^8+r^9)`。

右减左等于 `CD*(r^7+r^8+r^9)+CE*r^5`。由 hCD/hCE 的正性及 hr，每一项非负；源码 nlinarith 的两个显式乘积非负事实正好证明此差，没有需要 r≤1 或 n 无穷大的隐含前提。高频接近局部半径时 r 可大，这个非负项比较仍成立。

L78–80 先用环等式把目标差写为 `(Phi^n-exp Qn)+(exp Qn-Pn)`；复数加减中间项严格相消。这里采用差分显式求和，修复失败01的调用问题，且不改变任何 statement。L81–82 用 `norm_add_le` 给出正确方向的三角不等式。

L83–85 按上述同一 Qn、同一 Pn、同一 r/s/G，分别代入 hDuv.2 与 hEuv，取得 `CD*r^5/(n*s)*G + CE*(r7+r8+r9)/(n*s)*G`。没有乘丢 exp 因子、颠倒差分，或把 CE 的 r7+r8+r9 再乘一项 r5。

L86 通过环等式将同分母同 G 的两项合并。L87–88 用 hpoly 除以非负的 n*s，再乘非负（实际严格正）的 `exp(-S/8)`，不等式方向正确；分母仍为 `n*sqrt(n)`，没有变成 n、n² 或不同样本量。L89 的 rfl 仅展开 r/s/G，恢复 L47–49 的冻结目标。这一段覆盖了全部新 proof let、全部局部 have 和全部 calc 步骤。

边界核对：n=1 时 s和分母仍正，未使用渐近的 n≥N；u=v=0 时真实三四阶投影矩为0、Phi(0)=1（概率性）且 Pn=1，结论与两个合格输入的零误差一致；坐标轴及正负频率均含在欧氏半径条件中。证明本身无选择频率符号、有限指标枚举、数值实验或未处理的边界分支。

## 6. 实际 TYPE、let/VALUE 及全 owner 递归公理覆盖

实际输出 L1 唯一 owner 是 `Shao.OQ3.uniform_standardized_pair_edgeworth_polynomial_error`。L2–14 的全部 binder、概率/L2/均值/covariance/真实径向积分假设，与新源 L9–28 和冻结头一致。L15–22 明确包含四个字面 statement let 值 Phi/m3/m4/Pn：没有省略值的缩写、自由 coefficients、隐藏 typeclass/instance 参数或目标替换。L23–37 的常数先行、n≥1、全部 i/u/v、闭局部半径、CF 模界和加权多项式余项同 L41–49 逐项一致。全文已读，不只审查了 declaration 名字或头部摘要。

`u22ec-Audit.lean` L23–27 遍历整个 env.constants，以 `env.getModuleIdxFor?` 得到实际定义模块的方式选 owner，没有用命名空间前缀过滤 private/generated 名字；因此不会漏掉命名空间外或生成所有者。L28 拒绝任何新项目 axiom；L29–32 对每个实际 owner 调用 `Lean.collectAxioms`，拒绝白名单以外全部递归公理；L33 打印实际 type；L35–37 对 defnInfo 打印完整 value；L41–46 检查非空及冻结目标计数并报告总量。

当前实际计数由输出/receipt/audit-record 交叉一致：1 DECL、1 TYPE、1 theorem、0 非 theorem VALUE，0 另有 private/generated owner；该“0”来自完整模块 owner 枚举结果，不是只数公开源码行。四个声明 let 与四个 proof let 都已在前两节完整人工阅读；它们是定理内部绑定，不需要或虚构额外环境 VALUE 记录。

实际 TYPE L38 的递归公理完整为 `[propext, Classical.choice, Quot.sound]`，L39 为 `KIND theorem`。它们全部在标准白名单内；无 sorryAx、新 axiom、unsafe 或 native_decide 路径。没有从“依赖各自已通过”推断新模块免审，而是核对了当前1个实际 owner 的完整递归公理；旧依赖的精确已合格源/O/独审/AX 则按规则复用。

## 7. 裁决与释放

EC214 的当前92LF精确源在冻结前提下证明了完整冻结公共声明，source-to-statement/全部证明/实际 TYPE/声明及 proof let/0 required VALUE/全实际 owner 递归 AX 覆盖完整，合格首次原对象证据对齐。裁决 `CORRECT`，没有需要作者修改命题或证明的关键缺口。

本裁决不扩大 EC214 scope：只接受同一真实标准化概率族的局部二阶 CF 多项式与真实 CF 模界；原 order-six Edgeworth、全频/反演/CGF 导数、原 B/D、SAME single E/真实 rho 消费者继续 OPEN，严格 beta 界、p54 和既有外部归属保持。

审查完成后本实例停止并释放 `drafts/oq3/u22ec-proof-review.md` 的唯一写权；不继续证明、检查、发布或派生工作。报告之外的文件写权始终未持有。
