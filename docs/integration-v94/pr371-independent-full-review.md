# PR371 独立完整终审

STATUS: CORRECT

JUSTIFICATION: 精确源码忠实实现了原文中实际 early rare 与 early omitted 的有限范围概率支付。证明对同一真实 raw 人口、同一独立均匀标签排列、同一实际 `nu=energyCutoff(h0)` 和 `tau=min(energyCutoff(H),n-m)` 工作；两个实际账真正可测、可积，并分别得到声明中的相对高斯尾界及遗漏项的 `C beta sqrt(H)/n` 界。完整源证明、三个冻结声明、全部 39 个实际展开类型、全部 3 个实际非定理值、真实 module-owner 选择逻辑及全部递归公理证据均已核查，没有发现关键缺口。复用的原 whole016 内核与同一原对象上的一次 owned audit 均为 RC0；本审查没有新 Lean/AX 调用。

## 1. 精确对象与独立性

本报告只认证新增模块 `Shao.Probability.SourceEarlyRetainedProbability`，PR [371](https://github.com/randomcat4/shao-lean/pull/371)，head `7f8f76e694072e22adefc768137d17ed5e7e0bb2`，tree `784c2302a0b6654da2db738e12eb954d18dccfa9`，Git blob `c987054010143052e5c374752ebb141e42cee1b3`。唯一生产源为 1153 行、67191 字节、UTF-8 无 BOM/LF，SHA256 `2aa6c4e9f338e068109a76c84e95bd4c2f75b6b3ee6d7afa483a85ca120d8066`。

审查者是新的独立上下文 `/root/early_retained_probability_final_review`；未参与作者实现或声明修订，作者在审查前已完整 source/execution RELEASE0。使用 math-theorem，未使用 math-ultra，未新增子上下文。写入限于本审查目录，未改作者生产源、封存证据、共享实现、协调、缓存或任何旧证明。配置要求为 `gpt-6.1-sol/xhigh`；平台实际模型/effort 遥测及 input、cached input、output、reasoning subset 用量均不可获得，记录为 null，不推断订阅比例。

读取方法是直接逐块完整阅读生产源 1–1153 行、原 actual audit 1–2622 行；没有抽样、前缀筛选、结构摘要或省略重复子表达式的替代阅读。全部 theorem 证明在生产源码中完整读完；依据工作区 Mechanical audit output boundary，没有要求重新展开 tactic 生成的 theorem proof terms。三项非定理完整 VALUE 均逐项阅读。`coverage.json` 给每个实际 owner 的原 TYPE/VALUE 精确区间和文本散列。

## 2. 原文范围与冻结忠实性

直接读取原文 `C:/game/shao/current/c12/main.tex` 1261–1410，覆盖必读 1305–1318、1356–1364；读取 `supplement.tex` 4978–5077，覆盖必读 4978–5044、5046–5076。两份原文散列分别为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`、`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。

源声明保持以下精确数学含义：固定 `K=2^64`；对真实概率测度 rho，显式 AE 有界支持 `|z|<=Bcap`、中心 0、二阶矩 1；`n>0,x>=16`；beta 是实际第三绝对矩，delta=beta/sqrt(n)，u=delta(1+x)^3，输入 `u<=exp(-3x^2)`。这是原 bounded auxiliary regime 上的承重单元；原文更强的支持小量条件在这两个早支中不需要，删除它使本单元更强，而非把有限第三矩暗加到一般原 root。

public 源头在 579–633 行，17 个字面 lets；private cubic 在 27–49 行，5 lets；private low-grid V2 在 332–360 行，8 lets。三个完整头与 Root 对应 freeze 逐字一致，总计 30 lets。public V2 相对最初 public freeze 仅增加 `Elab.async false` 与 `maxHeartbeats 5000000` 两行上下文选项，数学头未变。private2 的 V2 明确固定 c、CF、CS 在 rho 之前；`hc` 只是固定数 `(1-exp(-2))/8` 的正性，由 public proof 第 637 行证明，不是新 law 假设。原 private2 中未指定存在常数的旧形式已被 Root 在实现前明确修订，未发生作者悄改前提。

L 使用真实 `eventCompletionKernel J Q` 和三个实际导数，停止参数始终是 nu。earlyRare 的 guard 是 `r<=n/2`、`r<nu`、所有 `k<=r` 的同一路径严格双墙 prehit、`|remainingSum|>(3x/2)sqrt(T)`，账是 `|Linterval-Lupper-Llower|`。earlyOmitted 的 guard 是 `r<=n/2`、`tau<=r<nu`，账是三个 `|L|` 加实际 interval separated overshoot 的负部 `max(-O,0)`。它没有另加共同 prehit 指标，没有把 L 的 nu 改成 tau 以置零遗漏账。最终结论保留两个账的可测/Integrable、earlyRare 的 `C delta Psi(x)`、earlyOmitted 的 `C beta sqrt(H)/n` 与 `C delta Psi(x)` 三个界。

源文件顶端“Mathematics-only / No formal body”是候选遗留注释，与最终实际 body/收据不同步。它不改变声明或证明，不能据此否认真实完成的 formal body，也不应为清理注释重写已合格字节。

## 3. 真实局部余项的粗三次控制

private1 的完整证明（50–329）固定同一个实际 a/sigma/r，令 w=x sqrt(energy a)、y 为真实已揭示前缀、T 为真实剩余能量、z 为总和、b=a(sigma r)。`r<nu<=energyCutoff(H)` 与 H>0 给 T>=H>0。`remaining_population_geometry` 给 b²<=T；`actual_reveal_zero_future_reachable` 给 `T-b²=0 -> y+b=z`。这两个条件来自真实有限人口，并未作为新的 public 前提。

按每个 domain 的 `sourceAlive` 分支工作。若不 alive，该域 source L/O 定义为零；若 alive，则 raw energy>0，w>0，当前 y 与 endpoint z 严格在该域内。upper/lower 由同一个 hB 得实际 Brownian 反射公式，构造实际 derivative identification，并把 `completionExt`、local remainder 和 retained projection 展开为已合格 `actual_upper/lower_retained_bound` 的相同值。wall envelope 指数非正，每个半线得到 `8000100 G`，其中 `G=(|b|/sqrt(T))^3(1+|z-y|/sqrt(T))^3`。

interval 使用 actual spatial derivative theorem 得实际 regularity；并非把未证 image/regularity 合同放进 public 输入。展开 projection 的小步不撞墙、上墙、下墙及大步分支，`localRetainedRemainder` 与 qualified interval `retainedRemainder` 逐点相同。负部分支也逐点相同：下墙 `lowerOvershoot` 的三个负号经 ring 化简得到 source 的 `-(b-p)(1-(b+p)(z-y)/T)Gderiv`，不是把概率事件包含关系直接求导。未撞墙时 p=b 因而 O=0；大步 O=0；闭撞墙等号落在投影分支。两个 wall envelope 之和<=2，所以 interval 的 `|L|+max(-O,0)` <= `2(2CP+40)G`。

因此 C0=`2(2CP+40)+2*8000100` 同时支付三域绝对值和 interval 负部。公开 rare 差值随后由三角不等式放大。未来零能量只在大步 b 的真实可达状态使用 y+b=z；小步投影的未来时间>=T/2>0。当前 T=0 不进入局部除法/导数论证。严格 current/endpoint wall 与闭 crossing equality 均按实际 source 定义处理，不需无原子假设。

## 4. 低能量 private grid 与普适常数

private2 的完整证明（361–576）在任何概率参数前选固定 c=(1-exp(-2))/8>0、CF 为 qualified finite-cutoff producer 在真实实数参数 `(a,q)=(3,3)` 的见证、CS 为 qualified scalar Gaussian budget 在 c/4 的见证。public proof 的 C0、CQ(p=3)、CF、CS、Cearly、Clow 和最终 C 同样在 B/PB/rho/Bcap/n/x 前选择。最终 C 的普适性没有依赖 law 或目标积分。

实际 h2、h3 由 AE 有界支持与常函数 Bcap²、Bcap³ 支配得到（671–680），并非利用不可积积分约定。旧第三矩截断定理给 beta>=1、h0=4beta²>0、`E[X²;X²<=h0]>=1/2`。所以旧 finite-cutoff producer 的 gamma 精确为 -c。

对每个 `t in Icc((n+1)/2,n)`，先证 t>0、n<=4(t-1)，再写 t=m'+1。其 first coordinate 标记仍是该真实后缀的坐标 0。正能量支中 `1/sqrt(T)^3=Real.rpow T (-3/2)`，`rpow(...,3)` 与三次整数幂相同。以 b=h0、同一 H、m'=t-1 调用旧 producer，获得真正 Integrable(low) 和核界

`E low_t <= CF int_(0,1/h0) s^(1/2) a3(s/2) exp(-c(s+1/H)(t-1)) ds`。

由 t-1>=n/4，核指数逐点受 `exp(-cn/(4H))*exp(-(c/4)ns)` 控制。非负核积分可从 Ioo 扩到 Ioi；有限项数<=n，CS 的真实 scalar budget 给 n 倍积分<=CS R0。对真实归一化 map law 使用 `truncationF(z)<=|z|^3`，且先证明两个被积函数可积，从而 `R0<=beta/sqrt(n)`。这里归一化 law 只用来搬运上界，未替换实际 source nu/tau。

于是网格和<=CF CS (beta/sqrt(n)) exp(-cn/(4H))。令 v=n/H>0，利用 sqrt(v)<=1+v、exp(av)>=av、a=c/4，得 `sqrt(v)exp(-av)<=1+4/c`，从而精确为 `(CF CS (1+4/c)) beta sqrt(H)/n`。h0=H 时 low 事件为空仍合法；全部 rpow/除法推理在 T>0 支中执行。没有循环消费目标 grid、额外高矩或未证 inverse master。

## 5. 合法重排、后缀律与删指标顺序

公开证明 875–920 用真实 pi 坐标 X_i(a)=a_i 的可测性、独立性和同 rho law，调用已合格 `iid_randomPermutation_map_eq_pi`，得到实际 `reorder(a,sigma)` 在 `revealLaw(P)=P.prod(uniformPermutationLaw n)` 下具有 P 律。`uniformPermutationLaw` 是 finite label permutations 上的规范化计数测度，重复数值保留不同标签。

固定 r 的 head/tail 通过 `piCongrLeft` 与 `sumPiEquivProdPi` 得真实产品 pushforward，tail 的边缘律是 Pt(n-r)。`gaussian_weight_source_state` 的有限和恒等式给 tail energy=T、tail sum=d、tail firstCube=|b|³。没有断言实际随机 cutoff 后仍为条件 iid，没有把路径最大值当作逐点排列不变，也没有因子化任意 prefix mask。

993–1044 先用逐点非负粗三次界，再删除多余 prehit/endpoint 等选择指标。余下 rareW 或 lowW 此时才仅依赖完整真实后缀，故可用上述无条件 pushforward。`r -> n-r` 与 early `r<=floor(n/2)` 的精确双射对应 `Icc((n+1)/2,n)`；r=0 对应 t=n，偶数中点恰计一次，奇数下界是 ceil(n/2)，空后缀不进入这个网格。

对 omitted guard，qualified `omitted_adaptive_cutoff_iff` 给 `h0<=T` 且 `(T<H or n-r<=m)`。PR361 在同一 law/n/x/residual 下给 m>=4、m<=n/4，因而 n>=16；在早秩有 m<n-r，第二支不可能。所以同一个 actual guard 真正推出 `h0<=T<H`，闭 h0 等号保留、H 等号排除。nu/tau 是固定全人口后的 reveal stopping ranks，证明没有把它们替换为 deterministic clock。

## 6. 真正可测、可积与两个相对尾界

741–873 从实际 hB 推出 halfline reflection 与 interval spatial regularity，继而得 F/FY 可测及 `KernelBounds ... 4`。`actual_energy_cutoff_measurable` 给 nu/H-cutoff 的每个 sigma section 可测，min 给 tau。有限前缀交及两个实际 guard 可测；有限离散 LabelPerm 的 top 可测空间允许从逐 sigma 提升到联合可测。

`source_parts_measurable_integrable` 在这些实际 kernel 数据下分别给所有 L^J 与 O^I 的真正 Bochner 可积性；绝对值、负部、有限和及 0/1 guard 保持可积。negative part 用 `max(-O,0)<=|O|` 的实际范数支配。全部 Integrable 在积分单调比较之前已经付出，未让 Lean 对不可积函数的总积分零值代替数学论证。

对于 rare，非零项给严格 `|d|>(3x/2)sqrt(T)`，它包含于旧 PR361(p=3,q=3) 的闭 rare event，非负放大合法。旧 early grid 得 `C0 CQ delta Ax`，Ax=`sqrt(Psi(3x/2))+exp(-x²)`。这里不能声称 Cdelta exp(-x²)。公开证明 1061–1098 用 Mills 上界及 sqrt(2pi)>=1 得 `Psi(3x/2)<=exp(-9x²/8)`，于是 sqrt <= exp(-9x²/16)。x>=16 保证 `9x²/16>=x+x²/2` 和 `x²>=x+x²/2`，两次 qualified exponential-to-tail 给 `Ax<=(16/3)Psi(x)`。最终 rare 界为所声明的 CdeltaPsi。

对于 omitted，逐点 bound、真实 tail law 与 private low grid 得 `Clow beta sqrt(H)/n`。因为 sqrt(H)=sqrt(K) beta(1+x)^3、delta²=beta²/n，精确有 `beta sqrt(H)/n=sqrt(K)delta u`。输入 u<=exp(-3x²) 与同一 exponential-to-tail 给 `beta sqrt(H)/n <=(8/3)sqrt(K)delta Psi(x)`。最终 `C=1+Cearly+Clow(1+(8/3)sqrt(K))` 正且同时支配三项常数，无对目标积分的假设。

## 7. 全部实际 TYPE/VALUE 与递归公理

原审计 driver 是完整读取的 `OwnedAudit.lean`，散列 `93af7fcd593017a12dd301d7f8e460f286dc2366b245c4a318428250b7d20fb4`。它遍历 `env.constants.toList`，对每个名字用 `env.getModuleIdxFor?` 与实际 `env.header.moduleNames` 比较精确模块 owner；不是按 public 名称列表或 namespace/prefix 过滤。publicNames 仅检查唯一公开头确在 owner 集中。每个真实 owner 调 `Lean.collectAxioms` 递归/传递审计，并拒绝三项标准 whitelist 外的 axiom。每个 owner 输出 pp.all ACTUAL_TYPE，所有非 theorem `.defnInfo/.opaqueInfo` 输出完整 VALUE。

原 owned JSON 与原展开日志的 owner 名字精确集合一致：39 actual owners=36 theorem+3 definitions；3 个 source theorem+33 generated theorem。所有 39 TYPE 完整阅读后与相应源头/局部生成义务核对。generated theorem 包括三个 domain match 等式、网格 cardinal/非空/截断减法/reindex arithmetic 的 `_proof_*`、有限集合/命题/非零幂等 `_simp_*`；它们均为源码中的实质推理生成的闭 theorem，没有引入新未证假设。

3 个完整非定理值是本模块 `labelPermMeasurableSpace`、private cubic `.match_1`、`.match_1.splitter`。第一个完整 VALUE 是 n 上的 `MeasurableSpace.top`，不是零个实际定义；源码的 local instance 仅在本模块局部注册，它与 `SourcePermutationReveal` 所用 local top 可测空间定义约化相同。实际公开 TYPE 可见 Measurable 使用新 local top，而 Integrable/revealLaw 使用原模块 top，两者无概率空间偷换。match_1 是 `MonitoredDomain.casesOn`，按 upper/lower/interval 取三个给定分支；splitter 完整 VALUE 直接指向该 matcher。两项 matcher 的 AX 为空；top 的 AX 和所有 theorem AX 均只在 `{propext, Classical.choice, Quot.sound}` 内。没有新增 axiom/sorry/admit/unsafe/native_decide。

## 8. 原成功证据与物理绑定

原 whole016 收据：2026-10-25 08:15:04.289137Z，RC0，124.916933 秒，原 `producer016.olean` 4006592 字节，SHA `26dfb083906f0eacd516c02130c7ef104e621afbc85f8619651893e7449d50d1`；原 kernel log SHA `63409f06a0f414d0d561b20ecc07dc234331b4d7052b2b58c1b7623954569f37`。原成功日志完整在服务器只读到模型上下文，未下载复制到工作区。它含弃用/未用 tactic/style 等诊断和 mathlib 工作区变化提示；收据 RC0，没有 kernel error 或 sorry 认证。保留这些实际诊断，不清理 source 或重跑证明。

同一原对象的唯一 all-owner audit 在 08:15:36.167801Z RC0，6.707722 秒；AX JSON SHA `14492ced7cd1ef411c188b0b9b02371888da24309a83fcbcf17c0dec5e6c3395`，39 TYPE/3 VALUE 原日志 SHA `16546d813377234e9b033d853ef76a3640b6e2c9c019fdfb982b236ccbd865dc`。原命令持有 root-heavy.lock，CPU40–43、native-M8192-j4，与当前资源约束一致。

本审查 08:54:28.768142Z 的只读服务器观察重新哈希了 11 个实际路径。生产源、attempt016.source、Git blob bytes 均为本报告 source SHA；实际 `.lake/build/lib/lean/.../SourceEarlyRetainedProbability.olean` 解析到原 `outputs/.../producer016.olean`，两者散列相同。原日志、收据、driver、AX JSON 全部匹配。Git HEAD/tree/blob 精确一致，原 commit 仅新增一个生产源，工作树仅有预期未追踪 `OwnedAudit.lean`。这直接绑定了“原成功 producer”和“审计实际 import 对象”，不依赖作者文字声称。

本地静态验证另核 151 个文件绑定和 33 个旧依赖源绑定，3 个全头/30 lets、39 名实际 owner 集合、3 VALUE、source 禁用 token、UTF-8/LF 都通过。31 个 accepted-v91 旧源与 immutable receipt source map 相同；另两项 PR361/PR363 按精确 Root qualification/source/original object/独审/RELEASE 散列绑定。95 个旧消费接口及完整 ambient context/实际 source values 已完整读完并对使用前提逐项核对；旧完整 proof/kernel/AX/独审信用按精确 source 复用，未进行旧证明重复终审或新对象遍历。固定 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 未修改。

## 9. 边界攻击与未完成范围

零 raw energy 时 nu=0 或 source guard 关闭；r<nu 强制 T>=h0>0，故当前 T=0 不参与错误除法。reachable future=0 按真实 y+b=z 支付。r=0、奇偶中点、自然数 n-m 截断、T=h0、T=H、wall equality、支持原子与重复值均覆盖。n>0 保留完整量词，旧 residual geometry 实际推出 n>=16；没有向 public 输入暗加大 n。

作者的 Rademacher late-mask-deletion obstruction 检查正确：固定 t 和 x=16，全部真实 suffix 同号原子使删尽 prefix mask 后的 late inverse-cubic 量有不随 n 消失的正均值，而 deltaPsi(16) 随 n 趋零；取 n 足够大仍可满足 residual/support 小量约束。它只证伪错误的中间“late 裸 suffix 可直接支付”界。本 source 仅对 early r<=n/2 删去不需要的 mask，不作该错误推论；obstruction 既非本单元反例，也非完整原目标反例。

CORRECT 限于已声明 early rare/early omitted producer。实际 late rare true-wall-strip/weighted-survival/M/record、late omitted、terminal maximal corridor、one-wall 正 overshoot 返回、after-first-hit/opposite-wall 及原有限 p 矩律回迁均未由本单元完成。PR363 regular 旧账可与本 early rare 账相加，但剩余 late 项不可删除。原 C1 immutable-v85 的旧完成范围保留；C2/C12/OQ56 仍 OPEN，OQ3 仍 PAUSED_BY_USER。本报告不授予 root completion、merge 或额外执行权限，也不主张新的数学新颖性。

审查工件为本目录 `full-review.json`、`coverage.json`、`bindings.json`、`validation.json`；原 source/封存证据均保持原字节。最终 `RELEASE.json` 记录审查者零 in-flight、无 source/execution/cache/shared authority。
