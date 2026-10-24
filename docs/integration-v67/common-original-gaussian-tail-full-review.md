STATUS: CORRECT

独立完整终审结论：精确最终版本 `Shao.Probability.OriginalGaussianTail` 的两个冻结公开命题及其完整证明正确，可供根协调者按本报告接受。本审查由新上下文 `/root/common_original_gaussian_tail_full_review` 执行，非作者，配置为 `gpt-6.1-sol / xhigh`，使用 math-theorem，未使用 math-ultra、子代理或任何新的 Lean、构建、所有权审计命令。作者已经释放写权；我未修改最终源、冻结候选、旧报告或生产对象。

有一项已由本报告补齐的记账更正：作者 `source-declaration-index.json` 的 40 项索引漏了最终源第 143 行的 `· letI : IsProbabilityMeasure (cond P A) := cond_isProbabilityMeasure hA`。最终源实际有 **41 处 let/letI：36 处证明局部，5 处陈述局部**；后者为第 372–375 行和第 481 行。这里不是数学修复：我完整读了该实例的字面值、正纤维分支和用途，覆盖表新增这条记录并保留全部原索引 40 项。作者旧证据保持原字节；根接受记录应使用这个更正后的分母，无需改源或重跑内核。

**精确对象与冻结。** 最终源 35,272 字节、640 行，UTF-8 无 BOM、LF、无 CR，SHA256 `f6b3df97e75be79ffcad5d0cb0cd9479e919dabad096796a16d3e54e1576a583`。同次 `check008 -o` 原对象 SHA256 `ddf6815a43d250a2d4f8cd6ebd9afcf40ce5faf40977504086a279ab87c2a337`。分支 `feat/common-original-gaussian-tail`，head `335ec95d164d1e1841716bade84c7e8547521764`，tree `fe234520ecb52ccf6526c63b0b1a72c2659c012e`，parent `d32ac06685132eeae5534cf3603ac5bcc6bc73a5`。服务器原生只读核对确认 HEAD blob、当前工作源、`check008.lean` 与本地已读源逐字一致；提交仅新增此一源文件，其余三个无关未跟踪文件未提交。没有推送、PR 或合并。

完整读了根声明冻结、两个公开完整头、七个私有完整头和数学候选，并独立作空白归一化比较，全部九个源头与各自冻结一致。绑定为：根冻结 `293e8e37ffff1c684fb0fe171ebddd70e7f3b7281bc1dd738bbcf780c6543068`，公开候选 `8b03d88660561cc0cc584760733f96ed859a9fe62a25916ab03b20e14328d0d9`，私有头冻结 `871db00da88d1fef9fa939ff0e1994b1c2f870654bc3a1f57ab199cde632ae4d`，完整数学候选 `0b1daf94923037f9c1eb2f7257b42fbcdf872614f529501deae45247f655fc5e`；作者 handoff.json `fb62e1b759cf0144928272f058dbbcfd8d1a18efc16aef85ed6fdf2797533497`，handoff.md `5095aef8b250ef593186ca3fb9e3994a3f796f25d1825e82a5707edbaa7ef48c`。候选错误的 `Shao.Probability.TruncationBudget` 导入依根的事前授权，改由真实 `Shao.Basic.TruncationBudget` 经 RetainedSample/Deletion 闭包提供；候选字节和两公开类型均未改。

**源到陈述的忠实性。** 已读原文 main.tex 第 150–166、301–349、424–539 行，supplement.tex 第 73–295、1201–1387 行；两个原文哈希分别为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06` 和 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。只审此两条粗尾/标记尾接口，不把原文对完整相对误差的其他前提或外部结果归入已证明范围。

两公开头中的 C 均在 nu、n、t、h、s 前统一选定。原律只要求实际概率测度、有限二阶矩、原均值零、n 倍原二阶矩为 1；t>0、t⁶≤n、n∫F(tz)≤1。F 是真实 `z² min(|z|,1)`，不是新增占位函数。有限二阶矩保证所有实际使用的 F 积分可积；无需原律全局三阶矩或指数矩。`energy` 为真实平方和，`upperMax` 为时间 1 至 n 的正长度前缀最大值，`upperCrossing` 为乘法弱事件 t√Q≤M，保留 Q=0 和等号。标记头为真实 `upperMax (s • a)` 与存在坐标 `h<|a i|` 的同时事件，s=±1，h>0；未替换为末项、绝对最大值或独立发生的标记概率。

完整读取了所消费旧公共接口的类型、定义及所在作用域，包括 Path/prefixSum/energy/upperMax/upperCrossing、retentionSet/retainedIndex/retainedPath、闭截断集合/质量/真实 cond 律、条件 iid、样本乘积 map、全部 retainedSample 守卫、D=2 bounded 随机分母界、删除墙与 Gaussian tail/Mills 接口。其已合格旧证明、内核及公理证据复用；未重新完整审 BoundedGaussianTail 的旧证明。

**九个新源证明逐项结论。**

| 源声明 | 完整源行 | 独立核对 |
|---|---:|---|
| ogt_fiber_mass | 24–40 | 真实固定保留集纤维等于混合坐标矩形；有限乘积给 p^card q^(n-card)，零质量和空集合均在公式内。 |
| ogt_binomial_weight | 42–57 | 对全部真实有限保留集的有限乘积展开等于 (p+exp(l)q)^n；指数只作用于坏点数。 |
| ogt_binomial_weight_le | 59–80 | 可测 B 得 p+q=1，l≥0 得 exp(l)-1≥0，nq≤1 和 1+v≤exp(v) 给实际 Bernoulli 指数权重界。 |
| ogt_retained_fiber | 82–180 | 常数从 D=2 bounded 公共头取得。j=n-card、y=√(t²-j)、eta=真实闭截断 cond 律；所有支持、原二阶时钟、通常非零条件均值和条件三阶守卫逐一成立。 |
| ogt_exp_tail | 182–206 | Mills 下界和 1+t≤2exp(t²/2)，乘除因子均为正，给所有 t≥0 的 exp(-t²)≤2√(2π)T(t)。 |
| original_coarse_gaussian_upper | 208–322 | C0 的三个加项为有限正常数；t<8 用概率≤1与尾单调性。t≥8 对全部纤维覆盖，j≤t²/2 用 retained 界，其余用 exp(-t²)exp(2j)≥1；两真实有限指数权重合并。 |
| ogt_mark_retained_factor | 324–362 | i∉s 使单坐标组与 s 坐标组独立；有序注入保留其独立共同原律；两个真实可测原像交事件的质量恰为乘积。 |
| ogt_rescaled_law | 364–469 | 实际 rho=map(z↦s·c·z)nu，m=n-1、y=√(t²-1)、c=√(n/m)。证明概率、有限二阶、均值零、m 原二阶=1、y>0、y⁶≤m、m∫F(yz)≤1 七项，未假设变换后守卫。 |
| original_marked_crossing_gaussian_upper | 471–638 | t<2 用逐标记坐标联合界，覆盖 n=1；t≥2 用真实有序删去该坐标，保留 signed 路径，再正 c 缩放，通过 rho 产品 map 使用粗尾界，最后单坐标独立因子与 T(y)≤3exp(1/2)T(t) 合并。 |

retained 证明的承重点不是形式上的“条件化”命名：在第 138–143 行先分 P(A)=0。零纤维交事件质量严格为零，不使用空条件测度；正纤维明确建立 `cond P A` 为概率测度，并由固定纤维条件 iid 和 `iid_samplePath_map_eq_pi` 得到 Y 的真实 eta 产品律。删除集是 s 的补集，基数 j、s 的实际顺序和正长度全部传入已验收 Cauchy–Schwarz 删除墙。Qret=0 的弱事件由该接口完整覆盖，源未增加正能量分支假设。

缩放证明中 t≥2 得 n≥64、m>0、c>0、y>0；t²≤n 推出 cy≤t，(t²-1)³≤t⁶-1≤n-1 推出 y⁶≤m。|s|=1 与 F 的绝对值单调性逐点给 F(y·s·c·z)≤F(tz)，且两边及推前后的 F 均有真实可积性证明，m≤n 与 F≥0 才传递预算。均值保持只使用原均值零，二阶恢复只用 s²=1、c²=n/m。标记因子发生在原产品律和固定互不重叠的坐标组上，未在穿越条件后假称独立。s=-1 的处理为真实推前和路径乘法，不要求原律对称；原子、闭截断边界和所有零能量样本始终保留。

**原生所有权、完整类型与公理。** 已完整读取最终源全部 640 行、九个证明、全部 33 个实际模块自有完整类型，以及覆盖表中所有 41 个完整局部字面值。33 项为 2 个公开源定理、7 个私有源定理及 24 个生成定理；实际全局、私有、生成定义和非定理值均为 0。所有完整类型直接读字面原生 pretty-print，没有因子化或真正省略；`...`、`⋯`、`…` 均为 0。24 个生成类型包括有限集/原像/交并成员的 simp 等式、非零幂的 simp 等式和由 n≥64、n≥2 等推出保留长度正性的反证式算术定理；没有无条件 False 或隐藏数学前提。

每条原生 `collectAxioms` 结果均完整核对，只包含 `propext`、`Classical.choice`、`Quot.sound` 的子集。最终 actual-owned-types.json、所有权 JSON 和 audit002.log 的 owner 名集、kind、完整类型和逐项公理完全对应。原生审计以 `env.getModuleIdxFor?` 选整个目标模块，未限于公开名；脚本对非白名单公理报错并强制零定义。无 sorry/admit/新增 axiom/unsafe/native_decide。

**服务器检查与版本史。** 本轮只读消费已有原生文件，不运行编译或审计。check007.log、check008.log 和四个直接退出码全文读；audit.log/audit002.log 的全部原生字节经无损解析消费，完整类型块与上面已全文读的字面类型逐字比较，再读取全部未替换余文；逆构精确还原原日志。旧版新增 matcher 的完整类型及定义值也单独全文读。没有仅凭摘要或计数放行。

| 版本 | 源 SHA256 | 同次原对象 SHA256 | 真实结果 |
|---|---|---|---|
| 007 | 3b658b779ec4782cda2fd51af256f248ac15d78b6ddbd0beb9d7876832ca6118 | 8bbf4b4051b2590aa5ebcdaaef318811e157e818fdf2c912e01e2963f2867d65 | 两公开头整源内核 rc=0；随后 owner 枚举 34 常量=33 定理+1 定义，审计 rc=1。 |
| 008 | f6b3df97e75be79ffcad5d0cb0cd9479e919dabad096796a16d3e54e1576a583 | ddf6815a43d250a2d4f8cd6ebd9afcf40ce5faf40977504086a279ab87c2a337 | 最终零定义版本首次整源内核 rc=0；audit002 首次对此精确源 owner 枚举 33 定理、0 定义、rc=0。 |

007 的失败为 `original_coarse_gaussian_upper.match_3` 这个由模式 lambda 生成的逻辑匹配器违反既有零定义冻结；不是数学内核拒绝。实际两源差异仅是最终第 279–283 行将 `fun ⟨_, _, ha⟩ => ha` 的集合覆盖证明改成 `constructor/rintro` 逻辑消去。两公开头和数学假设完全未变；原 007 源、对象、完整 type/value、失败日志和 rc 均保留。这里是必要的 changed-source 校验，不能称同源重跑，也不能称“内核从未通过后改源”。007/008 总计两次实际 owner 枚举；最终精确源只有一次 owner 审计，通过后生产重跑 0、同源成功重跑 0、依赖生产者重编译 0。

最终 kernel 使用记录的固定 Lean `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，root-heavy.lock、CPU10–13、`-M8192 -j4 -DautoImplicit=false`，`Elab.async=false`。原生 check 日志只有既有 mathlib 工作树提示和样式 linter，没有错误。check008.log SHA256 `627ea16ee0b60674e2028c619fcd16c4f9c25f35bc726f9741a9a0ea992c2d82`，audit002.log `c1d7c3744c5fe80d05fd69f532a2e76a7d913468e46bece1e49905f11da05ed1`；旧 check007.log `b4b0f5de228de995a9389b460f48e9c772157b5b309631d7838faeaab6ff009f`，旧 audit.log `73c09385cae0cdf89b8412c9b883e67e14d283ef4c65bae387b6bca7add6f82e`。直接 rc 文件 0 的 SHA256 为 `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa`，旧失败审计 rc=1 的为 `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865`。

**依赖复用。** BoundedGaussianTail 已在 v66 合格，根资格 JSON SHA256 `ffb08b751f2afb91bafb364cdf5dce01a1a2a96c668905fed24d4053ca461cc3`，其源 `876559b2921ffe0e23c8c3a2c55d00c458985ace6036de4b8bc7f6a6aa24f4bd`、原对象 `8b618278b77c7dd6dc43be42a207aebd18f6a5fb3092ab9fe217e1bdd736d098` 均原样复用。21 个 audit-view008 项是 20 个旧依赖原对象和本单元原对象的符号链接；服务器逐行核对源哈希、原对象哈希、真实路径、符号链接目标全部一致，20 个旧项在 007 与 008 间同源同对象，本地 curated library 的相应 20 源亦相同。没有对象复制、共享缓存写入、依赖生产或旧公理审计回放。原始完整日志和二进制继续仅留服务器。

覆盖表：`coordination/common-original-gaussian-tail-full-review-coverage.json`，SHA256 **3d1b272ef86a613895ba5168c4f3ddd4c2797290d85403fe52484ddff9b074fa**，逐项含 33 完整 actual type、其原生公理、源证明位置/生成类型解释和全部 41 个完整局部声明。只读原生绑定收据：`drafts/c12-original-gaussian-tail-review/native-readonly-verification.json`，SHA256 **a4cc1d09c279565d20c62bd80f8dcb7f4ee54bdb8a3b4f6724c0626386bebe85**。记录中有一次只读日志解析脚本字符串转义错误，尚未读取或写入远端文件，修正后完成解析；这不是 Lean/审计运行，也没有重放任何生产命令。

**接受边界与释放。** 此审查只资格化原有限二阶律的 coarse Gaussian upper 与真实带标记单删点 Gaussian upper。它不证明原固定 x 的 strict CDF pullback、原端点相对误差及 Shao–Zhou2016 外部归属、同 cutoff bounded/growing 公共见证、PB、END、full-y、D2、加权收缩或 C1/C2/其他原始根组；它们继续 OPEN。下一依赖是根接受本精确版本后进行原 fixed-x conditioning/CDF pullback 的真实消费者，不能把本报告当作持续运行机制。

本审查写权在报告落盘后释放，无在途工具、Lean 或审计操作；最终只读进程观察未发现本单元 Lean 进程。平台未暴露本代理输入、缓存输入、输出及推理子集计数，均记录为 `not_exposed_by_platform`，没有 null、订阅百分比或额度估算。
