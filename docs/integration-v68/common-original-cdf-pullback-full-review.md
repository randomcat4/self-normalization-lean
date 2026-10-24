# OriginalCDFPullback 新鲜独立完整审查

STATUS: **CORRECT**。

审查人 `/root/common_original_cdf_pullback_full_review`，实际配置 `gpt-6.1-sol / xhigh / fresh`，与作者 `/root/common_original_cdf_pullback_author` 独立。使用 math-theorem，未使用 math-ultra。作者已经释放源与执行权；本审查只读服务器，未运行 Lean、构建或审计，未改生产源、冻结、旧证据或别名，未 push、建 PR 或 merge。这里给出独立审查结论，根资格与整合仍由 root 决定。

## 精确版本与完整覆盖

- 模块：`Shao.Probability.OriginalCDFPullback`；工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/common-scalar-fourier-v44`；分支 `feat/common-original-cdf-pullback`。
- HEAD：`d3a5258b3af6845be3b623fc6e059c7b0d8e09c7`；树 `b931b61dda627448d82bce32cbc8ac5517389930`；父提交 `335ec95d164d1e1841716bade84c7e8547521764`。
- 唯一提交变更为 `Shao/Probability/OriginalCDFPullback.lean`。四个原有未跟踪依赖源保留，其精确字节属于合格依赖映射。
- 本地新源、服务器当前新源、HEAD blob、`check005.lean` 均为 SHA256 `e8d7c5c67118f31dfb05bbb47313326e0c8a1815fcaeb1db91f5869ab582a1e7`；440 行全部读完，UTF-8 无 BOM、LF。禁止项 `sorry/admit/axiom/unsafe/native_decide` 搜索为零。
- 三个完整公开头与冻结候选逐字相等（仅去掉头块外层空白）：第49行 `sourceTruncation_original_two_signs_bad_crossing`，第195行 `endpoint_cdf_exact_zero_energy_identity`，第253行 `sourceTruncation_original_max_cdf_pullback`。两个完整私有头与实现前的 `private-head-freeze.md` 逐字匹配。
- 完整阅读全部5个源证明（3公开、2私有），以及全部43个局部绑定的完整字面值：20个声明内绑定，23个证明内绑定；普通 `let` 40个、`letI` 3个。多行集合、函数、真实条件律、概率实例都按实际源读取，没有只读别名名目。
- 完整头文本、全部43个局部字面值、逐证明范围、原生类型逐项索引与哈希均保存在 [coverage](<C:/game/shao lean/coordination/common-original-cdf-pullback-full-review-coverage.json>)。该文件是精确覆盖表，不替代本次实际完整阅读。

冻结文件 SHA256 `61b130f91e829ca0bd84d7f1f52515bb9be5de6d68265157dd08a249897a254c`；完整候选头 SHA256 `eac6e2abaf71d83e0ee1c93f6b3b7bffebc8661a6642f927cddb1cb567f334d9`；完整数学证明候选 SHA256 `8eb5c581aa350103b4f0a54d3781f86296b15c8ed3dfcd6fa3eb3897f67507aa`。这些材料完整读过。

## 逐项数学裁决

**原文与范围。** 完整阅读只读原文 `C:/game/shao/current/c12/main.tex` 的149–200、300–312、420–535、762–860及1530–1565行。原文使用实际最终平方和、弱乘法穿越、严格补事件、固定 x 的闭截断条件律和非正参数零延拓。新头使用归一化原律 `nu` 的有限二阶矩、均值零、`n E_nu z²=1`，正是原增量除以 `sigma sqrt n` 后的范围；没有要求原律第三矩或指数矩，没有把高阶矩域或全根结论附加进来。条件律 `rho` 的均值可以非零，证明从未把它中心化或假定为零。`N` 在所有邻近 u 变化时保持同一个 x 截断，闭边界 `|v_j|<=epsilon/(1+x)` 原样保留。

**私有 `ocp_strict_compl`（19–38）。** 对 u>0，正能量时墙严格为正，`max(0,upperMax)<wall` 等价于 `upperMax<wall`。反方向若能量不是正数，非负性给能量零，已有逐路径零能量接口使弱上穿越成立，与补事件矛盾。故这是包含零能量和墙上原子的精确集合等式，没有假定零能量零概率。

**私有 `ocp_strict_nonpos`（40–47）。** u<=0 时墙非正而 `maxWithZero>=0`，严格事件为空。该结论不需 n>0 或概率假设。

**双号坏穿越（49–193）。** 在任何律、n、x、epsilon、u之前选取合格标记生产者的 `Cm>0`，再取 `C=3 Cm exp(2)`。epsilon<=1/800推出 `epsilon³/8<=1/16`；样本量下界与 `0<u<=1+x` 给 `u^6<=n`。实际径向截断函数单调性和有限二阶可积性给 `n E F(u z)<=R_n(x)<=1`。这些正是原律标记生产者的全部输入，均已在使用点支付。

标记的存在式 `exists i, h<|v_i|` 与闭截断补集逐字等价。原律尾预算给 `n nu{|z|>h}<=R/epsilon³`，完整邻域尾比较给 `Psi(u)<=exp(2)Psi(x)`，所以每个符号的坏穿越先有 `Cm exp(2) w/epsilon³`。最终时间 n 确实在1至n的监测中；端点绝对值弱穿越包含于正负两个最大值弱穿越的并集，能量零时该包含也成立。并集界支付两份，正号最大值再加一份，故完整三项输出都由同一个 `3 Cm exp(2)` 支付。未假定标记与端点独立，也未输入目标 PB 费用。

**任意律端点恒等式（195–251）。** 对任意概率 P、任意 n及t>0，严格正能量端点事件等于两个弱尾并集的补集；两个弱尾的交集恰为 `{Q=0}`。正能量时正墙排除双尾同时成立；零能量时所有坐标与最终和都为零，两个弱尾均成立。可测性与概率容斥于是给出完整的 `1-P(Wplus)-P(Wminus)+P(Q=0)`。n=0完全包含：两尾均为全空间，零能量也为全空间，两侧都等于零。既未加无原子/对称性输入，也未删除 Q0 修正。

**实际原律最大值CDF回拉（253–438）。** 先由前一新定理取 `Cb`，统一常数取 `Cb+2 exp(2)`，位置在全部律与参数之前。原坐标投影在 `P0=nu^n` 下具有实际 iid 原律；既有 `sourceTruncation_conditioned_sample` 的完整头已核对，其实例化导出 `p>=7/8`、实际闭截断条件样本律及 `cond P0 N=P`。真实 `rho=cond nu B` 的概率实例从合格原律截断数据导出，随后才得到 `P=rho^n` 的概率实例；没有把它们当成额外输入，也没有假设 p 或 rho 已经归一化。

u>0 时两严格CDF分别是各自弱上穿越概率的补；条件概率乘p与原律交集精确相等，弱穿越按N及其补集划分，得到全等式 `E=p(F-G)+bias-bad`。u<=0时F0、F和所有零延拓量均为零，所以等式覆盖所有实数u，而非仅正邻域。`bad,bias>=0`，p<=1、尾比较和 `1-p<=R/epsilon³` 给 `bad+bias<=(Cb+2 exp(2))w/epsilon³`。由精确等式，绝对误差是 `|bad-bias|`，不超过费用和。先除以已证明正的p获得锐的除p界，再由p>=7/8推出1/p<=4/3，最后分别处理s=1及s=-1，方向和所有除p位置正确。不存在把 p>=7/8、目标费用、END 或SM结论偷作前提的情况。

## 原生所属类型与传递公理

完整读过既有 `original-cdf-pullback-owned-audit.lean`。它遍历 `env.constants`，通过 `env.getModuleIdxFor?` 选择实际所属模块，未按命名空间筛选，对每个所属常量执行传递 `Lean.collectAxioms`。完整打印选项为 `pp.all/deepTerms/proofs=true`、`pp.maxSteps=10000000`。

既有 `audit001.log` 的1–837行分四个无重叠连续段全部读完，20个完整实际定理类型逐字读齐，包括全部实例参数、原子表达式、局部绑定和有序结论；没有采用因子摘要或省略。逐块原始哈希与索引独立重算，完整所属名称集合与原生审计JSON一致。实际为3公开定理、2私有源辅助定理、15生成定理，合计20；所有20项均为 theorem，非定理值（包括私有/生成定义及other）为零。两个私有项属于 `_private...` 名称，仍完整纳入；没有任何外命名空间遗漏。

生成项逐项覆盖：双号头的 `_simp_1` 至 `_simp_4`；端点头的 `_simp_1` 至 `_simp_2`；回拉头的 `_simp_1` 至 `_simp_9`。完整20个实际名称及各自类型哈希/公理表在 coverage 中。每一项传递公理都属于 `propext, Classical.choice, Quot.sound`；实际并集恰为这三项。并非只检查三个公开头。

原生日志 SHA256 `fd961e2e855164d5aca845fab85ceb250ae96df8b2d2e96c3556d291c6678b4a`；原生JSON `78b399e4deb84b4ca67a44db1888817dca52ed3bdecac8e88459fb9f3800e84e`；完整类型索引 `2c5ce9b1666620de91c349d967dd9e30b9aed1d7743a34a5af2b0e218f26bf61`；审计源码 `646f0a24eb6974ed2234bc82dccaa9bdd4a4b9531edd10ccc194cfa6a9979ea1`。

## 首次成功证据、失败分母与旧依赖复用

只复用 `check005`：原生 `check005.directrc=0`，成功日志无 error，日志 SHA256 `622b9a4fa42656cfaff583b8fc4886d153870bd7fe86032551df5716c73de02a`。同次原对象 `/root/rivermind-data/shao-lean-20261021/outputs/common-original-cdf-pullback/check005.olean` 的SHA256为 `5e5060b82bb52b278e9c1ffda3d1875420bd41f74a2e01c3091f0de6c7e84745`；模块执行别名实际解析到该原对象。原生 `audit001.directrc=0`。源码快照、对象、直接返回码、审计日志与审计直接返回码的原始时间顺序相符。成功日志只有风格/弃用提醒和既有mathlib本地变更提示，固定版本与合格字节身份核对通过；不为报告样式重编。

诚实分母为4个失败源检查、1个最终成功源检查；所属审计1次成功、0次失败。check001–004的原始快照、日志哈希与直接返回码均独立核对，返回码都是1；源错误行数依次1、19、5、1。check005返回码0且错误行数0。失败原因为import前模块文档语法、技术展开/改写、零能量与符号推导接口、最后一处可测坐标类型推断，均未被覆写。作者交接另外记载3项非Lean管理事件：服务器缺rg、成功提交后回执脚本转义失败、下载尚不存在回执失败；不把这些当成数学结果或另算Lean失败。

39个root激活依赖逐一核对：当前源SHA、合格原对象SHA及实际执行别名SHA均精确匹配。36个别名的解析路径与登记原对象路径不同，但两处对象字节同一，按项目规则接受；完整真实路径映射保留于只读证据，没有改写别名或复制对象。

关键依赖已核对现有合格资格及接受收据：OriginalGaussianTail为v67，源 `f6b3df97e75be79ffcad5d0cb0cd9479e919dabad096796a16d3e54e1576a583`、原o `ddf6815a43d250a2d4f8cd6ebd9afcf40ce5faf40977504086a279ab87c2a337`；SourceDesmoothing为v66，源 `8947e669f554a7d4aaefe04250a90b4deed2ec909da260f13ac5f58925790240`、原o `ae8e9426e44823c222ac026cf63508ddf9693c14b34c420e985db726a0eed967`。现有完整独审、root资格文件的哈希与接受收据相同。只核对本次使用的完整输入头及接口，没有重复审查旧证明、重跑旧公理或重编旧依赖。

固定Lean `leanprover/lean4:v4.36.0-rc1`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。既有作者资源收据记载共享root锁、CPU10–13、`-M8192 -j4 -DautoImplicit=false -DElab.async=false`；本次只读核对不取得重型锁，也未触碰受保护任务。原始大日志和对象保留服务器，本地只有紧凑覆盖/哈希证据。

## 交付、释放与限制

[完整机器可读裁决](<C:/game/shao lean/coordination/common-original-cdf-pullback-full-review.json>)、[逐项覆盖](<C:/game/shao lean/coordination/common-original-cdf-pullback-full-review-coverage.json>)、[只读原生身份核对](<C:/game/shao lean/drafts/c12-original-cdf-pullback-review/native-readonly-evidence.json>)。

本次完成了全部3头所声明的CDF回拉、双号坏截断费用与任意律端点精确恒等式。端点恒等式没有支付END相对误差；本审查不宣称full-ySM、加权收缩、C1/C2或任何原研究根完成。所有原根保持 **OPEN**。无待修关键数学或证据缺口。

审查写权及执行权已经释放，无在途操作；后续仅root可给予资格/整合裁决。输入、缓存输入、输出、推理子集的实际令牌数未向本上下文暴露，均记未知，不折算为订阅百分比。
