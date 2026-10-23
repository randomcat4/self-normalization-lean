# Actual source-noise sandwich：独立完整审查

STATUS: **CORRECT**

本结论仅认证冻结的实际源噪声严格 CDF 夹逼，以及同一实际噪声下的
`delta` 支撑与一阶矩界。未发现关键缺口。根协调者实现此源码；本审查由
新鲜、独立的 `gpt-6.1-sol / xhigh` 上下文完成，使用 `math-theorem`，未使用
`math-ultra`，未参与实现或修改证明，未另跑 Lean。

## 精确版本与覆盖

- 源码：`drafts/c12-source-noise-sandwich/SourceNoiseSandwich.lean`，完整读取第
  **1–419 行**；19767 字节，419 LF，0 CR，无 BOM。
- 源码 SHA256：`f972d6271477f37751d8b5b1bfcf74ef55348d00426e8a83b21942f3fd332d79`。
- 原成功同次 `-o` 对象 SHA256：
  `71cc730b05fbd4582076af890a4405ab48cabaa98b05e9d41f34a1116fc7ca91`。
- 远程工作树：`workspaces/common-scalar-fourier-v44`，分支
  `feat/common-source-noise-sandwich`；唯一新增源
  `Shao/Probability/SourceNoiseSandwich.lean`。
- source-only commit：`5893148b514a6feaa5f4c36d12485135fae83024`；parent
  `33e3336937c4bd2ed6301effc5e6c18b89b575d3`；tree
  `7a40a5a00e52a21850b2dc0f38a3f739029e20f0`。
- 原实际 owner 枚举得到 **10 个所属常量，全部为定理：2 public、8 private、
  0 definition、0 额外 generated**。这由 owner 集合与逐名源映射的双射得出，
  不是从作者所称数量推测。完整读取全部 10 条实际类型及每条传递公理记录；
  因实际定义数为零，无遗漏的定义值。
- 逐声明源码区间、完整实际类型 UTF-8 SHA256、AX、证明审查说明及裁决见
  `coordination/common-source-noise-sandwich-full-review-coverage.json`。
  全部非声明源码行也已读取，覆盖文件记录其区间。

已完整读取候选证明、两个完整候选声明、冻结文件、冻结绑定、作者交接、
名称/API 修复说明及原审计程序。独立字节检查确认冻结的三个文件哈希仍分别为：

| 文件 | SHA256 |
|---|---|
| declaration-freeze.md | `0d15c056c4755f7c20c79a356ce2948e1d8148fb417cc588d705b366633c955d` |
| candidate-declarations.lean.txt | `9a44110f0a7f4fa39ee37846191eb18e3a44020e193242878cb95c307dccd60f` |
| candidate-proof.md | `a2f3f57690b75e80adc5fd9c5f256bd4e21692ad4dd21c1782195d029be48c5c` |

两个实现 public 头及其中所有 literal lets 与冻结候选仅按空白归一后逐字一致。
`open Probability` 将既定未限定名称解析为实际
`Shao.Probability.sourceFourierTest` 和 `sourceKernelCutoff`；实际完整类型已
确认该解析，没有替换数学对象或前提。删除 `sourceTruncation_law_data` 调用中
多余的 `hmean` 参数符合原已验接口；公开 `hmean` 仍保留，并传入真正使用它的
`sourceTruncation_fullNoise`。

## 原文到声明的忠实性

完整读取原 `main.tex` 第 762–850 行、`supplement.tex` 第 3851–3909 行；为
核对对象还读取主文 372–393、545–645 行的固定参数、条件样本、真实能量、
Lindley 过程、严格 CDF、实际平滑测试和同一固定噪声约定。此单元形式化 S.7
第 3857–3885 行的逐样本及积分夹逼；不会把后续加权代价与收缩算作本单元成果。

1. `sourceFourierTest_noise_sandwich_pointwise`（53–107）使用真正的测试
   `chi(q+t) * 1_{|u+z| < y sqrt(q+t)}`、真实 plateau `[1/8,3]`、
   好时钟 `[1/4,2]` 与 `delta=4(|z|+(1+x)|t|)`。
   量词保留 `x>=0`、`0<y<=1+x`、`|t|<=1/8`，上下均为严格 `<`。
   它没有输入欲证比较或隐含原子排除条件。
2. `sourceTruncation_actual_noise_cdf_sandwich`（340–417）固定
   `h=epsilon/(1+x)`、`rho=cond nu {|z|<=h}`、`P=rho^n`、
   `law=quadraticFullNoiseLaw rho`、`gamma=m3(rho)/variance(rho)`，随后才量化
   所有可测 `U` 与 `0<y<=1+x`。同一 law 用于所有 y，未随阈值重新条件化。
   `energy a` 是 `sum_i (a i)^2`，没有替换成方差或中心化的平方和。
3. `F(v)=P.real{0<energy a ∧ |U a|<v sqrt(energy a)}` 是真正的正时钟严格
   CDF。取端点和时为 `|S_n|`；取非负 Lindley 统计量时 `|W_n|=W_n`。
   任意实值可测 U 的接口忠实包含这两个用途，未额外假定 U 可积。
4. `v<=0` 时该事件确为空；严格等号与原子完整保留。`energy=0` 的样本
   被正时钟条件排除，同时属于坏时钟集合；带噪测试在该样本上的值由坏时钟损失
   覆盖，未作任何除以能量的操作。没有 `n>0` 的暗中假设：`n=0` 与原
   `n * E z^2=1` 前提直接不相容。
5. 原始分布只输入有限二阶矩、原均值零、二阶归一化和实际截断 budget。
   不要求原始三阶矩有限，也不要求 rho 均值零。已冻结的新辅助接口明确要求
   `epsilon<=1/800`，这是为实际支撑常数 100 支付 `|Y|<=1/8`；没有修改旧
   结果的前提。原文固定参数取法满足足够小的 epsilon。原文局部半窗蕴含
   `y<=1+x`，所以本夹逼的 y 范围足以覆盖原用途。

核对了已接受的 `SourceFullNoiseBridge` 全部消费接口、`SourceTruncation_law_data`
完整头、`SourceFourierTestKernel` 的真实 cutoff/test 定义与数据、`FinitePath.energy`、
`TruncationIntegrals.truncationBudget` 与 `truncationF`，以及实际
`quadraticFullNoiseLaw` 的映射/输入乘积法则、真实 chord/标量噪声定义。
旧 `fullNoise` 确实输出同一 law 的概率性、支撑常数 100 与一阶矩常数 100。
独立确定性检查确认 activation 中全部 **20 个**已接受依赖源与本地只读 curated
snapshot 的哈希相符；复用已验对象，没有重审旧证明或重编旧依赖。

## 完整证明审查

| 声明/源码区间 | 核查内容与结论 |
|---|---|
| `sns_sqrt_shift` 18–51 | 从 q、q+t 非负建立平方根平方恒等式；两根之和至少 1/2；差乘和等于 t。取绝对值后用非负乘积得到 `|sqrt(q+t)-sqrt(q)|<=2|t|`。q+t 的闭区间为 `[1/8,3]`，边界无除零。CORRECT。 |
| public pointwise 53–107 | `delta>=0`，根下界和 `y<=1+x` 给出 `|z|+y|根差|<=delta sqrt(q)`。plateau 后分别用 `|u+z|<=|u|+|z|` 和 `|u|<=|u+z|+|z|` 传递严格阈值。四个 if 分支均已覆盖；下移参数非正时不能出现 lower=1。CORRECT。 |
| `sns_test_data` 109–128 | 连续根和绝对值产生可测严格事件；真实 cutoff 可测，写成 cutoff 的指示函数。真实 cutoff `[0,1]` 界同时支付非负及上界，无额外 y 限制。CORRECT。 |
| `sns_indicator_integral` 130–135 | 概率测度下常数 1 可积；对可测集限制后可积，其实积分等于真实 `P.real A`。CORRECT。 |
| `sns_bad_clock_sandwich` 137–157 | 好时钟调用已证点态夹逼；补集用 `lower-1<=0<=test<=1<=upper+1`。同一补集每侧损失恰为一个指示量，包括所有非正时钟。CORRECT。 |
| `sns_section_probability_integrable` 159–184 | 对实际 product 上的集合指示函数先证可积；每个 section 由可测映射取原像得到可测。`integral_prod_right` 提供截面积分可积，`integral_prod_symm` 与指示积分定理给出真实概率恒等式；未把目标 Fubini 或夹逼作为前提。CORRECT。 |
| `sns_product_test_integrable` 186–206 | `(a,z)->(U(a)+z1,Q(a)+z2)` 可测，测试范数不超过 1，因此在概率 product 上可积，继而得到 sample-side 噪声平均可积。无需 U 或 Q 的矩假设。CORRECT。 |
| `sns_delta_support` 208–221 | `1+x>=1` 和小 epsilon 给 `h<=1/800`；真实支撑界扣除非负项后得到 `|Y|<=100h<=1/8`。直接乘 4 得到 `0<=delta<=400h`。闭边界正确。CORRECT。 |
| `sns_averaged_sandwich` 223–338 | 两个 shift 事件在 Ω×R² 上联合可测，截面定理真正提供两种 `F(y±delta)` 可积。固定满足噪声界的 z，sample-side 三个指示量与测试均可积，因此可积分上下点态比较并精确扣/加 bad。再对 L 积分，测试 Fubini 交换次序；L 概率性把常数 bad 的积分还原为 bad。所有积分比较的可积性在使用前已付清。CORRECT。 |
| public actual source 340–417 | 原 law_data 真实提供 rho 概率性，`fullNoise` 保留并消费原 hmean，输出实际 law 支撑与矩。支撑给两个坐标绝对值各自有界，从而 delta 可积；线性积分是 `4(E|Z|+(1+x)E|Y|)<=400gamma`。真正的 energy 可测，所有 U,y 用同一 P/law 调用已证 averaged 定理。CORRECT。 |

未发现循环依赖、把欲证比较塞入 helper 前提、缩小 U 的量词、偷加可积性/无原子
假设、条件均值零、阈值端点遗漏或有限样本探针替代一般证明。所有实际类型均已
完整读取，包含大公开头的全部 23248 字符，而非 pretty 摘要。

## 原服务器证据复用

固定环境为 `leanprover/lean4:v4.36.0-rc1`、mathlib
`807d3836b165983210ee2ecf3cd28f239436949c`。原命令通过 activation 后进入指定
工作树，以 CPU10–13、`root-heavy.lock`、`-M8192 -j4 -DautoImplicit=false`
运行。审查者未启动服务器或本地 Lean 命令。

- `check001–003` 的原 compact exit 均为 **rc1**，失败快照/原日志保留在服务器，
  未据空摘要冒充成功。
- 第一次完整整源成功为 `check004`：**rc0，7.095925807952881 秒**；该调用
  同时产生被审计的 `-o` 对象。原日志 SHA256：
  `b9f18d2707b8aa43843d19b1bbbd7196fbc9ca8a1ac9ce2470e31ea34157c6cd`。
  原有弃用/linter 提示不影响内核成功；没有为清警告重编或改动冻结源。
- 唯一原 owned audit 已结束：**rc0 / PASS**；包括锁队列的总等待时间
  983.92738032341 秒。精确源与对象在前后均未变化。
- audit 源 SHA256：
  `37185c41e3a9a5b3c860a9151c6ed02761e58cd9c5626e5b7087001c93bf5f80`；
  原日志 SHA256：
  `a5b40ee3d928b3ed6aa7529ac98b4031532eee5353c3453ab25cda44dd05cc2a`。
- owner JSON SHA256：
  `49d2083daa20c7329493085039206f10d6185a0c811b6527b74a3f351a64d987`；
  完整实际类型 JSON SHA256：
  `037107e1993584e70242b091f17b1fb922af9512d7bc9fc0beeccffb3ed97c99`。

已完整阅读原审计程序：它通过 `env.getModuleIdxFor?` 枚举目标模块所有实际
所属常量，包括 private/generated；对每名调用传递的 `Lean.collectAxioms`。
10 条记录的公理均恰为 `propext`、`Classical.choice`、`Quot.sound`；没有额外
公理或未分类所属常量。审计强制零定义，并用 `pp.all`、`pp.deepTerms`、
`pp.proofs`、`pp.maxSteps=10000000` 输出实际类型。完整原日志及类型扫描的
`⋯`、`…`、ASCII `...` 数均为零。确定性独立检查核对 owner/type 的完整
逐名双射、相关 JSON/审计源码哈希、源禁用构造扫描及冻结头；所有结果 PASS，
见 `drafts/c12-source-noise-sandwich-review/observations.json`。

## 接受边界与写权释放

可复用本份独立完整审查和原服务器精确源证据接受此单元；没有另加一次完整旧证明
复审或重复编译的需要。本单元不声称 `b_x` 的实际数值/加权代价、Gaussian
加权噪声代价、加权上确界收缩、原 CDF pullback、端点逼近或 C1/C2 根定理闭合。
主文 780、785–850 行与补充材料 3887–3908 行涉及的这些剩余义务仍为 OPEN；
未来 cost 候选尚未实现，不是本证明的依赖。

审查者只写本报告、对应 JSON、coverage JSON 及授权的 review 观察目录。未写
Lean、原 receipt、冻结文档、library/cache，未提交 PR 或 merge，未 spawn。
**本审查写权全部释放；无在途工具操作或后台检查。** 每上下文 token 计数未向
审查者开放，JSON 分别记录未知值，没有推算订阅占比。原始日志及对象仍只留服务器。
