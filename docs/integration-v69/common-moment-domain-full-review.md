# SourceMomentDomain 独立完整终审

STATUS: CORRECT

审查者为不同于作者的新鲜独立上下文 `/root/common_moment_domain_full_review`，指定模型 `gpt-6.1-sol`、推理强度 `xhigh`。本轮使用一次 math-theorem 工作流，未使用 math-ultra，未开子代理。完整阅读冻结的两个公开头、新源全部 286 行、全部局部 `let`/实例字面值，以及 9 条实际模块归属声明的全部展开类型（共 30590 UTF-8 字节，真实省略为 0）。无生产源、冻结、旧证据、别名修改。

## 精确接受范围

- 模块：`Shao.Probability.SourceMomentDomain`。
- 分支：`feat/common-moment-domain`；父提交 `b92157fea6705e1c1ed3e74d4d504606148d7058`。
- 提交：`fff5061e2ac508d094e4e6cf07bbfe4ff49f7e04`；树：`293c9bb0e5b3beabc379db7036c16ea15b568f01`。
- 唯一提交文件：`Shao/Probability/SourceMomentDomain.lean`；源 SHA256：`38001730626dfcd13ffc6cee1b226dea9e1361b0f0514f663becfaaf7970eed2`，UTF-8/LF。
- 两个完整公开头分别对应源 20–33、133–163 行，逐字匹配冻结文本；头 SHA256 分别为 `36b44c3a16ffd9c1768bd5f0ea98e57a6980ef2724dc1e30c78b629bb4f18484`、`acf1172f4c832c7db79cfd4e62449499619ddaf42f290cbed7c6d628872d93a6`。

这是原 C1 装配所需的两个辅助结果；未证明 END、SmallBoundary、原单侧或双侧根尾界，也未实现冻结候选中的其余三个根头。全部原 C12/OQ3/OQ4/OQ56 根组仍为 OPEN。本报告不执行推送、PR、合并或 root 接受。

## 完整证明核对

| 源行 | 已完整阅读的证明内容与裁决 |
|---|---|
| 34–49 | `Real.rpow_eq_pow` 只改记法；局部 beta、H 与头中的完整字面值相同。`n>0`、`n≥1`、`p>0` 全由原前提给出。对每个 z，`(n*z²)^(p/2)=n^(p/2)*|z|^p` 的底数非负条件均已支付；实际 p 阶矩可积性给出 U 的可积性。 |
| 50–75 | 对 `U=n*z²≥0`、`q=p/2>1` 使用 Bernoulli 切线 `1+q(U-1)≤U^q`。常数、仿射项和右侧均实际可积，概率质量为 1；逐项积分并使用 `n*E z²=1` 得 `1≤n^(p/2) E|z|^p`。未假设均值为零，也未把目标比较作为前提。 |
| 76–107 | 严格正的 `n^(p/2)` 允许相消，指数和为 1，给出真实 Lyapunov 下界 `n^(-(p-2)/2)≤beta`，从而 beta>0、H>0。负指数反单调方向正确；`(p-2)/(2p)≤1/6` 使用 p≤3，底数 n≥1。`H^p*beta=1` 使用 beta>0 和 p≠0，未误用零底数幂。 |
| 108–131 | 任意 `0≤x≤H` 均满足 `x⁶≤n`。`F(x*z)` 的可积性来自二阶矩，`|x*z|^p` 的可积性来自实际 p 阶矩；`F≤|·|^p` 的 2≤p≤3 条件被支付。积分比较给出 `n E F(xz)≤x^p beta≤H^p beta=1`。参数确为 x，未替换为 1+x。 |
| 164–186 | sigma、nu、beta、Praw、Pnorm 均为冻结的完整字面值。`b=sigma*sqrt n>0`、`c=b⁻¹>0`，二者的正性分别来自真实 raw2>0 与 n>0。实际商映射可测，`nu` 概率实例由真实推前测度构造，局部实例字面值为 `hprob`。 |
| 187–214 | `|z|≤1+z²` 从二阶矩可积性支付原变量一阶可积性，排除了不可积 Bochner 积分默认值造成的假均值。实际商映射的积分公式给出均值 0、二阶矩 `c² E z²` 和 `n E_nu z²=1`；没有额外一致性假设。 |
| 215–247 | 正底数的 rpow 乘法、sqrt 与指数乘法给出 `b^p=sigma^p*n^(p/2)`。p 阶矩可积性通过实际映射传递，并精确得到对应积分商；`n^(p/2)=n^((p-2)/2)*n` 给出原文 beta 的精确恒等。beta>0 调用本模块已证明的第一个 helper，没有循环引用或额外三阶矩假设。 |
| 248–251 | `Measure.pi_map_pi` 应用于每个坐标的实际商映射，所得正是 Praw 到 Pnorm 的有限乘积推前等式；nu 的概率实例支付所需有限性。没有替代 iid 法律或假定目标乘积映射等式。 |
| 252–284 | 对每个实数 x、符号 s，路径商映射与 s 的缩放均可测；弱交越集由 energyWall 和 `upperMax` 可测性支付。逐点将映射写成 `c • a`，交换实标量，使用 `energy(ca)=c² energy(a)`、正平方根与 `upperMax(ca)=c upperMax(a)`，最后仅消去 c>0。`Measure.map_apply` 对已支付的可测事件给出精确概率等式。实际上证明对任意实数 s 成立，因此包含冻结的 s=±1。 |
| 1–19、132、285–286 | 全部导入、选项、命名空间和收尾均完整阅读；没有私有定理、全局定义、隐藏新假设或额外逻辑绕过。 |

所有新局部 `have`（含嵌套 h、hright、hpow、he、hTa、hcomm）和最终 `show` 等式均已完整字面阅读；逐项源跨度与 SHA256 记于覆盖文件。所有公开头和证明体内的 17 处 `let`/实例 occurrence 均记录完整原文及哈希。该计数由精确源自动推导，详见覆盖文件。

## 原文忠实性与边界

完整核对只读原文 `C:/game/shao/current/c12/main.tex` 的 150–218 行，并核对其与服务器相同来源的字节哈希。原文二阶矩、均值、p∈(2,3]、`mu_p`、`beta=mu_p/(sigma^p*n^((p-2)/2))` 和 moment 分支 x≤beta^(-1/p) 均得到忠实表达。F 的定义为 `z²*min(|z|,1)`；本 helper 支付的是 F(xA) 的 coarse guard，未声称支付原 R_n(x)=n E F((1+x)A) 的同一上界。原文扩大区间中的 small-budget 分支仍属独立依赖。

已逐项检查 n=1、x=0、2<p≤3 的全部允许端点、非对称原分布、任意原子与全零样本。p=2 不在冻结域中，未擅自扩域。`upperMax` 的已接受定义为正时间 `Icc 1 n` 的上确界，参数明确为路径与 hn，不包含时间零。弱乘法事件从未除以 sqrt(Q) 或 x，所以 Q=0 与 x=0 保持原语义；任意负 x 也在第二个 helper 的量词内。没有假对称性、原法第三矩或路径上 Q>0 假设。

## 服务器内核与全归属公理证据复用

本轮服务器操作全部为只读文件、哈希、Git 状态与接口头检查；新 Lean/build/audit/cache 命令均为 0，未取 heavy 锁。当前工作树干净，HEAD、tree、parent、branch 与委派目标一致。当前源、HEAD blob、attempt03 源快照和本地审读源完全同哈希。

首次整源成功为 attempt03，原生 directrc=0。同次原始对象位于 `/root/rivermind-data/shao-lean-20261021/checks/common-moment-domain/attempt03.olean`，SHA256 `8f7ccf7d80680f86f52df88e6b239f5d35f51530202422e371dc2f2d3c6ce776`；执行别名为符号链接，解析后正是该对象，字节相同。成功日志 SHA256 `b674014cfffd1d042cb959722d0081b4799d6327a3efee42a44319efc2c2a822`，完整读取后仅见既有 package-view 提示和未使用 tactic 风格警告。未为消除风格警告改源或重复成功编译。

独立审读原生 owner 审计器：按 `getModuleIdxFor?` 精确模块相等遍历全部常量，无命名空间/公开前缀筛选；每个实际归属常量运行递归 `Lean.collectAxioms`，任何非 theorem 或非白名单公理均报错。owner local index 为 4760。原生 owner directrc=0、日志末尾为 `9 PUBLIC 2 THEOREMS 9 DEFINITIONS 0`。两个公开定理及 7 个 generated `_simp` 定理的全部原始类型逐字读齐，导出类型逐字匹配原生日志，逐项类型哈希、字节数、AX 列表均独立复核。没有任何非定理值需要补读，真实类型省略为 0。

- 审计器 SHA256：`2dd786f25b596a083ebc806e59c09fce7e1a9217c075ce88c0b1b93c9f421d9d`。
- 原生全归属日志 SHA256：`caca2fb35d754d7bcc61a8dea90b1d668fe5941ad7a3cd129273c6362852513b`。
- 全类型导出 SHA256：`fac452879fb6737c9adb4df6e84295e5f8f07d5c2a1f08d0a3a333a408547dc5`。
- 仅允许且实际出现：`propext`、`Classical.choice`、`Quot.sound`；具体每条列表见覆盖文件。

现成证据的工具链为 `leanprover/lean4:v4.36.0-rc1`，mathlib 精确提交 `807d3836b165983210ee2ecf3cd28f239436949c`。作者回执记录 activation-before-cd、CPU10–13、共用 root-heavy.lock、-M8192/-j4、autoImplicit=false、Elab.async=false；本轮没有新执行需要复验资源。历史命令次数的“成功后重复为 0”依作者持久回执与现有产物账复用，不把只读哈希观察夸大为独立的全会话执行追踪。

## 依赖与失败历史

原 6 对依赖激活文件 SHA256 `278065461674da5d6c3f6b4bb112ba96cdc66997d2a67069711ec2dca80784d9` 未变，当前前六行对象逐项完全保留。因实际事件可测性需要，root 增补 `MeasurablePath`、`C2.TwoSided`、`Basic.Events`、`C1.Normalization` 后为 10 对。对每一对独立核对当前源、原接受工作树源、原对象和实际执行别名；10 对均精确匹配所记 source/object SHA256。物理原对象的解析路径保留在只读证据文件中，未改别名、复制对象或重复旧 Lean/AX。只补读本证明实际使用的旧定义字面值/接口头；旧证明与旧资格审查不重演。

attempt01、attempt02 是真实 elaboration/interface 失败，原生 directrc 均为 1，均无成功对象。各自完整源快照、SHA 文件、完整日志、directrc 保存在原服务器位置，独立核对全部日志哈希及文件长度。其源 SHA256 分别为 `6042aadf54585ec0f5dbcddfe886492be4acefa6d6cada4e897c81b37ed09716`、`098b68e15abbea7e6aa60484c7988b12f1998f081a6e227e5dd7768f9b643ccc`；日志 SHA256 分别为 `325bee0b83ab7f1fd40016088c4863474ad19e2f02d0dce8eaad96ef23b24f54`、`eb77a0fd729a92c2ea0f492a0865a4c0f708f2a4b24cc7d1e4af300c57919e8f`。错误摘要明确为 rewrite、积分参数、类型和当前可测性 API 等失败；不计为通过。作者另披露全类型后处理器最初的单行 AX 正则失败，修正为多行解析后没有重跑 Lean；本轮多行解析独立复核了原日志所有 9 条 AX/type。

## 审查交接

精确源的两辅助定理获完整独立证明与陈述忠实性裁决 CORRECT；机械层复用现成精确源的整源内核及全部归属递归公理通过证据。逐项覆盖见 `coordination/common-moment-domain-full-review-coverage.json`，只读服务器证据见 `drafts/c12-moment-domain-review/server-evidence.json`，本地冻结/远端绑定复核见 `drafts/c12-moment-domain-review/local-bindings.json`。

审查写权与执行权释放，无在途操作。下一步由 root 消费本精确版本，并继续真实的 END/SmallBoundary/C1 装配依赖；本独审者未接管这些实现。平台未提供分项 input/cached-input/output/reasoning-subset 使用数，未估算订阅百分比。
