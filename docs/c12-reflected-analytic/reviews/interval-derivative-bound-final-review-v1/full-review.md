# Unit27：IntervalDerivativeBound 独立完整终审

结论：**CORRECT**。最终冻结的四个条件命题均已得到完整证明；完整实际类型与冻结声明一致。可复用作者的精确源码服务器内核及全部所属声明的递归公理验收。该结论只覆盖本单元的条件性一阶导数包络，所有原始 C12/OQ3/OQ4/OQ56 根组仍为 **OPEN**。

审查者为全新、独立的 `/root/interval_derivative_bound_final_review`，按任务配置使用 `gpt-6.1-sol / xhigh`。作者为 `01a16c4c-25a6-7740-a10e-12635a13edae`，协调者为 `01a16be2-3e35-7e13-97d3-7b11b603dead`。本审查仅写 `interval-derivative-bound-final-review-v1/`，未改生产源码、冻结、共享协调文件或 Git，未使用子代理。已应用 math-theorem 与中文优先技能，未启用 math-ultra。计量不可取得，输入、缓存输入、输出、推理子集均记为 null。

## 精确版本及阅读范围

| 对象 | SHA256 |
|---|---|
| `IntervalDerivativeBound.lean`，3778 字节 | `24a86dccc502a8293f6aad8cc59824803a057bcb036035a9ac37023d96c30abd` |
| 成功及已安装 `.olean`，179320 字节 | `d83cb3eb83cf75438a176e96649add34930141102940d00951763ff546fea8b6` |
| `frozen.lean.txt`，2074 字节 | `ffa1979cecd949a9f9290a4857ca6c3ebe7c9d17f69e4ff6b7b207d114218a2f` |
| 作者 `receipt.json` | `308e6420b4924aba48abae4fc04974cc66cd50a51094fe9cf7521b4a36128f55` |
| 作者 `RELEASE.json` | `58d0b1e6cc9e2fde5a6789d2bd077ac66cb25e783129ccb8b6453b5686599598` |
| 四份完整实际类型导出，50821 字节 | `a27914def4a335ffff3b04da2c4d666a8a4a3a1b8708988173b1c264ded188cd` |
| `owned-audit.json` | `8311525897e9bb1841f70ea980628e321afe57085756f69855532bba462c874f` |
| 实际定义值导出，0 字节 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

完整读取了目标源文件、四个完整冻结声明、说明文件和审计程序。四个声明头（包括全部显式及实例假设）、导入/命名空间上下文逐项一致；最终命名空间结束一致。目标源码为 UTF-8、无 BOM、无 CR。禁用的 `sorry/admit/axiom/unsafe/native_decide` 标记均不存在。

完整实际类型采用精确子表达式字典阅读：已直接读取全部 42 项字典及全部目标编码，没有省略实例、拓扑、可测空间、量词、类型字段或声明。展开后与原始 50821 字节逐字节相同；源摘要和往返校验见 `lossless-reading-manifest.json`。原始导出没有 `⋯`、`...` 或 `sorryAx`。这不是仅看公开声明头或类型摘要。

同时完整读取本单元实际消费的旧接口类型和透明值：BridgeDomination 的九个定义（BridgeTime、BridgeNoise、bridgePath、三类严格事件、三类 completion）及 signed_derivative_domination_of_hasDerivAt；HalfLineReflectionFormula 的两个定义、两个 HasDerivAt 定理、两个导数界。依赖选择保留完整类型块和完整定义值块，均作精确字节往返校验。旧模块完整证明与全所属审查继续复用既有合格审查，不另发旧模块编译或审计。

## 原文到声明的忠实性

只读原文为 `C:/game/shao/current/c12/supplement.tex` 第 4192–4253 行：严格 Brownian bridge 存活概率、两端内点、正时间、固定墙和终点下的空间微分；半直线标量公式为 `1-exp(-2uv/T)`。精确原文摘录 SHA256 为 `7c114b02812a59089a18904d502318e4ac65a8574c7a80f735aa16dc3a8283f2`。

这里的 completion 是已接受的实际连续路径严格存活事件在 `P` 下的实值测度，而非新增的自由标量替身。BridgeNoise 的路径在单位区间连续且两端钉于零；bridgePath 为 `(1-t)y+tz+sqrt(T)g(t)`；上、下事件分别对所有时刻要求 `<a` 和 `-a<`，区间事件是二者交集。它们在这四个目标的实际类型及透明值中保持一致。

两个微分转移命题对任意测度 `P` 与全部实参数量化，只分别假定 `y<a` 或 `-a<y`，并要求对应 completion 在整个开半直线上等于显式公式。这足以提供所需点的邻域恒等，但该恒等本身并未被本单元证明。

区间导数界另要求 `P` 为概率测度、`T>0`、`|y|<a`、`|z|<a`、两个半直线反射恒等，以及实际区间 completion 在 `y` 可微。结论是

\[
\left|\frac{d}{dy}\operatorname{intervalCompletion}(P,a,y,T,z)\right|
\le \frac4{\sqrt T}\left(1+\frac{|z-y|}{\sqrt T}\right).
\]

一致版本保留概率、严格内点、反射恒等及实际可微假设，以 `H>0`、`H≤T`、`a≤A` 给出

\[
|\partial_y\operatorname{intervalCompletion}|
\le \frac4{\sqrt H}\left(1+\frac{2A}{\sqrt H}\right).
\]

`|y|<a` 已推出 `a>0`，并与 `a≤A` 推出 `A>0`；未偷偷增加墙正性的假设。两个结论均按原文固定墙、时间和终点，只对起点微分。原文更强的剖面因子 `P(y,T;z)` 没有出现在本单元结论中，因而本单元的无剖面包络不能充当原文完整导数引理的证明。

## 四个证明逐项核对

1. **upperCompletion_hasDerivAt_of_reflection（源第 9 行）**：旧模块给出 upperReflection 的真实 HasDerivAt，`h.deriv` 把其斜率识别为显式函数的 `deriv`。因 `y<a`，开区间 `Iio a` 属于 `y` 的邻域；`hReflection` 在该邻域给出实际 completion 与公式的函数相等。`congr_of_eventuallyEq` 将 HasDerivAt 传给实际 completion。没有从单点数值相等推出导数，也没有使用区间 completion 的可微假设。

2. **lowerCompletion_hasDerivAt_of_reflection（源第 19 行）**：同一论证使用 `Ioi (-a)`，其邻域成员性正由 `-a<y` 提供。下墙符号、函数参数次序与公式保持一致。此处同样得到真实 HasDerivAt，而非仅对可能不可微函数调用总定义的 `deriv`。

3. **interval_deriv_bound_of_reflection（源第 29 行）**：`abs_lt` 把两端内点拆成上下墙的四个严格不等式。前两引理给出实际半直线函数的 HasDerivAt；`hRegular.hasDerivAt` 给出实际区间函数以其真实 `deriv` 为斜率的 HasDerivAt。旧 signed_derivative_domination 的完整类型正是对同一 `P,a,y,T,z`、同一个空间变量、三个真实导数给出 `du≤di≤dl`，无遗漏条件。令 `B=4/sqrt(T)*(1+|z-y|/sqrt(T))`；旧上下界分别给出 `|du|≤B` 和 `|dl|≤B`。代码取上半直线绝对界的下侧与下半直线绝对界的上侧，得到 `-B≤du≤di≤dl≤B`，最后恢复 `|di|≤B`。夹逼方向正确，没有把上半直线负斜率误作正界，也未从半直线可微性推断交集概率可微。

4. **interval_deriv_uniform_bound_of_reflection（源第 47 行）**：`0<H≤T` 给出 `T>0`、两平方根严格为正和 `sqrt(H)≤sqrt(T)`。两端严格内点及 `a≤A` 给出 `|z-y|≤2A`；这是从已写假设直接线性推出。非负分子除以正且增大的平方根满足相反单调性，因此 `4/sqrt(T)≤4/sqrt(H)` 及 `|z-y|/sqrt(T)≤2A/sqrt(H)`。再以 `mul_le_mul` 使用 `1+|z-y|/sqrt(T)≥0` 和 `4/sqrt(H)≥0`，把上一结论的右侧放大到目标。没有把总定义除法在零点的值拿来支持正时间估计，也没有遗漏乘法所需的非负条件。

边界检查：`H=0` 和最终估计中的 `T=0` 均被明确排除；墙上或墙外端点不在估计范围内；严格内点可任意接近墙，不额外要求最小墙距。前两转移引理允许全部实时间，含零时标量公式的总定义，但它们仅在所写邻域恒等前提下断言导数转移。不存在有限枚举、数值实验、隐藏独立性或期望到逐样本的替换。

## 既有证据及服务器绑定

BridgeDomination 复用合格 `bridge-permutation-final-review-v1/full-review.json`，SHA256 `568c781dac68a0ecb79e401897d30ceaa70dead2966fa77f47f9972406b29ed2`。其源码为 `45b6733a6341fcf002bfa44738074419c118818e88ea8f0f2e07dc66d381e7b9`，已安装对象为 `e527ff9d0a16c9585b1769e6286349b6a1a3f520ade44cd6bd28205ca109cf27`。

HalfLineReflectionFormula 复用 unit26 合格终审，JSON SHA256 `7f994541cb9e7999a0007570f92314086c9f5db9e999c171716c0d5a4e7a3240`，Markdown SHA256 `af8af60019af8dabbf98373c482d74b08d6acb2a18825d121514f0d8a90cfa09`。作者收据为 `bc317d24523edb05615fd3f98dd89dc12d6a70457c41d099ecb513181fb65e77`，源码为 `e852b2878fe686464158ce509b45de20c5cc8c478e65316e25d39bf6543dbf8c`，已安装对象为 `479ce890330887f671e1b0f2a9142514230830bd9d5416db24dabd142eaecbe3`。这些旧源码和对象均在服务器只读逐一核实一致。

目标服务器 worktree 为 `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`，分支 `author/c12-uniform-permutation-law-v71`，观察到 HEAD `fe32939af989d80cfebfb9c245d456a63b262ce6`。工具链文件仍为 `leanprover/lean4:v4.36.0-rc1`，mathlib HEAD 仍为 `807d3836b165983210ee2ecf3cd28f239436949c`，包目录解析到受认可的 `cache-overlays/shared-v34/packages`。

只读比对作者收据全部九项工件的大小与 SHA256 均通过；当前目标源、attempt002 的精确源快照一致，输出对象与实际已安装对象一致。原始 audit 日志去掉固定前导警告及最终计数行后，与全部实际类型导出逐字节一致；定义值导出为空且原日志没有定义值输出。时间顺序为成功源快照→成功对象→已安装对象→审计日志→类型导出→收据。attempt002 内核及 audit 的退出码由绑定收据记录为 0，内核日志仅有既有 mathlib 本地改动警告。

审查了既有 `OwnedAudit.lean`：它遍历整个环境，使用 `env.getModuleIdxFor?` 得到每个常量的实际所属模块，再对所有属于目标模块的常量调用递归 `Lean.collectAxioms`。不存在命名空间/公开名称筛选；公开名单仅额外校验预期四个定理。每个常量的公理超出 `propext / Classical.choice / Quot.sound` 就报错。实际四行所属记录均为 theorem，故实际计数为四定理、零定义、零其他常量，也无未披露的 private/generated 声明。四行均只依赖上述三个标准公理。

保留的 attempt001 与最终 attempt002 的四个声明头相同；唯二源差异是两处 `rw [← h.deriv]` 改成 `rw [h.deriv]`。失败源和日志的收据摘要均核实保留。此次审查没有重跑任何成功 Lean/audit，没有安装 Lean、编译旧 producer、写缓存或改动已冻结字节。作者资源收据保留 CPU14–17、c12-heavy.lock、`-M8192 -j4`；本审查只读观察不占重型命令。

## 接受范围和未闭合义务

四个最终冻结命题的完整源到声明、证明、全部实际类型、全部所属递归公理及接口交互均无关键缺口。数学正确性为 CORRECT；精确冻结局部目标的机械状态为 `LEAN_FULLY_CHECKED_FOR_FINAL_FROZEN_LOCAL_TARGET_REUSED_AUTHOR_RECEIPT`。

这里未构造 Brownian bridge 法律，也未证明它与 `P` 的对应；未证明两个实际反射恒等；未证明实际区间 completion 的 DifferentiableAt。这些是明确输入而非已闭合子定理。原文的剖面因子、联合导数可测性、墙上单侧界、高阶及混合导数、PDE、补偿 Taylor 余项、零能量/零墙宽的完整约定及所有原始根定理均不在本单元已证范围内。本单元不作新颖性认证，按既有结果的源约束组合辅助引理归属。

审查范围内没有未覆盖的实际声明或待修补关键缺口。终审自身的写入和执行权限在 `writer-release.json` 中单独释放；这不释放或改变父级下一工作单元的权属/执行状态。
