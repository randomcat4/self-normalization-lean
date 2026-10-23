# Actual low-frequency D/W 完整独立终审

STATUS: CORRECT

审查者 `/root/common_low_whole_review`，实际模型 gpt-6.1-sol / xhigh，fresh 独立验证上下文；未参与声明或证明编写。使用 math-theorem，未使用 math-ultra。本轮只写本报告及配套 JSON，未修改 Lean，未执行 Lean 或重新收集公理。

接受对象为 `Shao.Probability.QuadraticFullNoiseLowDerivatives`，提交 `6e6e59ee94c6fd5775e45513c6621a1b6662d9d5` 的完整 593 行、33799 字节源码。SHA256 `67cf873490270a75f136486d99d258e252256729036758de4802ab9d7d32e70f`；对象 SHA256 `7fa6d0e9f697c8a290c07c7a160248023bf35c30bfafcaba584d8207a6d05658`。已只读核对本地、服务器现存源码及冻结 Git blob 三者相同。后续 HEAD 前进不扩大本报告的接受对象。

公开定理 `sourceTruncation_odd_even_fullNoise_lowFrequency_derivatives` 与 root 冻结声明作独立完整提取比较，仅空白归一后逐字相同。候选 SHA256 `a9e74e1210c2cf94fcaa5d3ba0b6a303f64941fc4c8bf4ffdc11a5725034d948`，合同 SHA256 `a5f67737611638e48a361d3148bbc2290d69b7e6767d3f7886317a035f76f3ea`。本次只验收 producer；同一冻结文件内 Region1/2 两个消费者未因此完成。

## 来源与陈述

实际读取 read-only `C:/game/shao/current/c12/supplement.tex` 的 LF2325–2410、3400–3510，完整覆盖要求的 LF2370–2397、3419–3505 及 D/E 定义。整份源 SHA256 为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。

ρ 是 ν0 在 `|z|≤epsilon/(1+x)` 上的真实条件律；m=n−i、μ=∫z、m3=∫|z|³、T=m∫z²、γ=m3/variance(id) 全由同一 ρ 定义。D=(φ(u,v)^m−φ(−u,v)^m)Ξ/2，W=u(φ(u,v)^m+φ(−u,v)^m)Ξ/2，均为原文真实对象。未将条件 μ 设为零，未把方差替换为 raw 二矩，未引入自由乘子或所求 D/W 界作为前提。

唯一常数 C 在所有律、n/i、尺度及频率之前存在。完整 ν0 二矩归一、原均值零、truncationBudget、x/epsilon、h 下界、0<κ≤1/128、L2≥20、1≤κ√L2、L2γ²≤T 和闭低频两不等式全部保留。1≤κ√L2 是保留的 source guard，证明不必使用每个 guard。结论先给全低频 D''，再对 u≠0 的闭锥 `|v|≤|u|/(4h)` 给 D''/W''。所有导数均是标准实参数 `deriv` 的真实嵌套导数。

LF3437 的剩余长度在内部实际导出：m2≤γ² 与 L2γ²≤T=m m2、γ>0 得 L2≤m，因此本合同给 m≥20；实现只将所需较弱 m≥6 传给余幂引理。这不是添加长度前提。i=n/m=0 不被偷偷删除，而是无法同时满足已冻结的 L2γ²≤T 条件。全低频分支含 u=v=0；闭锥端点与频率端点均用非严格不等式保留。

## 全部源码及实际声明覆盖

完整源码 1–593 和既有 log 的全部 28 个 ACTUAL_TYPE 均已阅读；包含 13 个手写 private lemma、1 个 public theorem、14 个 generated theorem，0 个定义值。所有数值、测度、类型参数、假设及量词均保留；仅重复标准实例/投影树压缩，另用 394 个唯一实例别名反向替换验证与原 log 精确复原。无省略号。actual log 的 28 名称、kind、逐项 transitive AX 与 owner JSON 精确相同。

| 声明/源码行 | 独立核对 |
|---|---|
| signed_power_diffs 11–32 | 有限 iid product law 先给真实幂的一/二阶可微性，再以任意 σ 的链式法则处理反射；无低频假定混入可微性。 |
| half_add_bound 35–40；half_sub_bound 42–44 | 复数三角不等式及除以正 2。 |
| odd_even_calculus 46–107 | 先建立全局 D/E/W 一阶身份再求二阶；准确 W''=2E'+uE''，故 2c1+|u|c2。 |
| residual_exponential 110–122 | m≥6、j≤3 给 m≤2(m−j)，结合 m2≤4V 得 m m2≤8(m−j)V；q=exp(−Vu²/32) 的余幂确实 ≤exp(−T u²/256)。 |
| normalized_drift_payment 124–148 | 3/4≤n m2、n|μ|≤1、m≤n 给 (m|μ|)²≤(4/3)T，故 ≤2√T；未假定 μ=0。 |
| polynomialPowerBounds 151–189 | 精确二次求导系数 m(m−1)，项为 (f')²f^(m−2) 与 f''f^(m−1)；自然减法先于 cast，所有余幂保留。 |
| productNorms 191–226 | 真正一/二阶乘积法则，二阶交叉项系数 2；使用真实 q 的零阶 norm≤1。 |
| secondHalf_le 228–231 | 对真实嵌套导数除以 2，再使用 norm/2≤norm；不需要可微性假定的错误反推。 |
| signedSingleBounds 233–264 | σ=±1 时一阶 σ、二阶 σ²，norm 不变；真实 iμ 先减后加，得到 |μ|+m2|u|+m3|v| 及 m2。 |
| odd_third_pos 266–283 | 若真实 m3=0 则 id=0 a.e.，真实方差为零，矛盾。 |
| actualGaussianPowers 286–385 | 低频支付 m3|v|≤m2|u|/128，mL≤2Q，Q²≤2T(1+Tu²)。余幂 j=0/1/2 各自保留，得到 G、2QG、9T(1+Tu²)G；两反射幂都覆盖。 |
| oddProductBound 387–414 | 实际 odd 幂差三行 2/4/18 与 X/X'/X'' 相乘，系数 2 的交叉项保留；100K 吸收为 M+(Q+s)B+(H+sQ+t)A。 |
| public theorem 416–591 | 原条件律桥支付概率、二/三矩、正方差、γ>0、m2≤γ²、γ≤2h、n m2≥3/4、m2≤4V 与 n|μ|≤1。实际 Ξ 全局导数 67γ/3、70hγ/3 与闭锥 C1/|u|、C2/u²逐项使用。K=100+C1+C2 与 C=100K 在全部参数前选择。 |

14 个生成声明逐个核对：residual_exponential._proof_1_1 为剩余长度算术；actualGaussianPowers._proof_1_1 为 m≥2，._proof_1_2/3/4 分别为 0/1/2≤3；polynomialPowerBounds._proof_1_1 为 m−1−1=m−2；public._proof_1_1 为 n−i≤n。public._simp_1_2/3/4 为任意 Zero/OfNat/NeZero 类型下 2/3/4≠0 的命题化简，._simp_1_5 为 NoZeroDivisors 下非零乘积，._simp_1_6 为 IsReduced MonoidWithZero 下非零自然幂，._simp_1_7 为 GroupWithZero 下非零整数幂，._simp_1_8 为 CharZero AddMonoidWithOne 下 cast(n)+1≠0。其实际通用类型全部保留，非额外数学假设。

W'' 分支不是从 odd 差界推得：分别对真实 pΞ、qΞ 用余幂 Gaussian 界与闭锥噪声导数，再用 half-sum 和 W'' 公式。实际末式为 G[9T|u|(1+Tu²)+(4+4K)Q+3K/|u|]，由 C=100K 支付。全局 odd 分支取 s=γ、t=hγ；闭锥 odd 分支取 s=1/|u|、t=1/u²，Q/|u| 的代数转换正确。

## 复用证据与接受边界

服务器 worktree 为 `/root/rivermind-data/shao-lean-20261021/workspaces/common-cone-derivatives-v44`。作者 receipt SHA256 `8a4d62265f23595c7f5d172e8cedd023c7b6d5cb1a53e62d665204ba03d97429`。已读取成功 kernel log `low-derivative-check05.log`（SHA256 `aebc06de36a847f35afc9bce60be9ab61520ed5241c8eabc55dbddad4bc2c39f`），复用其 exit0。line563 仅多余 tactic sequencing lint，未因此改源或重跑。工具链 v4.36.0-rc1、mathlib807d3836、CPU10–13/root-heavy.lock、-M8192/-j4/-DautoImplicit=false 与记录一致。

完整 actual log SHA256 `c3a84622bb829a840e2f2ab4a2a087b63ae764b4ef2e86fe8114a36481f448c8`（373509 字节）；owner audit JSON SHA256 `b6c9eebfb32163f327386b57286073cebf4936f7648bd0c604e9ae9af90e1e9d`。已完整阅读 audit 实现，按 getModuleIdxFor? 精确 owner 遍历所有 private/generated/public，每项 Lean.collectAxioms 为传递闭包；28 项全部通过且仅 propext、Classical.choice、Quot.sound。禁止构造扫描为零、源码零 CR。

已成功独审旧依赖只核对消费接口及源/对象绑定，未重复其证明：OddPower 源 d526459c/对象46f3506b（既有完整独审 common-v25-OddPower-proof-review），Xi cone 源 ebc5d3c7/对象32c4bba9（common-xi-review），global 源7256c6f1/对象999cf81e（common-global-review），以及 SourceTruncationBridge、SourceFourierScale、FullNoise/Derivatives 的既验收接口。完整哈希见 JSON。

本次闭合原低频 actual D'' 的 global/closed-cone 界及 actual (uE)'' 的 closed-cone Gaussian 界。未声称 Region1/2 积分、whole-u IBP、marked Fubini、反演、去平滑、概率贡献或 C1/C2 根完成；无新颖性声明。无待修复问题。下一独审对象为另已冻结的 SourceOddEvenWholeLineIBP，Low 的完成证据无需重放。
