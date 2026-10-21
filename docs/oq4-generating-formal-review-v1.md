# Laplace 生成函数 S2–S3 独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 明确 S1 序列下界与 SP 型等式下的确定性解析链

LEAN_STATUS: 独立服务器无-o目标检查及完整源动态审计均 exit 0，无警告

JUSTIFICATION: 最终源完整证明 W/G 的实际 Summable、有限调和界、严格 k>J 的非负幂尾真实可求和及 S2 安全常数。S3 保留全区间上的精确 SP 型等式前提，系数提取使用含 a0 的真实有限前缀、正确 Antitone 方向、m≥1 和正分母，常数恰为 sqrt(2)exp(2+3C)。全部25个实际新增常量通过传递公理白名单，禁用项为空。

## 对象与隔离

审查日期：2026-10-21。先仅阅读冻结声明和匿名推导，完成并冻结 `laplace-generating-math-review-v1.md` 后，才读取最终实现。数学票冻结 SHA256 为 `e8f6f6fac05be4bb8626761de257b175fddaef18c784569b30341da8c8418f56`，未因形式检查改写。未读作者 receipt、summary、declarations、作者会话或其他审稿票。没有修改源、冻结声明、公共文件、Git 或缓存，没有生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-laplace-generating-v1.md` | `a6fddda60883208834258b774b8f77455973584c468afabac76cd8c885eae577` |
| 所审匿名 `drafts/oq4/generating/proof.md` 快照 | `1484b50453d9df0f9879848f8fe4f74965c316812b283ab417a7e82d37dd4099` |
| 本机 `drafts/oq4/generating/LaplaceGenerating.lean` 与远程 `Shao/OQ4/LaplaceGenerating.lean` | `eab53afb87248fc0f9b94ddf84e986eedae51f2446e9b7ea176e517c4a861ed8` |
| 指定服务器直接 mathlib 依赖 `Analysis/SpecialFunctions/Log/Deriv.lean` | `09eb4a39077348d27168fdfaf02db61120690e1b87fc5d6c42fdd0c49aad994e` |

以下行号均为最终 `LaplaceGenerating.lean` 的一基行号。

## 实际定义、量词与 Summable

第12–15行准确使用真实 tsum 定义 `W=Σ_{n≥0}s^(n+1)A(n+1)/(n+1)` 与 `G=Σ_{j≥0}s^j a_j`。W 的全部输入只涉及 A 的正自然指标；没有对无关 A0 加条件。G 真正包括 a0。

第17–30行在 0<s<1 和所有 k≥1 的 0≤A_k≤1 下，使用几何级数的实际 Summable 与逐项范数支配证明 W 真正可求和。源明确证明项非负、范数≤s^(n+1)/(n+1)≤s^(n+1)≤s^n；这是绝对控制，没有依赖 tsum 的默认0。

第32–38行对所有自然 j≥0 的 0≤a_j≤1 同样以范数≤s^j证明 G 真正可和。后续主结论保留这些前提；系数提取又实际调用该 Summable 处理有限前缀。签名没有隐藏的概率 law、矩或额外求和假设。

## 内部调和与严格幂尾证明

第150–169行从正 x 的真实对数不等式 `one_sub_inv_le_log_of_pos ((x+1)/x)` 及 log商公式证明 `1/(x+1)≤log(x+1)-log x`，再以有限归纳建立 H_J≤1+log J。辅助定理还合法处理 J=0（H0=0，mathlib log0=0）；主 S2 中 J≥1，不对0取倒数。

第171–194行对 x>0，以 a=sqrt(x)、b=sqrt(x+1) 的正性、a≤b、(a+b)(b-a)=1 和 a(a+b)≤2b²，经过正分母交叉相乘，证明下一项倒三次幂根号的望远镜上界。

第196–209行在 J≥1 下对 N 归纳，左侧精确索引 n+J+1（n∈range N），即 k=J+1至J+N，右侧为 `2(1/sqrt(J)-1/sqrt(N+J))`。N=0 和 J=1 都包含，没有把 k=J 混入严格尾。

第211–224行逐项证明幂尾非负，并由每个真实有限前缀≤2/sqrt(J)，调用 `summable_of_sum_range_le` 真正建立 Summable；再用部分和趋于 tsum 得完整尾和上界。这个非负对象是幂尾，后面有符号差级数 D 不被错误假设为非负。源没有借未缓存积分比较模块来跳过这一步。

## S2：floor、首尾分割与安全常数

第227–231行完整量化 L≥1、C≥0、A 的正自然有界条件、所有正自然 k 的 S1 下界，以及 0<s<1，结论恰为冻结 `W≥-(1/2)log(1-s)-log L-(1+3C)`。

第232–250行内部取 J=floor(L²)，由 L≥1 得 J≥1；floor 给 J≤L²<J+1。联合 J≥1 得 L²≤2J，因此 J≥L²/2。代码直接以这些不等式和根号平方计算安全 `2L/sqrt(J)≤3`，并将调和界放宽为1+2log L。没有将 J 引入定理签名，也没有暗改 L 阈值；L=1 时 J=1。

第251–257行先实际取得 W 的 Summable。对数部分用钉死 mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`，实际 HasSum 值为 -log(1-s)；独立服务器核对了该外部完整签名。源将其乘1/2后减去真实 W 的 HasSum，构造有符号 D 的真实 HasSum，而非形式级数差。

第258–274行的首段 n∈range J 对应 k=1至J。先丢掉非负 W 项，再用 s^k≤1，所以即使 D_k 为负，首段上界仍正确。第275–296行对 D(n+J) 使用 k=n+J+1 的 S1，先乘非负 s^k，再用非负 CL/sqrt(k) 支付 s^k≤1；所得主项是 CL/(k sqrt(k))，严格 k>J。

第297–306行同时具备真实 D 尾的 Summable 和真实主界幂尾的 Summable，才用 tsum 单调比较与标量乘法，得到尾≤3C。第307–309行用真实有符号级数的首段+尾 tsum 恒等式和其 HasSum 值，得到冻结 S2；实际上初段代价1/2，最终安全放宽到1。C=0、J=1 不需要额外分支或除以 C。

## S3 明确保留精确 SP 型等式

第68–87行的标量辅助引理只从给定 W 下界与明确 `G=(1-s)⁻¹exp(-W)` 推出 S3。hL>0、s<1 给正的 L、1-s、sqrt(1-s)，从而 exp/log 与倒数计算全部合法，精确化简为 `exp(1+3C)L/sqrt(1-s)`。

第312–321行主接口保留 L≥1、C≥0、A 的完整正时刻条件、a 的全部自然有界性、Antitone a，以及**每个**0<s<1上的精确 SP 型等式。源明确取得实际 G 可和性，然后调用 S2 和此点处的显示 hSP。Antitone 在该上界步骤不需要但仍保留冻结完整接口。没有把 SP 当作已证明 law 或新增公理。

## m≥1 的有限前缀与系数提取

第40–65行从自然 m≥1 得正实 m 与 0<1/m≤1，使用真实 exp(x)≥1+x 及 x(1-x)≥0，证明 `0<exp(-1/m)<1` 和 `1-exp(-1/m)≥1/(2m)`。m=1 合法，未混入默认除0。

第90–148行的系数引理明确要求 a 有界非负、Antitone a、非负 B，以及对每个0<s<1的真实 G 上界。选择 s=exp(-1/m)，第102–106行利用正 m 证明 s^m=exp(-1)。第107行取得 G 的真实 Summable。

第108–118行使用 `range m`，明确包含 j=0。j<m 蕴含 j≤m，`hanti hjm` 给 **a_m≤a_j**，幂比较给 s^m≤s^j，并以 a_m≥0、s^j≥0 正确相乘。因此 m 个前缀项每个≥s^m a_m，且整个前缀≤真实 G。没有删除 a0 或反转 Antitone。

第119–148行只除以正 m，并乘 exp(1)。由 gap 和正平方根得到 `1/sqrt(1-s)≤sqrt(2m)`，乘非负 B 后接 G 界，再以 m>0 的根号恒等式精确化为 `sqrt(2)exp(1)B/sqrt(m)`。

第324–341行保留全部 S1/SP/有界/非增前提，取 B=exp(1+3C)L≥0，实际供应上面的 G 界，并以指数加法合并常数，得到准确 `sqrt(2)exp(2+3C)L/sqrt(m)`。m=1、L=1、C=0 均在完整签名内，没有对允许为0的序列项或 C 取倒数。

## 独立服务器证据

先经共享 broker 做有界只读健康探测，实际源哈希为上表固定值，UTC `2026-10-21T14:48:55Z`、exit0、stderr为空。本轮没有运输拒绝、不确定操作、重放或 direct 备用调用。

随后在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`，脚本使用 `set -e`、`set -o pipefail`，先 activate 后 cd，顺序执行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/LaplaceGenerating.lean
{ 最终完整源码 + #print/#check 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，不生成目标 olean，不构建/更新 Lake 或获取缓存。目标与完整源审计均无警告，broker exit_code=0、stderr为空，分别输出 `TARGET_CHECK_EXIT=0` 和 `SOURCE_DYNAMIC_AUDIT_EXIT=0`；UTC 为 `2026-10-21T14:50:11Z`。最终源前后 SHA256 均为eab53afb全值。

全部15个显式声明的完整类型/定义均实际 `#check/#print` 核对。动态遍历实际 `env.constants.toList` 中**全部** `env.getModuleIdxFor? declName = none` 的声明，无 namespace/root 名称筛选；对每项 collectAxioms，仅允许 `{propext, Classical.choice, Quot.sound}`，否则立即报错。完整当前源真实经 stdin 检查，结果为：

```text
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 25
SOURCE_DYNAMIC_AUDIT_EXIT=0
```

实际15个显式声明全部枚举：

```text
Shao.OQ4.laplaceW
Shao.OQ4.laplaceG
Shao.OQ4.summable_laplaceW
Shao.OQ4.summable_laplaceG
Shao.OQ4.exp_neg_reciprocal_gap
Shao.OQ4.generating_upper_of_W_lower
Shao.OQ4.antitone_coefficient_bound_of_generating_bound
Shao.OQ4.reciprocal_log_step
Shao.OQ4.finite_harmonic_log_bound
Shao.OQ4.sqrt_reciprocal_step
Shao.OQ4.finite_sqrt_tail_bound
Shao.OQ4.reciprocal_sqrt_tail
Shao.OQ4.laplaceW_lower_bound
Shao.OQ4.laplaceG_upper_bound
Shao.OQ4.laplace_coefficient_bound
```

10个实际生成辅助声明也全部审计：

```text
Shao.OQ4.summable_laplaceW._proof_1_1
Shao.OQ4.sqrt_reciprocal_step._simp_1_1
Shao.OQ4.sqrt_reciprocal_step._simp_1_2
Shao.OQ4.sqrt_reciprocal_step._simp_1_3
Shao.OQ4.sqrt_reciprocal_step._simp_1_4
Shao.OQ4.sqrt_reciprocal_step._simp_1_5
Shao.OQ4.sqrt_reciprocal_step._simp_1_6
Shao.OQ4.sqrt_reciprocal_step._simp_1_7
Shao.OQ4.laplaceW_lower_bound._proof_1_1
Shao.OQ4.laplaceW_lower_bound._proof_1_2
```

25项传递公理均为标准白名单子集；15项显式声明使用标准三项。真实幂尾 Summable/全和界、S2、S3 和系数主界另逐项独立 `#print axioms`，同样只有标准三项。没有 sorryAx 或新增公理。

最终远程源禁用项正则 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 扫描输出：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

这里只证明确定性解析链。SP 型等式保持明确假设；A/a 的实际概率实例、a 的 law 非增性及后续 Markov 支付仍须单独证明。若以后取 C=1+C_BE 并另乘 e，常数代数上为 sqrt(2)exp(6+3C_BE)，本源不因此提前认证实际生存结论。

**SP、BE、实际随机游走 law、无条件 S/AC/O0、B1、长期 K/Kv、4/π、完整 OQ4 及其他全部根组保持 OPEN。**
