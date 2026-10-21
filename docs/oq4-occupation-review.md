# 有限占据层支付独立审查 v1

STATUS: CORRECT

SCOPE: FROZEN_FINITE_INTERFACE

LEAN_STATUS: LEAN_FULLY_CHECKED

JUSTIFICATION: 匿名数学推导、最终完整签名和证明体未发现关键缺口；主有限支付及源所需非负闭顶层推论均忠实覆盖约定范围。首阶段仅数学/签名审查的历史记录保留如下；限制解除后，已对同一最终哈希完成独立无-o服务器目标检查、全部四个新增常量的动态传递公理审计及禁用项扫描，全部通过。

## 审查对象与版本

审查日期：2026-10-21；最终独立服务器认证完成于 `2026-10-21T09:33:38Z`。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-occupation-payment-v1.md` | `3d467fed3dfdfa2c6fe02f3c5fa6f0535cecef2831853a31179ce3c3bcbbff6d` |
| 首阶段所审匿名 `drafts/oq4/occupation/proof.md` 快照 | `f259d097f23aca611e8d70b6de021713bb273b3d32ec6817d14a978ed9079867` |
| 本机最终 `drafts/oq4/occupation/OccupationPayment.lean` | `3ed77e585a0a687b471d46e004872d35c18d7181388a7828c34e83085bd094d9` |
| 远程最终同名目标（两阶段一致） | `3ed77e585a0a687b471d46e004872d35c18d7181388a7828c34e83085bd094d9` |

远程路径：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/OccupationPayment.lean`。以下 Lean 行号均指上述最终源。

审查者独立读取冻结声明、新匿名推导和本机最终代码；未读取作者 receipt、作者会话或其他票，没有修改实现、前提、公共定义或缓存。作者此前目标通过的自述未作为本票的独立机械认证证据。唯一写入为本报告。

## 主有限支付：量词与陈述

STATUS: CORRECT

JUSTIFICATION:

1. 冻结第 5–13 行与 Lean 第 28–35 行一致：任意可测空间上的有限测度 `μ`，可测 `d`，仅要求 `F` 可积，任意 `L:ℕ`、`C≥0`，且只对 `j<L` 要求 `a j≥0`。没有概率归一化、测度非零、`L>0`、`F≥0`、`F` 有界或无原子条件。
2. 第 20–21 行的 `boundaryLayer d j` 正是左闭右开层 `j≤d<j+1`，两个端点方向与冻结一致。第 23–25 行的可测性由两个可测不等式集合相交得到，只用原始的 `Measurable d`。
3. 第 32 行的深度范围是 `∀ᵐ ω, 0≤d ω ∧ d ω<(L:ℝ)`，没有改成逐点深度界；第 33 行也是几乎处处同时满足所有有效层的上界，没有把它替换成对所有样本点的条件。层质量假设第 34 行完整保留为独立输入。
4. 第 35 行准确返回 `∫F≤C∑_{j<L}(j+1)a_j`。`μ.real(E_j)` 是有限集合质量的实值表示；由于 `μ` 有限，每个 `μ(E_j)` 都有限，不会出现把无限测度经 `toReal` 默认变零的语义漏洞。

## 主有限支付：完整数学理由

1. 匿名证明第 11–15 行、Lean 第 36–43 行构造 `G=∑_{j<L}a_j 1_{E_j}`。每个常值函数在有限测度下可积，乘可测层的指标后仍可积，有限和因此可积。该构造不要求 `F` 有界，也不要求 `d` 的原几乎处处范围在零集上成立。
2. 第 44–52 行只在两个给定满测集的交上选择 `j=⌊d ω⌋₊`。此处已知 `d ω≥0`，所以自然数下取整满足 `(j:ℝ)≤d ω<(j:ℝ)+1`；再由 `d ω<L` 得 `j<L`。自然数转实数的严格序没有弱化成非严格序，没有允许无效层索引。
3. 第 53–66 行对全部求和指标证明指标项非负，选中项因 `ω∈E_j` 恰等于 `a_j`，于是 `F ω≤a_j≤G ω`。这里只比较 `F` 与上界，不使用 `F` 的非负性。`F` 可以向下无界；仅其可积性是积分步骤所需。
4. 第 68 行使用 `integral_mono_ae hF hGI hupper`。两个被积函数均已可积，比较也恰为几乎处处比较，没有将可积性或零测例外集忽略。
5. 第 69–75 行交换有限和与积分，每一项的可积性由同一 `htermI` 提供；指标常数积分为真实有限层质量乘 `a_j`。第 76–85 行逐层用原始质量输入，并且只乘非负的 `a_j`，再用有限和分配律提取 `C`。`C≥0` 虽非这一步代数比较的必要条件，仍完整保留于签名。

以上给出完整非循环推导。没有证明或假定未写明的统一占据估计。

## 退化情形和层端点

1. **L=0。** 不加入 `L>0`。假设 `0≤d<0` 几乎处处意味着其不可能事件的补集即全空间为零测，故 `μ=0`。因此实际符合全部输入时 `∫F=0`，空和也为零。选层证明只在这个满测且空的好集合上进行，局部前提不一致时推出有效索引不会额外限制定理。
2. **μ=0。** 深度和层上界的几乎处处前提可为真而不限制零集代表元；全部积分及层质量为零。一般 `L` 下目标右侧由 `C≥0`、`a_j≥0` 为非负，不要求它等于零。因此结论仍成立。
3. **整数深度和原子。** 若 `d=r` 为非负整数，则选择 `j=r`。该点不属于上一层的右端，却属于当前层的左端；没有删去层界上的原子。证明不需要层无原子或密度，也不必通过忽略边界来获得分层覆盖。
4. **零集上的坏深度或层值。** `hd.and hcap` 的选择限制始终在满测集内，代码没有把自然数下取整的非负性要求用于原假设以外的样本点。

## 闭顶层推论

STATUS: CORRECT

JUSTIFICATION:

1. 源所需的非负闭深度上界由 Lean 第 88–95 行给出，显式保留 `h≥0`、几乎处处 `0≤d≤h`，并把所有层的范围一致替换成 `j<⌊h⌋₊+1`。主有限支付本身没有新增任何 `h` 条件。
2. 第 96–99 行使用精确不等式 `h<⌊h⌋₊+1`，故仅以几乎处处 `d≤h` 推出 `d<⌊h⌋₊+1`，然后合法调用主定理。深度前提依然是几乎处处，没有在推论中改为逐点有界。
3. 若 `h=q` 为非负整数，则 `L=q+1`，最高有效层索引为 `q`，端点 `d=h=q` 落在 `E_q`，不会被 `range q` 漏掉。若 `h=0`，仍有 `L=1`、`d=0` 的层 `E_0`，并非错误地使用空分层。非整数 `h` 的部分顶层同样覆盖 `d=h`。
4. 该推论仅是主有限接口的参数实例化；没有新增 `F` 有界、层无原子或概率生存前提。

## 层质量输入与根范围

`hmass` 是冻结的每层质量输入，Lean 第 34 行及匿名证明第 43 行均明确使用它，并未证明它。模块头部第 9–11 行也明确表明这是 O0/OC 到积分支付的条件性确定性桥，不是 killed 随机游走占据定理。

应用若使用带能量权重的测度，仍需另证该测度有限、权重可积及 O2；本接口没有自动提供这些性质。与 R6 或原缺陷卷积的具体连接，以及后续 R3，均不能从本票直接宣布完成。

## 首阶段只读探测与历史范围

首阶段按当时服务器操作限制，完整数学/声明审查后只发出一次 `tools/server.py` 请求：

```text
action: exec
command: sha256sum /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/Shao/OQ4/OccupationPayment.lean
timeout: 15
```

结果正常返回：远程 `exit_code=0`、`stderr` 为空、目标 SHA256 为表中 `3ed77e58...bd094d9`。这表明该次只读请求成功；该探测本身不是编译或公理审计。首阶段没有重试、绕过 broker、改动服务或生成模块 olean。

**首阶段未执行独立目标编译、全部新常量动态传递公理审计和机械禁用项扫描。** 当时范围明确为 `MATH_ONLY_AND_SIGNATURE_REVIEW / LEAN_NOT_RUN`；静态阅读和作者检查自述都没有被当作最终形式认证。该历史状态保留，不追溯改写成首阶段已经运行 Lean。

## 限制解除后的独立最终机械认证

协调者明确解除首阶段限制后，对同一最终源执行如下目标检查；前后远程 SHA256 均为 `3ed77e585a0a687b471d46e004872d35c18d7181388a7828c34e83085bd094d9`，本机最终源及冻结声明哈希也再次核对一致。没有代码修改或前提漂移。

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/OccupationPayment.lean
```

使用项目已核验的钉死环境 Lean `4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。该命令没有 `-o`，目标检查退出 `0`、无警告。所有 Lean 都在指定服务器执行，没有本机 Lean、缓存下载、共享缓存改写或作者模块 olean 的生成操作。

随后将最终目标源、两个支付定理的 `#print axioms` 及动态审计附录经标准输入送入服务器 `taskset -c 0-3 lake env lean --stdin`。动态审计遍历实际环境常量，筛选 `env.getModuleIdxFor?` 为 `none` 且属 `Shao.OQ4` 的当前模块声明，对每项调用 `Lean.collectAxioms`，逐项检查公理白名单。没有借用作者的审计回执。

实际枚举恰为全部四个新增常量，没有遗漏的生成辅助声明：

```text
NEW_DECL Shao.OQ4.boundaryLayer: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.measurableSet_boundaryLayer: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.finite_occupation_payment: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.finite_occupation_payment_of_le: [propext, Classical.choice, Quot.sound]
NEW_DECL_COUNT 4
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
PROHIBITED_TOKEN_HITS []
```

两个主定理的独立 `#print axioms` 输出同样仅含 `[propext, Classical.choice, Quot.sound]`。机械词项扫描覆盖作者目标源的 `sorry|admit|axiom|unsafe|native_decide`，结果为空。

本阶段 `tools/server.py` 正常返回远程 `exit_code=0`、空 `stderr`，没有失败重放或旁路 broker。结合前面的完整数学和签名审查，最终冻结接口可记为 `LEAN_FULLY_CHECKED`。

## 根状态

**冻结的主有限支付及非负闭顶层推论均为 CORRECT / LEAN_FULLY_CHECKED。O0/OC 质量输入、R3、K、Kv、完整 OQ4 以及全部其他根组保持 OPEN。**
