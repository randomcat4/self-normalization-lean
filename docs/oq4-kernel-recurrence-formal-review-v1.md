# 条件核递推与精确归一化独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 实际杀死核上的条件有限 D0–D4

LEAN_STATUS: 独立服务器无-o目标检查及源加动态审计附录均 exit 0，无警告

JUSTIFICATION: 最终源的全部签名和证明体与冻结接口一致。主余弦的非负性只在闭域使用，精确缺陷不需要矩条件；R3/R4 块界是显式假设。自然减法合法，归一化保留 ερ^{-(m+1)}、Aρ^{-m}、Bρ^{-m}，D4 仅给有限范围的实际幂界。实际枚举的 37 个新增常量全部通过传递公理白名单，禁用项扫描为空。

## 审查对象与隔离

审查日期：2026-10-21。先独立审匿名数学推导并写 `kernel-recurrence-math-review-v1.md`，再读取实现；保留该票的 MATH_ONLY/LEAN_NOT_RUN 历史范围。本次未读取作者 receipt、作者会话或其他正确性票，没有修改实现、冻结声明、共享文件、缓存或目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-kernel-recurrence-v1.md` | `6fec7c4c9c6475fac7beff73e825311eb1ea230396d18df4097f97e81244933a` |
| 所审匿名 `drafts/oq4/recurrence/kernel-proof.md` 快照 | `21efae0981167ac245422edcd126fee04e8252979501974ef078a19c596d8671` |
| 本机 `drafts/oq4/recurrence/KernelRecurrence.lean` 与远程 `Shao/OQ4/KernelRecurrence.lean` | `a4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940` |
| 已审直接依赖 `KilledIteration.lean`，本机/远程一致 | `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5` |
| 已审直接依赖 `AveragedResidual.lean`，本机/远程一致 | `ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2` |

以下行号均为本次最终 `KernelRecurrence.lean` 的一基行号。

## 全部冻结接口与证明体

### 实际对象、闭域正性与可积性

- 第15–29行定义实际主余弦、普通未杀死的余弦系数 ρ、真实核作用 F，以及乘 `(ρ^n)⁻¹` 的两个归一化量。ρ 的定义不是杀死核特征值；F 直接使用已审 `killedAction`，没有另造抽象标量列。ν 的唯一测度类假设是标准实数 Borel 概率律，没有中心、方差或矩前提。
- 第31–46行给全局 Borel、绝对值≤1，并在 h>0、|w|≤h 时由 `|(π/(2h))w|≤π/2` 证明非负。闭端点包含在内；没有除以端点余弦。
- 第48–61行给任意 n∈ℕ、闭域起点 z 的 `0≤F_n(z)≤G_n(z)≤1`。非负性使用 `killedIterKernel_ae_support ... hz`，其零步情形需要并保留起点条件；上界来自真实有限核上的绝对值质量支配。φ 是全局有界 Borel，故所有这些积分真实可积，而非依赖不可积时的积分默认值。
- 第63–94行把 `U_1φ` 与旧 `Kcos` 精确绑定；r 是已定义的 `cosineResidual`，全局可测且 `|r|≤1+|ρ|`，并明确导出每个真实幂核行上 r 和 |r| 的 Integrable。普通 ρ 的被积函数同样是概率律下绝对值≤1 的 Borel 余弦，实际可积。此处不需要任何矩条件。

### 精确缺陷与 D0

- 第97–116行的 `kernelCosine_defect` 对所有实 h,z 和自然 k 给出 `F_{k+1}-ρF_k=U_k r`。证明先为 φ 和 `U_1φ=Kcos` 建立真实行可积性，再使用已审半群以及 `integral_sub`、`integral_const_mul`。不是把特征方程作为前提。
- 第119–145行的 `kernelCosine_delayed_defect` 明确量化 m,k∈ℕ、m≤k、闭域 z、ε≥0，以及所有闭域 w 的独立块输入 `U_m|r|(w)≤ε`。先用绝对值支配，再用 `Nat.sub_add_cancel hmk` 把 k 写为 `(k-m)+m`。内层作用的参数可测性和全局有界性都传给 `killedAction_mono_closed`，外层是真实可积的有限核积分。比较只在闭域进行，积分常数产生精确 `εG_{k-m}`。
- k=m 时外层为零步 Dirac_z，hz 仍足以使用块假设；m=0 时恒等式和比较仍适用。没有遗漏零块或要求 k>m。第119行的 `_hh` 是保留的 h>0 接口前提，证明其实不依赖它，并未增加隐藏限制。

### D1

第148–174行的 `kernelMass_block` 将 A,B≥0 和闭域块输入 `G_m(w)≤Aφ(w)+B` 保留为显式假设，对所有自然 m,k 导出 `G_{k+m}≤AF_k+BG_k`。右侧测试函数在全实轴绝对值≤A+B，故真实可积；不要求其在域外非负。半群内层 G_m 的可测性、有界性及闭域比较均显式传入，最后的积分加法使用 `hφ.const_mul A` 和有限行上的 `integrable_const B`。k=0、m=0 都在签名内，没有把 R4 块输入说成该模块已证的概率结论。

### D2/D3 的精确因子

- 第176–182行先在明确 `0<ρ` 下证明归一化差分恒等式，倒数非零只来自该假设。
- 第185–203行在 D0 的全部假设下，乘严格正的 `(ρ^{k+1})⁻¹`。第200行用 m≤k 证明自然数等式 `k+1=(m+1)+(k-m)`，再精确分拆幂，右侧恰为 `[ε(ρ^{m+1})⁻¹]Ghat_{k-m}`。m=0 时保留 ε/ρ，k=m 时保留 Ghat_0；没有丢失额外一个 ρ。
- 第206–221行在 D1 的全部假设下乘正倒数并用 `pow_add`，得到分别为 `A(ρ^m)⁻¹`、`B(ρ^m)⁻¹` 的两个系数。D2/D3 不需要 ρ≤1，也没有将这些系数替换成未证的统一常数。
- `hρ` 是普通余弦系数正性的明确外部输入。没有从任意概率律、从未使用的矩条件，或从杀死核特征值解释推断其成立。

### D4

第223–241行分别给 Ghat 的所有起点非负性、Fhat 的闭域起点非负性，以及在明确 `0<ρ≤1`、n≤2m 下的 `Ghat_n≤(ρ^{2m})⁻¹`。后一个结论甚至对任意实起点有效，因为只用 G_n≤1。幂比较方向为 `ρ^{2m}≤ρ^n`，再对正数倒数反向，正确。

n=0 时真实零步质量为1；m=0 且 n≤2m 时只剩 n=0，上界为1。D4 保留实际 ρ、m；没有得到随 h 或律类统一的界，也没有给 B1 的初值极限。归一化从未除以 F、G、A、B、ε 或主余弦。

## 独立服务器证据

通过 `tools/server.py` 的共享 broker，在指定远程工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 运行。先激活既定环境，再顺序执行两个 Lean 进程，均限制 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/KernelRecurrence.lean
{ 最终源码 + #check/#print 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，未生成目标 olean，未运行 Lake 构建/更新或缓存获取。broker 总 exit_code=0，stderr 为空；目标检查和动态附录无警告。审计末尾明确输出 `TARGET_AND_DYNAMIC_AUDIT_EXIT=0`，UTC 时间为 `2026-10-21T10:58:58Z`。远程目标的前后 SHA256 均等于上表最终值；两个直接依赖也独立核对哈希。

在实际源环境中 `#check` 复核了闭域 F/G 界、r/|r| 可积性、精确缺陷、D0、D1、D2、D3、D4 的展开签名，与上述量词逐项一致；不存在隐含额外矩类假设或块结论漂移。

动态审计遍历实际 `env.constants.toList`，筛选 `env.getModuleIdxFor? declName = none` 且名称含当前 `Shao.OQ4.` 命名空间的声明，对每一项调用 `Lean.collectAxioms`，并对非白名单公理立即报错。这里编译的是完整最终源码，不是仅 import 作者 olean。源码的23个显式声明均被实际枚举，连同14个本次生成辅助声明，总计：

```text
NEW_DECL_COUNT 37
```

23个显式声明为五个定义与十八个定理：

```text
principalCosine
principalRate
kernelCosine
normalizedKernelCosine
normalizedKernelMass
principalCosine_measurable
principalCosine_abs_le_one
principalCosine_nonneg
kernelCosine_measurable
kernelCosine_bounds
principalKcos_eq_action
principalResidual_measurable
principalResidual_bound
principalResidual_integrable
kernelCosine_defect
kernelCosine_delayed_defect
kernelMass_block
normalizedKernelCosine_step
normalizedKernelCosine_delayed
normalizedKernelMass_block
normalizedKernelMass_nonneg
normalizedKernelCosine_nonneg
normalizedKernelMass_finite_bound
```

14个生成声明（同样全部实际审计，包括对导入名称生成的辅助声明）：

```text
principalCosine._proof_1
principalCosine.eq_1
kernelCosine.eq_1
kernelCosine.congr_simp
normalizedKernelMass.eq_1
killedAction.congr_simp
normalizedKernelCosine_delayed._proof_1_1
normalizedKernelCosine_step._simp_1_2
normalizedKernelCosine_step._simp_1_3
normalizedKernelCosine_step._simp_1_4
normalizedKernelCosine_step._simp_1_5
normalizedKernelCosine_step._simp_1_6
normalizedKernelCosine_step._simp_1_7
normalizedKernelCosine_step._simp_1_8
```

全部37项的传递公理集合均包含于 `{propext, Classical.choice, Quot.sound}`。所有23个显式声明均为该三项集合；生成辅助声明允许真子集。另对 D0/D1/D2/D3/D4 主结论逐项执行了 `#print axioms`，同样只有上述三项。没有 `sorryAx` 或新增公理。

为关闭命名空间筛选可能漏掉辅助声明的完整性疑问，另顺序运行一次同源 `--stdin` 动态审计，完全去掉名称筛选，对所有 `getModuleIdxFor? = none` 声明收集传递公理，并检测命名空间外的新名称。结果没有任何外部名称，`ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 37`、`ALL_NEW_AUDIT_EXIT=0`，stderr 为空、无警告；UTC 为 `2026-10-21T11:01:39Z`，目标 SHA 仍为最终冻结值。因此上面的37项确为该源全部实际新增常量，不只是一个名称子集。

最终远程源扫描 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 得到：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

本票认证的只是实际杀死核上、给定两个闭域块输入以及所需 ρ 假设后的有限 D0–D4 代数与精确归一化。没有从条件推导倒推 R3/R4 已证，没有将普通 ρ 称为杀死核特征值。

**实际 R3/R4 概率输入、O0、矩类下 ρ 正性、归一化块因子的一致控制、iid 路径表示、B1、Brownian 输入、长时间极限、4/π、K/Kv、完整 OQ4 及其他全部根组保持 OPEN。**
