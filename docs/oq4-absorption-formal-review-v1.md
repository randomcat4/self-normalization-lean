# 真实核条件有限吸收独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 给定明确 R3/R4 块输入的真实核有限 D8 桥

LEAN_STATUS: 独立服务器无-o目标检查及完整源动态审计均 exit 0，无警告

JUSTIFICATION: 最终完整签名和证明体满足冻结接口。实际自由系数正性与幂界从全部矩/阈值前提下的 Powers 导出，m≥1 从自然 floor 导出；初段 g≤R 与 f_m≤R 来自真实核，非循环。D2/D3 放大显式使用 g、f 的非负性，smallness 与 H 精确对应旧 DelayedRecurrence。全部4个真实新增常量（包括导入名称下生成的 helper）通过传递公理白名单，禁用项为空。

## 对象与隔离

审查日期：2026-10-21。先只审冻结声明和匿名推导，核对旧已审递推签名并完成 `kernel-absorption-math-review-v1.md`，保留其 MATH_ONLY/LEAN_NOT_RUN 范围，再读最终本单元实现。未读取作者 receipt、作者会话或其他正确性票。没有修改源、冻结声明、共享文件或缓存，没有生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-kernel-absorption-v1.md` | `5ddb3c77ac61f416ffe6d3569f76b20fb7fb05468e97e7e4ebbf742d9d36c767` |
| 所审匿名 `drafts/oq4/absorption/proof.md` 快照 | `a4bacbc0470fb88298fd739c80fab183349b0f0c937c5ec97f3f4eb011bc58a9` |
| 本机 `drafts/oq4/absorption/KernelAbsorption.lean` 与远程 `Shao/OQ4/KernelAbsorption.lean` | `b11d2f68db3581ed61abab670e72234b950df669b379e98f65172f3097f5d168` |
| 已审直接依赖 `KernelRecurrence.lean`，本机/远程一致 | `a4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940` |
| 已审直接依赖 `CosinePowers.lean`，本机/远程一致 | `2f54864af99038bfb3e751d59df9d0f09969ae4aa29cd456c1e0fd8fe6758704` |
| 已审直接依赖 `DelayedRecurrence.lean`，本机/远程一致 | `2b8655db071125a3ee51f1a28cdc06a60b56d9e79ccb930c59f32abb5f73e50b` |

以下行号均为最终 `KernelAbsorption.lean` 的一基行号。

## 完整签名

第12–32行的唯一公开定理 `kernel_finite_absorption` 完整量化 ν 为实数 Borel 概率律，id、y²、|y|³ 的真正 Integrable，均值0、二阶矩1、M≥0、β≤M、h≥1、π(1+M)≤h。N 为自然数且 floor(h²)≤N，z 满足 |z|≤h，A,B,E 均为非负实数。

第21–24行逐字保留闭域上所有 w 的两个独立块输入：真实 `killedAction` 对实际 |cosineResidual| 的 m 步作用≤E/h³，真实 `killedMass` 的 m 步质量≤A principalCosine+B/h。第25–26行 smallness 精确为 `(AR)(ER/h³)(N:ℝ)+BR/h≤1/2`，其中 R=exp(π²)。结论是全部 k≤N 的 `0≤Ghat_k≤H` 以及全部 m≤k≤N 的波动界，H=2(1+AR)R，差值中的 `(k-m:ℕ)` 明确先取自然减法再转实数。独立 `#check` 的完整展开签名与冻结一致，无额外 ρ 正性假设。

## 从真实核与 Powers 导出前提

- 第33–36行的 m,R,f,g 只是实际 floor 和既有核归一化量的局部别名，不是另造任意列再将其视为概率对象。
- 第37–45行由 h≥1 得 h>0、h²≥1，再用 `Nat.lt_floor_add_one` 和自然/实数转换导出 m≥1；没有假设 m>0 或把 floor(h²) 误当 h²。
- 第46–50行调用实际 `cosineCoefficient_large_h_bounds`，显式传入全部三项可积性、均值、二阶矩、M 和阈值，得到 ρ≥3/4 及 ρ<1。实际 principalRate 的定义就是该自由系数，因此 ρ>0 在这里证明，不是额外输入或谱假设。
- 第51–57行从 Powers 的两个 floor 逆幂界取得 ρ^{-(m+1)}≤R、ρ^{-2m}≤R；再由 m≤h²≤2h² 调用统一逆幂界得到 ρ^{-m}≤R。三个指数均正确，未遗漏增量所需额外一个 ρ。
- 第58–59行对所有 k 取得真实 g_k≥0，以及闭域起点的 f_k≥0；f 的非负性没有被错误推广到闭域外的主余弦。

## 初段控制非循环

第60–62行的 hinit 对 k≤N 且 k≤2m，使用已审 `normalizedKernelMass_finite_bound`（原真实 G_k≤1）再接独立的 ρ^{-2m}≤R，给 g_k≤R。此时尚未调用任何全局吸收结论。

第63–67行先从真实 `kernelCosine_bounds` 的 F_m≤G_m 乘严格正倒数，得到 f_m≤g_m；再仅使用 m≤N 和 m≤2m 的已得初段界，得到 f_m≤R。没有将目标 g≤H 或波动结论作为假设，也没有把 f_m≈1 的 B1 输入偷换成已证。

## 两条有限递推与精确系数

第68–77行构造旧定理所需的有限增量：当 m≤k 且 k<N，用真实 D2，ε=E/h³≥0。系数 `(E/h³)ρ^{-(m+1)}` 由幂界放大为 ER/h³，然后第77行明确用 `hg0 (k-m)` 的非负性放大乘积。自然减法位于明确 m≤k 的分支中，k=m 合法。

第78–89行构造旧定理所需的延迟质量递推：将真实 D3 中第二个块常数取 B/h，保持明确输入 hmassblock。系数 Aρ^{-m}≤AR 由 hA 给出，(B/h)ρ^{-m}≤BR/h 由 B≥0、h>0 给出。第88–89行分别用 `hf0 k` 和 `hg0 k` 的非负性放大两项，所以得到准确 `(AR)f_k+(BR/h)g_k`。这一步没有依赖全实轴余弦非负。

## 准确调用旧 DelayedRecurrence

第90–92行实际调用既有 `delayed_recurrence_bound`，参数依次为

```text
f, g, m, N, A*R, B*R/h, E*R/h^3, R
```

依次传入 m≥1、m≤N、四个非负系数、真实 g 非负性、刚导出的初段界、f_m≤R、两条有限递推和原 smallness。独立服务器同时 `#check` 旧定理完整签名，确认其要求的增量范围为 m≤k<N，延迟范围为 k+m≤N，smallness 为 A'DN+B'≤1/2，输出为 `2(1+A')C`；这里代入后与冻结 H 精确相同。

第93–96行只将旧定理的 g 上界与已得 hg0 组合，并保留其波动结论。既有非循环强归纳定理的调用没有新增递归假设。

N=m 时波动只有 k=m，右侧和左侧均0；A/B/E=0 均由非负前提允许，从未对它们取倒数。m≥1 排除了 N=0 的不相容情形，符合冻结的 m≤N，而不是遗漏有效端点。

## 独立服务器证据

通过 `tools/server.py` 共享 broker，在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 激活固定环境后，顺序运行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/KernelAbsorption.lean
{ 最终完整源码 + #check/#print 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，没有生成目标 olean、运行 Lake 构建/更新或获取缓存。目标与源加附录均无警告；broker exit_code=0、stderr 为空，明确输出 `TARGET_AND_DYNAMIC_AUDIT_EXIT=0`。UTC 为 `2026-10-21T11:41:27Z`。远程最终源前后 SHA256 均等于上表值，三个直接依赖也与本机已审版本逐项一致。

动态审计遍历实际 `env.constants.toList` 中全部 `env.getModuleIdxFor? declName = none` 声明，**不作 namespace 或作者根名称筛选**。对每项调用 `Lean.collectAxioms`，任何传递公理不在 `{propext, Classical.choice, Quot.sound}` 中即立即报错。完整最终源在 stdin 中重新核验，并未用作者枚举数量作依据。实际枚举为：

```text
Shao.OQ4.kernel_finite_absorption
Shao.OQ4.kernel_finite_absorption._proof_1_1
Shao.OQ4.kernel_finite_absorption._proof_1_3
Shao.OQ4.principalRate.eq_1
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 4
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
```

包括导入名称下生成的 `principalRate.eq_1`。四项的传递公理均恰为标准三项；主结论另经 `#print axioms` 独立核对相同。没有 sorryAx 或新增公理。

最终远程源禁用项扫描 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 输出：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

本票认证从真实核、完整矩/阈值和两个**未证块输入**到显式有限 D8 界的桥。它确实导出了旧标量递推的前提，并非只将任意标量变量重新命名；但该桥不能反向证明其两个块假设。

**块前提本身、O0、实际 R3/R4、B1 的 f_m→1、终端 Brownian 块、其他 iid 概率估计、4/π、K/Kv、完整 OQ4 与其他全部根组保持 OPEN。** 普通自由 ρ 的正性只在已保留的矩类和 h 阈值下使用，不赋予杀死核谱特征值解释。
