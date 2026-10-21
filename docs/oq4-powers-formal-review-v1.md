# 自由余弦系数幂与对数误差独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 显式矩类与 h 阈值下的实际自由系数估计

LEAN_STATUS: 独立服务器无-o目标检查与完整源码动态审计均 exit 0，无警告

JUSTIFICATION: 最终源的11个显式定理逐项对应冻结目标和匿名推导；实际系数部分完整保留真正矩可积性、均值、二阶矩、β≤M 以及两个 h 阈值。双边界、严格正性、逆幂、两个 floor 界和安全对数常数均正确。无名称筛选动态枚举出的全部25个新增常量均通过传递公理白名单，禁用项扫描为空。

## 对象与隔离

审查日期：2026-10-21。先只读取冻结声明和匿名推导，完成并保留 `cosine-powers-math-review-v1.md` 的 MATH_ONLY/LEAN_NOT_RUN 结论，再读取最终实现。未读取作者 receipt、作者会话或其他审稿票；没有修改源、冻结声明、共享文件或缓存，没有生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-cosine-powers-v1.md` | `7df498dcae4dc1e9510765a9bb6af9e1e5173ca29257df9d6c700ea9226174c7` |
| 所审匿名 `drafts/oq4/powers/proof.md` 快照 | `8f4dbbb8a9afc484283ca0bb3054a3aa89171d2eb867f443612e4da002430a10` |
| 本机 `drafts/oq4/powers/CosinePowers.lean` 与远程 `Shao/OQ4/CosinePowers.lean` | `2f54864af99038bfb3e751d59df9d0f09969ae4aa29cd456c1e0fd8fe6758704` |
| 已审直接依赖 `CosineCoefficients.lean`，本机/远程一致 | `8fa6f094c330a8006c5664f8912cafd035524cc461df95e81446d2384a46c104` |
| 已审直接依赖 `KilledCosine.lean`，本机/远程一致 | `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8` |

以下行号指本次最终 `CosinePowers.lean` 的一基行号。

## 签名与语义

第116–124行的实际系数区明确量化 ν 为实数 Borel 概率测度，hId、hSq、hCube 为 id、y²、|y|³ 的真实 Integrable，均值积分为0，二阶矩积分为1，M≥0、β≤M、1≤h、π(1+M)≤h。`include` 保证这些变量进入所有主结论的完整签名；独立 `#check` 已对全部11项展开核验。

实际 ρ 始终是现有 `cosineCoefficient ν (π/(2h))`。其定义位于已审 `KilledCosine.lean` 第20–21行，是未杀死的自由余弦期望。ν 为概率律，余弦全局 Borel 且绝对值≤1，因而该积分真实可积。没有新造抽象系数替代实际积分，也没有将它定义成杀死核特征值。

`cosineCoefficient_large_h_remainder` 第126行只省略 hM 和 hlarge；这只是一个在较弱前提下已成立的辅助余项结论。它仍保留三项真正可积性、均值、二阶矩、β≤M 与 h≥1。冻结所需的主界和所有后续结论均保留完整前提，未发生前提漂移。

## 逐项证明核对

| 冻结接口 | 最终源 | 独立核查 |
|---|---|---|
| 实际三阶余项绑定 | 第127–136行 | 用已审 `cosine_coefficients_h_bound` 对随机变量 id 的实例，取余弦分量，再由 β≤M 与正分母放大到 M。既有定理的量词、真实矩和1/48常数精确匹配。 |
| 双边界及 3/4≤ρ<1 | 第17–42行、第138–144行 | π(1+M)≤h 与 M≥0 给 π≤h、πM≤h。q=π²/h² 严格正且≤1；余项等于 `(q/48)(πM/h)`，故≤q/48。绝对值双边及 q>0、q≤1 给冻结四项结论，严格上界有正 q 支撑。 |
| 每个自然 n 的逆幂 | 第44–65行、第146–150行 | 先由 ρ≥3/4 得 ρ>0，再用 `Real.one_sub_inv_le_log_of_pos` 及 `(1-ρ)/ρ≤2(1-ρ)` 得 `-logρ≤π²/(2h²)`。指数恒等式使用正实数的 `exp_log`，乘 n 的方向由 Nat.cast_nonneg 确保。 |
| n≤2h² 的统一逆幂 | 第152–157行 | 分母 `2h²` 严格正，给定的实数转换不等式乘 π²≥0 后控制指数。无 n>0 限制。 |
| 两个 floor 指数 | 第159–170行 | `Nat.floor_le (sq_nonneg h)` 给 floor(h²)≤h²，h≥1 给 h²≥1。正确得到 floor(h²)+1≤2h² 及 2floor(h²)≤2h²，然后分别代入统一逆幂定理。整数 h² 时也成立。 |
| 对数安全常数 | 第68–112行、第172–177行 | 正ρ下的对数上下界给 `|logρ+1-ρ|≤(1-ρ)²/ρ≤2(1-ρ)²`。0≤1-ρ≤π²/(4h²) 允许平方比较，得二次项≤π⁴/(8h⁴)。h≥1 给 h³≤h⁴，正分母比较放宽到 π⁴/(8h³)；加三阶余项后恰为 `[π³M/48+π⁴/8]/h³`。 |
| 每个自然 N 的倍数版 | 第179–193行 | 先将左式精确因式分解为 N 乘单步对数误差，再用 N≥0 的绝对值乘法和正向乘界。常数与 N/h³ 因子无丢失。 |

逆幂和 N 倍结论分别覆盖 n=0、N=0：前者为1≤1，后者为0≤0。没有取自然数 n 或 N 的倒数。floor 两界中 `+1` 与 `2*floor` 的指数精确保留，没有将 floor 错换成严格小于 h²。

各处 `_hh`、`_hupper`、`_hM` 是辅助标量引理保留但证明不必使用的较强前提，不构成缺口。实际主结论的两个 h 阈值和矩条件都在最终完整签名内。不存在对称、密度、第四矩、有界增量、格点或杀死核谱假设。

## 独立服务器检查

使用 `tools/server.py` 的共享 broker，在既定工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 激活固定环境后，顺序运行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/CosinePowers.lean
{ 最终源码 + 全部 #check/#print 与动态审计附录; } | lake env lean --stdin
```

两个过程都不带 `-o`；未生成目标 olean，未运行 Lake 构建/更新或缓存获取。broker exit_code=0、stderr 为空，目标和源加附录均无警告，最终明确输出 `TARGET_AND_DYNAMIC_AUDIT_EXIT=0`。UTC 为 `2026-10-21T11:13:30Z`。

远程目标在检查前后均为上表最终 SHA256，本机同值；两个直接依赖也独立核对一致。检查未依赖作者 receipt 或作者声明数量。

动态审计逐项遍历实际 `env.constants.toList` 中所有 `env.getModuleIdxFor? declName = none` 的新常量，**没有命名空间或作者根名称筛选**。对每项调用 `Lean.collectAxioms`，若任何传递公理不在 `{propext, Classical.choice, Quot.sound}` 内就立即报错。完整最终源码经 Lean stdin 重新检查，不是仅 import 作者目标 olean。实际输出：

```text
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 25
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
```

11个显式定理均被实际枚举：

```text
cosine_powers_scalar_bounds
cosine_powers_inverse_scalar
cosine_powers_log_linear_scalar
cosine_powers_log_error_scalar
cosineCoefficient_large_h_remainder
cosineCoefficient_large_h_bounds
cosineCoefficient_inverse_pow_bound
cosineCoefficient_inverse_pow_uniform
cosineCoefficient_floor_inverse_bounds
cosineCoefficient_log_error
cosineCoefficient_log_error_mul
```

另14个实际生成辅助声明也全部审计：

```text
cosine_powers_scalar_bounds._simp_1_1
cosine_powers_scalar_bounds._simp_1_2
cosine_powers_scalar_bounds._simp_1_3
cosine_powers_scalar_bounds._simp_1_4
cosine_powers_scalar_bounds._simp_1_5
cosine_powers_scalar_bounds._simp_1_6
cosine_powers_scalar_bounds._simp_1_7
cosine_powers_inverse_scalar._simp_1_1
cosine_powers_inverse_scalar._simp_1_2
cosine_powers_inverse_scalar._simp_1_3
cosine_powers_inverse_scalar._simp_1_4
cosine_powers_inverse_scalar._simp_1_5
cosine_powers_inverse_scalar._simp_1_6
cosine_powers_inverse_scalar._simp_1_7
```

这些名称均在 `Shao.OQ4` 下，但没有靠该名称特征筛选后才计数。25项的传递公理均为白名单子集：11个显式定理及两个 `_simp_1_6` 使用三项标准公理，另12个辅助声明只有 propext。对实际双边界、floor 两界和 N 倍误差还独立执行 `#print axioms`，结果同样只有标准三项。没有 sorryAx 或新增公理。

最终远程源的禁用项正则扫描 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 得：

```text
PROHIBITED_TOKEN_HITS []
```

本机同源扫描亦无命中。完整过程未改作者最终源或缓存。

## 认证边界

本票认证上述显式矩类与充分大 h 阈值下，实际**自由**余弦系数的正性、有限逆幂统一界和定量对数误差。因此这里的 ρ 正性确已在这些前提下证明，不再作为额外未知输入；这不能被扩大为任意 h 或任意概率律的正性。

本票不赋予 ρ 杀死核特征值解释，也不把有限逆幂控制当作初值或长期核极限。**B1、O0、实际 R3/R4、iid 路径表示、Brownian 输入、长时间核极限、4/π、K/Kv、完整 OQ4 与其他全部根组保持 OPEN。**
