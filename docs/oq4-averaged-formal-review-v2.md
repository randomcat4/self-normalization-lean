# R3 解析平均支付最终形式版本独立审查 v2

STATUS: CORRECT

LEAN_STATUS: LEAN_FULLY_CHECKED

JUSTIFICATION: 最终源完整表达冻结 v2 的条件性解析平均支付，证明体忠实实现已审数学推导。参数积分可测性、所有固定参数截面的真实可积性、κ 下的 ψ 与绝对残差可积性、有限顶层和 R6 支付、子概率质量因子及两条数值常数均正确。独立服务器无-o目标检查、实际枚举的全部八个新增常量传递公理审计及禁用项扫描通过。

**认证只限明确 κ 层质量前提下的解析约化。统一共同常数为 `C_{M,C}`；不证明 O0 的实际概率输入或长时间 K。**

## 对象、版本及独立性

审查日期：2026-10-21；最终独立服务器检查完成于 `2026-10-21T09:58:57Z`。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-averaged-residual-v2.md` | `39a288d06c817ea1e745cf191b239d3b4a083d0367ebe8e16eee78724a755da5` |
| 本轮数学审查的匿名 `averaged/proof.md` 快照 | `e58349af4c0e1a7d788ab2ebca805517dcf5345058036925d81f46c3872f8079` |
| 最终本机 `drafts/oq4/averaged/AveragedResidual.lean` | `ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2` |
| 最终远程 `Shao/OQ4/AveragedResidual.lean` | `ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2` |
| 远程直接依赖 `KilledCosine.lean` | `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8` |
| 远程直接依赖 `OvershootMoment.lean` | `a785a61be3f7c5230f66e053c0a827c9bde7674fc27fa129e6306033c92aee10` |
| 远程直接依赖 `OccupationPayment.lean` | `3ed77e585a0a687b471d46e004872d35c18d7181388a7828c34e83085bd094d9` |

远程工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。本机与远程最终源哈希一致，实际目标检查前与动态审计后的远程目标哈希一致；直接依赖哈希与此前独立认证版本相同。以下 Lean 行号均对应最终 `ffe155...91aa2` 版本。

独立数学票 `review/averaged-math-review-v2.md` 保留为 `MATH_ONLY / LEAN_NOT_RUN` 的历史工件。该票中的早期声明草稿哈希不是本票认证对象；本轮重新完整读取了最终签名及证明体。没有读取 v1 审稿票、作者 receipt、作者会话或其他认证票；作者给出的声明数量和检查结果未用作本票独立证据。没有修改作者代码、冻结前提、公共接口或缓存，也没有生成作者模块 olean。

## 最终完整签名与 v2

第 106–120 行逐项保留：

- ν 为标准实数 Borel 空间上的概率测度；κ 仅要求有限测度，而非概率测度。
- `κ.real(univ)≤1` 与 `∀ᵐ w ∂κ, |w|≤h` 分别显式出现，没有把 a.e. 支持强化成逐点支持。
- `h>0`、独立 `C≥0`、id/平方/第三绝对幂三项可积性、均值零及二阶矩一完整保留。
- 每个 `j<⌊h⌋₊+1` 的 κ 层质量上界明确以 `(C/h²)(j+1)` 作为输入，未被省略或改名成无条件定理。
- β 是实际第三绝对矩；结论返回 `|r|` 对 κ 可积和冻结的两条精确分母 `h³` 不等式，第一式含实际 `I=∫|y|`，第二式含安全项 `1+2β`。

第 19–23 行局部定义与冻结的 r、ψ 完全相同。签名没有增加 κ 密度、额外 F 可积输入、第四矩、有界增量、非格点或分布对称性。没有 β≤M 的额外假设，也没有把 C 绑定成 M 的函数。

## 参数积分及可积性：逐项代码核查

1. **ν 参数积分可测。** 第 26–32 行证明截断余弦的联合 Borel 可测性，调用 `StronglyMeasurable.integral_prod_right'` 得到 Kcos 可测。ν 的概率实例提供所需 SFinite 条件；实数目标满足一般赋范空间及强可测性条件。第 35–39 行对连续的二元正部函数作同样处理。这里没有假设 Kcos 随 w 连续，也没有先假设某个未经证明的联合可积性。
2. **每个超越截面是真实可积函数。** 第 42–51 行对任意实 h,w，在原始一阶矩下证明 `max(|y|-(h-|w|),0)` 可积：其范数受 `|y|+|h-|w||` 控制，右侧由 `hId.abs` 加概率测度上的有限常数可积。该证明对每个 w 成立，并非只在 κ 的支持上。因此 ψ 的定义不依赖不可积截面默认积分零。
3. **每个 Kcos 和自由 ρ 积分真实可积。** 第 58–89 行分别确证截断余弦和普通余弦的 Borel 可测性、点态绝对值≤1及 ν 下可积性，再用积分三角不等式和积分单调性得到 `|Kcos|≤1`、`|ρ|≤1`。并非仅利用 Bochner 积分在不可积时的默认定义。
4. **r 与 |r| 对 κ 可积。** 第 56–57 行从参数可测性和连续余弦得到 r 可测。第 90–99 行由真正的积分界推出全实轴逐点 `|r(w)|≤2`；第 100–103 行再用有限 κ 得 `Integrable |r| κ`，不需要 κ 处处在闭区间内，也不需要 κ 的额外矩。
5. **ψ 对 κ 可积。** 第 137–145 行在 `|w|≤h` 时用两个真实可积截面作积分比较，得 `ψ(w)≤I`；ψ 非负由非负被积函数给出。随后把 κ-a.e. 支持仅用于 a.e. 范数上界，再以全局可测性和有限 κ 的常数 I 可积性得到 `Integrable ψ κ`。没有使用 κ 的逐点有界支持或额外一阶矩。

这五项分别核对了可测性、ν 截面积分及 κ 积分；没有将其中某一种性质误当成其余性质。

## 有限顶层和 R6 期望支付

1. 第 146–154 行对每个自然数 j 明确证明正部格项可积，使用的是 `max(|y|-j,0)≤|y|`，并给出 `b_j≥0`。
2. 第 155–156 行只从原 a.e. 支持得到 `0≤h-|w|≤h` 几乎处处。第 157–164 行由层成员关系 `j≤h-|w|` 和正部单调性证明 ψ 的层上界；使用 `integrable_overshoot_integrand` 及 `hcellint` 供应积分比较两侧的可积性。层上界是推出的事实，不是新增输入。
3. 第 165–167 行以真实可积的 ψ 调用 `finite_occupation_payment_of_le`，使用 `C/h²≥0` 及原始质量前提。闭顶层索引始终为 `j<⌊h⌋₊+1`，故整数 h 的 d=h 所在顶层、边界 `w=±h` 所在零层及层界原子均保留。
4. 第 168–171 行在 R6 期望接口中取 `U=|id|`。`hId.abs`、原 `hCube` 和处处非负条件精确匹配其要求。`integral_const_mul` 把加权 `b_j` 与 `overshootCell` 的积分对应起来，所用都是已证可积格项的有限和；没有未经证明的无限和换积分。
5. 第 172–173 行只乘非负 `C/h²`，得到 `∫ψ≤(C/h²)4(I+β)`。这一步仍条件于显式层质量假设，不证明 O0 本身。

## 平均残差、子概率质量和安全常数

1. 第 174–179 行只在原 κ 满测支持集调用已审一步残差界，将相位精确改写为 `aw`，得到 a.e. `|r|≤c+aψ`。其中 `a=π/(2h)>0`、`c=π³β/(48h³)≥0`，非负性由 h>0 和真实第三绝对矩给出。
2. 第 183–187 行的积分比较同时具备 `hrint`、常数 c 可积及 ψ 可积；常数积分精确为 `κ.real(univ)*c`。第 188–190 行明确使用质量≤1和 c≥0 才将其界为 c，没有误将任意有限 κ 当作概率测度。
3. 第 191–193 行用 a 非负乘层支付，并精确整理 `(π/(2h))*4C/h²=2πC/h³`。第一式中心系数为 `π³β/48`，支付系数为 `2πC(I+β)`，分母为 `h³`，与冻结完全一致。
4. 第 194–206 行对 `u=|y|` 分 `u≤1` 和 `u>1` 证明 `u≤1+u³`，所有积分相加和比较均有 id 及三阶矩可积性。概率归一化给 `I≤1+β`，未新增矩条件。
5. 第 208–211 行以 `h³>0` 和 `2πC≥0` 保序比较，得安全第二式中的 `1+2β`。允许 C=0 和 κ=0，没有除以它们。

## C 的独立依赖与根意义

最终主声明把 C 作为独立参数。若另限制 `β≤M` 且共同类的 C 固定，可取

`C_{M,C}=π³M/48+2πC(1+2M)`。

只有 O0 另外证明统一的 `C=C(M)` 后，才可在源应用中把常数记为 `C_M`。本模块没有这一概率证明，也没有识别 κ 为某个实际 m 步被杀终点 law。有限 κ、子概率质量和 a.e. 闭支持本身不供应层质量界。

## 实际独立服务器核验及全部新增常量

使用项目钉死环境 Lean `4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。经 `tools/server.py` 正常返回远程 `exit_code=0`、空 `stderr`，没有失败重放或旁路 broker。所有 Lean 在指定服务器执行；没有本机 Lean、缓存下载或共享缓存修改。

实际目标命令：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/AveragedResidual.lean
```

该无 `-o` 检查退出 `0`、无警告。随后将最终源、主定理的 `#print axioms` 和动态审计附录经标准输入送入服务器 `taskset -c 0-3 lake env lean --stdin`，退出 `0`，不生成作者模块 olean。

动态审计遍历实际环境常量，筛选 `env.getModuleIdxFor?` 为 `none` 且属 `Shao.OQ4` 的当前模块声明，排除所有导入依赖；逐项用 `Lean.collectAxioms` 收集传递公理并强制检查白名单。独立枚举实际得到两项定义、五项定理及一项自动生成方程声明：

```text
NEW_DECL Shao.OQ4.cosineResidual: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.cosineResidual.eq_1: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.overshootPotential: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.measurable_Kcos: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.measurable_overshootPotential: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.integrable_overshoot_integrand: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.integrable_abs_cosineResidual: [propext, Classical.choice, Quot.sound]
NEW_DECL Shao.OQ4.averaged_cosine_residual_bound: [propext, Classical.choice, Quot.sound]
NEW_DECL_COUNT 8
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
PROHIBITED_TOKEN_HITS []
```

主定理的独立 `#print axioms` 也仅含 `[propext, Classical.choice, Quot.sound]`。作者源中 `sorry|admit|axiom|unsafe|native_decide` 机械词项扫描为空。数量、动态结果和编译均来自本票独立执行，不依赖作者检查自述。

## 最终范围

**冻结 v2 的、带 κ 层质量前提的解析平均支付为 CORRECT / LEAN_FULLY_CHECKED。** ν/κ 原子、任意大跳、整数 h 顶层、边界点及 κ=0 均包含。

**实际随机游走 R3、O0、R4、Brownian 初值/末端块、E1–E6、K、Kv、完整 OQ4 及其他全部根组保持 OPEN。** 不能把已形式化的条件性解析不等式改称这些实际概率或长时间结论已闭合。
