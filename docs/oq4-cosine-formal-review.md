# R0 三角系数最终形式版本独立审查 v1

STATUS: CORRECT

LEAN_STATUS: LEAN_FULLY_CHECKED

JUSTIFICATION: 最终源的完整签名与冻结 R0 有限接口一致，证明体忠实实现已审数学推导，没有前提漂移。独立服务器目标编译、四个公开定理的传递公理检查，以及包含七个自动生成辅助声明在内的全部十一项动态公理审计均通过。此状态只认证冻结的 R0 三阶矩系数界。

## 版本与独立性

审查日期：2026-10-21。目标及公开定理检查结束于 `2026-10-21T09:00:13Z`；最终全部声明动态审计结束于 `2026-10-21T09:04:11Z`。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-cosine-coefficients-v1.md` | `194d309514fd3096b3a3bceaa0d381e2e8fc8cebc778c9d36d0a3bb7f749f4a4` |
| 当前匿名 `drafts/oq4/cosine/proof.md` | `03e833469346b427d11765ef64b06f884ced46cff4baaeff318dde26f3913d2d` |
| 最终本机 `drafts/oq4/cosine/CosineCoefficients.lean` | `8fa6f094c330a8006c5664f8912cafd035524cc461df95e81446d2384a46c104` |
| 最终远程 `Shao/OQ4/CosineCoefficients.lean` | `8fa6f094c330a8006c5664f8912cafd035524cc461df95e81446d2384a46c104` |

远程工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。本机与远程最终源哈希一致；目标检查前、公开定理检查后和最终动态审计后的远程 SHA256 均一致。以下行号均指该最终源。

本票复用先前 `cosine-math-review-v1.md` 对匿名数学推导的正确性结论，但重新完整读取了最终形式源的全部签名和证明体。当前匿名推导仅更新了第 3 行检查状态说明，其数学推导与此前已审内容一致。作者自述、作者 receipt 和其他检查者的结果均未用作本票的认证替代；未读取作者 receipt、作者会话或其他票。本票没有修改作者代码、冻结声明或缓存。

## 完整签名对应冻结声明

1. **两个标量界。** 第 23–24 行和第 28–29 行分别量化任意 `t:ℝ`，结论正是冻结第 10 行的正弦和余弦全局三阶界，没有 `|t|≤1`、`t≥0` 或非零条件。
2. **任意实频率的概率积分界。** 第 64–75 行明确量化任意可测空间、概率测度 `μ`、实函数 `Y` 和任意 `a:ℝ`。`Y`、`Y²`、`|Y|³` 的三项可积性、均值零和二阶矩一完整保留。`β`、`ρ`、`η` 的 `let` 定义分别为第三绝对矩、普通余弦积分和普通正弦积分；两条结论精确使用 `|a|³*β/6`。没有有界支持、无原子、分布对称、四阶矩或指数矩条件，也没有把 `ρ` 定义为杀死核特征值。
3. **每个正 h 的精确界。** 第 140–151 行保留同样概率和矩条件，另只要求 `h>0`；相位确为 `π/(2h)`，中心项确为 `1-π²/(8h²)`，两条余项确为 `π³β/(48h³)`。没有额外的“h 充分大”或 `β≤M` 假设。
4. **退化和边界量词。** 第一组结果明确包含 `a=0`、负 `a` 和任意大 `a`；第二组明确适用于全部正 `h`。所有函数为普通实函数，原子分布及几乎处处可测代表元均未被排除。

最终完整签名与冻结第 5–14 行一致。

## 证明体与数学语义

1. **正弦全局性。** 第 25 行直接调用实际全局声明 `Real.abs_sub_sin_le t`，仅交换绝对值中差的顺序。此前数学审查已从固定 Mathlib 源核对该外部声明没有大小限制；本轮该调用又经实际服务器内核检查。
2. **余弦大参数分支。** 第 30–38 行先由 `Real.one_sub_sq_div_two_le_cos` 确证余项非负。对 `x≥3`，以 `x²(x-3)≥0` 和 `cos x≤1` 得 `cos x-(1-x²/2)≤x³/6`。没有把一个非绝对值估计误当作绝对值估计。
3. **余弦小参数分支与端点。** 第 39–55 行定义的 `F` 及其实际导数正是已审推导中的 `F(u)=u³/6-(cos u-(1-u²/2))`、`F'(u)=u²/2+sin u-u`。连续性、内部可微性和凸区间条件由 `fun_prop`/`convex_Icc` 提供；在区间内部由 `interior_subset` 获得 `0≤u≤3`，再合法调用 `sin_ge_sub_cube`。导数非负由 `u²(3-u)≥0` 确证。第 51–55 行使用 `F(0)=0` 推出所需结果；`x=0` 包含在闭区间，`x=3` 由大参数分支覆盖。第 56–60 行再以余弦偶性和绝对值处理负实数。没有隐藏的局部频率前提。
4. **系数积分真实可积。** 第 77–86 行分别证明余弦和正弦复合的几乎处处强可测性，用概率测度上的常数界 `1` 得到可积性。第 87–94 行明确证明二次多项式 `P` 可积，并利用二阶矩及概率归一化求其积分。第 95–100 行的积分相减分别有 `hcosint`、`hPint`、`hsinint` 和 `hY.const_mul a` 支持，没有非法拆积分。
5. **第三矩支付。** 第 101–132 行先从 `hYcube` 证明控制函数可积，再用实际全局标量界和 `|aY|³=|a|³|Y|³` 给出逐点范数上界。`norm_integral_le_of_norm_le` 的控制函数条件被明确供应。原余项也由前述可积函数之差可积，因此本结论没有借助不可积实积分的默认取值。第 133–137 行使用真实的余项积分恒等式得到冻结结论，未加入额外矩假设。
6. **h 代入。** 第 152 行由 `h>0` 和 `π>0` 得相位正。第 153–159 行确证中心项等式和因子等式，分母非零由原正性前提保证；数值 `8=2²*2`、`48=2³*6` 正确。第 160–161 行仅实例化任意频率结论，保留每个正 `h` 的精确不等式。

未发现证明体与冻结前提或既审数学推导的偏移。

## 独立服务器检查

使用本审会话已核对的项目钉死环境：Lean `4.36.0-rc1`、Lake `5.0.0-src+c9afcdd`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。本轮所有编译仅在指定服务器执行；没有本机 Lean、版本更新、缓存下载或共享包缓存写入操作。

实际目标命令：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/CosineCoefficients.lean
```

目标退出 `0`，无警告。随后将最终目标源与四个公开定理的 `#print axioms` 命令拼接送入服务器 `taskset -c 0-3 lake env lean --stdin`，退出 `0`；四项传递公理均为 `[propext, Classical.choice, Quot.sound]`。

## 全部十一项声明的动态传递公理审计

本源仅导入 Mathlib，全部自身声明位于 `Shao.OQ4`。为涵盖生成的辅助声明，另在最终源末尾追加临时 `run_cmd`，遍历实际环境 `env.constants.toList` 中名称含 `Shao.OQ4.` 的全部常量，对每项调用 `Lean.collectAxioms`，并逐项检查公理是否只含 `propext`、`Classical.choice`、`Quot.sound`。审计代码只经标准输入运行，没有写入作者模块。

实际枚举为四个公开定理和七个自动生成 `_simp` 声明。最终审计退出 `0`，输出为：

```text
Shao.OQ4.sin_taylor_cubic_bound: [propext, Classical.choice, Quot.sound]
Shao.OQ4.cos_taylor_cubic_bound: [propext, Classical.choice, Quot.sound]
Shao.OQ4.cosine_coefficients_third_moment_bound: [propext, Classical.choice, Quot.sound]
Shao.OQ4.cosine_coefficients_h_bound: [propext, Classical.choice, Quot.sound]
Shao.OQ4.cosine_coefficients_h_bound._simp_1_1: [propext]
Shao.OQ4.cosine_coefficients_h_bound._simp_1_2: [propext]
Shao.OQ4.cosine_coefficients_h_bound._simp_1_3: [propext]
Shao.OQ4.cosine_coefficients_h_bound._simp_1_4: [propext]
Shao.OQ4.cosine_coefficients_h_bound._simp_1_5: [propext]
Shao.OQ4.cosine_coefficients_h_bound._simp_1_6: [propext, Classical.choice, Quot.sound]
Shao.OQ4.cosine_coefficients_h_bound._simp_1_7: [propext]
DYNAMIC_DECL_COUNT 11
DYNAMIC_AUDIT_EXIT=0
```

最终作者源的 `sorry|admit|axiom|unsafe|native_decide` 词项扫描为空。没有新增公理或非许可的传递公理依赖。以上计数和结果来自本票独立执行，不依赖作者的动态枚举报告。

## 裁决范围

本票补足此前数学票的最终形式认证；此前 `MATH_ONLY/LEAN_NOT_RUN` 票保留其当时作用域，不被改写。

**最终 `0<ρ<1`、R1/R2、R3、K、Kv、完整 OQ4 均保持 OPEN；全部其他根组也保持 OPEN。** 此处 `LEAN_FULLY_CHECKED` 只指冻结的 R0 自由一步三角系数三阶矩界，不表示杀死核或长时间主定理已关闭。
