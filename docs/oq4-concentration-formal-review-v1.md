# BE 到闭区间集中独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 实际高斯比较下的显示 BE→闭单位区间 AC 约化

LEAN_STATUS: 独立服务器无-o目标检查及完整源动态审计均 exit 0，无警告

JUSTIFICATION: 最终签名与证明体完整满足冻结四项接口。任意概率 law 的闭区间界用 a-δ 截口保留左原子；实际 gaussianReal 0 1 的真实密度积分证明其 CDF 1-Lipschitz。β≥1 仅用真正平方/三阶可积性和二阶矩1。最终 AC 构造真实可测和的概率推送并保留显示 BE 前提，t≥1 保证正分母。全部13个实际新增常量通过传递公理白名单，禁用项为空。

## 对象与隔离

审查日期：2026-10-21。先只读取冻结声明与匿名推导，完成并保留 `interval-concentration-math-review-v1.md` 的 MATH_ONLY/LEAN_NOT_RUN 范围，再读最终实现。未读取作者 receipt、作者会话或其他审稿票，没有修改源、冻结声明、共同文件或缓存，没有生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-interval-concentration-v1.md` | `ef262e8e8ff61fa0cd2966e6a56c0d73182e54237437a3854af87ba15878cf85` |
| 所审匿名 `drafts/oq4/concentration/proof.md` 快照 | `c0824f37ae8fe783830b82e06f1c55e4a996ee8b74c6be4cd5a185f669f463ec` |
| 本机 `drafts/oq4/concentration/IntervalConcentration.lean` 与远程 `Shao/OQ4/IntervalConcentration.lean` | `491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875` |
| 共同直接依赖 `Shao/Probability/MeasurablePath.lean`，本机 library/远程一致 | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |
| 共同前缀定义 `Shao/Basic/FinitePath.lean`，本机 library/远程一致 | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 指定服务器 mathlib `Probability/Distributions/Gaussian/Real.lean` | `9edebfff169cb577b6dab1a7912f2e8fec0e70a8dac39db105263e1a0f31b383` |
| 指定服务器 mathlib `Probability/CDF.lean` | `f82c6b525c53db6b856c6759d5c6ec1a7f1c26dfea8a74b3c264eaa75d878b0f` |

以下行号均为最终 `IntervalConcentration.lean` 的一基行号。

## 任意 CDF 近似与闭区间原子

第18–23行以概率测度的真实有限性和 Iic 集合差证明 `μ.real(Ioc a b)=F(b)-F(a)`，明确要求 a≤b。该式只在左开区间使用，没有被误用于闭区间。

第26–30行主接口完整保留任意 Borel 概率 μ、实数 L,ε≥0、任意函数 G 的全轴 L-Lipschitz 界、每个实 x 的真实 Iic-CDF 误差，以及 a≤b。没有密度、无原子或严格 a<b 条件。

第31–48行对任意 δ>0 证明 `[a,b]⊆(a-δ,b]`，先由真实测度单调性和 Ioc 差公式，再用两端 CDF 误差与 G 的 Lipschitz 界，得到所需界另加 Lδ。第49–58行使用 `le_of_forall_pos_le_add`，对任意 η>0 取 δ=η/(L+1)>0，并证明 Lδ≤η。只除以严格正的 L+1，不除以可为0的 L；不需要假设 CDF 在 a 连续。

因此 a=b 的完整原子质量仍被界为2ε。L=0、ε=0 合法，左端原子从未被扣掉。`_hε` 虽不是证明所必需，仍保留冻结的 ε≥0 接口前提。

## 实际高斯 CDF 的全轴 1-Lipschitz

第60–63行 `standardNormalCDF` 就是 mathlib 实际 `cdf (gaussianReal 0 1)`，并用 `cdf_eq_real` 明确绑定到实际 γ.real(Iic x)。独立服务器 `#print` 确认其定义，不是留作假设的比较函数。

第65–75行展开实际 `gaussianPDFReal 0 1`，由 π≥2 得 sqrt(2π)≥1，其正倒数≤1；指数 -x²/2≤0 给 exp≤1，再以非负系数乘界，证明全轴真实密度≤1。

第77–85行使用 `gaussianReal_apply_eq_integral 0 (1≠0)` 的实际测度公式，以及密度的非负积分，把真实 γ 的 Ioc 实质量化为密度积分。比较使用真正 `integrable_gaussianPDFReal ... .restrict` 和有限区间上常数1的可积性，再以 Lebesgue 长度给≤b-a。独立服务器同时核对该外部公式的完整签名及密度的全轴 Integrable；不是不可积默认0。

第88–100行依 x,y 的顺序，分别用实际 cdf 的单调性、Ioc 质量界和真实 CDF 差，正确处理绝对值的两个符号方向，得到全轴 `|Φ(x)-Φ(y)|≤|x-y|`。没有另加高斯 Lipschitz 前提。

## β≥1 无隐藏矩或均值前提

第103–106行完整签名只有 ν 为实数 Borel 概率测度、y² 与 |y|³ 的真实 Integrable、二阶矩积分=1。没有 hmean、id 可积、第四矩或密度假设，独立服务器 `#check` 已确认。

第107–109行以 `(|y|-1)²(2|y|+1)≥0` 和 |y|²=y² 得逐点 `3y²≤2|y|³+1`。第110–114行的积分比较、加法与常数倍分别明确使用 hSq、hCube 及概率测度下的常数可积性；利用二阶矩1和总概率1得 3≤2β+1。第115行推出 β≥1。这是独立的无条件矩事实，不依赖 BE。

## 真实乘积归一化推送与 BE→AC

第118–127行完整保留 ν 的上述两项真正可积性、原始二阶矩1、自然 t≥1、C_BE≥0，以及**每个实 x** 的显示真实 Π_t 归一化和 CDF 误差。没有均值条件或有限样本密度，允许比源 BE 实例更一般但满足此显示前提的 law。结论是每个实 a 的真实和落在 Icc(a,a+1) 的概率界，闭端点完整。

第128–130行用本模块独立矩事实得实际 β≥1，再由 t≥1 推出 s=sqrt(t)>0。第131–138行把共同可测 prefixSum 除以 s，构造实际 X 和 `μ=map X Π_t`，并直接验证 μ 的总质量1，因此不是抽象比较 law 假设。

第139–142行对可测 Iic 使用真实 map_apply，使 μ 的 CDF 误差精确等于显示 hBE；第143–149行以正 s 证明 Icc(a/s,(a+1)/s) 的原像恰为原始闭单位区间事件，未漏任一端点或原子。

第150–154行实际取 L=1、ε=C_BEβ/s，ε 非负由 C_BE≥0、β≥1 和 s>0 得出；比较函数是本模块已证 1-Lipschitz 的实际 standardNormalCDF。区间端点顺序也以正 s 验证。第155–161行把真实 law 质量改写回来，宽度精确为1/s，最后仅由 β≥1 将 `(1+2C_BEβ)/s` 放大成 `(1+2C_BE)β/s`。

t=0 没有进入接口；没有默认除0或对允许为0的 C_BE 取倒数。实际 Π_t 的原子、零路径、不对称增量和任意大跳均未排除。该证明没有声称缺少均值条件时 BE 自动成立，也没有生存后独立性前提。

## 独立服务器证据

通过 `tools/server.py` 共享 broker，在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 激活固定环境后，顺序运行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/IntervalConcentration.lean
{ 最终完整源码 + #print/#check 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，不生成目标 olean，不构建/更新 Lake 或获取缓存。目标及源加附录均无警告；broker exit_code=0、stderr 为空，明确输出 `TARGET_AND_DYNAMIC_AUDIT_EXIT=0`。UTC 为 `2026-10-21T13:00:11Z`。目标源前后 SHA256 与本机最终值一致，共同依赖及实际 mathlib Gaussian/CDF 源哈希亦如上表。

全部9个显式声明的完整签名或定义均经独立 `#check/#print` 核对。动态审计遍历实际 `env.constants.toList` 中**全部** `env.getModuleIdxFor? declName = none` 的声明，未按 namespace/root 名称筛选。每项调用 `Lean.collectAxioms`，若任一传递公理不在 `{propext, Classical.choice, Quot.sound}` 中则立即报错。完整最终源码真实经 stdin 重新核验，结果为：

```text
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 13
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
```

实际枚举的9个显式声明为：

```text
Shao.OQ4.real_Ioc_eq_real_Iic_sub
Shao.OQ4.closed_interval_mass_bound_from_cdf
Shao.OQ4.standardNormalCDF
Shao.OQ4.standardNormalCDF_eq_real
Shao.OQ4.standardGaussian_density_le_one
Shao.OQ4.standardGaussian_Ioc_mass_le_length
Shao.OQ4.standardNormalCDF_lipschitz
Shao.OQ4.third_absolute_moment_ge_one
Shao.OQ4.iid_closed_unit_concentration_of_cdf_error
```

4个实际生成辅助声明也全部审计：

```text
Shao.OQ4.real_Ioc_eq_real_Iic_sub._simp_1_1
Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._proof_1_1
Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._simp_1_2
Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._simp_1_3
```

13项传递公理均为标准白名单子集；9项显式声明使用标准三项。闭区间主界、实际高斯 Lipschitz、β≥1 和最终 AC 还逐项独立 `#print axioms`，同样只有标准三项。没有 sorryAx 或新增公理。

最终远程源禁用项正则 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 扫描输出：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

本票认证实际高斯 CDF 的 1-Lipschitz、独立 β≥1 矩事实，以及从**显示的实际 BE-CDF 误差前提**到闭单位区间 AC 的约化。它没有给 BE 加公理，也没有证明此前提在某一 iid 矩类下成立。

**BE、无条件 AC、SP、一侧 S、O0/R3/R4、B1/Brownian 输入、长期 K/Kv、4/π、完整 OQ4 及其他全部根组保持 OPEN。**
