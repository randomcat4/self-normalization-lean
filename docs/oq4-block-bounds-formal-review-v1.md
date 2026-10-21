# 从 S/AC 到真实杀死块界独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 明确全时刻 S/AC 概率输入到真实层界/R3/R4及条件有限D8

LEAN_STATUS: 独立服务器无-o目标检查及完整源动态审计均 exit 0，无警告

JUSTIFICATION: 打包谓词展开后精确保留实际全乘积 law、所有正自然时刻、所有实区间起点及所有非负实墙高。层界由这些输入逐 j 导出，R3 使用真实核质量/支持与真正可积性，R4 使用真实路径包含和仅闭域有效的余弦弦界。最终 D8 没有 R3/R4 假设，而以内部分别已证的块结论供应 KernelAbsorption。全部23个实际新增常量通过传递公理白名单，禁用项为空。

## 对象与隔离

审查日期：2026-10-21。先只读冻结声明与匿名推导，并核对既审平均残差接口，完成并保留 `killed-block-bounds-math-review-v1.md` 的 MATH_ONLY/LEAN_NOT_RUN 范围，再读最终实现。未读取作者 receipt、作者会话或其他审稿票。只写所分配报告，没有修改实现、冻结声明、共同文件或缓存，没有生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-killed-block-bounds-v1.md` | `68f3d3ae683ea1f69910e3373bd373da4f17f7aa4eb25e0e97f489c11163c28c` |
| 所审匿名 `drafts/oq4/block-bounds/proof.md` 快照 | `f33fe5f361c3cafbcb8af9ea0b63250bb2c622eeb2d381e9c85763123eeec08d` |
| 本机 `drafts/oq4/block-bounds/KilledBlockBounds.lean` 与远程 `Shao/OQ4/KilledBlockBounds.lean` | `cc46dc9257cc89d6e31139a60593a419d296fd5f691f10eb565d6310d9dd2408` |
| 已审直接依赖 `BoundaryOccupation.lean`，本机/远程一致 | `1568e5514fc4ca8053ccd9b0f123f86e61cc294df0f6de199c8a688b9d7de8a6` |
| 已审直接依赖 `KernelAbsorption.lean`，本机/远程一致 | `b11d2f68db3581ed61abab670e72234b950df669b379e98f65172f3097f5d168` |
| R3 所用已审依赖 `AveragedResidual.lean`，本机/远程一致 | `ffe155446ff31b1f1e20dc6ff1b8dc14b1c5274b2593a4cc774183b053491aa2` |

以下行号均为最终 `KilledBlockBounds.lean` 的一基行号。

## S/AC 谓词与显式常数

第11–14行 `iidIntervalConcentration ν β Cq` 展开为：每个自然 t≥1、每个实 x，真实 `Measure.pi (fun _ : Fin t => ν)` 下共同 prefixSum 的 t 步和进入 Icc(x,x+1) 的实概率≤Cqβ/sqrt(t)。没有限制到某个预先固定的块，也没有把 x 改成 a.e. 或固定起点。

第17–20行 `iidOneSidedSurvival ν β Cs` 展开为：每个自然 t≥1、每个实 d≥0，真实全乘积 law 下共同 `closedUpper d` 和既审 `lowerBlockSurvival d` 的概率分别≤Cs(d+β)/sqrt(t)。上、下两种事件均保留，d=0 及零前缀条件包含。谓词中没有核层界、R3/R4 或归一化列结论。独立服务器 `#print` 实际展开确认了两个定义。

第22–25行常数精确为 `C_layer=12CqCsM(1+M)` 与 `E=π³M/48+2π C_layer(1+2M)`；R4 和 D8 中 A=2Cs、B=2CsM 直接写入签名。全部常数显式依赖 M,Cq,Cs，没有在这些数尚未固定时声称只依赖 M。

## floor 参数与闭域弦界

第27–38行从 h≥3 的真实自然 floor 推出 m≥6、两个半块≥1及 `h≤2sqrt(m)`。使用 h²≥9、`h²<floor(h²)+1`、`h²≤2floor(h²)` 与非负平方根，不把 floor 近似替代为 h²。

第41–56行的 `principalCosine_depth_lower_bound` 明确只在 h>0、|z|≤h 上断言 `(h-|z|)/h≤principalCosine h z`。角度 `π|z|/(2h)` 被显式证明落在 [0,π/2]，再应用 mathlib `Real.one_sub_mul_le_cos`。独立 `#check` 确认其原始完整陈述正是 `0≤x → x≤π/2 → 1-(2/π)x≤cos x`。分母合法、余弦偶性处理负 z，含 z=0 和 z=±h；没有全局余弦非负假设。

## 真实逐层质量

第61–70行的 `killed_block_layer_bound` 对所有闭域起点 z、所有自然 j，实际核行 P^floor(h²)(z) 给出冻结层界。辅助接口允许任意非负 β≤M（更一般，不需要此处额外矩条件）；实际 R3 和 D8 后续显式将 β 取为真正第三绝对矩。

第67行取得两个半块的正长度，第69–70行将全时刻 AC 在首半块、S 在末半块与 d=j+1≥0 处分别实例化，真实调用已审 `boundary_occupation_hsq_bound`。因此层质量是结论，不是新增输入；整数顶层或 j>h 都没有被排除。

## 实际 κ、可积性与 R3

第73–85行 `killed_block_residual_bound` 完整保留 ν 的三项真正 Integrable、均值0、二阶矩1、M≥0、实际第三绝对矩≤M、Cq,Cs≥0，以及将 β 绑定为该实际积分的 S/AC。输出明确是实际核行下 |r| 的 Integrable **与** 真实 killedAction 的 E/h³ 界。

第86–93行证明 h>0、实际 β≥0、C_layer≥0，并由刚证明的真实层界供给平均残差定理需要的全部有限顶层 j<floor(h)+1。上面更强的所有 j 结论正确覆盖整数 h 的顶层，没有将顶层遗漏。

第94–96行将 κ 取为精确 `(killedIterKernel ν h floor(h²)) z`，真实质量≤1 由 `killedIterKernel_real_mass_le_one` 供应，a.e. 闭支持由 `killedIterKernel_ae_support ... hz` 供应；有限核行的 IsFiniteMeasure 实例来自已审真实核幂。并传入完整矩、均值、二阶矩及已得层界，实际调用 `averaged_cosine_residual_bound`。

第97行保留其 `ht.1` 真正可积性和 `ht.2.2` 安全界，第98–103行在正 h³ 上使用 β≤M 与非负系数，将其放大到精确 E/h³。没有把任意测度只改名后跳过实际质量/支持，也没有以不可积默认0证明 R3。

## 实际 R4

第106–109行允许任意非负 β≤M 和真实全时刻 S 输入，给实际 G_m 的 `(2Cs)φ+(2CsM)/h` 界，不需要额外 AC 或矩前提；最终调用仍将 β 绑定到实际矩。

第110–114行证明 m≥1、d=h-|z|≥0，并在真实时刻 m、真实墙高 d 处取上/下 S 输入。第115–135行展开已审 `killedMass_eq_path_probability`，按 z 符号证明集合包含：z≥0 时 shifted survival 包含于共同闭上事件，z<0 时包含于闭下事件。两支都单独处理 k=0，使用 d≥0；正时刻由真实闭生存分别取上位置界和下位置界，没有条件独立或对称分布假设。

第136–143行证明 sqrt(m)>0 和非负分子，使用已得 h≤2sqrt(m) 在正分母间比较，得到 `2Cs(d+β)/h`。第144–148行用刚证的**闭域**弦界与 β≤M，得到精确 A、B。没有在域外使用 φ≥0，也没有除以允许为0的 Cs、β 或 M。

## 最终有限 D8 的完整签名与内部块供应

第151–169行 `killed_block_finite_absorption` 完整保留 h≥3、三项真正可积性、均值0、二阶矩1、M≥0、实际 β≤M、Cq,Cs≥0、实际 β 对应的全部 S/AC；另保留 TH：π(1+M)≤h、N≥m 以及完整 smallness `(AR)(ER/h³)N+BR/h≤1/2`。**最终签名没有 R3/R4 或层质量前提。** 独立服务器 `#check` 完整展开签名确认这一点。

第170–176行证明实际 β≥0、E≥0，以 h≥3 导出 h≥1，并将 A=2Cs、B=2CsM、E 传给真实 `kernel_finite_absorption`。第177–178行对每个闭域源点 w 供应 `killed_block_residual_bound ... w hw` 的第二个结论；第179行对每个闭域 w 供应 `killed_block_mass_bound`。这是用已经导出的块结论完成旧定理前提，未把块假设重新塞回最终接口。

输出 H=2(1+AR)R 与 `(ER/h³)((k-m:ℕ):ℝ)H` 的波动项精确匹配冻结，R=exp(π²)。自然减法只在 m≤k≤N 结论中使用，N=m 时波动为0。块结论允许 h=3；最终 D8 仍必须满足额外 TH，不因已有 h≥3 省略它。

## 退化情形与限制

所有事件为闭生存或既有半开边界层，没有抛弃原子或等号。ν 可以不对称并允许任意大跳；没有新增第四矩、密度、无原子、非格点或有界支持。所有允许的非负零参数均在签名内，没有除以 Cq、Cs、β、M、A、B 或 E。上述结论仍以未证的真实 S/AC 输入为条件，不使这些输入自动成立。

## 独立服务器证据

通过 `tools/server.py` 共享 broker，在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 激活固定环境后，顺序运行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/KilledBlockBounds.lean
{ 最终完整源码 + #print/#check 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，不生成目标 olean，不构建/更新 Lake 或获取缓存。目标和源加附录均无警告；broker exit_code=0、stderr 为空，明确输出 `TARGET_AND_DYNAMIC_AUDIT_EXIT=0`。UTC 为 `2026-10-21T12:24:43Z`。目标源前后 SHA256 均为上表最终值，两个直接依赖及 R3 所用平均残差源与本机已审版本一致。

动态审计遍历实际 `env.constants.toList` 中所有 `env.getModuleIdxFor? declName = none` 声明，**无 namespace/root 名称筛选**。每项调用 `Lean.collectAxioms`，若任一传递公理不在 `{propext, Classical.choice, Quot.sound}` 内即立即报错。最终完整源码真实经 stdin 检查，而非仅 import 作者目标 olean。实际结果：

```text
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 23
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
```

10个显式声明全部实际枚举：

```text
Shao.OQ4.iidIntervalConcentration
Shao.OQ4.iidOneSidedSurvival
Shao.OQ4.killedLayerConstant
Shao.OQ4.killedResidualConstant
Shao.OQ4.hsq_block_parameters
Shao.OQ4.principalCosine_depth_lower_bound
Shao.OQ4.killed_block_layer_bound
Shao.OQ4.killed_block_residual_bound
Shao.OQ4.killed_block_mass_bound
Shao.OQ4.killed_block_finite_absorption
```

13个实际生成辅助声明也全部审计：

```text
Shao.OQ4.killedLayerConstant._proof_1
Shao.OQ4.killedResidualConstant._proof_1
Shao.OQ4.killedResidualConstant._proof_2
Shao.OQ4.principalCosine_depth_lower_bound._simp_1_1
Shao.OQ4.principalCosine_depth_lower_bound._simp_1_2
Shao.OQ4.principalCosine_depth_lower_bound._simp_1_3
Shao.OQ4.principalCosine_depth_lower_bound._simp_1_4
Shao.OQ4.principalCosine_depth_lower_bound._simp_1_5
Shao.OQ4.principalCosine_depth_lower_bound._simp_1_6
Shao.OQ4.principalCosine_depth_lower_bound._simp_1_7
Shao.OQ4.killed_block_mass_bound._proof_1_1
Shao.OQ4.killed_block_mass_bound._proof_1_3
Shao.OQ4.killed_block_mass_bound._proof_1_5
```

23项传递公理均为标准白名单子集；全部10项显式声明使用标准三项。四个主接口（层界、R3、R4、有限 D8）还独立逐项 `#print axioms`，同样只有标准三项。没有 sorryAx 或新增公理。

最终远程源禁用项正则 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 扫描输出：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

本票关闭明确全时刻 S/AC 到真实层质量、R3/R4 块界及条件有限 D8 的约化；R3/R4 在最终接口中已经由内部证明消除，但 S/AC 概率输入完整保留。常数只在 M,Cq,Cs 共同固定后统一，不能先隐去 Cq,Cs。

**S/AC 本身、无条件概率输入、B1、Brownian/终端估计、长期 K/Kv、4/π、E1–E6、完整 OQ4 与其他全部根组保持 OPEN。** 普通自由 ρ 不获杀死核谱特征值解释。
