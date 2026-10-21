# 有限杀死核路径 law 独立形式审查 v1

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 实际有限核幂与未归一化 iid 生存终点 law

LEAN_STATUS: 独立服务器无-o目标检查及完整源动态审计均 exit 0，无警告

JUSTIFICATION: 最终源逐行满足冻结的全部有限路径接口。任意 n,h,z 的精确行测度等式包括零步空乘积与 δ_z，不对时0额外 kill。证明拆分未条件化有限乘积，并复用共同 iid 联合 law；有界实测试的两侧可积性和积分等式均单独导出。闭 strip 比较逐点成立且明确要求 h≥0。全部35个实际新增常量通过传递公理白名单，禁用项为空。

## 审查对象与隔离

审查日期：2026-10-21。先只读冻结声明与匿名数学推导，完成并保留 `killed-path-law-math-review-v1.md` 的 MATH_ONLY/LEAN_NOT_RUN 范围，再读最终源及共同定义。本票未读取作者 receipt、作者会话或其他审稿票。只写所分配报告，没有修改实现、冻结声明、共同文件或缓存，没有生成目标 olean。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-killed-path-law-v1.md` | `6be5723b10a67aa0542f845db74fdbbe6bf2c68f7ead1286136d41c067617d31` |
| 所审匿名 `drafts/oq4/path-law/proof.md` 快照 | `a4ec974b1b3b886a491f508e05ab55e5ed91612022c2732b259a932992c6a11c` |
| 本机 `drafts/oq4/path-law/KilledPathLaw.lean` 与远程 `Shao/OQ4/KilledPathLaw.lean` | `1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f` |
| 已审 `KilledIteration.lean`，本机/远程一致 | `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5` |
| 共同 `Shao/Probability/FiniteIID.lean`，本机 library/远程一致 | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同 `Shao/Probability/MeasurablePath.lean`，本机 library/远程一致 | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |
| 共同 `Shao/Basic/ClosedSurvival.lean`，本机 library/远程一致 | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同定义依赖 `Shao/Basic/FinitePath.lean`，本机 library/远程一致 | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |

以下未另说明的行号均为最终 `KilledPathLaw.lean` 的一基行号。

## 共同对象与完整量词

共同 `FinitePath.lean` 第18–24行定义 `Path n = Fin n → ℝ` 以及按 `i.val<k` 取和的真正前缀和；第33–34行保证零前缀为0。共同 `MeasurablePath.lean` 第53–55行给此前缀和的 Borel 可测性。共同 `FiniteIID.lean` 第20–24行定义坐标样本路径及其可测性，第32–43行的 `iid_samplePath_map_eq_pi` 恰在可测坐标、iIndepFun、逐坐标 IdentDistrib 为 ν 的前提下给未条件化乘积联合 law。没有复制或改写这些定义。

本源第15–19行定义正时刻生存事件和终点，准确复用共同 prefixSum。第21–31行用可测加法、绝对值、弱不等式和可数交建立两者的 Borel 性。第67行之后 ν 仅假设为实数 Borel 概率律。主要 law 和测试结论中 n 为任意自然数，h,z 为任意实数，没有 n>0、h≥0、|z|≤h 或矩类的隐藏限制。

## 零步、拆分与精确行测度

- 第33–38行明确证明 S₀(h,z)=univ，任意 h,z 都成立。第100–103行的归纳基使用真实核零次幂 δ_z 和空有限乘积；终点为 z。区间外起点及负 h 也不在时0额外杀死。
- 第40–65行先证明 `prefixSum_cons`、终点分拆和生存事件分拆。首步条件为 `|z+y|≤h`，剩余部分为从 z+y 起点的同一正时刻事件。反向构造涵盖 j=0 与 j>0，没有漏首步或将闭条件换成严格条件。
- 第70–83行用实际 `measurePreserving_piFinSuccAbove ... 0` 的逆等价把**未限制** Πₙ₊₁ 拆为 ν⊗Πₙ；`Fin.cons` 的可测性来自该等价。先用保测积分公式，再用 `lintegral_prod`，没有生存后的独立性假设。
- 第85–92行的一步转换直接展开已审真实 killedKernel 的平移 map 与 Icc 限制。区间成员等价 `abs_le` 对任意实 h 成立，不做归一化，也不假设密度。
- 第95–124行对任意非负可测 ENNReal 测试归纳。第105–108行使用真实核幂组合，方向是先一次 killedKernel 再 n 步。第109行明确取得内层核参数积分的可测性，第110–113行取得生存截断路径测试的可测性；随后用核组合积分、一步转换和未限制乘积拆分。分 hy 的两支都逐点使用闭生存恒等式，原子没有被丢弃。
- 第126–135行由全部非负可测测试的积分相等，经 `Measure.ext_of_lintegral` 得冻结的**测度本身**恒等式。其结论是对每个实 z 的核行相等，而非仅总质量、仅矩或 a.e. 起点相等。右侧就是 `(Πₙ.restrict Sₙ)` 的终点推送，没有除以生存概率。

## 任意有界 Borel 实测试

第137–163行的 `killedIterKernel_integral_path` 完整返回三个结论：真实核行下 f 的 Integrable、Πₙ 下生存截断复合测试的 Integrable，以及两个实积分相等。这一接口没有被前述非负测试强式替代。

第145行调用已审有限行有界测试可积性。第146–149行给截断测试的可测性，第150–157行从全局 |f|≤M 在实输入0处导出 M≥0，再逐点证明截断测试绝对值≤M，使用概率 Πₙ 的 `Integrable.of_bound`。因此不是利用不可积默认积分0。第159–163行在已证明的实际 law 上应用可测推送积分和指示/限制积分公式。第165–174行取 f=1，精确得到实质量等于 Πₙ.real(Sₙ)。

## 共同 iid 样本转移

第178–191行在任意概率空间 Ω,μ 上保留全部可测坐标、iIndepFun 和逐坐标 `IdentDistrib (X i) id μ ν` 前提。第187–188行只调用共同样本路径可测性及已证共同 iid 联合法律；再经可测生存事件的 `Measure.restrict_map` 和可测终点的 `Measure.map_map` 得所需逐行样本 law。没有重证共同联合 law，也没有在限制到生存事件后声称独立。

第194–227行同样完整返回核行 f 可积、μ 下样本截断实测试可积以及积分等式。事件是共同可测 samplePath 的可测原像，终点可测；M≥0 与 M 界逐点证明后，用概率 μ 的真实可积性。第229–243行取常数测试给样本实生存概率。n=0 空家族仍在完整量词内，iid 前提为空量化而 μ 保持概率测度。

## closedStrip 与端点

共同 `ClosedSurvival.lean` 第26–27行定义 `closedStrip h` 为所有 k≤n（包括0）满足 `|prefixSum a k|≤h`。第248–257行在 z=0、明确 0≤h 时逐点补入 k=0 的恒真条件，其余 k 正好是 shiftedClosedSurvival；得到的是集合相等。第259–270行直接代入乘积和任意共同 iid 样本的质量等式。

这保留了 n=0、h=0、全零路径、格点及所有达到 ±h 的原子。n=0 且 h≥0 时 closedStrip 为全集；h=0 时所有正前缀必须恰为0，零路径保留。对 h<0，局部正时刻接口仍合法，n=0 为全集、n>0 为空；closedStrip 比较没有越过明确的 h≥0 限制。

弱闭生存条件对应严格离开 `|z+S_k|>h`；源起点 |z|≤h 时没有与源约定的冲突。没有认证额外的无限路径停止时刻定理。

## 独立服务器证据

通过 `tools/server.py` 共享 broker，在指定 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4` 激活固定环境后，顺序运行两个单 Lean 过程，均限 `taskset -c 0-3`：

```text
lake env lean Shao/OQ4/KilledPathLaw.lean
{ 最终完整源码 + #check/#print 与动态审计附录; } | lake env lean --stdin
```

两个过程均不带 `-o`，不生成目标 olean；没有 Lake 构建/更新或缓存获取。目标和动态审计均无警告，broker exit_code=0、stderr 为空，输出 `TARGET_AND_DYNAMIC_AUDIT_EXIT=0`。UTC 为 `2026-10-21T11:29:40Z`。最终源前后 SHA256 均为表列值，直接共同依赖和 FinitePath 也与本机已读源码逐项核对一致。

独立 `#check` 核对了零步、生存拆分、乘积拆分、非负路径积分、两个逐行 law、两个完整有界实测试接口、两个质量接口和三个 closedStrip 接口；与上面的全部量词及可积性结论一致。

动态遍历实际 `env.constants.toList` 中**全部** `env.getModuleIdxFor? declName = none` 声明，没有任何 namespace/root 名称筛选。对每项调用 `Lean.collectAxioms`，任何白名单 `{propext, Classical.choice, Quot.sound}` 外的传递公理都会立即报错。实际完整源重新经 stdin 检查，结果为：

```text
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 35
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
```

20个显式定义/定理全部实际枚举：

```text
shiftedClosedSurvival
shiftedEndpoint
measurable_shiftedEndpoint
measurableSet_shiftedClosedSurvival
shiftedClosedSurvival_zero
prefixSum_cons
shiftedEndpoint_cons
shiftedClosedSurvival_cons
path_pi_lintegral_cons
killedKernel_lintegral_shift
killedIterKernel_lintegral_path
killedIterKernel_eq_path_law
killedIterKernel_integral_path
killedMass_eq_path_probability
killedIterKernel_eq_iid_path_law
killedIterKernel_integral_iid_path
killedMass_eq_iid_path_probability
shiftedClosedSurvival_eq_closedStrip
killedMass_eq_closedStrip_probability
killedMass_eq_iid_closedStrip_probability
```

15个实际生成辅助声明也均审计：

```text
shiftedClosedSurvival.eq_1
shiftedEndpoint.eq_1
shiftedClosedSurvival_zero._proof_1_3
shiftedClosedSurvival_zero._simp_1_2
shiftedClosedSurvival_cons._proof_1_1
shiftedClosedSurvival_cons._proof_1_2
shiftedClosedSurvival_cons._proof_1_3
shiftedClosedSurvival_cons._proof_1_4
shiftedClosedSurvival_cons._proof_1_5
shiftedClosedSurvival_cons._proof_1_6
shiftedClosedSurvival_cons._proof_1_7
killedKernel_lintegral_shift._simp_1_1
killedKernel_lintegral_shift._simp_1_2
killedIterKernel_lintegral_path._simp_1_2
shiftedClosedSurvival_eq_closedStrip._proof_1_1
```

全部35项的传递公理均为标准白名单子集；20项显式声明为全部三项，生成声明可为真子集。另对两个 law、两个实测试接口及 iid closedStrip 质量结论逐项 `#print axioms`，同样只有标准三项。没有 sorryAx 或新增公理。

最终远程源禁用项扫描 `\b(sorry|admit|axiom|unsafe|native_decide)\b` 输出：

```text
PROHIBITED_TOKEN_HITS []
```

## 认证边界

本票只关闭实际有限核幂与未归一化 iid 闭生存终点 law 的连接及上述有限测试/质量等式，不需要 ν 的矩、中心、方差、密度或无原子条件。

**O0、实际 R3/R4、B1、Brownian 近似、能量分母 E1–E6、长时间核极限、4/π、K/Kv、完整 OQ4 与其他全部根组保持 OPEN。**
