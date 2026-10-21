# 单步被杀可测核最终形式版本独立审查 v2

STATUS: CORRECT

LEAN_STATUS: LEAN_FULLY_CHECKED

JUSTIFICATION: 最终代码构造真正的 `ProbabilityTheory.Kernel ℝ ℝ`，精确行为平移像测度限制到闭区间，保留未归一化质量和所有实 h。相对于行测度的 a.e. 支持、有界 Borel 测试两侧的实际可积性及精确积分式均忠实对应冻结 v2。独立无-o服务器目标检查、全部十五个新增常量动态传递公理审计和禁用项扫描通过。认证仅限单步核对象和有界测试接口。

## 对象、版本与隔离

审查日期：2026-10-21；最终独立服务器检查结束于 `2026-10-21T10:19:39Z`。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-killed-kernel-v2.md` | `034cbec4c7e447e9fa27a2c71bc87194924bea2528bef0d7fe7da15667ca3ecf` |
| 数学首阶段所审匿名 `drafts/oq4/kernel/proof.md` 快照 | `d1564da918ada948f94cbfbed2b64c1d92f5961310cd0b8bc6c9267c552cc540` |
| 最终本机 `drafts/oq4/kernel/KilledKernel.lean` | `f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f` |
| 最终远程 `Shao/OQ4/KilledKernel.lean` | `f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f` |
| 远程直接依赖 `Shao/OQ4/KilledCosine.lean` | `054816685c54b0001d10063cabf445755e54bd33017289be6a0356a31a5b3de8` |

远程工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。本机与远程最终哈希一致，目标检查前与动态审计后的远程哈希一致；直接依赖与此前独立认证版本一致。以下 Lean 行号均对应最终 `f90c...626f` 源。

先仅依据冻结 v2 和匿名证明完成了独立数学审查，保留于 `review/killed-kernel-math-review-v2.md`，该历史票仍为 `MATH_ONLY / LEAN_NOT_RUN`。之后才完整读取最终代码的签名与证明体。未读取作者 receipt、作者会话、v1 审稿票或其他正确性票；没有修改作者代码、冻结声明、共享文件、缓存或根导入，没有生成作者模块 olean。

## 真正的核及精确未归一化行

1. 第 20 行的 `translationKernel` 和第 25 行的 `killedKernel` 都显式返回 `Kernel ℝ ℝ`；服务器实际 `#check` 确认为 `ProbabilityTheory.Kernel ℝ ℝ`。不是用任意测度族或函数别名替代核对象。
2. 第 21–22 行使用确定性 id 核与常值 ν 核的同起点乘积，再取加法的像。ν 只带标准实数 Borel 概率实例；确定性和常值核具有所需有限性，映射加法可测。第 28–33 行经实际核和测度逐行公式确证 `translationKernel ν z = ν.map (fun y => z+y)`。
3. 第 25–26 行直接对固定闭集 `Icc(-h,h)` 限制输出。第 36–38 行对任意实 h,z 证明精确等式

   `killedKernel ν h z = (ν.map (fun y => z+y)).restrict (Icc(-h,h))`。

   没有存活概率分母、行归一化或质量重新分配。
4. 所有声明仅要求 ν 为概率测度，没有中心、方差、id 可积、其他矩、密度、非格点或有界支持条件。平移和取像不需要任何增量矩。
5. 起点 z 为任意实数，恰是冻结为使用标准核类型所允许的全实轴延拓。没有把源域外起点的其他 killed 过程约定偷换为本构造的结论。

## 行质量与正确的行 a.e. 支持

1. 第 41–44 行给出真正的 `IsFiniteKernel` 实例；服务器实际 `#check` 确认其类型。第 47–53 行另给全 h,z 的明确统一上界 `P_h(z)(univ)≤1`，用限制不增质量和平移像的总质量一证明，不依赖自动实例中的某个未说明数值常数。
2. 第 55–58 行将 ENNReal 质量界合法转为实质量界，上界 1 有限，故不存在无限测度经 `toReal` 变零的漏洞。每行实际有限，统一界为一。
3. 第 61–65 行支持声明明确为 `∀ᵐ w ∂killedKernel ν h z, |w|≤h`。证明在精确行上使用 `ae_restrict_mem`，再用 `abs_le`，没有相对于原 ν、其他 κ 或全实轴点态支持作错误断言。
4. h 完全没有正性条件。h<0 时 `Icc(-h,h)` 为空，行等式给出零行；相对于零行的 a.e. 支持合法。h=0 时限制集为 `{0}`，ν 在 `y=-z` 的原子仍以其原质量保留。闭边界等号从未被排除。
5. 测试 f=1 的直接含义是行总质量 `ν{y:|z+y|≤h}`，一般小于一；这与未归一化杀死完全一致。

## 有界 Borel 测试：两侧真实可积及等式

冻结第 14–16 行对应第 68–74 行，完整签名返回：f 对每行可积、条件组成函数对 ν 可积、两积分相等。

1. `hf : Measurable f` 是标准实数 Borel 可测性；`hbound : ∃ M:ℝ, ∀w, |f w|≤M` 正是全局有界 Borel 测试，不是一个额外的 f 矩条件。第 75–76 行从非空实域中取 w=0 证明 M≥0，未额外假设行非零或限制集非空。
2. 第 77–80 行利用有界 Borel f 和实际有限行测度返回左侧 `Integrable`。行有限性来自已证核有限实例；该论证适用于所有实 h,z。
3. 第 81–89 行证明右侧条件函数可测，内部用同一 M 控制，外部零用 M≥0 控制，再借 ν 概率性返回右侧 `Integrable`。没有将不可积实积分默认零当作其存在性。
4. 第 90 行先返回两个可积结论后才处理等式。第 91–93 行使用精确行等式、可测闭集的指标积分公式和可测平移的像测度积分公式；`hf.indicator measurableSet_Icc` 明确供应中间指标函数的强可测条件。该指标函数也有同一 M 的范数界，完整平移像测度有限，故中间积分同样真实可积。
5. 第 94–96 行逐点把 `z+y∈Icc(-h,h)` 改写为 `|z+y|≤h`。这对所有实 h 成立，不使用无原子性，保留等号边界和任意大跳。

该接口没有宣称任意不可积 f 的线性；源需要的常数、余弦和已证有界残差均落在其范围内。

## 余弦测试与旧 Kcos 的精确对应

第 99–102 行对任意实 a,h,z，将 `f(w)=cos(aw)` 及界 1 代入一般有界 Borel 定理。两个可积性由同一定理提供，输出的条件积分按旧定义恰为 `Kcos ν a h z`。没有相位、归一化或边界差异，也没有只得到不等式或渐近关系。

自由余弦系数没有被当成核特征值；该接口不使用 R0 中心矩条件，也不证明核幂或时间递推。

## 独立服务器检查与全部新增常量

使用项目钉死环境 Lean `4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。通过 `tools/server.py` 正常完成；返回远程 `exit_code=0`、空 `stderr`。所有 Lean 仅在指定服务器执行，四核亲和、一次一个 Lean 进程，无本机 Lean、缓存下载或共享缓存写入。

实际目标命令：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KilledKernel.lean
```

该无 `-o` 检查退出 `0`、无警告。再将最终源、真实核/有限实例的 `#check`、关键定理的 `#print axioms` 及动态审计附录经标准输入送入服务器 `taskset -c 0-3 lake env lean --stdin`，退出 `0`，不生成目标 olean。

动态审计遍历环境常量，筛选 `env.getModuleIdxFor?` 为 `none` 且属 `Shao.OQ4` 的本模块声明，排除导入依赖；对每项独立调用 `Lean.collectAxioms` 并强制检查白名单。实际共十五项，含十个显式声明与五个生成辅助声明：

```text
Shao.OQ4.translationKernel: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel.eq_1: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel._proof_1: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel.congr_simp: [propext, Classical.choice, Quot.sound]
Shao.OQ4.translationKernel_apply: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel_apply: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel_isFiniteKernel: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel_mass_le_one: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel_real_mass_le_one: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel_ae_support: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel_integral_bounded: [propext, Classical.choice, Quot.sound]
Shao.OQ4.killedKernel_integral_bounded._simp_1_1: [propext]
Shao.OQ4.killedKernel_integral_bounded._simp_1_2: [propext, Quot.sound]
Shao.OQ4.killedKernel_integral_cos: [propext, Classical.choice, Quot.sound]
NEW_DECL_COUNT 15
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
PROHIBITED_TOKEN_HITS []
```

行等式、行支持、有界测试及余弦测试四个关键定理的独立 `#print axioms` 也仅含白名单三项。作者源的 `sorry|admit|axiom|unsafe|native_decide` 机械扫描为空。没有依赖作者的声明数量或 audit receipt。

## 最终范围与根状态

**冻结 v2 的一步真实核、精确行、统一有限子概率界、行 a.e. 支持和有界测试积分接口为 CORRECT / LEAN_FULLY_CHECKED。**

**核幂与有限 iid 路径事件的对应、O0、实际概率 R3、Markov 半群长时间估计、K、Kv、完整 OQ4 及全部其他根组保持 OPEN。** 本票不能被用作这些尚未形式化依赖的证明。
