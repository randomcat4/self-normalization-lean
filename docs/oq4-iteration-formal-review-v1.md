# 被杀核有限迭代最终形式版本独立审查 v1

STATUS: CORRECT

LEAN_STATUS: LEAN_FULLY_CHECKED

JUSTIFICATION: 最终代码忠实覆盖冻结的有限核幂、子概率质量、零步/正步支持、有界 Borel 测试及精确质量界、真实半群积分、实线性、绝对值支配和两种序比较。每次使用积分代数或比较都有实际可积性。独立服务器无-o目标检查、全部三十三个新增常量的动态传递公理审计和禁用项扫描均通过。认证只限有限核代数。

## 对象、版本及独立性

审查日期：2026-10-21；独立服务器检查完成于 `2026-10-21T10:48:31Z`。

| 对象 | SHA256 |
|---|---|
| `drafts/oq4/frozen-killed-iteration-v1.md` | `256810e98f25fbe2a5f5fc6e73cf189083292892363b55b0df481e153c4223f2` |
| 数学首阶段匿名 `drafts/oq4/iteration/proof.md` 快照 | `0b2d66aae33ee180cd1c4066efc241f0c32a3f046a909c76a0818c0ad4e5f07b` |
| 最终本机 `drafts/oq4/iteration/KilledIteration.lean` | `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5` |
| 最终远程 `Shao/OQ4/KilledIteration.lean` | `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5` |
| 远程直接依赖 `Shao/OQ4/KilledKernel.lean` | `f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f` |

远程工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。本机与远程最终源哈希相同，实际检查前后远程目标哈希一致，直接依赖与此前独立认证版本相同。以下 Lean 行号均对应该最终源。

先只读冻结文件和匿名推导完成独立数学审查，保留为 `review/killed-iteration-math-review-v1.md` 的 `MATH_ONLY / LEAN_NOT_RUN` 历史票，之后才完整读取最终签名和证明体。未读取作者 receipt、作者会话或其他正确性票，未使用作者声明数量或检查自述作为证据。没有修改作者源、冻结前提、共同文件、缓存或根导入，没有生成目标模块 olean。

## 实际核幂、统一有限性和正确的支持范围

1. 第 16–19 行仅量化 ν 的标准实数 Borel 概率实例及任意实 h，`killedIterKernel` 定义正是实际 `(killedKernel ν h)^n`，返回真正的 `ProbabilityTheory.Kernel ℝ ℝ`；服务器 `#check` 已确认类型。没有把一个独立的路径事件函数命名成核幂，也没有额外矩或 h 正性前提。
2. 第 29–30 行对任意 z 给出零步行 `δ_z`。第 32–44 行用真实核幂的后继 lintegral 公式与单步质量≤1，归纳得到全部行的 ENNReal 总质量≤1；没有使用 Bochner 积分默认值。
3. 第 46–47 行显式用共同上界一构造 `IsFiniteKernel`，因此是统一有限性而非仅逐行存在某个有限界。第 49–53 行在上界一有限的条件下合法转为实数质量≤1。
4. 第 56–63 行正时间支持明确要求 `0<n`，但允许任意起点 z。它将正幂写成单步 P 与先前幂的合成，使用所有单步行的 a.e. 闭支持及可测闭集，通过真实核合成 a.e. 定理得到结论。
5. 第 66–70 行所有 n 的支持明确增加 `|z|≤h`。零步分支用 Dirac 和该起点条件；没有错误地声明任意区间外起点的零步行受闭域支持，没有在时间零补做杀死。

h=0 仍允许单步闭集上的原子；h<0 时正步行由空闭域支持为零，零步仍为 Dirac。所有这些边界都由真实单步核和幂定义保留，没有额外 h 假设。

## 有界 Borel 测试、参数可测与 M G_n

1. 第 22–27 行 U_n 和 G_n 定义与冻结完全一致：真实幂行的实积分及常数一作用。第 72–76 行对任意有界 Borel f、全部 n,z 显式证明 `Integrable f (P^n(z))`，依据真实有限行及常数范数界。没有将 f 本身作为概率律或要求其矩。
2. 第 78–80 行用实际有限/SFinite 核的强可测参数积分定理，得到 `U_n f` 可测。这个辅助可测性声明对一般可测 f 更强；它没有声称不受界控制的 f 都可积。冻结涉及的所有有界测试另有第 72–76 行的真实可积性，故不存在默认积分零漏洞。
3. 第 82–92 行证明 `G_n(z)=P^n(z).real(univ)` 及 `0≤G_n≤1`。幂行有限由此前实例保证，实质量不是由无限质量的默认 `toReal=0` 得到。特别是零步 G_0=1，对所有 z 成立。
4. 第 95–104 行先取得 f 的真实可积性，再用积分范数不等式、`hfi.abs` 与可积常数 M 的单调比较，给出精确的 `|U_n f(z)|≤M G_n(z)`。没有删去存活质量因子或把正步行归一化。
5. 第 106–116 行从全局范数界在点 0 推得 M≥0，再用 `G_n≤1` 得 `|U_n f|≤M`，返回作用后函数的真实全局有界性。M=0、零行都不需要除法或严格正性。

## 零步、单步和半群：内外积分逐项核查

1. 第 118–119 行给出 `U_0 f(z)=f(z)`，包括区间外 z 和任意实 h。该辅助陈述甚至不要求有界 Borel f；实数域 Dirac 积分可给更强结论，冻结的有界 Borel 情形是其子情形，没有前提漂移。
2. 第 121–126 行用 P¹=P 和已审单步接口，显式返回条件平移测试对 ν 可积及精确 U_1 表达。左侧 f 对行的实际可积性由统一的第 72–76 行提供。弱边界与原子完整保留。
3. 第 129–133 行单独证明外层 `Integrable (U_n f) (P^m(z))`，使用的是已经证明的内层参数可测性及作用后的全局有界性。没有把外层可积性当作额外假设。
4. 第 138–141 行按实际幂加法律和自然数加法交换，将 `P^(m+n)` 精确改写成 `P^n ∘ₖ P^m`。这只使用同一 P 的幂代数，不假定任意不同核交换。
5. 第 142–146 行首先从有界测试定理得到 f 对真实 `P^(m+n)(z)` 行可积，再改写为复合行可积，把该条件传给 `Kernel.integral_comp`。每个内层 f 行积分对所有中间点实际可积，内层函数可测/有界及外层真实可积由前述独立声明满足。因此 `U_(m+n)f(z)=U_m(U_n f)(z)` 是真实 Bochner 半群恒等式，包含 m=0、n=0，没有非法 Fubini 或默认零替换。

## 实线性、绝对值支配及序

1. 第 148–154 行加法直接传入 f,g 的两个真实可积性给 `integral_add`。其和自动可积，故左侧不是不可积积分的默认值；没有要求 f,g 非负。
2. 第 156–161 行允许任意实 c，明确返回 cf 的真实可积性，然后应用实常数乘积分公式。负 c 和 c=0 均包含。
3. 第 163–168 行明确返回 |f| 的可积性，并用真实行积分的范数不等式给 `|U_n f|≤U_n|f|`。
4. 第 170–175 行对任意起点的全局 f≤g，使用两项真实可积性和逐点比较转成 a.e. 比较，再用积分单调性。
5. 第 177–184 行闭域比较保留起点前提 `|z|≤h`，使用所有 n 的正确行支持把闭域点态比较转成行 a.e. 比较。零步时该前提没有被删去，所以不会将闭域比较错误应用于区间外 Dirac 行。h<0 时闭域起点陈述真空成立。

上述签名和证明完整覆盖冻结第 11–16 行，没有加入中心、矩、密度、非格点、有界跳跃或 h>0 条件。

## 独立服务器检查和全部新增声明

使用项目钉死环境 Lean `4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。经 `tools/server.py` 正常返回远程 `exit_code=0`、空 `stderr`，没有失败重放或旁路 broker。所有 Lean 均在指定服务器四核亲和、单进程序列执行，没有本机 Lean、缓存下载或共享缓存改写。

实际无-o目标命令：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/KilledIteration.lean
```

目标退出 `0`、无警告。再将最终源、真实核类型 `#check`、五项关键定理 `#print axioms` 和动态审计附录经标准输入送入服务器 `taskset -c 0-3 lake env lean --stdin`，退出 `0`；不生成目标 olean。

动态遍历环境常量，筛选 `env.getModuleIdxFor?` 为 `none` 且属 `Shao.OQ4` 的当前模块声明，排除全部导入依赖。每项独立调用 `Lean.collectAxioms` 并强制核对公理白名单。实际得到二十六个显式声明与七个生成辅助声明，共三十三项。以下用 `S` 表示完全相同的许可集 `[propext, Classical.choice, Quot.sound]`：

```text
killedIterKernel: S
killedAction: S
killedMass: S
killedIterKernel_zero: S
killedIterKernel_mass_le_one: S
killedIterKernel_isFiniteKernel: S
killedIterKernel_real_mass_le_one: S
killedIterKernel_ae_support_pos: S
killedIterKernel_ae_support: S
killedAction_integrable: S
killedAction_measurable: S
killedMass_eq_real: S
killedMass_nonneg: S
killedMass_le_one: S
killedAction_bound_mass: S
killedAction_bound: S
killedAction_bounded: S
killedAction_zero: S
killedAction_one: S
killedAction_iterated_integrable: S
killedAction_semigroup: S
killedAction_add: S
killedAction_smul: S
killedAction_abs: S
killedAction_mono: S
killedAction_mono_closed: S
killedAction.eq_1: S
killedIterKernel.eq_1: S
killedIterKernel.congr_simp: S
killedMass.eq_1: S
killedMass.congr_simp: S
killedIterKernel_ae_support_pos._proof_1_1: [propext, Quot.sound]
killedIterKernel_ae_support._proof_1_2: [propext, Quot.sound]
NEW_DECL_COUNT 33
TARGET_AND_DYNAMIC_AUDIT_EXIT=0
PROHIBITED_TOKEN_HITS []
```

上述名字均带前缀 `Shao.OQ4.`。正步支持、精确质量加权界、外层可积性、半群和闭域序比较五个关键定理的独立 `#print axioms` 也均为 S。作者目标源的 `sorry|admit|axiom|unsafe|native_decide` 机械词项扫描为空。数量和结果来自本票实际独立枚举，不依赖作者自述。

## 最终范围

**冻结 v1 的有限核代数为 CORRECT / LEAN_FULLY_CHECKED。** 零步仍是全实轴上的恒等核；只有正步或闭域起点才使用闭支持，h=0 原子及负 h 语义均保留。

**有限 iid 路径表示、实际生存概率、O0、实际概率 R3/R4、D0/D1 的概率输入、Brownian 近似、K、Kv、完整 OQ4 及其他全部根组保持 OPEN。** 不能将真实核有限幂及代数的认证，改称这些后续概率或长时间结论已闭合。
