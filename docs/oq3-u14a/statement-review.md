# U14a 二元相对熵下界：独立声明与来源审查

STATUS: CORRECT

仅独立声明/source gate；本单元尚无实现。reviewer lease 1，只写本新报告及授权 `runs/oq3/u14a-20261021/statement-review.md`；不修改 source/scope/旧票/共享文件/缓存，不 spawn，不运行 Lean/API 探针、构建或 commit。先仅提取冻结 Lean fence 的两个定义体和四完整类型，独立盲译并先落盘，再读解释、R1 与固定库。

## 1. 冻结代码块的先行盲译

冻结 `thirty-second-unit-scope.md` SHA256 `15a8b914a070b6633d60801a2d1b1d27053673a556e93edfa2bb4f67789fffe3`。本阶段未读 scope 其余解释/证明路线或源文；以下按代码字面翻译。

1. `entropyRemainder x` 定义实函数 F(x)=x·Real.log x−x+1，定义域为全部 ℝ，没有类型内 x>0 门。定理将限制 x≥0；Real.log 在 x=0 及负数的库总化语义，必须后续核对，不能以经典正域 log 默默替代。
2. `binaryRelativeEntropy p z` 定义实表达式 B(p,z)=p·Real.log(p/z)+(1−p)·Real.log((1−p)/(1−z))，字面定义对任意实 p,z；公开下界只在 p∈[0,1]、z∈(0,1) 断言。没有概率测度类型或扩展实无穷值，端点 p=0/1 与零权对数项需要实际库语义核对。
3. `entropyRemainder_quadratic_of_le_one`：对任意实 x，0≤x≤1 时，(x−1)²/2≤F(x)。包括 x=0 与 x=1，没有漏掉零端点。
4. `entropyRemainder_quadratic_of_one_le`：对任意实 x，1≤x 时，(x−1)²/(2x)≤F(x)。该门使分母 2x 严格正；x=1 同样包含。
5. `entropyRemainder_nonneg`：对任意 x≥0，0≤F(x)。不是对所有实 x 断言，也没有额外 x≠0 或归一化假设。
6. `binaryRelativeEntropy_refined_lower`：任意实 p,z，只要 0≤p≤1 且 0<z<1，就有 (p−z)²/(2·max(p,z))≤B(p,z)。p 的两端点都允许，z 的两端点排除；max(p,z)≥z>0。该完整类型只是这一明确充分下界，没有声称最优常数、所有参数全局最小值、熵不等式的新颖性或与无限测度 KL 的无条件等同。

本节盲译先行落盘，尚未判断源归属、数学可证性或静态环境。根 A/B/C/D 均 OPEN。

## 2. R1 来源与冻结说明

盲译先落盘后才读 scope 说明及真实原文。拟文件 BinaryEntropyBounds.lean，导入 Log.NegMulLog、**Analysis.Calculus.Deriv.MeanValue** 和已缓存的六个 proof-only 分模块 FieldSimp/Ring/Positivity/Linarith/FunProp/NormNum；namespace Shao.OQ3、noncomputable。本地冻结 scope 与服务器 run/scope.md 的实际 SHA256 均为 `15a8b914a070b6633d60801a2d1b1d27053673a556e93edfa2bb4f67789fffe3`，两定义/四完整类型与盲译一致。

真实 R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` 已核，实际读取 161–259。180–188 的 Bernoulli kernel 与数据处理把原测度 KL 降至 d(p‖z₀)；196–225 的 (11)–(13) 再控制这个二元实表达式。本候选提供的正是后一阶段可用的**标准充分纯实下界工具**，不是 (10) 的 kernel/data processing 定理，也未完成 (9) 的 likelihood/KL 差恒等式或 231–237 的全局最小性/尾内点降熵。

有效域 p∈[0,1]、z∈(0,1) 下，B(p,z) 数学上是有限 Bernoulli 相对熵，两参考原子 z、1−z 都正，p 的零权项按实际 0log0=0 解释。因此与源 d(p‖z₀) 对应；正式与某个实际 Bernoulli kernel/测度 KL 定义的绑定仍属后继工作，不能只由函数名宣称数据处理已证。

源 (11) 的系数含 1/[z₀(1−z₀)]，本目标在 p≤z₀ 只给 1/z₀，确较弱；但代入源 p−z₀=q(R−1)(R+1)/H 后，其率比仍为 `q²(R+1)²/(2H²z₀)`，源所给数值范围使它 >3.9/(2·51·0.03)>1，足够该范围的正间隙。p≥z₀ 时本目标给源 (12) 中的 `q²(R+1)²/(2H(qR²−1))` 非严格下界；源后续严格数值裕度仍可把它用于充分间隙，不必声称这里复现 (12) 的最强严格首不等式。

源 (13) 的另一个标准解析片段也与第三目标相符：对补比率 y=(1−p)/(1−z)≥0，(1−z)F(y)≥0 给 `(1−p)log((1−p)/(1−z))≥−(p−z)`，包括 p=1；之后还需要源的 p/z>e³ 等实条件，才能推出 >2p。**单独的最终二次下界不等于整个 (13) 或全局最小性证明**。本票只确认这些源接口的正确适配，不计 kernel、数值率间隙、唯一性或根闭合。

这些是经典熵/对数的充分估计；本候选没有最优常数、全参数最小值、最弱修复或新颖性主张，本票亦不认证这些性质。

## 3. 数学可行性与端点

### 3.1 实际实对数与零端点

固定库 Real.log 的真实定义在 x>0 是通常自然对数、在 x<0 用 log|x|、在 x=0 定为 0；`Real.log_zero` 与 `log_one` 已实际核验。定理域始终不使用负数的“熵解释”。实际 `Real.continuous_mul_log` 给整个 ℝ 上 xlogx 的真正连续性，故 x=0 的乘积延拓为 0；这不是在 0 使用 log 导数或假定 log 本身在 0 连续。

F(0)=1，所以首目标在 0 是 1/2≤1，非负目标为 0≤1；F(1)=0，两个二次下界在 1 都为等号。第一目标的闭域允许 0，需要这一真实连续性；第二目标的 x≥1 则始终有 x>0、2x>0。

### 3.2 首两个二次下界的独立验证

在 D=[0,1] 上令 g₁(x)=F(x)−(x−1)²/2。由 continuous_mul_log 与多项式运算，g₁ 在闭 D 上真 ContinuousOn；只在 interior D=(0,1) 取导，此时 x≠0，实际 HasDerivAt_mul_log 给

`g₁'(x)=log x−(x−1)≤0`

（实际 `Real.log_le_sub_one_of_pos`）。D 凸，g₁ 在内部真 DifferentiableOn，故实际 `antitoneOn_of_deriv_nonpos` 给 g₁(x)≥g₁(1)=0，包括两个端点。没有对 x=0 求导，也没有只在开区间证后直接遗漏闭端点。

在 D=[1,∞) 上令 g₂(x)=F(x)−(x−1)²/(2x)。x≥1 使有理分母不为 0，故 g₂ 真 ContinuousOn；只在内部 x>1 求导，实际 HasDerivAt_mul_log 和 quotient/inverse 导数给

`g₂'(x)=log x−1/2+1/(2x²)`。

用 `Real.one_sub_inv_le_log_of_pos` 得 log x≥1−1/x，于是

`g₂'(x)≥1/2−1/x+1/(2x²)=(x−1)²/(2x²)≥0`。

这些分母的消去只在 x>0、x²>0 后进行。实际 `monotoneOn_of_deriv_nonneg` 在凸闭半轴 D 上适用；它只需内部可微、整个 D 连续，无需 D 有界。于是 g₂(x)≥g₂(1)=0，包括 x=1。第一、第二目标的数学方向与正分母均正确。

### 3.3 非负目标

对 x≥0 分 x≤1 与 1≤x，前两下界左端分别是平方/2、平方/(2x)，均真非负，立即给 F(x)≥0。也可直接消费当前已有 `Real.self_sub_one_le_mul_log` 的完整非负域版本；该固定 API 本身已覆盖 x=0，不要求额外 log 正域。此目标不是从未经证明的一般 KL 非负性套名得到。

### 3.4 二元熵精确分解与 refined lower

给定有效域，z>0、1−z>0，p/z≥0、(1−p)/(1−z)≥0。直接展开 F，用**仅 z≠0、1−z≠0**的分母消去和环运算，得到真实恒等式

`B(p,z)=zF(p/z)+(1−z)F((1−p)/(1−z))`。

这里完全不需要拆 `log(p/z)=log p−log z`，也不需要取消可能为 0 的 p 或 1−p；所以 p=0/1 无 log_div 或 0/0 漏洞。第二项由 F 非负与 1−z>0 真非负，可丢掉以取得充分下界。

若 p≤z，则 0≤p/z≤1，第一二次界乘 z>0 得 `zF(p/z)≥(p−z)²/(2z)`，且 max(p,z)=z。此分支容许 p=0，没有取消 p。若 z≤p，则 p≥z>0，p/z≥1；第二二次界乘 z 并在 p,z 真非零后整理，得 `zF(p/z)≥(p−z)²/(2p)`，且 max(p,z)=p。p=1 时补比率为 0，F(0)=1、补项非负照常有效。p=z 时比率均为 1，B=0、下界 0。

因此完整四假设确实足够覆盖所有端点，max(p,z)≥z>0 保证最终 2max 分母真正。不是只证 p∈(0,1) 后遗漏 p=0/1，也不是把 complement 的熵项自身错当非负（非负的是相应 F 项）。

作为端点核对，B(0,z)=−log(1−z)，B(1,z)=−log z，均有限；下界分别为 z/2 与 (1−z)²/2，实际通常 log 不等式也直接支持。定义在 z=0/1 及其它实参处虽为总化表达式，公开类型没有在那里给 Bernoulli KL 或当前下界解释。

## 4. 固定库、环境与哈希

所有库与 cache 检查通过共享 server.py 在指定服务器只读完成；未运行 Lean、API probe、数值重型计算或构建，也没有写 cache。

| 固定 actual API | 本次核验的完整前提/语义 | 源 SHA256 |
|---|---|---|
| Log/NegMulLog:39–42,45–59,68–74 | x≥0 的 x−1≤xlogx；真 continuous_mul_log 含 0；hasDerivAt_mul_log 仅 x≠0 | `00039257907338466419ea23f63e9e403f1f7f4a431d57d0f09bdf9bda6577a1` |
| Log/Basic:39–45,103–108,138–145,307–313 | log 的实际零/负域定义；log_zero/log_one；log_div **需要分子、分母均非零**；log_inv；正域的上下界 | `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97` |
| Analysis/Calculus/Deriv/MeanValue:412–416,481–485 | 真实 monotoneOn_of_deriv_nonneg/antitoneOn_of_deriv_nonpos，要求凸 D、ContinuousOn D、DifferentiableOn interior D、内部真导数符号 | `b6f3e52c283bdd2c3eb01173c8ac32b82dff0efdfc1890c361f8eed63359edb8` |
| Analysis/Calculus/Deriv/Inv:112–115,174–176 | 实际 HasDerivAt.inv/div 及分母非零门，可供 g₂ 有理项求导 | `97bf4871f60ae5571aa9e1f84be6ccdc5bb7dfbfee5517fb7c927e9d5591947d` |

这里使用的是 **Analysis/Calculus/Deriv/MeanValue** 的实际签名；quotient 导数 API 在 **Deriv.Inv**。实际 public 路径为 NegMulLog→Log.Deriv→Calculus.LogDeriv→Deriv.ZPow→Deriv.Inv，Log.Basic 亦由 Log.Deriv 公开可见；凸域 API 经 Deriv.MeanValue 的实际公开链到 Convex.Basic。无需新增 import 或缓存。

实际 `.olean` 只读存在：NegMulLog 43896 bytes，Deriv.MeanValue 76040，FieldSimp 1681840，Ring 1648，Positivity 1832，Linarith 2536，FunProp 2488，NormNum 2496；相关 Log.Basic 264384、Log.Deriv 87472、Deriv.Inv 141992、Convex.Basic 314640 亦可见且有缓存。Mathlib.Tactic 总入口实际不存在，但冻结明确不导入它，只用上述六个已缓存分模块；这不是候选的环境缺口。

纯实声明无需 OQ3 前置、MeasureSpace、Matrix norm 或概率 typeclass，新 namespace/scoping 与定义/四类型相容。本地/远端 scope hash 如 §2；实际 lean-toolchain 为 `leanprover/lean4:v4.36.0-rc1`，manifest mathlib rev 与真实 mathlib git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。这些是静态源码/cache/pins 核验，不是新目标 elaboration 成功记录；本单元尚无 implementation 或作者 receipt/Audit 可读。

## JUSTIFICATION

**STATUS: CORRECT。** 两个冻结定义体及四完整类型的数学域、端点、分母正性与标准实 log 语义正确；固定缓存/API/imports 足够支持所需证明，未发现必须修订的声明或环境 blocker。首个闭域二次界可通过 xlogx 的真实连续性和内部负导数覆盖 x=0；第二界在 x≥1 的正分母域由内部正导数得到；非负界包括 0；二元分解只消正 z/1−z，结合两分支给所有 p∈[0,1] 的明确 refined lower。

来源定位为 R1 (10)–(13) 后续全局估计可用的**标准充分下界**，不是最优性、全局最小值或新颖性认证。没有完成实际 Bernoulli kernel、数据处理、测度 KL/likelihood 差、数值率间隙、唯一性/尾内点降熵，也不由 U13c 条件特征收敛推出这些结论。根 A/B/C/D 全部 **OPEN**。

本票只批准声明/source gate，尚未审查实际 Lean implementation/actual TYPE/内核或作者机械门。仅交付本地 `drafts/oq3/u14a-statement-review.md` 与授权 run `statement-review.md`；两端最终 SHA256 随交付独立核验。未改 source/scope/旧票/共享文件/缓存，未 spawn、运行 Lean/API probe、构建或 commit。
