# U22p 独立完整最终证明审查

STATUS: CORRECT
ACCEPTANCE_STATUS: REVIEW_COMPLETE_FOR_LF_EXACT_SOURCE

日期：2026-10-23。角色：唯一 fresh 独立完整最终审查员，与作者分离；调度指定 gpt-6.1-sol / xhigh，未切换模型。本上下文不提供可靠的逐类 token 使用统计，故不编造使用量。采用 math-theorem，不采用 math-ultra；未派生其他上下文。

最终裁决为 CORRECT，适用于新 LF 精确源码 SHA256 `7ecd01d72c2f28ec06080d628f5d5370b3ae03b312acbae18a104569f8fef1b6`（2752 B、66 行）。全部源代码、唯一实际所有者及其完整类型均已独立完整审查，无数学证明或证据缺口。第 1–7 节保留首次完整数学审查、旧字节证据及发现的 CRLF 缺陷；第 8 节在同一 fresh 上下文核对确定性换行修复及新精确服务器成功凭据。旧冻结字节与所有历史回执保持不变，未将旧版直接记 accepted。

## 1. 冻结对象与完整实际声明

模块：`Shao.OQ3.LocalCubicTaylor`。首次完整数学审查源码当时位于 `drafts/oq3/u22p-source.lean`，现另存为 `drafts/oq3/u22p-source-frozen-crlf.lean`，66 行、2818 字节，SHA256 `abecbbb23d3ad1e859b778d46de1631f370c1e6af3baeb442d93ca260f21b4c1`。首次审查时本地、服务器归档 `source-03.lean` 与服务器工作树同路径源码均直接读取字节，确认完全同哈希。修复后的当前版本见第 8 节。

冻结范围为 `drafts/oq3/ninety-seventh-unit-scope.md`，28 行、2523 字节，SHA256 `cb8f37ca9bfee4a2f5238480bf46d5a701cc7eed0ea59323a7a65594250e63f1`。完整冻结声明与最终源码 10–14 行、实际审计输出逐项一致。

实际唯一所有者：`Shao.OQ3.exists_uniform_cubic_taylor_bound_at_zero`。完整实际类型为：

```lean
∀ (g : ℝ → ℝ),
  ContDiffAt ℝ 3 g 0 →
    ∃ rho C,
      0 < rho ∧ 0 < C ∧ ∀ (r : ℝ), |r| ≤ rho →
        |g r - g 0 - deriv g 0 * r - deriv (deriv g) 0 / 2 * r ^ 2| ≤ C * |r| ^ 3
```

实际类型文件 `u22p-actual-types.txt` 已完整读取全部 6 行、308 字节，SHA256 `4ea16b67c60c8582bff36323cc900166d10d6888af29630928bd4cb86a263f6f`。它包含唯一声明的全部类型及公理列表。零公开定义、零实际定义，故没有遗漏的定义值待审查；零私有定理、零生成定理。实际所有者总数为 1，实际定理总数为 1。没有隐含的额外数学前提、概率律、参数族或项目证明依赖。

## 2. 全部 66 行源码覆盖

以下范围互补地覆盖源文件全部 1–66 行，包括空行与闭合命令；无抽样审查。

| 源码行 | 已审查内容及结论 |
| --- | --- |
| 1–9 | 全部三个标准 Mathlib 导入、namespace/open/scoped/noncomputable section。没有项目假设导入、逻辑绕过或额外声明。 |
| 10–14 | 唯一公开定理的完整参数、前提、量词、严格正半径/常数与闭双侧结论，与冻结类型一致。 |
| 15–24 | 从有限阶 C³ germ 得到同阶邻域，取正球半径 a，构造开凸区间 s=(-a,a)，证明 0∈s、s⊆u，并限制 C³。 |
| 25–29 | 对 n=3 调用完整三阶 Peano Taylor 小 o 定理；通过 s 为零点的邻域，将 within 滤子正确改为完整零点邻域。 |
| 30–39 | 在开区间内将全部需要的 within 迭代导数改为全域实际迭代导数；完整展开 0、1、2、3 次项，核对 1、1/2、1/6 系数及乘法方向。 |
| 40–45 | 用小 o 的常数 1 最终界，产生一个严格正 delta；取 rho=delta/2 和 C=1+|A|，在引入 r 之前固定两个常数并证明其严格正性。 |
| 46–52 | 对任意满足 |r|≤rho 的 r，证明 dist(r,0)<delta，包括闭半径端点；应用统一余项界并代入已核对的多项式身份。 |
| 53–63 | 完整代数分解、三角不等式、|A*r³|=|A|*|r|³，以及 (1+|A|)|r|³ 的合并；无符号缺口、无除以 r 的步骤。 |
| 64–66 | 空行及 section/namespace 正确闭合；无额外未覆盖声明。 |

全源词法检查未发现 `sorry`、`admit`、新增 `axiom`、`unsafe`、`native_decide` 或 `implemented_by`。源码没有弱化检查的选项。`noncomputable section` 不增加数学公理，不绕过内核。

## 3. 独立数学证明复核

设 g:ℝ→ℝ 且 g 在 0 具有有限阶 C³ germ。这里 `ContDiffAt ℝ 3 g 0` 是同阶局部光滑性，不是仅声称三个导数在孤立一点存在。Mathlib 的 `ContDiffAt.contDiffOn` 对有限阶 3 允许保持同阶，产生某零点邻域 u 上的 C³；其有限阶附加条件在 3≠∞ 下成立，不使用 C∞ 点态光滑的错误开放性推论。

由度量邻域基，存在 a>0 且 ball(0,a)⊆u。令 s=(-a,a)，则 s 开且凸、0∈s；在实线上 dist(r,0)=|r|，所以 s⊆u。g 因而在 s 上 C³。三阶 Taylor 小 o 定理给出 E(r)=g(r)-T₃(r)=o(r³)，原滤子为 𝓝[s]0。s 是 0 的开邻域，故该滤子等于完整 𝓝0；由此得到两侧而非单侧或仅序列的结论。

在 s 的内部点 0，within 的 k 次迭代导数与全域 k 次迭代导数相等。逐次展开 Taylor 多项式得到

`T₃(r)=g(0)+g'(0)r+g''(0)r²/2+A r³`，其中 `A=iteratedDeriv 3 g 0/6`。

迭代导数的递推式给出一阶项为 `deriv g 0`，二阶项为 `deriv (deriv g) 0`。C³ 前提保证相应实际导数存在；因此没有借用总函数 `deriv` 在不可微点的默认值来伪造系数。三次项 A 是一个实数，无需额外假设其符号或预先给出三阶导数界。

取小 o 定义中的正系数 1，存在 delta>0，使所有满足 dist(r,0)<delta 的 r 都满足 |E(r)|≤|r|³。注意这是以完整邻域为滤子的最终不等式，没有对 r³ 作除法。令 rho=delta/2>0，C=1+|A|>0。当 |r|≤rho 时，由 delta>0 得 |r|≤delta/2<delta，故同一余项界适用于所有这样的 r。去掉 Taylor 多项式的三次项后，二次 Taylor 余项为 E(r)+A r³，因而

`|E(r)+A r³| ≤ |E(r)|+|A r³| ≤ |r|³+|A||r|³ = C|r|³`。

这正是完整冻结结论。rho、C 先于任意 r 被选择，可以依赖 g；没有声称对一族 g 统一。r=0 时左右均为 0；r=±rho 满足严格 delta 邻域条件；负 r 通过绝对值处理；A=0 或 A<0 时 C 仍严格正。证明没有要求 rho≤a：完整邻域的小 o 最终界已经负责保证所需局部性，而多项式展开在系数固定后对所有实 r 成立。没有循环使用所需余项界，没有把 o(r²) 当成 O(|r|³)。

## 4. 固定主 API 的完整条件核对

在已指定服务器工作树的只读 Mathlib 包视图中读取主源码。工具链文件为 `leanprover/lean4:v4.36.0-rc1`，Mathlib commit 为 `807d3836b165983210ee2ecf3cd28f239436949c`。下列七个实际读取文件均逐字节等于该 commit 对应 Git blob；未联网修改依赖，也未改包缓存。

- `Mathlib/Analysis/Calculus/ContDiff/Defs.lean:1013–1015`：`ContDiffAt.contDiffOn` 的 m≤n 与 m=∞→n=ω 条件；本证明 m=n=3，条件成立。该文件 1010–1011 行亦给出足够阶光滑推出可微。
- `Mathlib/Analysis/Calculus/ContDiff/Deriv.lean:121–123`：有限阶 C³ germ 传递到实际导数的低阶光滑性，支持一、二、三阶实际导数的语义。
- `Mathlib/Analysis/Calculus/Taylor.lean:243–262`：`taylor_isLittleO` 需要凸集、中心属于集、集上 Cⁿ；三项均已提供，阶数确为 3。该定理本身的归纳证明也已读取核对，并非假设目标 O 界。
- 同文件 `88–102`：`taylorWithinEval_succ` 与零阶值公式；在 n=2、1、0 的展开中得到准确的阶乘系数。
- `Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:304–321`：`iteratedDeriv_succ` 与 `iteratedDerivWithin_of_isOpen`；开集与中心成员条件满足，不需要伪造全局光滑性。
- `Mathlib/Analysis/Asymptotics/Basic.lean:59–60` 及 `Asymptotics/Defs.lean:69–79`：小 o 产生系数 1 的 `IsBigOWith`；`.bound` 是真正的范数最终界，并处理分母为零的情形。
- `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:778–786`：邻域提供正球半径，最终邻域性质提供统一的正 delta；半径减半将开球界推广到所需闭半径。

Mathlib 工作树提示存在本地变化，是作者凭据已记录的包视图警告。所有本次实际数学 API 源码均与固定 commit 的 Git blob 相同；该警告未遮盖本次所用 API 的数学修改。

## 5. 原源到声明及真实限制

完整读取只读原源 `C:/game/shao/current/oq3/proofs/r2/repair01.md`。其第 3 节定义实际二维边界率 F，式 (11) 要求在固定小矩形统一成立的 `O(|r|³+|r|z+z²)`；后续还有式 (12) 振幅、式 (13) 正下界和式 (14) Laplace 渐近。

U22p 精确提供标准标量分析 producer：若某个真实切向截面 g 具有 C³ germ，就能从实际一、二阶导数产生正的统一闭双侧半径与三次余项常数。这与冻结范围完全一致，有助于式 (11) 的切向三次部分，且没有将目标余项假设写进前提。

本单元没有将 g 实例化为实际 F(r,0)，没有证明真实 F 的 C³、g(0)=Λ₀、g'(0)=0 或 g''(0)=Λ₁；也没有证明二维 z 法向项、混合项、固定矩形上的统一性、正下界、振幅、Laplace、Edgeworth、小单元、远场概率或原 B/D 根结论。这些范围保持 OPEN。该定理是既有 Taylor 理论的标准微积分辅助结果，不作新颖性声明，不作根结论闭合声明。

## 6. 复用的旧版精确服务器内核与全所有者公理证据

服务器 run：`/root/rivermind-data/shao-lean-20261021/runs/oq3/u22p-20261023`；工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；分支 `feat/oq3-boundary-laplace`，记录父提交 `3346440dea28ce226bad375c62b288163ea7479e`。直接比对本地与服务器相应文件的字节哈希，全部一致。

| 工件 | SHA256 |
| --- | --- |
| `u22p-receipt.json` / `receipt.json`，5112 B | `db70760bee990f0c8d0a41742143d31737b1d20eaaef749b63a4ccb2f8f317d9` |
| `u22p-Audit.lean` / `Audit.lean`，1875 B、44 行 | `e474d430607f87a94ba1299934e12c27cf65080ee3b9b1fc232896fcbaef09fd` |
| `u22p-build-history.json` / `build-history.json`，2389 B | `dc9fcdebcaa85e8fff6bab85a1ff1e6d802e40fc474478c7ede3849062e43012` |
| `u22p-audit-record.json` / `audit-record.json`，497 B | `d06c8d15a85c0ec14a468c24d7290d14eb69d3199d974f685fba11a8020b4946` |
| `u22p-audit-environment.json` / `audit-environment.json`，500 B | `369caf3ecd0fb81ce99885b419d50e272faa529d7c37343efed654013aa6c22e` |
| 成功 `build-03.log`，133 B | `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626` |
| 成功 `audit.log`，555 B | `8539dd07f269a0dbd387c5602df7df5d9c3c06fafd9ca47061dde8f41b5c5163` |

作者 source03 内核门退出码 0，用时 5.339434819296002 s；首次完整所有者审计退出码 0，用时 5.826007880270481 s。两者均记录 CPU14–17、native memory 8192 MiB、jobs 4、autoImplicit=false；已存在成功门，本审查员未重编或重审计。原 source01/source02 失败记录均保留，没有将失败写成成功。

完整读取审计源码全部 44 行及成功日志全部实际输出。它按 `getModuleIdxFor?` 的实际模块 owner 遍历环境全部常量，不只扫描公开目标名称或 namespace；对每个实际 owner 使用递归 `Lean.collectAxioms`，拒绝新增项目 axiom，并拒绝三公理白名单以外的传递依赖。成功输出：frozen definitions=0、frozen theorems=1、all theorems=1、all declarations=1、AXIOM_GATE PASS。唯一实际声明及其全类型已在本报告第 1 节完整覆盖，实际没有额外私有/生成声明或定义值漏审。

唯一实际所有者的递归公理精确为 `[propext, Classical.choice, Quot.sound]`。无 `sorryAx`，无额外假设公理，无原源外部结果的 axiom 化。本数学裁决来自上面的完整独立推导与源语义核对，未把 elaboration 或内核成功单独当作数学正确性判断。

## 7. 已发现并保留的格式缺口与待补 delta

直接按字节检查旧源码：2818 B，CR=66、LF=66、CRLF=66，无 UTF-8 BOM。本地源码、服务器归档 source03、服务器工作树三处同哈希且同样为 66 个 CRLF。旧审计源码也有 44 个 CRLF，1875 B。它们违反现行 AGENTS 对未来 Windows 创建并转移的 Lean/Python 源在首次 source-bound 门前使用 UTF-8 LF 的明确要求。这个发现不否定数学证明，但构成该未验收单元的真实格式验收缺口；本报告未将旧版记 accepted。

本审查员没有修改任何实现、审计源码、共享文件或缓存，没有执行任何 Lean 命令。仅在内存作确定性 `CRLF→LF` 推导：旧证明源码预计变为 2752 B、66 行，SHA256 `7ecd01d72c2f28ec06080d628f5d5370b3ae03b312acbae18a104569f8fef1b6`；旧审计源码预计变为 1831 B、44 行，SHA256 `a4d552f14bcde5d4c8e35d7028cbeb7bebb59ed39edbf59c5d016519aff6d9f8`。这两个内存推导值尚不是新的服务器成功凭据。

负责人随后仅修复受影响的证明/审计换行，保留旧冻结字节和所有回执，并完成受影响的精确源码内核/全所有者门。本上下文保持唯一 fresh 最终审查身份，第 8 节完成字节 delta 一致性、类型/所有者不变及新证据绑定，不重新进行已完成的完整数学阅读。

## 8. 最终 LF 版本：确定性字节差异与新精确成功证据

本节最终封存，关闭第 7 节格式验收缺口。当前 `u22p-source.lean` 为 UTF-8 无 BOM、LF，2752 B、66 行、CR=0，SHA256 `7ecd01d72c2f28ec06080d628f5d5370b3ae03b312acbae18a104569f8fef1b6`。实际读取旧字节归档 `u22p-source-frozen-crlf.lean`（仍为 2818 B、原 SHA `abecbbb23d3ad1e859b778d46de1631f370c1e6af3baeb442d93ca260f21b4c1`）并进行确定性比较：`old.replace(CRLF,LF)` 与新源码完全相同，所得 SHA 与第 7 节事先独立推导的 LF SHA 相同。仅删除 66 个 CR，没有修改任何其他 Unicode 字符、数学文本、空格、声明或证明步骤，66 行的全部数学覆盖及行号原样适用于最终版本。

新 `u22p-lf-Audit.lean` 为 1831 B、44 行、CR=0、SHA256 `a4d552f14bcde5d4c8e35d7028cbeb7bebb59ed39edbf59c5d016519aff6d9f8`。实际比较旧审计源码作同样规范化后与它完全相同，亦符合第 7 节预先推导值；审计逻辑及全部所有者覆盖没有改变。`u22p-lf-actual-types.txt` 为 308 B、6 行，SHA256 仍为 `4ea16b67c60c8582bff36323cc900166d10d6888af29630928bd4cb86a263f6f`，与已完整审查的实际类型和公理文件逐字节相同。唯一实际 owner、完整类型、零定义及零额外私有/生成声明的完整审查由此全部覆盖最终 LF 源。

新服务器 run 为 `/root/rivermind-data/shao-lean-20261021/runs/oq3/u22p-lf-20261023`。直接读取并核对本地与该 run 的源、审计源、实际类型、完整 receipt、build history、audit record、audit environment；对应文件均同哈希。新 run 的 `source-01.lean` 与当前工作树 `Shao/OQ3/LocalCubicTaylor.lean` 都是上述 2752 B 最终 LF SHA；新 `Audit.lean` 为上述 1831 B LF SHA。旧 run 的 source03 与 receipt 同时再次核实仍为原 SHA，未被覆盖。

| 最终 LF 工件 | 字节数 | SHA256 |
| --- | --- | --- |
| `u22p-lf-receipt.json` / 新 `receipt.json` | 4177 | `93c635cbe7c01579a9fba5abaca8e7273c51e396cdb5ee76cdd0a0150491eb87` |
| `u22p-lf-build-history.json` / 新 `build-history.json` | 798 | `1d30d927b38ca8ba8ea9fe44d075fc3cd4d26450120f1584ab633179b925d0c4` |
| `u22p-lf-audit-record.json` / 新 `audit-record.json` | 496 | `ec383d522f9790c6c70611e12b677d8fb341eb708e3825c5ef5d3cf326785740` |
| `u22p-lf-audit-environment.json` / 新 `audit-environment.json` | 500 | `369caf3ecd0fb81ce99885b419d50e272faa529d7c37343efed654013aa6c22e` |
| 新 `build-01.log` | 133 | `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626` |
| 新 `audit.log` | 555 | `8539dd07f269a0dbd387c5602df7df5d9c3c06fafd9ca47061dde8f41b5c5163` |
| 本地 `u22p-lf-format-delta.json` | 413 | `d144f1e67dd4510addfe822fc7177d2feabbdf3d7a2446fb096be07c89cdea00` |

本次作者仅对受影响的新 LF 精确源执行新字节门：第一次 LF 内核检查退出码 0，用时 5.531512485817075 s；新 LF 全实际所有者递归公理审计退出码 0，用时 5.86491028778255 s。资源仍为 CPU14–17、native8192 MiB、jobs4、autoImplicit=false。新内核日志与此前已完整读过的成功日志逐字节同哈希，只有同一已知包视图警告；新审计日志也与此前完整输出逐字节同哈希。再次从新日志核实 frozen definitions=0、frozen theorems=1、all theorems=1、all declarations=1、AXIOM_GATE PASS；唯一所有者递归公理仍严格为 `[propext, Classical.choice, Quot.sound]`。

最终裁决：CORRECT；最终精确 helper 已满足完整独立源到声明/数学证明/全部实际类型与零定义值覆盖，以及该 LF 精确源的服务器内核和全所有者传递公理证据。可按项目流程验收这一标量辅助单元，不能外推第 5 节列出的仍 OPEN 原源范围。本审查员只写本报告；没有改实现、编译、重审计、改缓存或启动新任务。本报告封存后停止所有工具调用与写入。
