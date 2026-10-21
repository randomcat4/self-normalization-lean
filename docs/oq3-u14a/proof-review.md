# U14a BinaryEntropyBounds 完整独立证明审查

STATUS: CORRECT

reviewer lease 1，仅本新报告与授权 run/proof-review.md 可写。不独占代码库，不改作者源/scope/旧票/共享文件或缓存，不 spawn、不运行 Lean/API probe、不构建/commit。已有声明 gate 上下文；本轮仍先仅从**服务器 actual 实现**抽取两定义体和四完整公开类型独立盲译并先落盘，之后才读 scope/R1/证明与机械证据。

## 1. 实际公开声明先行盲译

实际工作树 `Shao/OQ3/BinaryEntropyBounds.lean` SHA256 `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228`。actual imports 为 Log.NegMulLog、Calculus.Deriv.MeanValue 以及 FieldSimp/Ring/Positivity/Linarith/FunProp/NormNum 六个 tactic 分模块；namespace Shao.OQ3、noncomputable、open Set。本阶段只抽取这些环境行、公开定义体和完整类型，没有读取私有证明体、scope 解释、作者 receipt 或机械日志。

1. `entropyRemainder x` 是实际实函数 F(x)=x Real.log x−x+1；定义本身允许所有实 x。四个定理只在明确的非负/正域使用，库对 log0 的总化与 xlogx 真连续性后核。
2. `binaryRelativeEntropy p z` 是实际实表达式 B(p,z)=p Real.log(p/z)+(1−p)Real.log((1−p)/(1−z))，定义无参数域门；最后定理再限制 p∈[0,1]、z∈(0,1)。不能由名字将所有实参域的值解释为概率 KL。
3. `entropyRemainder_quadratic_of_le_one`：任意实 x，0≤x≤1 时，(x−1)²/2≤F(x)。x=0 与 1 都在完整类型内，没有 x≠0 门。
4. `entropyRemainder_quadratic_of_one_le`：任意 x≥1，(x−1)²/(2x)≤F(x)。此门保证分母正，x=1 包括。
5. `entropyRemainder_nonneg`：任意 x≥0，F(x)≥0；不是全部实域或仅严格正域的断言。
6. `binaryRelativeEntropy_refined_lower`：任意 p,z:ℝ，0≤p≤1 且 0<z<1 时，(p−z)²/(2max(p,z))≤B(p,z)。p=0/1 必须覆盖，z 两端排除；最终 max≥z>0。此类型仅给明确充分下界，没有最优性、新颖性、全局极值、测度数据处理或根闭合结论。

盲译先行落盘，尚无最终数学/类型/机械判定。根 A/B/C/D 均 OPEN。

## 2. 冻结声明与真实来源

actual 服务器源 SHA256 `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228`（128 行）已核。冻结 scope SHA256 `15a8b914a070b6633d60801a2d1b1d27053673a556e93edfa2bb4f67789fffe3`；原独立声明票 SHA256 `0553ba05cab28d4cd21f711f69763181072c53f4d023dff25f8640d1a9eb627d`。实际两定义体、四完整公开类型从 actual 源抽取并与 frozen Lean fence 白空格规范比较全部相同；actual 八个 imports 与冻结声明环境相同。实现额外 `open Set` 只是 private/局部证明中 Icc/Ici 等名字的便利，不改变公开类型或实例。

真实 R1 原件 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` 已核并读取 161–259。源 (10) 先由实际 Bernoulli kernel/data processing 降到 d(p‖z₀)，(11)–(13) 再用二元熵估计。这一实际单元只给标准纯实 F 与 B 及充分下界，不是 kernel/data processing、likelihood/KL 差 (9)、数值率间隙或 231–237 全局唯一性证明。

在公开有效域 p∈[0,1]、z∈(0,1) 中，两个权重非负且总和 1，参考权重均严格正；B(p,z) 的实际实式对应有限 Bernoulli 相对熵，零项按 0log0=0 连续约定。它没有正式绑定某个库测度 KL/实际随机 kernel 的导出目标。本 refined lower 在 p≤z 时比源 (11) 少 1/(1−z) 因子，较弱但仍足够源给定的数值裕度；p≥z 时提供源 (12) 的充分非严格首项。F 的补项非负也可供源 (13) 的补对数项下界，但源剩余比例/数值比较仍未在此单元证明。标准工具的有效性不等于最优性、新颖性或全局最小值认证。

## 3. 全部实际证明、私有/局部辅助与固定库

### 3.1 两定义与两个 authored private theorem（15–27）

两实际定义与盲译字面相同，没有改成参数依赖 surrogate。固定 Real.log 的实际语义是正域通常自然对数、负域 log|x|、log0=0；因此 F 虽定义全 ℝ，其公开熵下界只在非负域。B 的公开解释也只在给定 p/z 有效域，未将其它总化值当作 KL。

`entropyRemainder_hasDerivAt`（20–24）明确要求 x≠0，真实 `Real.hasDerivAt_mul_log hx` 给 (xlogx)'=logx+1，减 id 导数 1、加常数后得到 F'=logx。`convert` 后的 ring 只整理导数代数，没有声称在 0 可微。

`entropyRemainder_continuous`（26–27）消费实际库 **continuous_mul_log** 而不是 continuous_log；其真实证明特别处理 0 的极限，故全实域 F 连续包含 x=0。此区别正是闭区间目标的端点门；没有把 log 本身在 0 不连续一事隐藏掉。

### 3.2 0≤x≤1 的二次下界（29–50）

31 的 g(y)=F(y)−(y−1)²/2。32–35 局部 hd 要 y≠0，由 private F 导数和真实平方/除常数导数得 g'=logy−(y−1)。36–46 使用**实际 Analysis.Calculus.Deriv.MeanValue** 的 antitoneOn_of_deriv_nonpos：D=Icc0,1 凸；38–39 用 F 全域连续加多项式真 ContinuousOn D；40–46 的 DifferentiableOn/导数符号只在 interior D 上，`interior_Icc` 给 0<y<1，明确消费 y≠0 和真实正域 logy≤y−1。没有在 y=0 套导数，也没有只给开区间而漏闭端点。

47 真正将 x∈[0,1] 与 1∈[0,1]、x≤1 交给反单调性，得到 g1≤gx；48 的 log1=0 给 g1=0，49–50 化为平方界。x=0 时 F0=1、左端1/2，已由同一闭域连续性覆盖；x=1 是 0=0。

### 3.3 x≥1 的二次下界（52–82）

54 实际局部 g(y)=F(y)−y/2+1−y⁻¹/2。55–60 的 hd 仍明确 y≠0；真实 inverse 导数是 −1/y²，减 inverse/2 正好给 g'=logy−1/2+(y⁻¹)²/2，符号正确。

61–64 在完整 Ici1 上由 y≥1 推 y>0、y≠0，建立真 DifferentiableOn；65–72 用其 ContinuousOn，再限制内部微分，实际凸 Ici 单调性 API 的三门齐全。69–72 内部 y≥1 推正域，用真实 `one_sub_inv_le_log_of_pos` 和平方 `(y⁻¹−1)²≥0` 给

`logy−1/2+(y⁻¹)²/2 ≥ ((y⁻¹−1)²)/2 ≥0`。

这里没有越过 0 的逆数求导，也不需不合法地乘可能负的分母。73–75 从 1≤x 得 g1≤gx，g1=0。76 另立 x≠0 后，77–80 才用 field_simp/ring 把实际 g(x) 精确改写为 `F(x)−(x−1)²/(2x)`；真实 2x>0。81–82 给目标，包括 x=1。Ici1 无界不妨碍该 actual convex-domain MeanValue API；并未假设全实域有理项连续。

### 3.4 非负界（84–88）

只用实序 le_total 将非负 x 分为 x≤1 或1≤x；前支平方/2 非负，后支平方/(2x) 非负，后一支确有 x≥1>0。再传递前两完整界得到 F≥0。x=0/1 分支均合法，没有新增 log 正域假设或未证明的一般 KL 非负性。

### 3.5 二元熵、真实分母和 p 端点（90–125）

93–95 给 1−z>0、p/z≥0、(1−p)/(1−z)≥0，真实消费 p≥0、p≤1、0<z<1。96–101 的 hdecomp 直接展开实际 F/B，用**仅 z≠0、1−z≠0**清分母与 ring，得

`B(p,z)=z F(p/z)+(1−z)F((1−p)/(1−z))`。

actual 源没有调用 log_div，也没有拆 log p 或 log(1−p)，没有要求或约掉可能为 0 的 p、1−p。102–103 的非负项确为 `(1−z)F(complement ratio)`，不是把可能为负的 complement 对数项自身误当非负。

105 的 p,z 全序覆盖所有参数。p≤z 分支（106–114）将 max 改为正 z，div_le_one 明确消费 hz0；第一 F 界包括 ratio=0，再仅用 z≠0 化为 `(p−z)²/(2z)`。乘 F 界时 z≥0 保不等号方向，丢掉的补 F 项真非负。**p=0 确实进入这一支，不曾取消 p。**

z≤p 分支（115–125）先在 116 明确推 p>0，再以 one_le_div hz0 给 p/z≥1，消费第二 F 界；119–121 只在 p,z 真非零后清分母，准确给 `(p−z)²/(2p)`。p=1 时 complement ratio=0，已证 F(0)=1≥0，因此同一 hcompnonneg 有效；没有漏掉 p=1 或对 log0 套 log_div。最终 max(p,z) 分母由两个分支各自 z>0/p>0，等价于总门 max≥z>0，严格正性真正成立。

p=z 时两 ratio=1，B=0、平方下界0；p0/p1 的 B 分别等于 −log(1−z)、−log z，均是参考 z 内点的有限实值。x=0 F=1 和 p 端点的0log0约定与固定库语义一致。z=0/1 在公开域外，没有那里 KL 或分母下界的错误延伸。

### 3.6 固定 actual Mathlib 数学语义

在 TYPE/receipt/绿灯之前，经 broker 只读固定服务器真实源码：

| 实际库及位置 | 核对的前提/语义 | SHA256 |
|---|---|---|
| Log/NegMulLog:45–59,68–74 | xlogx 真连续（特别是0）；hasDerivAt_mul_log 要 x≠0，F private proof正确消费 | `00039257907338466419ea23f63e9e403f1f7f4a431d57d0f09bdf9bda6577a1` |
| Log/Basic:39–45,103–108,138–145,307–313 | actual log0/负域定义与 log1；log_div需分子分母非零（本源不调用）；正域对数上下界 | `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97` |
| Calculus/Deriv/MeanValue:412–416,481–485 | 凸 D、ContinuousOn D、DifferentiableOn interior D、真实内部导数符号；适用闭 Icc 和闭无界 Ici | `b6f3e52c283bdd2c3eb01173c8ac32b82dff0efdfc1890c361f8eed63359edb8` |
| Calculus/Deriv/Inv:112–115 | HasDerivAt.inv 的非零门与负导数 −c'/c²，第二目标实际使用正确 | `97bf4871f60ae5571aa9e1f84be6ccdc5bb7dfbfee5517fb7c927e9d5591947d` |

两公开函数/四目标均为纯实结论，actual imports 中无 Shao 模块，**项目 transitive prerequisites 为零**；没有从此前 OQ3 theorem 假设当前熵界。分模块 tactic 只是生成证明对象，真实额外 generated 项仍待下一阶段逐项核 TYPE；不以作者成功编译替代上述数学审查。

**独立数学阶段结论：实际两定义、四完整目标、两 authored private theorem 与全部 128 行局部证明未发现数学、来源或端点缺口。** 本判断在任何 actual TYPE、receipt 或机械绿灯读取前落盘，最终 STATUS 待所有 generated TYPE 与最后机械绑定。

## 4. 全部 actual owned TYPE

数学阶段结论落盘之后，仅读真实 Audit.log 的 DECL/TYPE 和全部缩进续行，未先读取 receipt、Audit 源、AXIOMS 或 PASS。实际 **16** 个 owned 常量按日志顺序逐项核对：

| # | 实际常量 | 完整类型及其前提的核验 |
|---|---|---|
| 1 | `Shao.OQ3.binaryRelativeEntropy_refined_lower` | ∀p,z:ℝ，0≤p→p≤1→0<z→z<1→(p−z)²/(2max p z)≤实际 B(p,z)。四门全部保留、p端点包括、无隐藏内部性假设。 |
| 2 | `Shao.OQ3.entropyRemainder_quadratic_of_one_le` | ∀x:ℝ，1≤x→(x−1)²/(2x)≤实际 F(x)，有真实正分母域。 |
| 3 | `_private.Shao.OQ3.BinaryEntropyBounds.0.Shao.OQ3.entropyRemainder_hasDerivAt` | ∀x:ℝ，**x≠0**→HasDerivAt F(log x)x；实际类型确无0处可微主张。 |
| 4 | `Shao.OQ3.binaryRelativeEntropy_refined_lower._simp_1_7` | ∀{R:Type u}[AddMonoidWithOne R][CharZero R](n:ℕ)，(↑n+1=0)=False。真正 CharZero 下自然数 successor 非零，未添加概率或熵假设。 |
| 5 | `_private.Shao.OQ3.BinaryEntropyBounds.0.Shao.OQ3.entropyRemainder_continuous` | Continuous F 的全实域真命题，来源是已核连续 xlogx，含0。 |
| 6 | `Shao.OQ3.entropyRemainder_nonneg` | ∀x:ℝ，0≤x→0≤F(x)，包括0而未扩至负域。 |
| 7 | `Shao.OQ3.entropyRemainder` | ℝ→ℝ，与实际定义体和 #9 方程绑定。 |
| 8 | `Shao.OQ3.binaryRelativeEntropy_refined_lower._simp_1_2` | ∀{α:Type u}[Zero α][OfNat α 3][NeZero 3]，(3=0)=False。明确 NeZero3 门，实数实例真实满足。 |
| 9 | `Shao.OQ3.entropyRemainder.eq_1` | ∀x:ℝ，F(x)=x Real.log x−x+1；实际 generated 定义方程，不改 log 或域。 |
| 10 | `Shao.OQ3.binaryRelativeEntropy_refined_lower._simp_1_1` | ∀{α}[Zero α][OfNat α 2][NeZero 2]，(2=0)=False；真正 numeral 非零侧条件。 |
| 11 | `Shao.OQ3.binaryRelativeEntropy_refined_lower._simp_1_4` | ∀{M₀}[Mul M₀][Zero M₀][NoZeroDivisors M₀]{a b}，a≠0→b≠0→(a*b=0)=False。乘积非零门明确，未无条件消分母。 |
| 12 | `Shao.OQ3.binaryRelativeEntropy_refined_lower._simp_1_3` | ∀{α}[Zero α][OfNat α 4][NeZero 4]，(4=0)=False；实数4非零。 |
| 13 | `Shao.OQ3.binaryRelativeEntropy` | ℝ→ℝ→ℝ，实际定义体已从服务器全文和冻结 fence 独立比较；不凭名称认作库 KL 对象。 |
| 14 | `Shao.OQ3.entropyRemainder_quadratic_of_le_one` | ∀x:ℝ，0≤x→x≤1→(x−1)²/2≤F(x)；真实类型包含 x0/x1。 |
| 15 | `Shao.OQ3.binaryRelativeEntropy_refined_lower._simp_1_6` | ∀{G₀}[GroupWithZero G₀]{a}(n:ℤ)，a≠0→(a^n=0)=False。整数幂非零真实侧门，含负指数。 |
| 16 | `Shao.OQ3.binaryRelativeEntropy_refined_lower._simp_1_5` | ∀{M₀}[MonoidWithZero M₀]{a}[IsReduced M₀](n:ℕ)，a≠0→(a^n=0)=False。实际 IsReduced/非零假设齐全，当前 ℝ 场满足；没有无门消0。 |

实际分类：2 public def、4 public theorem、2 authored private theorem、**8 generated theorem**（1 个 F 定义方程与7个标准代数非零 simp 辅助），故 16 owned、14 theorem。所有生成项均按实际类型读取，没有预设每个 definition 必有某个 equation helper。128 行中 g/hd/hanti/hmono/hdiff/hzero/heq、ratio/decomposition/complement 与分支局部条件已在 §3 逐项审查。至此数学与十六项 TYPE 均未发现缺口，机械证据仍待读取。

## 5. 最后机械绑定

在独立数学及全部十六项 TYPE 均完成并落盘之后，才读取作者 receipt、Audit 源和既有机械结果。实际工作树 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；run `/root/rivermind-data/shao-lean-20261021/runs/oq3/u14a-20261021`。经共享 broker 只读核验，没有下载原始完整日志，没有运行 Lean/API probe、target 或 Audit。

| 实际绑定对象 | bytes / SHA256 / 事实 |
|---|---|
| 工作树 `Shao/OQ3/BinaryEntropyBounds.lean`、run 同名快照、本地 `drafts/oq3/BinaryEntropyBounds.lean` | 三者 SHA `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228`，128 行，run 实际 5574 bytes；本次先审的是真服务器源 |
| 本地冻结 scope / run `scope.md` | 4082 bytes，`15a8b914a070b6633d60801a2d1b1d27053673a556e93edfa2bb4f67789fffe3` |
| 本地独立声明票 / run `statement-review.md` | 11843 bytes，`0553ba05cab28d4cd21f711f69763181072c53f4d023dff25f8640d1a9eb627d` |
| 本地 `U14a-receipt.json` / run `receipt.json` | 2785 bytes，`a8c7265dda07c04a657f66aa0173e6b3a2fbdc347882508d482fc0d19d082399` |
| 实际 run `Audit.lean` | 1653 bytes，`0b471dca1ebec719ced4555b2b7738a77be3f68f2270378d43c1863b4f10ec7d`，全文只读核对 |
| 实际 run `Audit.log` | 2916 bytes，`9c75f4fcc6215834649051906eedbe5a2d0fd4eebbbbd433b71cda8b58fad475` |
| 实际 run `build-04.log` | 实际空 0 bytes，SHA `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`；receipt 记载作者既有 build exit_code=0 |
| 实际已存在 `.lake/build/lib/lean/Shao/OQ3/BinaryEntropyBounds.olean` | 574016 bytes，`7aa6b41fb2654fffa8d76560143a2dcc68134c002f5e1bddad89a6d0cdc5a2f3`；只读查看，未重生成 |

actual 源无 Shao import，独立检查项目依赖为零，与最后读取的 `imported_project_sources_sha256: {}` 一致。没有旧 OQ3 源 hash 或隐藏项目定理承担此单元证明。

真实 Audit 源先核四冻结目标均为 theorem；stems 包括两定义和四目标的全部后代，并覆盖 `_private.Shao.OQ3.BinaryEntropyBounds` 整个私有前缀。对每项拒绝 isAxiom，并 `Lean.collectAxioms` 递归收集全部传递公理，再逐个核 `{propext,Classical.choice,Quot.sound}` 白名单。源码两 private theorem 和全部 generated 项均在覆盖中，actual 十六项 TYPE 与完整源码一致。十六项 AXIOMS 全是白名单子集；真实日志输出 `U14A_FROZEN_THEOREMS 4`、`U14A_ALL_THEOREMS 14`、`U14A_ALL_DECLARATIONS 16`、`U14A_AXIOM_GATE PASS`。不是只核四目标就推测其它 helpers 安全。

receipt 的 author 状态为 `AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW`，nonclaims 正确标记 U14a 在 author-check 时终审 pending、未 commit/PR/merge。build/Audit exit_code=0 是作者既有过程记录，本审查只读确认 actual 源/快照/空 log/olean/Audit 产物和 hash，不冒称进行了新内核运行。当前独立 CORRECT 是上述全数学/类型审查的结论，不是直接转述作者门。

实际 branch `feat/oq3-binary-entropy-bounds`，HEAD `89a45a56f451b58f45743c388bb3416db762404c`，工作树仅 `?? Shao/OQ3/BinaryEntropyBounds.lean`。actual lean-toolchain `leanprover/lean4:v4.36.0-rc1`，文件 SHA `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；manifest 文件 SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`；manifest mathlib rev 与 actual mathlib git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。只读文件与 git 元数据核 pins，没有调用 Lean。

actual source 独立扫描 LF 无 CR、无尾空白，禁止项词界 `sorry/admit/axiom/unsafe/native_decide/implemented_by` 无命中；128 行人工检查亦未见替代内核或未审顶层声明。两 frozen 定义体与四完整类型的匹配由本审查独立重做，非只读作者 PASS。未修改 source、scope、旧票、共享文件或缓存。

## JUSTIFICATION

**STATUS: CORRECT。** 已按强制顺序完成服务器 actual 两定义体/四完整类型盲译先落盘→scope/R1→全部 128 行证明、两个 private theorem、所有 locals 及真实固定库语义→全部十六 actual owned TYPE 长续行→最后 receipt/实际 build/Audit/source/pins/hash 绑定。未发现数学、来源、实际端点/分母、类型或机械绑定缺口。

闭 Icc0,1 的 xlogx 真连续和内部导数门完整，x0不被排除或错误求导；Ici1 上真正正分母/逆导数、连续性、内部微分与导数符号完整；非负目标真实覆盖两种域；二元恒等式只消正 z/1−z，两个 p 分支正确对应 max，p0、p1 及 complement ratio0 均保留，最终 max 分母真正。

这是**标准充分二元熵下界**的完整独立审查通过，不认证最优常数、新颖性或全参数全局极值。未证明实际 Markov kernel、KL 数据处理、源数值率间隙、全局 minimizer/唯一性、Lévy/弱收敛、hW 或根闭合；根 A/B/C/D 全部 **OPEN**。未 spawn、运行 Lean/API probe、重编成功 target/Audit、写缓存或 commit/PR。最终报告交付本地 `drafts/oq3/u14a-proof-review.md` 与授权 run `proof-review.md`，两端最终 SHA256 随交付独立核验。
