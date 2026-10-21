# U14b 完整独立证明、来源与类型审查

STATUS: CORRECT

审查者沿用唯一 lease 1，仅拥有本报告及指定服务器对应 proof-review.md；不修改实现、scope、旧票、共享文件或缓存，不 spawn。既有声明审查上下文已经存在；以下仍先仅提取 actual 源码公开类型，重新独立盲译并先落盘，尚未读取本次实现证明、scope 解释、R1 或机械证据。

## 第一阶段：actual 三个完整公开类型的独立盲译

实际输入 drafts/oq3/SourceBinaryEntropyGap.lean，SHA256 f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9，173 行。本阶段只读取提取后的三个公开完整类型，无新公开定义。记 D(p,z)=既有 binaryRelativeEntropy p z。

1. `binaryRelativeEntropy_ge_first_term (p z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)`：对任意 p∈[0,1] 和 z∈(0,1)，p log(p/z)−p+z≤D(p,z)。包括 p=0 和 p=1，故不得在证明中消去 p 或 1−p。使用实际总定义的实自然对数；零质量项须由乘零解释。

2. `binaryRelativeEntropy_gt_two_mul (p z : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) (hlog : 3 < Real.log (p / z))`：对任意 p∈(0,1]、z∈(0,1)，若 log(p/z)>3，则 2p<D(p,z)。严格乘法必须消费 p>0，p=1 仍合法。

3. `binaryRelativeEntropy_source_gap (q H R : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100) (hH0 : 50 < H) (hH1 : H < 51) (hR0 : 0 < R) (hR1 : R ≠ 1) (hp0 : 0 ≤ (q * R ^ 2 - 1) / H) (hp1 : (q * R ^ 2 - 1) / H ≤ 1)`：对同一组任意实数 1<q<103/100、50<H<51、R>0 且 R≠1，若 p=(qR²−1)/H 实际属于[0,1]，则 (7/200)(R−1)²<D(p,(q−1)/H)。z=(q−1)/H 的 0<z<1 需要从参数导出。严格性包括 p=0 的可能可行边界，R≠1 保证平方严格正。该目标没有测度/KL 核或全局极小化参数，也没有隐含的最优常数断言。

本阶段已先落盘，后续才读取冻结 scope/R1、完整实际证明、全部 actual TYPE，最后读 receipt 与机械证据。根 A/B/C/D 均保持 OPEN。


## 第二阶段：冻结来源与实际类型对应

盲译先落盘后，直接读取完整冻结 scope、本单元已接受的声明票、实际 173 行源码和 R1 第 161–237 行。实际三个公开类型与冻结 scope 的三个完整类型，去空白逐字比较为相同；无公开定义或签名修改。scope SHA256 `0db55bb2ed6bbcd20e41011211b0b5ce6851c8335afb94be2a5633112cf2a053`；声明票 SHA256 `c3af40867baf48b68130bf14112000da25997a14cc5b2ee3fa0cbd06f47fc8b0`；实际 R1 SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。

实际导入为 BinaryEntropyBounds、Mathlib.Analysis.Complex.Exponential 及六个明确 tactic 模块，namespace Shao.OQ3，无测度、矩阵范数或隐含概率实例。本单元消费实际 `entropyRemainder x=x log x−x+1`、实际二元相对熵定义 `D(p,z)=p log(p/z)+(1−p)log((1−p)/(1−z))`，并消费已完整独立审查的 `entropyRemainder_nonneg` 和 `binaryRelativeEntropy_refined_lower`。项目承重前置只此一个模块，不把同名抽象熵替换成实际定义。

R1 第 184 行给出同一 p=(qR²−1)/H 和 z=(q−1)/H，第 193–225 行对应三段实数熵估计，第 221–224 行对应互补项和 >2p。实际实现只证明这些纯实数充分估计，没有消费或证明第 180–188 行的随机核或 KL 数据处理。7/200=0.035 是源中间估计的充分统一后果，不是第 225 行 103/3000 的数值弱化，也不声称最优。第 229 行 ell q<103/3000<7/200 是它可以服务后续比较的原因，不是本单元额外已证明的 KL/global-minimum 结论。

## 第三阶段：全部实际证明与局部辅助独立核对

以下数学审查在读取 Audit TYPE、receipt、构建绿灯前完成并落盘。

### 源码第 13–27 行：实际互补项

`_hfirst_ratio : 0≤p/z` 由 p≥0,z>0 正确建立；此记录虽未被后续代数使用，并非缺失 log_div 的前提。后续不使用任何 log_div。hcz=1−z>0，补比率 (1−p)/(1−z)≥0 由 p≤1 和正分母得到。将 `entropyRemainder_nonneg` 乘 1−z，再展开 F 的 heq，仅用 hcz≠0 做 field_simp，恰得

`(1−z)F((1−p)/(1−z))=(1−p)log((1−p)/(1−z))−(1−p)+(1−z)`。

这只取消 1−z；既不取消 p 也不取消 1−p，log 内的零补比率不需非零。随后展开实际 D、线性整理得到目标一。p=0 的首项与 p=1 的补项均真正乘零，均合法；z 两端被假设排除。

### 第 29–34 行：真实严格 >2p

先在 hp0.le 下调用目标一，再使用 `mul_pos hp0 (sub_pos.mpr hlog)`，即 p(log(p/z)−3)>0。和 z>0 一起给 D≥p log−p+z>2p。没有将严格 p>0 偷换为 p≥0，也没有排除 p=1。

### 第 36–44 行：唯一 authored private theorem

`exp_three_le_twenty_seven : Real.exp 3≤27` 没有参数或新公理。实际 `Real.abs_exp_sub_one_sub_id_le` 在 x=1 的合法门 |1|≤1 给 |exp1−2|≤1，再由 exp1−2≤|exp1−2| 推出 exp1≤3。`Real.exp_nat_mul (1:ℝ) 3` 给 exp3=(exp1)³；乘幂比较真实消费 exp1≥0；最后 3³=27。未假定 e≤3，也未调用缺失的指数数值包。

### 第 46–62 行：同组参数与合法域

局部 p、z 分别是实际冻结式。q>1 给 q>0、q−1>0；q<103/100 给 q−1<3/100；H>50 给 H>0。hz0 由正数相除，hz1 由 q−1<H 并使用 `div_lt_one hH`，所以本次实际调用 U14a 时真正满足 z∈(0,1)。hp0、hp1 直接来自原假设并按局部 p 展开匹配。R≠1 经 sub_ne_zero 给 `(R−1)²>0`，并非非法除以该平方。q>1 给 q²>1。hbase 消费真实概率域，得到实际 refined lower，未取消零 p。

### 第 63–94 行：小 R 段

R<1 与 R>0 给 R²<1，正 q,H 使 p≤z，从而真实 max=z。代数 heq 只在 H≠0、q−1≠0 下取消分母：

`(p−z)²/(2z)=[q²(R+1)²/(2H(q−1))](R−1)²`。

p 可能为零而没有被取消。R>0 使 (R+1)²>1，q²>1 使分子>1；H<51、0<q−1<3/100 给 H(q−1)<51·3/100。目标系数 7/200 乘正分母后小于 `(7/200)·(153/50)=1071/10000<1`，故 hc 的 nlinarith 结论严格成立。最后使用平方严格正来乘 hc，再用 heq 和 hbase。可行 p=0 边界完全覆盖；无需 R>0.98 或源中的额外 1/(1−z) 因子。

### 第 95–139 行：非小段与中段

非 R<1 加 R≠1 给 R>1；于是 R²>1、R²<qR²，A=qR²−1>0，p>0，且 z≤p。R≤3/2 分支中 max=p，局部 heq 在 H,A 非零下给

`(p−z)²/(2p)=[q²(R+1)²/(2HA)](R−1)²`。

此段 p 被分母使用前已显式证明 p>0。实际 hcert 使用精确恒等式

`(R+1)²−(7/100)51((103/100)R²−1)`

`=61861/40000+(3/2−R)((26771/10000)R+40313/20000)>0`。

本次 proof 的 ring 身份与声明阶段独立有理数证书一致，所有系数精确；R≤3/2 保证第一因子非负，R>1 保证第二因子正，正剩余 61861/40000 保证端点 R=3/2 也严格。hden 先用 A>0 乘 H<51，再用 R²>0 乘 q<103/100，故 HA<51((103/100)R²−1)。hnum 由 q²≥1 乘非负平方得 (R+1)²≤q²(R+1)²。三者确实推出

`(7/200)·2HA < q²(R+1)²`。

lt_div_iff₀ 的分母 2HA 已真实为正；因此 hc 严格。最后乘严格正平方并接 hbase，未丢失严格性。

### 第 140–170 行：大段和全部参数边界

最后分支实际是 R>3/2，R=3/2 已被中段包含。它给 R²≥9/4，与先前 qR²>R² 合得 A>5/4。hratio 仅在 H≠0、q−1≠0 下化简 p/z=A/(q−1)。hratio27 将正分母 q−1 乘过去；由于 27(q−1)<81/100<5/4<A，确实得到 p/z>27。随后才建立 0<p/z 并使用 `Real.lt_log_iff_exp_lt`，连接实际 private exp3≤27 得 log(p/z)>3。

目标二实际调用中 p>0、p≤1、0<z<1 全部真实存在。最后 hpoly 使用

`2(R²−1)/51−(7/200)(R−1)²=(R−1)(43R+757)/10200>0`，

两个因子正且 10200>0。hplower 则先在 R²−1>0、H>0、H<51 下证明 `(R²−1)/51<(R²−1)/H`，再在 H>0 下用 R²<qR² 增大分子。分母交叉乘的方向正确，未颠倒 H<51 的作用。最终严格链是

`(7/200)(R−1)² < 2(R²−1)/51 < 2p < D(p,z)`。

全部 R>0,R≠1 可行范围已覆盖。R=1 必须排除，因为此时 p=z、D=0；p=1 被目标二允许；p=0 只可能进入小段而已妥善覆盖。所有参数均为同一 q,H,R，不涉及替换概率族或未量化的其他参数。

## 第四阶段：实际承重语义及固定库 API

指定服务器只读源码确认 U14a SHA256 `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228`。其实际 F、D 和 refined_lower 的完整定义/类型/证明消费位置已读取；既有完整独立审查的语义包括 x=0 的连续 xlogx、端点非负性、正 z 和 1−z 的精确分解，以及 max=p 时才建立 p>0。本次消费与这些门完全吻合，不重编也不重新声明旧单元完成。

固定 Mathlib 实际源码已只读核对：

- `Analysis/Complex/Exponential.lean` SHA256 `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`：234–235 行 Real.exp_nat_mul；284–290 行 Real.exp_pos、Real.exp_nonneg；538–541 行 Real.abs_exp_sub_one_sub_id_le，前提恰为 |x|≤1。
- `Analysis/SpecialFunctions/Log/Basic.lean` SHA256 `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97`：103 行 log_zero，107–108 行 log_one；167 行 lt_log_iff_exp_lt 的必要门是被取 log 的 y>0。代码在 hratio27 后才消费这个门，方向为 exp3<p/z⇒3<log(p/z)。
- `Analysis/SpecialFunctions/Log/NegMulLog.lean` SHA256 `00039257907338466419ea23f63e9e403f1f7f4a431d57d0f09bdf9bda6577a1`，39–42 行 self_sub_one_le_mul_log 允许 x=0；与实际 F 非负性的合法端点一致。
- `Algebra/Order/GroupWithZero/Basic.lean` 1136–1137 行 lt_div_iff₀ 要求分母正；1456–1457 行 div_lt_div_iff₀ 要求两个分母分别正，结论为 a/b<c/d iff a*d<c*b；513–514 行 pow_le_pow_left₀ 要求较小底数非负和底数序。代码所有调用的符号与方向均正确。

源码各行只用有限实数代数与已有标准对数/指数结论，无可积性、总化测度或矩阵隐式实例问题。所有 authored private、局部 have、by_cases 与 ring/field_simp 的实际数学义务均已核对。数学阶段结论：CORRECT；尚待随后核对全部实际 TYPE 与最后机械绑定。


## 第五阶段：全部 11 个 actual owned TYPE

数学阶段已先落盘；随后仅从指定服务器现有 Audit.log 过滤读取 DECL/TYPE 与每个完整缩进续行，尚未读取 axiom/PASS/build/receipt。不是按预期数量推测生成项。实际枚举得到下列 11 个常量，均为 theorem：3 个公开目标、1 个 authored private theorem、7 个 generated 辅助；没有新定义。

1. `Shao.OQ3.binaryRelativeEntropy_ge_first_term._simp_1_6`：任意 GroupWithZero G、a、整数 n，a≠0⇒(a^n=0)=False。真实整数幂非零重写，n 可负但 a≠0 门保留，不隐藏概率或源目标假设。
2. `Shao.OQ3.binaryRelativeEntropy_ge_first_term._simp_1_3`：任意具有 Zero、OfNat 4、NeZero 4 的类型，(4=0)=False。数值非零重写，其 NeZero 门显式存在。
3. `Shao.OQ3.binaryRelativeEntropy_ge_first_term._simp_1_4`：任意 Mul、Zero、NoZeroDivisors 类型，a≠0⇒b≠0⇒(a*b=0)=False。完整第二行续行已读；零乘积非零性门正确。
4. `_private.Shao.OQ3.SourceBinaryEntropyGap.0.Shao.OQ3.exp_three_le_twenty_seven`：`Real.exp 3≤27`，无附加假设；恰为第 36–44 行已独立审查的辅助结论。
5. `Shao.OQ3.binaryRelativeEntropy_ge_first_term._simp_1_2`：任意 Zero、OfNat 3、NeZero 3 类型，(3=0)=False。真实数值重写。
6. `Shao.OQ3.binaryRelativeEntropy_ge_first_term`：∀p,z:ℝ，0≤p→p≤1→0<z→z<1→p log(p/z)−p+z≤D(p,z)。实际类型与 actual 源及冻结类型相同，p 两端包含，无额外实例或假设。
7. `Shao.OQ3.binaryRelativeEntropy_ge_first_term._simp_1_5`：任意 MonoidWithZero、IsReduced 类型、a、自然数 n，a≠0⇒(a^n=0)=False。其实际 IsReduced 门保留，因此不是在任意含幂零元的环上作无条件非零宣称；也包括 n=0。
8. `Shao.OQ3.binaryRelativeEntropy_gt_two_mul`：∀p,z:ℝ，0<p→p≤1→0<z→z<1→3<log(p/z)→2p<D(p,z)。与冻结类型一致；严格 p 门仍在。
9. `Shao.OQ3.binaryRelativeEntropy_source_gap`：已完整读取第 27–36 行的类型长续行：∀q,H,R:ℝ，1<q→q<103/100→50<H→H<51→0<R→R≠1→0≤(qR²−1)/H→(qR²−1)/H≤1→(7/200)(R−1)²<D((qR²−1)/H,(q−1)/H)。所有量词/可行性门/常数/实际熵一致，无偷偷改成非严格或替代目标。
10. `Shao.OQ3.binaryRelativeEntropy_ge_first_term._simp_1_1`：任意 Zero、OfNat 2、NeZero 2 类型，(2=0)=False。真实数值重写。
11. `Shao.OQ3.binaryRelativeEntropy_ge_first_term._simp_1_7`：任意 AddMonoidWithOne、CharZero 类型和 n:ℕ，(↑n+1=0)=False。真实特征零自然数后继非零重写，未要求概率或主目标前提。

七个生成项均是 field_simp/代数数值非零义务，不是假设主目标、sorry、私有公理或隐藏的数学接口。每个实际 TYPE（包括续行）均已独立逐项核对，类型阶段结论 CORRECT。随后才开始读取机械证据。


## 第六阶段：作者收据及真实机械产物最后核对

在前三个目标、private/locals、固定库语义及全部 11 TYPE 均已独立审查并落盘后，才读取本地作者收据和真实服务器机械产物。作者收据是证据绑定，未作为上述数学判断的替代。

- 本地 `U14b-receipt.json` 与实际 run/receipt.json SHA256 均为 `db1b905f56989373d094714593f7288cda58802661d40d8946d1c3c3f3a71724`。其状态明确为 AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW；“终审 pending”“未 commit/PR”均明确限定在 author-check time，符合历史时点，不是声称本报告交付后仍 pending。
- actual 工作树源、本地 draft、run/SourceBinaryEntropyGap.lean 三者 SHA256 均为 `f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9`，173 行；run 快照 7616 字节。实际 scope 与声明报告 SHA 均与前述冻结值相同。
- `build-03.log` 实际为 0 字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。作者既有收据记录的命令为 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/SourceBinaryEntropyGap.olean Shao/OQ3/SourceBinaryEntropyGap.lean`、exit_code=0。这里观察既存空日志与产物，未重跑该命令，也未把空日志自身当成独立的 exit-code 证明。
- 实际 `.lake/build/lib/lean/Shao/OQ3/SourceBinaryEntropyGap.olean` 存在，1297344 字节，SHA256 `e551a11a79ebc88fb3ea71e4dc99136416ccbfd5a4f0b0dd7ab2555d283bc142`。
- 实际 run/Audit.lean 为 1546 字节，SHA256 `10f3b30b94dacfe94ecdca3f92bd9302f429f289b97741d589217077a4f52c56`；已完整读取其源。它先断言三个冻结名称存在且为 theorem，再覆盖三个公开 stem 的所有后代及整个 `_private.Shao.OQ3.SourceBinaryEntropyGap` 前缀；每个常量禁止 isAxiom，并通过 Lean.collectAxioms 遍历传递依赖，白名单仅 propext、Classical.choice、Quot.sound。结合全部实际源码的声明清单（仅三个公开 theorem 和一个 private theorem、无其他定义/公理），此前缀覆盖与本模块实际 owned inventory 一致，不漏其他源码公开声明。
- 实际 run/Audit.log 为 2459 字节，SHA256 `d11b9be329bbef0668a18c092aef2d753f08a3f7b968fdf18c0aa967b8edd3e5`。全部 11 个 DECL/TYPE 已在前阶段逐一读取；本阶段又实际读取所有 11 条 AXIOMS，均为白名单子集，没有 sorryAx 或项目额外公理。实际末尾为 `U14B_FROZEN_THEOREMS 3`、`U14B_ALL_THEOREMS 11`、`U14B_ALL_DECLARATIONS 11`、`U14B_AXIOM_GATE PASS`。作者收据记录 Audit exit_code=0，source/log hash 与实际文件均一致。没有重跑 Audit。
- 已独立按实际 `import Shao.*` 递归枚举项目闭包，恰为 `Shao/OQ3/BinaryEntropyBounds.lean` 一个前置，SHA256 `291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228`；该前置本身无 Shao 导入。实际闭包与 receipt/imported_project_sources_sha256 和 run/prerequisite-hashes.json 完全一致，没有遗漏项目依赖。
- 实际 lean-toolchain 内容 `leanprover/lean4:v4.36.0-rc1`，SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。Mathlib manifest rev 与实际 `.lake/packages/mathlib` git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`。未执行 Lean/Lake 版本探针或构建。
- 观察时 actual 工作树 branch 为 `feat/oq3-source-binary-entropy-gap`，HEAD 为 `f843398ac538fa93e9ccf263371b43069a67a860`；git status 仅 `?? Shao/OQ3/SourceBinaryEntropyGap.lean`。这绑定此次审查时点，不约束 lead 后续获准的提交。独立源码扫描没有 sorry/admit/axiom/unsafe/implemented_by/extern，没有 CR 或尾空白。公开签名与冻结 scope 去空白匹配先前已独立核对。

上述核查全部通过共享 server.py 的只读文件/散列/版本记录查看完成；未改源/旧票/公共文件/缓存，未 spawn、Lean/API probe、成功目标或 Audit 复编，未下载任何完整原始日志。本轮唯一写入为本报告及授权的服务器报告副本。

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: 实际三个完整公开类型与冻结声明相同并准确对应 R1 的纯实数二元熵充分估计；全部 173 行实际证明、唯一 private 指数引理、所有局部代数/符号门和七个真实生成辅助项均已独立审查。补项在 p=0/1 合法，三段覆盖所有可行 R≠1，正分母、严格平方因子、精确中段证书、指数比较和大段系数方向均正确。全部 11 actual TYPE 完整匹配其实际语义，真实源码/前置/版本/现有 kernel 与传递公理审计证据一致。因此本票是完整独立数学、来源、类型与机械绑定后的 CORRECT，区别于作者先行门或仅声明批准。

本单元证明标准充分的严格 7/200 实数率间隙，未证明最优常数、新颖性、实际 Bernoulli 核、KL 数据处理/likelihood 差、R=1 的 KL 零等价、尾内点混合或全局唯一极小性；也不声称 Lévy、LLT、hW 或任何根闭合。根 A/B/C/D 全部保持 OPEN。本审查不执行 commit/PR。
