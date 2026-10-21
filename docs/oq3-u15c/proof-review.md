# U15c 完整独立证明、来源与类型审查

STATUS: CORRECT

审查者沿用唯一 lease 1，仅拥有本报告与服务器对应 proof-review.md；不改源码、scope、旧票、共享文件或缓存，不 spawn。承认此前声明审查上下文存在；本阶段仍先仅提取 actual 完整公开类型，独立重新盲译并先落盘，尚未读取本次实际证明或机械证据。

## 第一阶段：actual 两个完整公开类型盲译

实际输入 drafts/oq3/CompactTiltDomination.lean，SHA256 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623，59 行。零公开定义；本阶段只读提取出的两个完整公开类型。

1. `exists_compact_parameter_box (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ)`：对任意真实实数二重积紧集及任意参考系数，存在一个共同实数 L≥0，使全部 p∈K 的两个坐标相对 u0、v0 的绝对差均≤L。K 可以为空，参考点无需属于 K。L 在所有 p 外一次选取，不能逐 p 改变；证明不应从空 K 提取元素。

2. `exists_compact_quadratic_tilted_domination (mu : Measure ℝ) [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ)`：先给同一真实概率基准 mu、M≥0 及其 AE 支撑界、任意紧参数集 K 和参考系数，存在同一个实数 m>0，在全部 p∈K、全部实频率 s,t 之前固定；对每个 p，同时给出 (a) ofReal m 倍真实参考二次势倾斜律≤真实 p 倾斜律；(b) m² 乘参考同律二重积下实际 1−cos((x−y)(s+t(x+y))) 的实积分≤p 倾斜律的同核二重积积分。合取两支共享 m，不能分别选择两个常数；m 不依赖后续 p/s/t。M=0 和空 K 都包含。真实倾斜概率与可积性没有列成额外假设，须通过已接受实际前置合法获得。

本盲译先落盘。之后按 scope/R2→完整实际证明/locals/private/generated/固定库→全部 actual TYPE→receipt/机械证据顺序审查。根 A/B/C/D 与 WC 均保持 OPEN。


## 第二阶段：冻结范围与真实来源

盲译落盘后，已直接读取全部 scope、此前已接受的声明票、59 行 actual 源及 R2 第 343–369 行。scope SHA256 `d2d980d0c91aba2b420bf969817c081649380b5804ad843b1e9a47160d0b9ec6`，声明票 SHA256 `a1ef810936a84ad6e4a32d941b3a29c50fcda5af3f3b4f3450617cc4a597d4ef`；实际来源 R2 SHA256 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。actual 两个公开完整类型与冻结 Lean 块去空白逐字相同。

R2 第 345–352 行要求紧参数集上同一正下界 m 与 theta 无关，式 (20) 为密度下界；第 355–363 行式 (21)–(22) 使用二样本非负核与平方因子。actual 实现只补上紧参数统一常数选择，并调用已接受的真实测度/明确余弦积分估计；没有在代码中证明或假定缺失的特征函数恒等式。核仍相当于原 W=(X,X²) 差相位 `(x−y)(s+t(x+y))`，没有替换二维支撑或混用频率与倾斜系数。

实际 imports 为 ProductMeasureDomination、Normed.Group.Bounded 及六个明确 tactic 模块，open MeasureTheory、open scoped ENNReal NNReal，与冻结环境一致。唯一直接 Shao 前置 U15b 的实际 SHA256 `9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f`；传递 U15a 的实际 SHA256 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`。已重新读取本单元实际消费的完整公开接口并核对其语义，未重做旧成功 proof 门或构建。

## 第三阶段：全部实际证明与局部辅助

以下数学审查在读取 Audit TYPE、收据、构建/PASS 前独立完成并落盘。实际源码无 authored private theorem 或定义；生成项尚待实际 TYPE 枚举而不先推测。

### 第 15–28 行：真实紧集共同盒宽

hF 是整个 ℝ×ℝ 上 F(p)=|p.1−u0|+|p.2−v0| 的真实连续性，标准投影、减常数、绝对值及相加足够，fun_prop 的数学义务成立。第 18 行 hK.exists_bound_of_continuousOn 只使用紧性和 hF.continuousOn，得到某个实 C 及 ∀p∈K，‖F(p)‖≤C；未假定 C≥0 或 K.Nonempty。

第 19 行真实见证为 max C 0，其非负性来自 le_max_right。在任意 p∈K 后，hsum 先用 Real.norm_eq_abs 与 le_abs_self 得 F(p)≤‖F(p)‖，再用 hC p hp 和 le_max_left 得 F(p)≤max C 0。最后利用两个绝对值非负分别从和界取出两个坐标界，linarith 方向正确。

K=∅ 时仍可调用实际无非空门的库接口，后面的 intro p hp 是空全称义务；没有从 K 中取元素或调用需非空最大值。C 若为负也不破坏见证 L≥0。参考点不需属于 K，退化点集也合法。这里产生的单个 L 位于所有 p 之外。

### 第 30–56 行：同一个 m 在全部参数与频率外

第 43 行先从目标一一次取 L,hL,hbox；局部 B=L(M+M²)。第 45 行即选择 m=exp(−2B)，并由 Real.exp_pos 真实证明 m>0；这发生在第 46 行引入 p,hp 与第 50 行引入 s,t 之前。不存在将参数选择后移、逐频率选择系数或用两个不同存在常数满足两支合取的情况。

同一 p,hp 下第 47 行从 hbox 取得同一个 L 的 hu,hv。第一合取分支直接使用实际 U15a quadratic_tilted_measure_domination，参数 mu,M,L,hM,hL,hb,u0,v0,p.1,p.2,hu,hv 完整一致。目标的 ofReal m 与定理系数 ofReal(exp(−2L(M+M²))) 经局部 B 展开完全相同。

第二分支对任意 s,t，hsquare 用 pow_two、真实 exp_add 与 ring 给 `exp(−2B)²=exp(−4B)`。它只是精确实指数恒等式，不需要除 B 或要求 B>0。改写后实际 U15b quadratic_tilted_cosine_pair_domination 以同一组 mu,M,L、同一参考/新系数、同一 hu/hv 及 s,t 完成目标。左右实际积分与产品边际完全相同；m² 没有被误换成 m。

L≥0、M≥0 真实保留，所以 B≥0；因此所取 m 也≤1，符合非空 K 时两个概率律间的支配含义，虽无需另输出此结论。m 是有限实指数，ofReal m≠∞。M=0 时 B=0、m=1；L=0 时同样。没有在源码中除 M/L 或提取严格正盒宽；两个边界仍合法。K=∅ 时 m 仍真正 >0，后续 p 的两个义务为空，未对空 K 做非空提取。

### 真实可积性与概率语义继承

本代码没有自己重复建立倾斜概率，而是合法消费已完整独立接受的 U15a/b 公开定理。U15a 的实际二次指数可积定理消费同一 mu 概率、M≥0、同一 hb；任意参考及新参数均真可积。概率 NeZero 加此可积门给正归一化并使库 isProbabilityMeasure_tilted 的前提成立，避免不可积 tilted=0 的总化分支。

U15b 的实际被调用接口内部先用上述真可积性建立两个真实 tilted 概率，再用真正 SFinite 产品、连续且 0≤1−cos≤2 的核的真可积性、有限标量测度积分比较得到 exp(−4B) 系数。两条实际公开接口没有缺失的外部 hf/概率前提需要 U15c 另行供给；hM,hL,hb,hu,hv 正是全部数学输入。本次调用也未将不同基准 mu/不同参考参数的结论混接。

因此本模块真实继承的是实际测度/产品积分的证明，并非依赖未经核查的 RN 导数、特征函数恒等式或总化积分值。共同 m 依赖固定 K、u0,v0、M，可以允许依赖 mu，却绝不依赖后续 p,s,t。

## 第四阶段：固定库实际语义

指定服务器仅只读核对，未 Lean/API probe 或编译：

- `Analysis/Normed/Group/Bounded.lean` 实际 SHA256 `7ff0b64a69f6e44ea002c3f21fac6011801737d81629fc9c2d4280e4b8846042`，20 行 public section，27–28 行 seminormed group 上下文。91–95 行明确 `@[to_additive IsCompact.exists_bound_of_continuousOn]`，实际加法版接口要求 TopologicalSpace α、IsCompact s、ContinuousOn f s（实 codomain 满足 SeminormedAddGroup），结论 ∃C，∀x∈s，‖f x‖≤C。无 Nonempty s 门；证明来自紧连续像有界和 69–74 行实际 norm bound。此处 α=ℝ×ℝ、E=ℝ，默认实拓扑/范数一致，无任意矩阵范数或隐藏实例。
- `Analysis/Complex/Exponential.lean` 实际 SHA256 `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`，212 行 Real.exp_add，284–287 行 Real.exp_pos；正性对所有有限实数成立，平方改写的指数和恰是 −4B。
- `Measure/Tilted.lean` 实际 SHA256 `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`：42–43 行真实 withDensity(exp/真实积分) 定义，46–48 行不可积为零；126–135 行概率实例需要 NeZero 与 exp Integrable。实际 U15a/b 被调用定理保留所有这些数学门的正确继承。

actual U15a/b 两个消费接口完整类型及其固定源码 SHA 已在本次指定服务器直接读取；其既有完整独立数学审查仍有效，不重复旧构建或把作者绿灯当作本次证明。本单元全部 59 行、所有局部 C/hC/hsum/L/B/hu/hv/hsquare 与两次继承调用均已独立核对。数学阶段结论 CORRECT，随后核全部实际 TYPE，再最后读机械证据。


## 第五阶段：全部 2 个 actual owned TYPE

数学阶段先落盘后，从真实服务器现有 Audit.log 仅过滤读取 DECL/TYPE 与全部续行，未提前读 AXIOMS、PASS 或 receipt。实际 owned 清单为两项：

1. `Shao.OQ3.exists_compact_parameter_box`：实际第 2 行完整类型为 ∀K:Set(ℝ×ℝ)，IsCompact K→∀u0,v0:ℝ，∃L:ℝ，0≤L∧∀p∈K，|p.1−u0|≤L∧|p.2−v0|≤L。没有 K.Nonempty、参考点属于 K 或任意补前提；存在 L 的位置正确。
2. `Shao.OQ3.exists_compact_quadratic_tilted_domination`：第 5–35 行所有长续行完整读取。真实 mu 概率、M≥0、同一 AE 支撑门、K 紧及参考系数之后，先 ∃m>0，再∀p∈K；同一个 m 的 ofReal 测度下界与∀s,t 的 m² 实际参考/目标产品余弦积分下界为合取。两次产品的两个实际边际及相位完整括号均核对一致。无 Nonempty K，M=0 允许，没有逐 p/s/t 的新存在量词或替代常数。

实际 2 项均为公开 theorem；无 owned 定义、private 或额外 generated 常量。不是仅按预期计数判断，全部 actual TYPE 及其长续行均已逐项核读。类型阶段结论 CORRECT，随后才读取作者机械证据。


## 第六阶段：作者收据与真实机械产物最后绑定

完成并落盘全部数学与 actual TYPE 审查后，才读取 receipt、Audit 源/AXIOMS/PASS、实际 build 日志、依赖散列和 pins。作者门只作机械绑定证据，不替代独立判断。

- 本地 U15c-receipt.json 与真实 run/receipt.json SHA256 均为 `97af81c941a552d6f7e5e8d61efd105d4fff121f61c854e177a374dece9c3077`。status 为 AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW；nonclaims 的终审 pending、未 commit/PR 均明确限定在 author-check time，历史语义正确。implementation_environment_note 与实际源码保持冻结 imports/namespaces/两个完整类型相符。
- 本地 draft、真实 worktree/Shao/OQ3/CompactTiltDomination.lean 与 run/CompactTiltDomination.lean 三者 SHA256 均为 `6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623`，59 行、2459 字节。真实 run/scope.md SHA256 `d2d980d0c91aba2b420bf969817c081649380b5804ad843b1e9a47160d0b9ec6`，statement-review.md SHA256 `a1ef810936a84ad6e4a32d941b3a29c50fcda5af3f3b4f3450617cc4a597d4ef`，与本地冻结值相同。两个完整公开类型去空白一致由本审查独立核对，不只引用收据 PASS。
- 真实 build-01.log 为 0 字节，SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`。作者既有 receipt 记录命令 `lake env lean -o .lake/build/lib/lean/Shao/OQ3/CompactTiltDomination.olean Shao/OQ3/CompactTiltDomination.lean` 的 exit_code=0；本次不重新执行，核对的是既有实际日志与产物，不将空日志本身误称为独立 exit-code 证明。
- 真实目标 olean 存在，129088 字节，SHA256 `1d4de69af4fcc677890b6da5f96cba2d06c943a2d1cb48b52d6ecf09590bb948`。
- 真实 Audit.lean 1533 字节，SHA256 `aecd8f35d83100b8ea733b51637c8d63e09580b0a5b9222cff20d748c12760cf`，已完整读取。它检查两个冻结名称为 theorem，枚举两个公开 stem 的全部后代及整个 `_private.Shao.OQ3.CompactTiltDomination` 前缀，拒绝 isAxiom，并对每项 collectAxioms 的全部传递叶检查白名单 propext、Classical.choice、Quot.sound。结合完整源码仅两个公开 theorem、无定义/private/额外声明，该覆盖与真实 owned inventory 一致。
- 真实 Audit.log 1854 字节，SHA256 `b3dcfa6743a8fca22649ea938f2053ccf150c7710747c512955afda178ab2773`。此前已完整读取两个 TYPE；本阶段实际读取两条 AXIOMS，均只有白名单三项，无 sorryAx 或额外项目公理。真实末尾为 `U15C_FROZEN_THEOREMS 2`、`U15C_ALL_THEOREMS 2`、`U15C_ALL_DECLARATIONS 2`、`U15C_AXIOM_GATE PASS`。作者 Audit exit_code=0 记录与实际 source/log hash 一致；没有重跑 Audit。
- 独立从 actual imports 递归枚举得到恰好两个 Shao 前置：`Shao/OQ3/ProductMeasureDomination.lean` SHA256 `9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f`，`Shao/OQ3/TiltedMeasureDomination.lean` SHA256 `5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b`。其闭包与 receipt/imported_project_sources_sha256、实际 run/prerequisite-hashes.json 完全相同；没有隐藏依赖缺失的根公共特征模块。
- 真实 lean-toolchain 为 `leanprover/lean4:v4.36.0-rc1`，文件 SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。Mathlib manifest rev 与实际 package git HEAD 均为 `807d3836b165983210ee2ecf3cd28f239436949c`；未运行 Lean/Lake 版本探针或编译。
- 观察时实际 branch `feat/oq3-compact-tilt-domination`，HEAD `b84e36ff85f689de13a2f1826b08e2144b21af3e`，git status 仅 `?? Shao/OQ3/CompactTiltDomination.lean`。此为审查时点绑定，不限制 lead 随后获准提交。独立 actual source 扫描无 CR、尾空白、sorry/admit/axiom/unsafe/implemented_by/extern。

全程仅通过共享 server.py 只读核查源、既有产物及散列/指定日志内容；不改实现/scope/旧票/公共文件/缓存，不 spawn、Lean/API probe、重编成功 target/Audit 或下载完整原始日志。唯一写入为本报告及授权服务器对应报告副本，不执行 commit/PR。

## 最终完整独立裁决

STATUS: CORRECT

JUSTIFICATION: actual 两个完整公开类型与冻结声明相同且准确对应 R2 紧参数共同常数来源。全部 59 行实际证明及全部局部辅助已独立核查；真实无 Nonempty 门的紧连续像取界、max C 0、同一正指数见证先于全部 p/s/t、两个合取分支共享 m、精确指数平方、M=0 和空 K 均正确。实际 U15a/b 的真实可积性、倾斜概率与产品积分门被同一输入合法继承；全部 2 actual TYPE、两个项目依赖、source/pins/现有 kernel 与传递公理证据一致。因此本票为完整独立 proof/source/type/机械绑定后的 CORRECT，区别于作者先行门与仅声明批准。

结论仅为标准充分的紧参数共同测度/明确余弦核积分常数选择，不识别实际特征函数模平方差，不证明 WC、除二常数/标准化、无界扩展、最优性、新颖性、KL、Lévy、LLT、hW 或任何根闭合。根 A/B/C/D 与 WC 全部保持 OPEN。
