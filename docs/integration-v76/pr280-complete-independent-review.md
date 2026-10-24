# SourceIIDGaussianProfileBudget：独立完整终审

STATUS: **CORRECT**

本结论只认证 `Shao.Probability.SourceIIDGaussianProfileBudget` 的五个定义、八个公开定理及其全部实际所属生成声明。完整源到陈述审查、全部源证明审查、31 个完整实际类型、五个完整非定理值和原有服务器内核／递归公理证据均通过。没有发现关键数学缺口。原 C1/C2/OQ3/OQ4/OQ56 根均不因此关闭；OQ3 保持 `PAUSED_BY_USER`。

审查者是新鲜、独立最终验证上下文 `/root/iid_gaussian_profile_full_review`，未参与本模块证明或前提修改，只写本报告及 `drafts/c12-iid-gaussian-profile-full-review/`。按 math-theorem 执行，未启动 math-ultra、其他审查者或侧栏聊天。配置请求为 gpt-6.1-sol/xhigh；运行时未提供可独立验证的实际模型／用量遥测，因此实际模型和输入、缓存输入、输出、推理子集计数分别记为 UNKNOWN/null，不估算订阅占比。

## 精确认证版本

| 对象 | 绑定 |
|---|---|
| 完整 852 行新源 | `drafts/c12-iid-gaussian-profile-budget-production/SourceIIDGaussianProfileBudget.lean` |
| 源 SHA256 | `44960de7f98cd219860b8619b8f07ecfc52369a678fcb73331d8c9838ce1b8c7` |
| PR | [280](https://github.com/randomcat4/shao-lean/pull/280)，审查读回时 open，未合并 |
| 发布 head / tree | `27a05bbbf8905b4b5ffa2425ac169405da5a245d` / `b01f479228483a203de867a3af0a765ab1a53582` |
| 精确合格 Moment base | `f3932326e3d9c91d7582c62cbd418e464a406f97` |
| 唯一新增文件／Git blob | `Shao/Probability/SourceIIDGaussianProfileBudget.lean` / `b7deeb7311ca0439c4c9b2ac675fcc9111d8fe18` |
| 作者本地保留 commit | `bf7cd4d28201f921b2287e3bcad7d3a4f53940c9`；未把它与 API 发布 head 混为同一提交 |
| 原 successful object | `outputs/common-iid-gaussian-profile-budget-v73/attempt011.olean`，SHA256 `0ebfa854fef5807edce7a1847be00df146a684a802d915c7265047e766cb8f62` |
| 作者最终 receipt | SHA256 `2d476e60d4a219fed9825a12d771be28ad389b6028cd148c40721c23f82855f4` |
| 作者最终 RELEASE | SHA256 `83c5de778f12d6e8da46ef09291195bc6953e2608a27217bc2fc7cfac2806455`；写权／执行权释放，heavy=false，inflight=[] |
| 冻结 | `coordination/public-iid-gaussian-profile-budget-declaration-freeze.md`，SHA256 `e20dd769af52aaa8b8edb34185f7725f741ee89175c48e74aee67d2663318f7e` |
| 冻结完整声明候选 | SHA256 `f4191766b68d4cbac218e4a1ce5adf7c79bf37ff27e5c54b9ba0bcf6cb2deff9` |
| 冻结比较 | SHA256 `1323a9b21b42bdfa07cc24a052734e98efc048cf72a0d0de7588e5dcedb30f14`；另做独立逐声明比较，13/13、40 literal lets 相同 |

本地最终 receipt 所列全部十个工件均独立重算哈希并相符。新源严格 UTF-8、无 BOM、LF-only、44639 bytes、852 行，无 sorry/admit/新增 axiom/unsafe/native_decide。独立抽取完整五定义值与八 theorem head 后，与原冻结候选逐一比较；没有新 global/private helper、附加定义或实例。冻结中关于依赖“待生产”的历史文字保留原字节；本审查消费现已合格的精确最终依赖，未将历史 pending 状态当成当前状态，也未改写冻结前提。

## 原稿忠实性与真实范围

完整读了原稿 `C:/game/shao/current/c12/main.tex` 1077–1109，及 `supplement.tex` 4360–4392、4399–4533、4536–4600。两原文件 SHA256 分别为 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`、`b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。审查所依据的是这些完整承重段和实际定义，而非作者摘要或泛函数占位。

源 19–53 的五个值使用原位置的 `Spitzer.head/tail`；尾块首标签就是原样本 `a r`，即论文从 1 编号的下一坐标。源 56–128 将 T=Q−Qr、d=Sn−Sr、同一个最终墙 x√Q、q=|a r|/√T、D=1+|d|/√T、前缀生存事件及移位 |a r|+max(sd,0) 全部逐项识别。`prefixSurvival` 监测完整前缀最大值并含起点 0；closed=false 与原 strict survival 一致，closed=true 保留墙的等号。`gaussianProfiles` 确为 Σ exp(−max(w−M,0)²/T)，不是自由或 killed kernel 的新别名。

本模块支付的是原 `cn:localprofile` 上界 **q³D³Π 本身** 在前缀生存与闭能量 cutoff 下的 iid 期望和秩和。原稿中的实际局部 kernel、G=f_y、导数、Taylor、投影、保留 remainder、负 overshoot 到该包络的点态比较，均未作为输入假设偷偷加入，也未由这八头证明。原 stopping/terminal 以及完整 C1/C2 装配仍需独立完成。删除终点和停止指标可用于构造较大非负 Gaussian 权重，尚不能单凭这个权重预算宣称 `cn:paid` 的实际 L 或根定理已闭合。

## 全部八个证明的实质审查

1. **`gaussian_weight_source_state`，56–128。** 对 Fin r ⊕ Fin(n−r) ≃ Fin n 的实际坐标分割分别取 g(z)=z、z²，得到尾能量、尾和、总能量及前缀和恒等式。r<n 保证非空尾及首坐标 a r。正能量时使用 (√T)³=T√T 将归一化立方质量精确变为 q³；非正能量时选中条件为假，权重先归零。未把能量替换为确定方差。

2. **`fixed_gaussian_weight_measurable_bound`，130–242。** 能量、前缀和、首坐标、平方根、max、exp 和总实数除法的可测性，以及有限交的 strict/closed 生存集合，确实给出联合可测性。T>0 时指数非正，0≤Π≤signs.card；真实平方和几何给归一化首标记≤1、1≤D≤1+√t。因此 0≤F 且 |F|≤card(signs)(1+√t)³。空尾不可能有正能量；零能量时 Π 和 F 同时为零。该界对任意 H/x/signs 成立，无矩前提，合法先支付后续概率乘积测度上的 Bochner 可积性。

3. **`gaussian_weight_early_domination`，244–311。** signs⊆{1,−1} 给 card≤2。z≥0 上 4(1+z³)−(1+z)³=3(z−1)²(z+1)≥0；与 Π≤2 合并，恰得 8 倍的原 early cubic integrand。删除生存指标仅在非负上界内进行；正能量／闭 H≤T 守卫完整保留，未选中时两边零。

4. **`fixed_suffix_weighted_gaussian_integral`，313–390。** 先用第 2 头的确定有限常数界支付固定任意实际尾块后的前缀可积性。随后精确消费已接受 Profile 的 `iid_fixed_suffix_gaussian_wall_profiles`，其 V=r∫z²、归一化 law、Rprefix、随机最终墙、A 及每个移位与本模块一致。固定尾块的非负 q³D³ 可提出积分；Profile 的 D² 给出 D⁵，环恒等式恰为 Marked.lateMarkedWeight，而非假定目标 CR。H>0 确保 H≤T 选中时 T>0；其余分支两个权重均零。C 由上游存在量词先选定，不依赖 law、r、尾块、x 或符号。

5. **`iid_rank_gaussian_weight_fubini`，392–431。** piCongrLeft 的逆与 sumPiEquivProdPi 的复合逐坐标等于真实 head/tail，其推前恰为原 prefix law × 原 suffix law。联合 F 已以概率空间上的确定常数支配而真正可积；再用 integral_map 及 integrable product Fubini，得到先前缀、后尾块的积分与外层可积性。没有用 Bochner 对不可积函数的默认值制造等式；r=0 的空前缀乘积也覆盖。

6. **`iid_late_rank_gaussian_integral_bound`，433–507。** r>0 与原二阶矩正性给 V>0，r<n 给尾长正。Fubini 后才使用固定尾块的前缀上界，再消费 Marked 的实际 product-law 可积性及 marked integral=averaged integral。此时剩余 D⁵、T/V、Rprefix 确对尾标签对称，早于此时仍含生存／Π 的函数未被擅自平均。尾坐标嵌入 i↦r+i 单射，真实 iid 尾边缘的 IdentDistrib 使平均权重回到同一 Path n 上，未重抽下一坐标或改用条件于 Q、Sn 的律。

7. **`iid_gaussian_profile_early_late_budget`，509–785。** 只消费合格 Moment 的 raw geometry、early 和 late(p=5) 三个实际完整头；原 sigmaSq、scale、normalizedLaw、R、h=4n sigmaSq R² 及 prefix law 完全一致。raw geometry 从原有限正二阶矩支付 R>0、h>0，二者不作为新前提。每 rank 可积性在使用积分单调性前已由第 5 头得到，有限和也逐项可积。早秩 2r<n 经 t=n−r 单射进入 Icc((n+1)/2,n)，利用非负性补足区间；偶 n=2m 时实际早像 m+1,…,n，原 budget 额外 m 项只扩大上界。晚秩 n≤2r 给 r>0，t∈Icc(1,n/2)，且嵌套自然数减法运输到原 tail 后，LW5 与 Marked.lateAveragedWeight 逐点相同，闭 cutoff 由 h>0 正确匹配。早／晚不交并覆盖全部 Fin n，total=early+late。最终 C=8CE+CP·CL 在 law/n/r/x/signs/closed 前选定；用 R≥0 同时支付 early、late、total，不把已有个别 CR 上界误当本定理前提。

8. **`iid_family_gaussian_profile_budget`，787–850。** 三个实际秩和先证可测，再由 `iid_samplePath_identDistrib` 的真实联合 iid law 同时运输可积性及积分。Ω 任意可测空间；每坐标可测、iIndepFun 及与同一 ν 的 IdentDistrib 均按完整头保留。没有把交换性、条件独立或逐点相等替换为真实联合 law。沿用同一个全局 C。

## 依赖消费和边界攻击

Profile 源 `c22326bc59064fcabc05de2c718bc13b7e1ed47b0e753b587eaa475b7e745449`／对象 `bc7d012096eba0f0e00a5e6af23877a697e8f0f9d35e2cbea5432b65d37bfa3b`，Marked 源 `879023fb756a2b6ea31fea61ffe159ffe6053aa94221302d1f09a4e2762e01c9`／对象 `c1aa13831cc77f08be701ed197fe3dc02f4dca45d0e8090d41869d8159a3527c`，均精确绑定已接受结果。Moment 按 `coordination/common-suffix-moment-budgets-root-qualification.json` 消费源 `c0457040fec0cee18355f5028c7731e0ad8525deee28185aa0cf3b7a088d3c7b`／原 producer39 对象 `feb6b5c085f1be3dc9e5ccbc5a8414a1b99a022a9a238abf87a063d7092bb08f`。已定向实读所需完整公共头、全部 literal lets、Marked 实际定义值及 FiniteIID/Spitzer/FinitePath 的实际接口；复用其既有合格完整证明／类型／公理审查，不重复旧证明或旧检查。

- n=1 时只有 r=0，late 为空；空前缀 Fubini 与 early 正常工作，不调用 r>0 的 Profile。最终预算明确 n>0；n=0 没有 Fin n 秩，不伪造下一坐标。实际 r<n 总有非空尾。
- T=0、尾部全零、原律在 0 有原子时，Π/F 先归零；真实 h>0 自动排除所选零能量。H=T 保留。严格／闭生存均可测且由上游 Profile 支持，不删除等号原子。
- n 偶数的 r=n/2 属于 late；early 使用原 moment 区间时补入的是非负项，没有重复计算 total。
- signs 可空、单壁或双壁，有限集的 card≤2 有明确证明；尾样本相同数值仍是不同 Fin 标签，marked 平均不合并重数。
- 只输入原中心化及正有限二阶矩，无第三矩、对称性、有界支持、密度、无原子、目标可积性或预算前提。大 R、小 R、R=1/2、n≤3 的上游统一预算被原样消费，没有偷偷只保留小 R／大 n 子情形。

## 31 个实际所属声明与五个完整值

全文逐块读取原 `actual-owned-types-and-values.txt`，SHA256 `1a8a6307684204ece45872819196e3962d8568585cf65f94dbbaa3655d89830f`，105344 bytes；为降低重复显示，仅用 39 项精确字面子表达式字典，反向替换与原文件逐字节相同。完整字典及四段全部编码文本均实际读过，没有删除 binder、实例、类型、值或声明，没有省略号。结构化报告 JSON 为以下 **全部 31 项保存完整实际类型、五项完整值、对应源证明区间和判断**，可直接与原 transcript 复核。原所有者集合与 transcript 集合精确相同。

下表中短名前缀默认为 `Shao.Probability.SourceIIDGaussianProfileBudget.`；`Spitzer.head.eq_1` 特别保留其完整异命名空间身份，未按命名空间过滤遗漏。

| # | 实际声明 | 种类／源覆盖 | 完整类型／值判断 |
|---:|---|---|---|
| 1 | iid_gaussian_profile_early_late_budget._proof_3 | generated theorem；705–711、729–735 | n−r=n−s 与 Fin 边界给 r=s；完整 type 已读 |
| 2 | iid_gaussian_profile_early_late_budget._proof_5 | generated theorem；760–767 | 2r<n 与 n≤2r 不相容；完整 type 已读 |
| 3 | **Shao.Probability.Spitzer.head.eq_1** | generated equation；源 88–92 消费／SpitzerFinite 35–37 定义 | 原 head 按原标签求值的完整等式已读 |
| 4 | fixed_suffix_weighted_gaussian_integral | public theorem；313–390 | 完整全局 C／law／4 lets／可积性／上界均审查 |
| 5 | iid_late_rank_gaussian_integral_bound._proof_2 | generated theorem；471 | i<n−r 推 r+i<n；完整 type 已读 |
| 6 | rankGaussianWeight.eq_1 | generated equation；49–53 | 真实 head/tail 权重完整等式已读 |
| 7 | iid_late_rank_gaussian_integral_bound._proof_3 | generated theorem；472–477 | r+i=r+k 推 i=k；完整 type 已读 |
| 8 | iid_rank_gaussian_weight_fubini | public theorem；392–431 | 两项完整可积性与嵌套积分等式已审查 |
| 9 | firstValue.eq_1 | generated equation；19–20 | 非空首标签／空尾零完整依赖分支已读 |
| 10 | prefixSurvival | definition；23–29 | 完整类型与值已读：有限 signs、原最终墙、strict/closed |
| 11 | rankGaussianWeight._proof_1 | generated theorem；52–53 | r<n→r≤n；完整 type 已读，递归公理为空 |
| 12 | gaussianProfiles | definition；32–39 | 完整类型与值已读：T>0、原 shifted exp 有限和、否则零 |
| 13 | firstValue | definition；19–20 | 完整类型与值已读：dependent if，无虚构坐标 |
| 14 | fixed_suffix_weighted_gaussian_integral._simp_1 | generated theorem；389–390 | 任意 preorder 的 a≤a ↔ True 完整 type 已读 |
| 15 | iid_gaussian_profile_early_late_budget | public theorem；509–785 | 完整全局 C／40 lets 中本头11项／各可积性及三个 CR 均审查 |
| 16 | gaussian_weight_source_state | public theorem；56–128 | 九个完整 lets、四状态恒等式及实际权重等式均审查 |
| 17 | gaussian_weight_early_domination | public theorem；244–311 | 两个完整 lets、符号前提、精确 8 倍及守卫均审查 |
| 18 | iid_late_rank_gaussian_integral_bound | public theorem；433–507 | 完整全局 C／真实 r／四 lets／平均尾积分上界均审查 |
| 19 | fixedGaussianWeight.eq_1 | generated equation；41–46 | 含 Classical 决定的完整守卫及 q³D³Π 值等式已读 |
| 20 | iid_gaussian_profile_early_late_budget._proof_4 | generated theorem；736–741 | late 映射落入 1≤n−r≤n/2；完整 type 已读 |
| 21 | fixed_gaussian_weight_measurable_bound | public theorem；130–242 | 完整乘积可测性、非负常数界、零能量值均审查 |
| 22 | iid_late_rank_gaussian_integral_bound._proof_1 | generated theorem；465–466 | 0<0 的空尾矛盾；完整 type 已读 |
| 23 | iid_gaussian_profile_early_late_budget._proof_1 | generated theorem；637–640、712–717 | early 映射落入 (n+1)/2≤n−r≤n；完整 type 已读 |
| 24 | rankGaussianWeight | definition；49–53 | 完整类型与值已读：按同一原样本的真实 head/tail |
| 25 | fixed_gaussian_weight_measurable_bound._simp_2 | generated theorem；180 | Finset insert 的全称量词分解；完整 polymorphic type 已读 |
| 26 | iid_gaussian_profile_early_late_budget._proof_2 | generated theorem；665–666 | n≤2r 与 r:Fin n 推 r>0；完整 type 已读 |
| 27 | iid_gaussian_profile_early_late_budget._simp_1 | generated theorem；638、715、739 | 局部有限 preorder 的 Icc membership 等式；完整 type 已读 |
| 28 | fixedGaussianWeight | definition；41–46 | 完整类型与值已读：T>0、H≤T、生存、首标记³D³Π，否则零 |
| 29 | gaussianProfiles.eq_1 | generated equation；32–39 | 包括总实数实例、指数符号和零分支的完整等式已读 |
| 30 | iid_family_gaussian_profile_budget | public theorem；787–850 | 任意 Type u／真实 iid／十 lets／全部可积性及 CR 均审查 |
| 31 | prefixSurvival.eq_1 | generated equation；23–29 | 完整 proposition 值等式已读，含有限 signs 与 closed 判断 |

这恰为 26 theorem（8 public＋18 generated）＋5 definition，非定理均有完整值，没有 opaque、primitive、instance 或其它未覆盖种类。所有 generated arithmetic、equation 与 simp 声明均逐完整类型检查其数学含义，并由同源内核及递归公理回执覆盖；没有把它们仅计数即视作完成。

## 服务器证据、复用与释放

独立完整读了既有 `OwnedAudit.lean`。它通过 `env.getModuleIdxFor?` 选出 **exact-module-owned** 全集合，对每项调用递归 `Lean.collectAxioms`，打印 pp.all 完整类型并打印全部非定理值，而非仅扫描公开头或按命名空间选名。审计源 SHA256 `0e4191875975926388d991ea205cd007400061d3004beecb2f6cfe33efcc3a49`，JSON SHA256 `45f6b7c9d92aa4d001e69f63099873f48350b49ba929d3f68691c873b293fb99`，完整 audit log SHA256 `8ee35479df8fa7e0866e9c0d35f840a05acc0b92ab368557582e5f2d8d8860a8`。全部 31 项递归公理都在 propext、Classical.choice、Quot.sound 白名单内，无 sorryAx 和打印省略标记。

一次现有 broker 的轻量只读操作核对了最终服务器源、原 attempt011 对象及当前导入对象（同一哈希／原对象解析路径）、audit 源／JSON／log、Profile/Marked 精确导入对象、Moment 原 producer39 及只读导入对象。原 kernel log SHA256 `6d6c7ca624502f15c8ef78b6152a8381f319bb84738f52364c2ccdf04c0a1ac9` 与 receipt 一致；作者记录 kernel exit=0、audit exit=0。读回日志尾只有废弃名／风格／unused-variable 提示，无改变数学结论的错误。作者 receipt 保留此前失败尝试与 partial 里程碑；本审查未删除、替换或重跑它们。

同一次只读操作从 GitHub 读回 PR280 的确切 head、Moment base、唯一新增路径及完整 Git blob；服务器原源的 Git blob 相同，tracked source 干净。发布 tree 采用封存 publication 元数据中的精确值；PR 读回的 base＋唯一新增 blob 给出了相同的单源变更绑定。本报告未把 API 发布提交与保留的本地提交混同，也未执行合并。

工具链证据沿用作者的 Lean `leanprover/lean4:v4.36.0-rc1`／mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，CPU10–13、root-heavy.lock、-M8192/-j4。审查新执行 **0 Lean、0 AX replay、0 producer recompile、0 cache writes**；没有本地 Lean、环境安装或新 wrapper。已有精确源绑定成功证据与本次完整独审共同认证本模块，未重复旧 Profile/Marked/Moment 证明或其检查。

剩余实质边界是实际局部包络比较和原 stopping/terminal/root 装配；PR 的共享整合由 root 正常处理，本报告不代替整合验收，也不产生任何新颖性或原根闭合声明。审查报告完成后以 `drafts/c12-iid-gaussian-profile-full-review/RELEASE.json` 释放本审查的全部写权／执行权，inflight=[]，不继续充任下一源的 fresh 审查者。
