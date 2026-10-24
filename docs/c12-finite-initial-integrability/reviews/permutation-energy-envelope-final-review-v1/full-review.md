# 真实排列能量包络与正阈值可积性：独立完整终审

STATUS: CORRECT

两份最终冻结的局部命题及完整生产证明均正确，未发现关键缺口。该结论覆盖 7 个公开源定理、3 个透明定义，以及按实际模块所属选出的全部 22 个常量（19 个定理，其中 12 个生成定理；3 个定义）。C1/C2 原根保持 OPEN。

审查者 `/root/permutation_energy_envelope_final_review` 使用本次显式选定的 `gpt-6.1-sol/xhigh` 新上下文，未参与两模块的声明冻结、源或证明写作；追加单元也是作者在审查期间独立完成后送审。只写本审查目录，没有修改生产源、冻结、旧证据或库。用量四分项均未由工具暴露，记为 null。

## 语义与证明

`PermutationEnergyEnvelope` 的两完整定义保留原标签总和/平方和，减去位置严格小于 r 的已揭示项。令 b=a(σr)，d 为真实剩余和，T 为真实剩余平方和。完整阅读并核对已合格依赖 `PermutationCompensation.remaining_sum` 和 `remaining_square_sum` 的实际全类型及当前消费交互；其精确源/对象与旧合格版本相同，复用旧完整证明审查，没有重复审证明或编译。该依赖没有所属非定理定义需要补读。

对 U={i:r≤i}=Ici r，其基数恰为 n-r，且 r∈U。平方非负给 b²≤T；常数 1 与 a(σi) 的有限 Cauchy–Schwarz 给 d²≤(n-r)T。T>0 时得到 |b|≤√T 及 (|d|/√T)²≤n-r。于是 |b−b²d/T|≤√T+|d|。乘上明列的一阶导数标量输入 |fy|≤C/√T·(1+|d|/√T)，化为 C(1+x)²；再用 (x−1)²≥0 与 x²≤n-r，得到真实补偿贡献≤2C(1+n-r)。两个完成值属于 [0,1] 给差的绝对值≤1，因此实际余项≤1+2C(1+n-r)。完整证明每步的正分母与乘法保序条件均由 T>0、C≥0 明确提供。

`GuardedPermutationIntegrability` 的完整透明值是在 H≤同一真实 T 时取该真实余项，否则为 0。真实剩余和/平方能量由有限实坐标的和、平方、差构成；总除法和阈值集合可测，三个函数的显式可测性给分段函数可测。这里的可测性定理本身对任意 H 成立；这是 Lean 实数总除法的代数陈述，不将 T=0 的表达式解释成真实核导数。

在点态界中，live 分支由 0<H≤T 得 T>0，并消费本轮已完整审查的前模块结论；n-r≤n 与 C≥0 给统一界 1+2C(1+n)。dead 分支是 0。对任意 `Path n` 上的概率测度，该常数可积；可测性给几乎处处强可测，绝对值界给范数支配，`Integrable.mono'` 合法推出可积性。这里没有把目标余项界或 Integrable 作为前提，也没有要求样本高阶矩、无原子性或独立性。`Path n` 的完整缩写值是 `Fin n → ℝ`，实际全类型明确使用有限实坐标的产品 Borel 可测结构。

全部 22 个无省略实际类型和 3 个完整定义值均直接完整读取，没有用结构摘要或字典代替。各生成定理分别覆盖 filter/univ/Ici 成员、预序反身性、2/3/4 非零、非零乘积/自然幂/整数幂、特征零自然数加一非零，以及 guard 的精确展开式。逐名全类型、值及审查覆盖见 `full-review.json`。

## 来源和未关闭边界

核对原文 `C:/game/shao/current/c12/main.tex` 871–956，尤其 885–944 的真实补偿项与有限总体可积性论证，以及 `supplement.tex` 4194–4244、4325–4392 的完成核和零能量/边界约定。d 对应 S_n−S_r，T 对应 Q−Q_r，未用确定方差替代。源文的泛常数界被落实为显式的 1+2C(1+t)；这是同阶的有限统一界，不宣称相同数值常数。

本轮只接受明确冻结的局部结论。`fy/FY` 是实数或实值函数输入，一阶导数估计、真实核导数存在性/正则性，以及 FY/Vnext/Vnow 的实际核识别与可测性实例均没有在这里被证明。三个完成值函数必须由消费者满足现有可测性、[0,1] 值域和同一 T/d 的标量导数界。C 必须统一于总体 a，不能在积分步骤改为依赖 a 的常数。

σ 在两模块中是任意固定标签排列，值可以重复；uniform permutation 的条件补偿以及对排列的后续平均属于另一个接口。这一可积性结论针对固定 σ,r 的阈值截断项，尚未装配原样本上的条件有限 telescope 积分、真实 completed 过程、停止秩或掩码实例，也没有作原自然 iid filtration 的停止时刻断言。

阈值 guard 只处理 H≤T，不代替 crossing-kill、严格生存、exterior endpoint、a=0/Q=0 的零完成值或可达 T=0 终端约定。真实核消费者仍须遵守这些源约定。零能量不落入 H>0 的 live 分支；未以 T=0 的代数总除法补造核导数。n=0 无 Fin n 的 r，结论在该处无实例；r=n−1、单个剩余标签、零项、重复值及并列均未被排除。

## 精确证据与复用

| 模块 | 源 SHA256 | 原对象 SHA256 |
|---|---|---|
| PermutationEnergyEnvelope | `0a5acbf50a49e01da4dd9e70297a2a859d07ca3bd9a9281c26ab5c87af896d3e` | `8171b3dd5517878e333d3cd39431a8930116feab19df85467a828ebdec402e2d` |
| GuardedPermutationIntegrability | `a4fc6ce4bd78d26de1b1b88b44ad94a21e0fc624d66577821accdba29103bf2d` | `f34d8a8693ee574c1211a4f31533ba20dfdcbc3bba6cdc47bb5b7f350e3f31ee` |

前模块 4 个完整定理头和 2 个完整定义值与实现前冻结一致。追加模块的 3 个完整定理头和 1 个完整定义值同时与原冻结及 v2 冻结一致；v2 只补两个既有 Bochner/概率类型类导入。所有源为 UTF-8 无 BOM、LF，CR=0。前模块初次失败只是在 `field_simp` 已关闭目标后多余 `ring`；追加模块初次失败只缺导入。失败源/日志保留，没有改前提或定理值。

复用两份 attempt002 的成功内核与全所属递归公理审计。服务器当前源、原尝试源、当前对象、原对象及所有 receipt 所列工件 SHA256/字节数均相符。17+5 个类型块和 2+1 个值块逐块与原成功审计日志去除块边缘空白后的完整内容一致。全所属选择直接用 `env.getModuleIdxFor?` 的实际模块，不按命名空间或公开名筛选；`Lean.collectAxioms` 对每个所属常量递归收集公理，均只用 `propext`、`Classical.choice`、`Quot.sound`。没有 sorry/admit/新 axiom/unsafe/native_decide。

直接旧依赖 `PermutationCompensation` 当前源 `be8c406d01ff106b64fa52b0d65dda8817ea3095eeb6fbaba2a66b49a21cf5e9`、对象 `4ce8c941dd686accd628211baff78a9914c2b6c9a8a6a2836a5456d687807dbd` 与旧合格版本一致；旧完整独立审查 JSON SHA256 为 `568c781dac68a0ecb79e401897d30ceaa70dead2966fa77f47f9972406b29ed2`，本次复用。已有 MeasurablePath/FinitePath 源与已接受 main 和本地只读库完全一致，其旧证明不重审。

只读服务器核验运行在 `/root/rivermind-data/shao-lean-20261021/workspaces/c12-bridge-domination-v71`，分支 `author/c12-finite-initial-v71`，HEAD `01c4cb2b0092402bf89556fe2c75cd861ab7bfaf`。固定 Lean `v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c` 与 shared-v34 只读 package view 相符。只读绑定检查使用 c12-heavy.lock 与 CPU14–17；本审查 Lean 调用 0、producer 重编 0、audit 重跑 0。

一次只读绑定脚本在检查旧失败日志时将 `No goals to be solved` 误按小写精确匹配，导致脚本末段断言失败；失败响应保存在 `remote-binding-attempt001-response.json`。修正大小写分类后所有绑定通过。该行政检查失败未触及源或 Lean 证据，也不构成证明缺口。

`local-bindings.json`、`incremental-local-bindings.json` 和 `remote-bindings.json` 保存逐工件/逐声明绑定。当前 lead/root 与激活边界已核对；本审查无生产写权限。审查结束时没有本审查的在途重任务，执行和报告写入权限释放。后继由 C12 lead 继续把条件有限 telescope 在原总体上积分；真实核解析输入与 C1/C2 原根仍 OPEN。
