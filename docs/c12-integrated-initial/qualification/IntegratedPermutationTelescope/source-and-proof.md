# 均匀置换停止补偿：作者交接

状态：冻结接口的候选证明完成；服务器内核与全所属递归公理审计通过，等待 lead 指派的新鲜独立完整审查。作者没有给自己的结果作最终验收，没有 commit、push、PR 或合并。

## 精确绑定

- 生产模块：`Shao/C1/IntegratedPermutationTelescope.lean`。
- 冻结文件：`../frozen.lean.txt`，SHA256 `c87df837af191e8790e7d9b02146b41301b48d53f777f7956132195f1a898a1e`。
- 最终源 SHA256 `db9490e5e0b5ccff6be55ac22705a7fd18dd69d20f9a6a1e9f652879daadbb17`；8634 字节，UTF-8 无 BOM、仅 LF。
- 最终对象 SHA256 `2fa2a407f7395225eedf6cc58ed68765071e0172373343791d97f24f61b65522`。
- 源、完整实际类型/定义值、冻结比较、全所属图及精确服务器收据均在本目录；完整检查日志留在服务器 `outputs/c12-integrated-permutation-telescope-v71/`。
- 所有 3 个完整定理头、2 个透明定义的头与值逐字保留；只加入证明，没有新增顶层 helper、instance 或 private 声明。

## 原源与当前消除的义务

完整阅读原 `main.tex` 885–956（`cn:telescope`）及 `supplement.tex` 4192–4252 的核与导数语境。这个模块把已经合格的未归一化有限置换求和补偿式提升为真正概率律下的迭代期望，并显式证明两边对原总体概率 `P` 的可积性。直接下游是实际完成核的受保护停止补偿实例。

`uniformPermutationLaw n` 精确为 `card(Perm(Fin n))⁻¹ • Measure.count`。它独立于原样本 `a`；在有限可测单点空间，其真实 Bochner 积分等于普通实数归一化有限平均，且总质量为 1。`n=0` 时置换仍非空，概率定理无零除漏洞。

`integrated_stopped_compensation` 使用任意同一个原总体概率 `P`。`ν a σ ≤ n`、每个固定置换下的 `ν` 可测、停止事件与 `FY` 的真实标签前缀可观测性、真实剩余平方和的 `H>0` 截断、`V∈[0,1]`、各固定秩的可测性、显式第一导数标量界、可测且绝对值≤1的原样本掩码以及其置换不变条件全部保留。没有把余项可积性或所要证明的平均恒等式作为输入。

## 完整证明路线

1. `uniformPermutationLaw_isProbability` 用 `Measure.count_univ = ENat.card`、有限置换群基数非零及有限 `ENNReal` 倒数消去，直接构造 `IsProbabilityMeasure`；不注册新全局实例。
2. `integral_uniformPermutationLaw` 用已缓存的 `integral_smul_measure` 与 `integral_count`，得到真实积分的精确有限平均。
3. 固定 `σ`，把 `V a σ (ν a σ)` 写成 `k∈range(n+1)` 上 `if ν a σ=k then V a σ k else 0` 的有限和。由 `hνmeas`、`hVmeas` 得可测性。`V∈[0,1]` 使停止差值绝对值≤1，再用 `m` 的界获得每个左侧原样本截面的可积性。
4. 对每个固定 `σ,r`，直接调用已合格 `guarded_remainder_integrable`，完整传入 `hFYmeas`、两个 `hVmeas`、两个 `[0,1]` 界、真实 `hfy`。随后乘以可测的 `r<ν` 指示，得到每个 `stoppedGuardedRemainder` 对 `P` 的可积性；有限秩和、掩码、有限置换和及归一化常数保持可积。这独立证明右侧可积性，不靠积分的不可积默认值，也不从目标恒等式反推可积性。
5. 固定每个原样本 `a`，完整应用旧 `finite_stopped_compensation n a (ν a)`，以 `W=FY a` 和相同的真实剩余 `d,T`。当 `r<ν`，`hcutoff` 让 `guardedRemainder` 的 `H≤T` 守卫为真；其乘法次序仅用环恒等式整理。在非停止秩两种表达都为零。
6. 用归一化有限平均公式把逐样本未掩码有限和身份乘以该固定原样本的 `m a`，得到逐样本两个置换积分相等；最后用 `integral_congr_ae` 对同一个 `P` 积分。

`hminvariant` 保留在冻结实际类型里，当前代数未显式调用它：`m` 是完整 rawsample 的函数，条件在 `a` 后已经对所有 reveal 置换固定。这个证明实际允许更广的 rawsample 掩码，但接口没有据此删弱源条件，也没有允许 reveal-dependent 掩码。

## 边界及未消除的范围

- 停止时刻只指条件于完整原样本后的独立均匀标签 reveal；没有宣称原自然 iid filtration 下为停时。
- 真实标签值、前缀、剩余和、剩余平方和、下一步标签均由旧定义原样消费；没有用确定性方差替代真实 `T`。
- `ν=0`、`n=0` 由有限和/旧停止恒等式覆盖。`r<ν` 时 `T≥H>0`；不活动秩为零。
- 当前 `V`/`FY` 仍为满足显式输入的泛型过程。实际 Brownian 完成核、吸收/跨墙 kill、外部终点和可达 `T=0` 约定尚未在此实例化；源解析第一导数界仍是输入 `hfy`。源中这些机制及实际核适配仍 OPEN。
- 原文关于重排 iid 律的重新分布论证不是本模块的结论；此处仅给同一 `P` 与独立均匀 reveal 的迭代期望式。
- C1/C2 原根及所有未完成依赖保持 OPEN。

## 检查与审查覆盖

服务器固定 Lean `v4.36.0-rc1` / mathlib `807d3836b165983210ee2ecf3cd28f239436949c`，使用只读 shared-v34 包视图。所有实际 Lean 命令持 `c12-heavy.lock`、CPU14–17、`-M8192 -j4`，无旧 producer 重编、cache 写入或本地 Lean。

前两次失败分别只涉及 ENNReal 倒数消去/指示集合的隐式参数，以及点自由指示函数到 lambda 的归约匹配；失败源字节和对应服务器日志均保留。第三次内核检查成功后没有重跑、没有再改源。只剩旧库可变目录提示、一个弃用拼写提示及冻结未显式用到的 `hminvariant` 提示，均未为消除提示而改源重编。

审计复用既有 `OwnedAudit.lean`，仅改 import、target、公有清单及输出路径；`env.getModuleIdxFor?` 的 actual owner 选择不按 namespace 筛掉 private/generated。结果 8 所属常量 = 6 含生成定理 + 2 定义，公开源定理 3。每一项均 `collectAxioms` 递归检查，仅出现 `propext`、`Classical.choice`、`Quot.sound`。全部 8 个完整实际类型与全部 2 个非定理值已抽取且完整读取；源中的所有证明均完整可读。按当前 TEAM 边界未打印巨大的 `thmInfo` 生成证明项。

既有 `StoppedPermutationTelescope`、`PermutationCompensation`、`PermutationEnergyEnvelope`、`GuardedPermutationIntegrability` 的源及对象哈希与 qualified 版本逐项一致；未重复其成功编译或独立证明审查。完整消费的类型/定义和 source-to-statement 关系由本交接说明与生产源提供，最终正确性由新的独立审查裁决。

下一具体依赖：lead 对本精确源进行一次 fresh `gpt-6.1-sol/xhigh` 的完整独立 source-to-statement/proof/type/value 审查；通过后原样复用本服务器成功对象及公理收据。之后仍需实际源完成核/kill/终端约定与 `FY` 导数界实例，不能以此泛型积分身份关闭原根。
