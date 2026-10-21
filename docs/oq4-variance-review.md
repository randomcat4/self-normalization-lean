# K→Kv 有限方差标准化独立审查 v1

STATUS: CORRECT

JUSTIFICATION: 最终版本覆盖冻结的四部分接口，数学推导完整，Lean 陈述与冻结量词、弱端点、可积条件和数值常数一致。未发现关键缺口。以下裁决仅针对有限标准化接口，不针对长时间 K/Kv。

## 对象、版本与隔离

审查日期：2026-10-21；服务器最终检查完成于 `2026-10-21T08:28:56Z`。

| 对象 | SHA256 |
|---|---|
| 本机 `drafts/oq4/frozen-variance-scaling-v1.md` | `cd5994fba29fd63eb668909e0f8f7e763db6486095d39e5fcd67f52a1d3a7250` |
| 本机 `drafts/oq4/scaling/proof.md` | `3e271b3c17622a3af85f2dd4ede0554e87d818a6d6d337932deb626482a0946c` |
| 本机 `drafts/oq4/scaling/VarianceScaling.lean` | `f7e0b71c4a8ab372310c28e5ab5ceadc371eb00c7dccf2dca1a44cdf4cf70d21` |
| 远程 `Shao/OQ4/VarianceScaling.lean` | `f7e0b71c4a8ab372310c28e5ab5ceadc371eb00c7dccf2dca1a44cdf4cf70d21` |

远程工作树：`/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。本机与远程目标哈希相同，实际检查前后远程源哈希一致。以下行号对应该最终版本。

审查者只读取所分配的冻结声明、匿名推导、最终目标源，并在服务器核对目标实际导入的公共路径定义及两个缩放引理。未读取作者会话、作者报告或源语义票；未修改任何实现、冻结前提或公共定义。唯一写入为本报告。

## 1. 路径、能量及弱边界事件

冻结第 5–6 行对应 Lean 第 23–28 行，匿名证明第 7–19 行给出正确推导。

1. `Path n` 的实际公共定义为 `Fin n → ℝ`。服务器 `#print` 得到 `prefixSum a k = ∑ i : Fin n with (i:ℕ)<k, a i`，`energy a = ∑ i : Fin n, a i^2`。所以前缀确实在长度处截断，能量确为全部坐标平方和。
2. 实际导入的 `prefixSum_smul` 对任意自然数 `n,k` 给出 `prefixSum (c • a) k = c*prefixSum a k`，`energy_smul` 给出 `energy (c • a) = c^2*energy a`；均没有 `0<n` 前提。Lean 第 29–35 行取 `c=σ⁻¹`，只作乘法交换及逆幂整理，得到冻结的全部自然数 `k` 上的前缀等式和精确能量等式。
3. 第 36–43 行逐点使用 `abs_div`、`|σ|=σ` 和正分母除法保序等价，证明 `|prefixSum a k / σ|≤h/σ ↔ |prefixSum a k|≤h`，再对同一 `k≤n` 区间双向量化。严格正的 `σ` 保证保序方向和逆元合法；没有用 crossing 事件补集，没有将 `≤` 换成 `<`，也没有删除端点 `k=0` 或 `k=n`。
4. 当 `n=0`，全部坐标和及能量都是空和零，事件中唯一允许的自然数前缀指标为 `k=0`。第 23 行没有 `0<n`，证明没有调用 `absMax`。当 `h=0` 时闭事件保留全部零前缀，等价仍成立。`h≥0` 虽在代数证明中不必使用，仍由 `_hh` 保留在公开签名中。

结论：冻结第一部分完整且忠实。

## 2. 任意测度下的精确矩标准化

冻结第 7 行对应 Lean 第 47–60 行，匿名推导第 23–35 行完整。

1. `μ : Measure Ω` 任意，除 `MeasurableSpace Ω` 外没有有限测度、概率测度、无原子或额外空间正则性类。`Y`、`Y²`、`|Y|³` 的三个 `Integrable` 假设全部显式出现于第 49–51 行；均值和二阶矩条件精确为第 52–53 行的实积分等式。
2. 第 62–75 行给出真实的点态函数恒等式：`Z=σ⁻¹Y`、`Z²=(σ⁻¹)²Y²`、`|Z|³=(σ⁻¹)³|Y|³`。最后一个恒等式正确使用了 `σ>0`，故 `|σ|=σ`，没有漏掉绝对值或错误处理缩放符号。
3. 第 77–82 行分别从三个原始可积假设经常数乘法返回三个标准化函数的可积性。这里只乘有限实常数，不积分非零常数函数，因此任意测度完全合法，未暗用测度有限性。
4. 第 83–86 行再作实积分常数乘法。均值为 `σ⁻¹*0=0`；二阶矩为 `(σ⁻¹)²*σ²=1`，约分由 `σ>0` 排除 `σ=0`；三阶绝对矩保留精确系数 `(σ⁻¹)³`，即冻结的 `σ⁻³`。三个原始及三个输出可积性均已提供，结果不依赖不可积实积分的默认取值。

结论：冻结第二部分完整且忠实。没有加入四阶矩或有界支持。

## 3. 明确常数 8M

冻结第 8 行连同第 13 行允许的显式 `M≥0`，对应 Lean 第 89–94 行；匿名证明第 39–45 行完整。

1. 由 `σ≥1/2` 得 `σ>0`，置 `t=σ⁻¹`。Lean 第 95–99 行使用 `t≥0`、`σt=1` 和 `(σ-1/2)t≥0` 推出 `t≤2`，没有在符号不明时取倒数或乘不等式。
2. 第 100–104 行依次用非负乘法得 `t²≤4`、`t³≤8`。第 105–110 行保持精确的第三绝对矩缩放恒等式，再提取常数。
3. 第 112–114 行先用 `t³≥0` 乘原第三矩上界，得到 `t³∫|Y|³≤t³M`，再用显式 `M≥0` 得 `t³M≤8M`。所以数值常数确为 `8`，没有把较小系数乘可能负的上界。
4. 原始第三矩的显式可积假设 `_hYcube` 仍保留于公开签名。这个辅助结论不需要均值和二阶矩条件，是比冻结组合接口所需更强的辅助引理；没有削弱冻结第二部分。与 `standardized_moments` 合用时，三个标准化矩可积性及精确三阶矩恒等式全部保留。端点 `σ=1/2`、`M=0` 都包含，没有严格化原假设。

结论：冻结第三部分完整且忠实。

## 4. sqrt(v) 合法性、组合接口与精确尺度

冻结第 9 行对应 Lean 第 117–167 行；匿名证明第 49–55 行完整。

1. 第 117–124 行保留 `1/2≤v≤2`。由下界得到 `v>0`，调用 `Real.sqrt_pos` 和 `Real.sq_sqrt`，故 `σ=√v>0` 且 `σ²=v`。若 `0≤σ<1/2` 则 `σ²<1/4`，与 `v≥1/2` 矛盾，故 `σ≥1/2`。因此倒数、二阶矩约分和常数 `8` 的应用全部合法。上界 `v≤2` 虽未用于这一更强的下界结论，仍在签名保留；`v=1/2` 和 `v=2` 均未排除。
2. 第 127–145 行的组合声明保留原始三项可积性、均值、二阶矩 `v`、第三矩上界、`M≥0` 及整个 `v` 区间；结论同时返回三项平方根参数性质、三个可积性、均值零、二阶矩一、精确第三矩等式和 `8M` 上界。第 148–153 行先把 `∫Y²=v` 合法改写为 `∫Y²=(√v)²`，再调用已证接口，没有把目标标准化矩作为假设。
3. 第 156–159 行对任意 `N:ℕ`、`σ>0`、`h>0` 给出两条精确等式：`N/(h/σ)²=σ²*N/h²` 及 `N/(h/σ)³=σ³*N/h³`。所有 `N` 明确转为实数，分母的 `h` 和 `σ` 均非零，没有要求 `N>0`，也没有使用渐近记号。
4. 第 162–167 行以合法的 `σ=√v` 实例化，并只把二次系数 `σ²` 替换成精确的 `v`；三次系数正确保留为 `(√v)³`。`N=0` 时两边均零。这里的尺度等式按冻结仅要求 `h>0`，与第一部分允许 `h=0` 的路径事件是各自正确的适用范围，未互相混淆。

结论：冻结第四部分完整且忠实。

## 服务器目标检查与传递公理

本审会话已独立核验的钉死环境：Lean `4.36.0-rc1`，Lake `5.0.0-src+c9afcdd`，mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。本轮所有 Lean 命令只在指定服务器执行；没有安装本机 Lean，没有更新或下载缓存，也未修改共享定义或缓存。

实际目标命令：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/VarianceScaling.lean
```

退出 `0`，无警告。随后将最终目标源、公共定义 `#print`/缩放引理 `#check`、全部七个新声明的 `#print axioms` 命令拼接后送入服务器 `taskset -c 0-3 lake env lean --stdin`，退出 `0`。公理结果：

```text
'Shao.OQ4.path_variance_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.standardized_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.standardized_third_moment_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.sqrt_variance_parameters' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.sqrt_variance_standardization' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.normalized_scale_ratios' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.sqrt_variance_scale_ratios' depends on axioms: [propext, Classical.choice, Quot.sound]
```

最终源的 `sorry|admit|axiom|unsafe|native_decide` 词项扫描为空。全部七项传递公理均在白名单内。结合前述逐项语义审查，冻结的有限方差标准化接口为 **LEAN_FULLY_CHECKED**。

## 范围与根状态

本模块未更改路径或能量定义，未构造或擅改分布、独立性、有限 iid 搬运接口，也未将其当作暗含前提。它证明的是任意给定路径和给定可积函数的有限精确缩放。

**K、Kv、完整 OQ4 均保持 OPEN；C1/C2、OQ3、OQ5/OQ6 根组也保持 OPEN。** 不能把本有限接口的通过写成从 K 到 Kv 的全部长时间概率定理已闭合。
