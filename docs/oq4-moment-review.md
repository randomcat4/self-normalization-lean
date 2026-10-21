# R6 积分接口独立证明审查 v1

STATUS: CORRECT

JUSTIFICATION: 最终版本完整证明冻结接口的逐项可积与非负、任意有限截断上界、实级数可求和和全和上界。下列语义检查和服务器机械检查相互独立；源语义盲译者的结论未作为证明正确性依据。前两个有限模块未重审。

## 审查对象和精确版本

审查日期：2026-10-21；最终服务器目标及公理检查结束于 `2026-10-21T08:18:45Z`。

| 对象 | SHA256 |
|---|---|
| 本机 `drafts/oq4/frozen-overshoot-integral-v1.md` | `17edc8edcd8881426fa2f2cec472292b403a7527800706f5e047b17ec4be4463` |
| 本机 `drafts/oq4/overshoot-moment-proof.md` | `8a0aecae7161527dc1db95781fca77da2388c776660510ca27014fb4bf9a0d2b` |
| 最终本机 `drafts/oq4/OvershootMoment.lean` | `a785a61be3f7c5230f66e053c0a827c9bde7674fc27fa129e6306033c92aee10` |
| 最终远程 `Shao/OQ4/OvershootMoment.lean` | `a785a61be3f7c5230f66e053c0a827c9bde7674fc27fa129e6306033c92aee10` |

远程工作树为 `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4`。本机和实际检查的远程最终源哈希一致，远程检查前后哈希一致。以下行号均指上述最终版本。

审查者只读取所分配的冻结声明、匿名证明、目标源及本接口所用库定理的服务器签名；没有读取作者报告或其他审稿票，没有修改实现、前提或服务器模块。唯一写入工件为本报告。

## 自然语言与 Lean 陈述

冻结文件第 5–12 行对应 Lean 第 21–22、25–27、31–33、36–40、53–56、61–65 行。

- 任意 `Ω`、`MeasurableSpace Ω`、`μ : Measure Ω` 和 `[IsFiniteMeasure μ]` 对应任意有限测度空间，没有概率归一化假设。
- `U : Ω → ℝ`，`Integrable U μ` 和 `Integrable (fun ω => U ω ^ 3) μ` 正是冻结的一阶及三阶可积条件。没有另加全局可测性、有界性、四阶矩、无原子性或尾部连续性。
- `hU0 : ∀ᵐ ω ∂μ, 0 ≤ U ω` 是几乎处处非负，没有改为处处非负。
- 每个 `b_j` 均为冻结的实积分；有限截断采用 `Finset.range L`，对任意自然数 `L`；全和采用自然数指标的实数 `tsum`，同时另证 `Summable`，没有以不可求和级数的默认取值代替总和。
- 第 29 行的局部 `omit [IsFiniteMeasure μ] in` 仅使第 31–33 行的积分非负引理适用于更一般测度。其余冻结接口保留有限测度输入；这个辅助引理更强没有缩小冻结命题的量词。

## 完整可检查理由

1. **逐项可积。** 匿名证明第 3 行、Lean 第 25–27 行先用有限测度保证常值实函数 `j` 可积，然后由 `hU` 得到 `U-j` 可积。库引理 `Integrable.pos_part` 的结论恰为 `Integrable (fun ω => max (U ω-j) 0) μ`；再乘有限实常数 `j+1` 得到该格项可积。这不要求 `U` 处处非负，也不要求三阶矩。有限测度的使用位置清楚，没有在无限测度情形擅自积分常数。

2. **逐项积分非负。** Lean 第 31–33 行使用已认证的 `overshootCell_nonneg`，因为 `j+1≥0` 且正部非负，对全部实值 `U ω` 逐点成立，所以 `b_j≥0`。这个辅助引理在没有可积性时仍可能使用 Bochner 积分的默认定义；主接口另由第 25–27 行确证了每个格项可积，因此主结果并不依赖不可积函数的默认零积分。

3. **有限和与积分交换有全部条件。** 匿名证明第 5 行、Lean 第 41 行调用 `integral_finsetSum`，其要求是有限指标集中的每一项可积，已逐个由 `integrable_overshootCell hU j` 提供。第 46 行也明确供应了有限和函数本身的可积性，没有从形式上的线性符号跳过可积条件。

4. **几乎处处假设足够。** Lean 第 45–48 行使用 `integral_mono_ae`。左侧有限和已可积，右侧 `4*(U+U^3)` 由 `hU`、`hU3` 的加法和常数乘法可积。第 48 行只在 `hU0` 的满测集上调用 F-R 的逐点有限不等式；没有在零测例外集要求 `U≥0`。因此代表元可在零集上为负，论证仍成立。这里的几乎处处比较正是积分单调性所需的假设。

5. **右端线性化与有限性。** 第 49–50 行在 `hU` 和 `hU3` 下使用积分加法及常数乘法，得到精确的 `4*(∫U+∫U^3)`。两个积分均为真实可积函数的有限实积分。由于 `U≥0` 几乎处处，`U^3≥0` 几乎处处，右端亦非负；即使不单独使用这点，`L=0` 的有限截断结论已经给出右端非负。没有暗中引入更高阶矩。

6. **实级数可求和已独立证明。** 匿名证明第 7 行、Lean 第 53–58 行使用 `summable_of_sum_range_le`，已在服务器核对其精确签名：对实序列，若每项非负且所有 `range L` 部分和受同一实常数控制，则该序列 `Summable`。这里两项条件分别由第 31–33 行及第 36–50 行提供。没有假设可求和性，也没有循环引用全和上界。

7. **全和上界有效。** 第 61–67 行使用 `Real.tsum_le_of_sum_range_le`，其全部条件同样是逐项非负及全部初始有限和的统一上界。服务器已核对签名；输入正好满足。结合前一条单独给出的 `Summable`，此 `tsum` 表示通常意义的实数级数总和。证明没有使用未确证的 `∫∑'=∑'∫` 等式，也不需要先作无限积分交换。

8. **边界和源作用域。** `μ=0`、`U=0`、原子、整数值、无界 `U` 和 `L=0` 均不使上述任一步失效：没有除以测度、`U` 或积分，没有点态上界或分布正则性要求。接口明确保留独立的一阶可积输入，与冻结文件一致；不能据此声称原概率根新增了独立的一阶矩限制。本结果只完成 R6 的期望支付，不证明 O0、R2、R3、K/Kv 或 OQ4。

未发现最终版本的数学或语义关键缺口。

## 实际服务器核验与传递公理

本审会话核验的钉死工具链为 Lean `4.36.0-rc1`、Lake `5.0.0-src+c9afcdd`，mathlib revision `807d3836b165983210ee2ecf3cd28f239436949c`。所有 Lean 命令仅在服务器执行，先激活环境，再进入上述工作树；未安装本机 Lean，未更新、下载或写入共享包缓存。

最终版本实际目标检查：

```text
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/OvershootMoment.lean
```

目标检查退出 `0`，无警告。随后把最终目标源与全部五个新声明的 `#print axioms` 命令拼接，经服务器 `taskset -c 0-3 lake env lean --stdin` 重新检查，退出 `0`。全部传递公理输出：

```text
'Shao.OQ4.integrable_overshootCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.integral_overshootCell_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.sum_integral_overshootCell_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.summable_integral_overshootCell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shao.OQ4.tsum_integral_overshootCell_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

最终源中 `sorry|admit|axiom|unsafe|native_decide` 词项扫描为空。另一次干净导入的服务器 `#check` 核对了导入 F-R 的实际类型，以及 `Integrable.pos_part`、`integrable_const`、`integral_finsetSum`、`integral_mono_ae` 和两项实级数判据的全部条件，退出 `0`。

因此仅就冻结的 R6 积分接口，最终状态为 **LEAN_FULLY_CHECKED**。

## 已解决的机械缺口记录

本轮首次读取的代码版本 SHA256 为 `1cf8f7740048246c128e3040bcf830613e06d135edafe49132988e9b55d87266`。该版本旧第 29 行文档注释后接旧第 30 行 `omit`，独立目标检查实际退出 `1`：

```text
Shao/OQ4/OvershootMoment.lean:29:80: error: unexpected token 'omit'; expected 'lemma'
```

该缺口已报告给协调者，审查者没有修改代码。协调者提供修订后，审查者重新读取并核对本机、远程最终源：仅将 `omit` 移到该文档注释前，数学证明和定理内容一致。随后进行了上面的最终目标检查与全部公理审计；最终版本已解决这项语法缺口。本报告的 CORRECT 裁决仅适用于表中 `a785...ee10` 版本，不适用于首次失败版本。

## 根状态

**全部根组保持 OPEN：C1/C2、OQ3、OQ4（含 K/Kv）、OQ5/OQ6。** 本接口通过不自动关闭概率占据或 killed 核的其余依赖。
