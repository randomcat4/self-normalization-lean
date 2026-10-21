# SpitzerKernelBounds v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 显式实际矩、唯一ν-BE与两原始SP输入下的实际S/AC、可测可积R3/R4及有限D8

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、23模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；本轮服务器完成时间2026-10-21T16:39:40.075301+00:00。在协调者通知基线更新完成后才执行本轮服务器检查，实际读取HEAD为`e6f9d300dbd991d6a55d8e4c1717dab2f35a5e2c`。未依赖作者收据、声明数量、作者审计或其他审稿票。

## 冻结与版本绑定

先只读冻结接口及匿名证明，完成CORRECT / MATH_ONLY数学票并冻结为SHA256 `64b6780541ead74daf474a2487fd53d7e3f339c99962d080c1ba725528e23976`，之后才读取最终实现。数学票保持原字节；本票另审实现的全部签名、证明体与实际执行。

| 文件 | SHA256 |
|---|---|
| `drafts/oq4/frozen-spitzer-kernel-bounds-v1.md` | `d93f79afc43c6463e3dc2b954f27e92e6e5585fef0505fe4c205e7ba86223ccd` |
| `drafts/oq4/spitzer-kernel/proof.md` | `dee48d583229544b65c63cf91faf8c5ca46dc95afaad275cdb36750ebb477936` |
| 本机`drafts/oq4/spitzer-kernel/SpitzerKernelBounds.lean`及服务器`Shao/OQ4/SpitzerKernelBounds.lean` | `e9d956ed03c634f5214c4fd85905d86fa51f6b1e5663a43ed9d3f143fcf5e014` |
| 唯一直接import `ReflectedSurvival.lean` | `b54b2300ef77375782e60a541bcffd6bed05ac4de61a776c6e0fd5e189568809` |
| 使用的`KilledBlockBounds.lean` | `cc46dc9257cc89d6e31139a60593a419d296fd5f691f10eb565d6310d9dd2408` |
| 使用的`IntervalConcentration.lean` | `491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875` |
| 使用的`KernelRecurrence.lean` | `a4a5fc67cf47c8e188cbe2e2360afa4fa1bfe0a7082bb9f30fbacd6a5ad5c940` |
| 使用的`KernelAbsorption.lean` | `b11d2f68db3581ed61abab670e72234b950df669b379e98f65172f3097f5d168` |
| 共同`Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同`Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共同`Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同`Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |

目标111行、6621字节。上述本机可读副本与对应远端源一致。服务器全部23个OQ4源与4项共同依赖检查前后SHA清单完全一致；未修改旧模块、冻结或公共定义。

## 三个公开接口的语义核对

### 1. `spitzer_kernel_probability_inputs`（第10–29行）

β在CDF误差及所有输出中都直接写为真正积分`∫ |y|^3 ∂ν`，没有自由β参数、默认积分替代或β≤M误传。签名显式给平方、立方Integrable与二阶积分1，调用既有`third_absolute_moment_ge_one`得到β≥1；该旧定理的积分单调性两侧使用真实平方/立方可积性。此概率接口比冻结完整前提更强：省去后续块界才需要的id可积、均值0及M，不增加假设。

输入是唯一ν的所有自然t≥1、实x闭CDF误差，以及ν与`reflectedLaw ν`分别全L>0、0<s<1的原始SP。既审联合反射接口内部推出ν⁻-BE，不要求本模块另给。输出β≥1、C_S/C_q非负以及已有`iidOneSidedSurvival ν β C_S`、`iidIntervalConcentration ν β C_q`，实际参数次序与定义相符。C_S=√2 exp(6+3C_BE)、C_q=1+2C_BE，未混同β和常数位置。

### 2. `spitzer_kernel_block_bounds`（第32–66行）

完整保留任意实Borel概率ν、h≥3、id/平方/绝对立方真正可积、均值0、二阶1、M≥0、实际β≤M、C_BE≥0、唯一ν-CDF及两原始SP。结论对任意|z|≤h，显式返回四项：

- 实际残差绝对值`w ↦ |cosineResidual ν (π/(2h)) h w|`的Measurable；
- 该函数对实际行`killedIterKernel ν h ⌊h²⌋₊ z`的Integrable；
- 真实`killedAction`≤E/h³；
- 真实`killedMass`≤(2C_S) principalCosine(h,z)+(2C_S M)/h。

这不是假定块界的抽象序列接口。第59–60行内部从前一公开定理取得hS、hAC及常数非负；第61–65行将其与全部矩条件传给既有`killed_block_residual_bound`，并单独以`continuous_abs.measurable.comp (principalResidual_measurable ν h)`供应可测性。第66行再使用已推出β≥1⇒β≥0及β≤M调用旧质量界。

让C_layer=12 C_q C_S M(1+M)、E=π³M/48+2π C_layer(1+2M)。`simpa only [killedResidualConstant, killedLayerConstant]`只是展开旧已实现常数，系数与依赖精确一致。h≥3、m=⌊h²⌋₊及闭域起点未变；余弦弦界只由旧定理在闭域使用，没有把全实线余弦非负当作事实。

### 3. `spitzer_kernel_finite_absorption`（第69–109行）

最终签名同样显式保留上述全部矩、中心、M/C_BE、唯一ν-CDF和两个原始SP前提，并另列π(1+M)≤h、自然N及⌊h²⌋₊≤N、|z|≤h。没有hS、hAC、O0、R3、R4、均匀归一化质量界、非增性、可和性或所需D8结论作为输入。

第86–92行smallness的let逐项为同一C_q、C_S、C_layer、E及R=exp(π²)，正文恰为

```text
((2*C_S)*R) * (E*R/h^3) * (N:ℝ) + (2*C_S*M)*R/h ≤ 1/2.
```

第94–103行输出H=2(1+(2C_S)R)R、全部自然k≤N的`0≤normalizedKernelMass≤H`及m≤k≤N的余弦增量≤(ER/h³)((k−m:ℕ):ℝ)H。自然减法在转实数前执行，含k=m、N=m；质量部分另含k=0。h≥3保证m≥1，但未给零步额外闭支持条件。

第104–109行重新在本地从唯一ν-CDF及两原始SP供应hS/hAC，再调用旧`killed_block_finite_absorption`，只展开两个旧常数。核对旧定理第151–179行，其内部由实际R3、R4供应`kernel_finite_absorption`：A=2C_S、B=2C_S M、残差E，归一化系数AR、ER/h³、BR/h及H与本签名精确相同。因此是直接复用已审非循环有限吸收，未将R3/R4偷放回最终前提。

**自然端点与概率范围。** 三个接口均使用实际无条件Π_t及已实现核对象；ν无额外对称、密度、无原子、有界支持或第四矩条件。S/AC仍保留原子、闭端点、t=1、d=0及全零路径。实际二阶1与β≤M使M=0前提不可同时满足，不需隐式添加M>0或除M步骤。真实可积性被假设或作为R3结论返回，未利用实积分对不可积函数的默认值。

## 独立服务器执行及全新常量

所有Lean只在指定服务器执行：通过`tools/server.py`，先source固定activate.sh再cd指定lead-oq4 worktree；固定Lean/mathlib环境、共享缓存只读；每个命令`taskset -c 0-3`，单进程顺序运行，无`-o`、无目标olean发射、无缓存写入。本次broker正常，无需回退或重放不确定操作。

```text
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 7
ACCEPTED_23_MODULE_COEXIST_EXIT=0
ALL_23_SOURCE_AND_4_COMMON_HASHES_UNCHANGED=True
```

目标检查是`lake env lean Shao/OQ4/SpitzerKernelBounds.lean`。另将服务器最终完整源码直接接审计附录送`lake env lean --stdin`，`#print`全部三个公开定理、现有两个谓词及旧常数，`#check`所用矩、反射、可测、R3/R4与吸收API。附录随后遍历全部`env.constants.toList`，选取每一个`env.getModuleIdxFor? declName`为`none`的实际新常量，对每项执行`Lean.collectAxioms`并拒绝标准三公理之外的项，没有namespace、root或声明名过滤。

实际枚举七项（完整名称）：

```text
Shao.OQ4.spitzer_kernel_probability_inputs
Shao.OQ4.spitzer_kernel_block_bounds
Shao.OQ4.spitzer_kernel_finite_absorption
Shao.OQ4.killedResidualConstant.eq_1
Shao.OQ4.killedLayerConstant.eq_1
Shao.OQ4.normalizedKernelCosine.congr_simp
Shao.OQ4.normalizedKernelMass.congr_simp
```

三显式定理之外，四项均在导入名称下生成，已经全部包含在本次独立审计。七项传递公理全部为`[propext, Classical.choice, Quot.sound]`，无sorryAx。数量来自实际环境遍历，不以作者声称的数量替代。

**实际共存。** 同一Lean输入import既有22模块与新模块，共23：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds（均`Shao.OQ4.`前缀）。同时实际检查两个closedUpper可测性定理可用、三新定理完整签名及三者传递公理，均成功；没有用standalone目标替代共存检查。

本机和服务器目标禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三个独立日志均0 warning/0 error。完整原始日志仅留服务器`repro_outputs/oq4-spitzer-kernel/independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 33860 | `34e4e65f204760cb570803a9bec15fc7ffd63fb70a196971fb764839ab3def39` |
| `coexist-23.log` | 6345 | `f6f63a58f69879c2aa667f29f08614b68e72f87dbf37cbd29629d2eed784a2e7` |

## 裁决

未发现数学或形式关键缺口。最终认证仅为显式真实矩、BE、ν及ν⁻各原始SP等冻结前提下的有限供应链：实际S/AC、实际可测可积R3/R4及显示smallness范围内的有限D8。没有新概率输入、常数漂移、自然差改变或完整根的扩大断言。

**BE、两个原始SP、无条件S/AC/O0、Brownian B1、长期K/Kv、4/π、能量E1–E6、完整OQ4及其他全部完整根仍OPEN。**
