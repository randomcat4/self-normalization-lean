# TruncatedEnergy N0 v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 真实闭截断能量权重、有限矩支付、归一化上下界及精确一阶误差N0

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、24模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；服务器检查完成于2026-10-21T17:03:46.449683+00:00。实际检查HEAD为`9fd37d07bbda4830edf3bf7eba544c7de4dc04e8`。未读作者收据、ledger、summary、译者票或其他审稿票；作者成功信息不替代本轮独立检查。

## 冻结数学票与最终版本

先只读冻结接口及匿名证明，冻结CORRECT / MATH_ONLY数学票，SHA256为`ff20277210bf8cadb68e3a2346fff1baf788c10b45bfe864bb7ed6552af43a77`。收到最终源通知后才读取实现；数学票及原匿名证明均保持原字节。

| 文件 | 审查时SHA256 |
|---|---|
| `drafts/oq4/frozen-truncated-energy-v1.md` | `1f4cd0e5f1c21989763ee5bee78ebfd571488e55f8bee8723c3328b746cec8e8` |
| `drafts/oq4/energy/proof.md` | `afe5f5c496158d7903548d3d49a01a6bcca5799c3c541fe3937e5f3a68bd7dce` |
| 本机`drafts/oq4/energy/TruncatedEnergy.lean`及服务器`Shao/OQ4/TruncatedEnergy.lean` | `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` |
| 共同`Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同`Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共同`Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同`Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |

最终源411行、21487字节，仅直接import固定Mathlib模块，无新增Shao依赖。实际Lean版本4.36.0-rc1、commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`；沿用项目固定mathlib807d3836环境及共享只读缓存。24个OQ4源和4项共同依赖均在服务器验证前后SHA完全一致，完整清单留服务器日志。

## 完整声明与自然语义核对

### 对象、任意参数可测性与真实可积性

第17–24行三个对象分别是闭截断`if |x|≤2*h then exp(s*x²/h²) else 0`、实际实积分Z以及精确常数`1/8+T/2+exp(4*T)*T²`。未换成抽象权重或参数化normalizer。

第26–32行对任意实h,s证明Borel可测及逐点非负；没有h>0或分布前提。h=0的总除法也在此范围内。第34行零点权重只需h≥0；第37–42行对任意实h和有限ν证明s=0时Z恰为闭截断质量，而非1，闭端点原子包含在其中。

第44–57行在h>0、T≥0、|s|≤T、|x|≤2h上证明−4T≤sx²/h²≤4T。第59、66行分别给全局上界和截断内下界指标。第74–80行对有限ν，通过实际可测性、非负性与全局常数exp(4T)的`Integrable.of_bound`证明权重真可积。该辅助范围h>0强于冻结h≥1需求；未增加中心、id可积、第四矩或指数矩前提。

### 三阶矩支付与全部截断积分

第83–111行四个点态不等式的严格尾始终是`2*h<|x|`，第四项闭截断始终是`|x|≤2*h`；精确系数依次为1/(8h³)、1/(4h²)、1/(2h)、2h。分母正性均由h>0供应，等号端点没有进入尾。

第114–169行的公开结论同时返回尾|x|、尾x²、闭截断x⁴三函数的Integrable及四项积分/实质量界。证明先构造可测严格尾和可积指标，再各用可积|x|³的相应正标量倍作支配，随后才使用`integral_mono`及真实指标质量公式。全局x⁴可积并非前提；尾绝对值的可积性也没有要求全局id作为前提。实际β在所有输出中直接是`∫ |x|³ ∂ν`。

### 3/4有限正下界与上界

第172–202行只用概率ν、h≥1、平方Integrable及∫x²=1，先积分严格尾指标≤x²/(4h²)，得尾质量≤1/(4h²)≤1/4，再用可测补集精确等于闭截断，证明质量≥3/4。没有β小性或中心前提。

第204–231行先取得权重真实可积性，又证明exp(−4T)的闭截断指标可积。两次可积积分单调性给

```text
(3/4)*exp(-4*T) ≤ energyNormalizer ν h s ≤ exp(4*T).
```

下界严格正性由exp正与3/4>0直接推出；Z本身是有限实数，且已证明对应权重Integrable。Z>0不是输入，亦没有通过默认实积分0制造normalizer。

### 等价导数证明的精确Taylor系数

第234–276行公开定理只有实T,u、T≥0、|u|≤4T，结论精确为`|exp u−1−u|≤(exp(4*T)/2)*u²`。其证明与匿名Lagrange余项论证等价，逐步核对如下：

1. `Real.add_one_le_exp`给exp u−1−u≥0，因而去绝对值合法。
2. 记E=exp(4T)，g(v)=Ev−exp v+1、F(v)=(E/2)v²−(exp v−1−v)。实际导数计算为g′=E−exp v、F′=g，均由全局可微指数与多项式计算，无额外假设。
3. 在[-4T,4T]有v≤4T，故g′≥0，g在该闭区间单调；g(0)=0。
4. 在[0,4T]，g≥0，所以F单调，F(u)≥F(0)=0；在[-4T,0]，g≤0，所以F反单调，仍有F(u)≥F(0)=0。T=0时区间退化，端点0仍有效。
5. F(u)≥0正是精确E/2上包络，不是E或更大的系数。最终定理对负u、正u都成立，且没有分布、指数矩或支撑假设。

这里的导数单调性条件（凸区间、连续、内点可微）均由实际全局光滑函数供应。不是将Taylor结论或某未证余项当作假设。

### 截断余项与一阶展开

第278–283行`energyRemainder`是实际闭截断指数余项并独立证明可测。第285–297行将上项精确Taylor界代入u=sx²/h²，给

```text
|r(x)| ≤ (exp(4*T)*s²/(2*h⁴)) * (if |x|≤2*h then x⁴ else 0).
```

第300–331行先用已经真可积的截断x⁴及此支配证明r Integrable，随后才估计积分绝对值。Taylor的1/2与截断四阶支付2h精确抵消，得exp(4T)s²β/h³，再由|s|≤T及β≥0得到exp(4T)T²β/h³。无需全局第四矩，也未使用不可积积分的默认值。

第337–409行主展开签名显式且只给概率ν、T≥0、h≥1、|s|≤T、平方/立方Integrable及单位二阶矩；没有均值或id可积、β≥1额外条件。证明分别取得w、尾平方、r和尾指标的Integrable，再合法使用`integral_sub`/`integral_add`，逐点分B与严格尾证明精确恒等式

```text
Z−1−s/h² = −ν.real D − (s/h²)*∫1_D*x² + ∫r.
```

尾平方积分非负，三角不等式与四项支付给误差三项β/(8h³)、Tβ/(2h³)、exp(4T)T²β/h³；最后`field_simp`只合并冻结常数，未放大或变更依赖。故主结论恰为冻结`|Z−1−s/h²|≤C_Z(T)*β/h³`。

T=0、s=0、h=1、零点原子及±2h原子均在签名范围内。特别s=T=0时余项零、Z为截断质量，一阶误差只支付尾质量；没有错误地令其等于1。任意非中心、不对称、无界支撑ν均保留。

## 实际服务器验证与动态全部新常量

通过`tools/server.py`使用指定服务器，先source固定activate.sh再cd worktree；三个正式Lean验证命令均`taskset -c 0-3`、单进程顺序运行，无`-o`，未发射目标olean或写缓存。本次broker正常，无重放或旁路回退。仅写独立审查日志与本报告，没有改动作者源、匿名证明、冻结、公共源或Git。

```text
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 50
ACCEPTED_24_MODULE_COEXIST_EXIT=0
ALL_24_SOURCE_AND_4_COMMON_HASHES_UNCHANGED=True
```

目标是`lake env lean Shao/OQ4/TruncatedEnergy.lean`，无-o实际编译成功。完整源审计将最终服务器源直接接附录送`lake env lean --stdin`，打印4个定义、检查18个显式定理全部签名，随后遍历`env.constants.toList`。对每一个`env.getModuleIdxFor? declName`为`none`的实际新常量执行`Lean.collectAxioms`；无namespace、root或作者声明清单过滤，任何非`propext`、`Classical.choice`、`Quot.sound`公理会报错。

实际50项为4个定义、18个显式定理与28个生成helper，全部传递公理为标准三项的子集。没有sorryAx；部分helper只有`[propext]`，其他项为白名单三项。实际显式项如下（均`Shao.OQ4.`前缀）：

```text
energyWeight
energyNormalizer
energyNormalizerErrorConstant
energyRemainder
energyWeight_measurable
energyWeight_nonneg
energyWeight_at_zero
energyNormalizer_at_zero
energy_argument_bounds
energyWeight_le
energyWeight_lower_indicator
energyWeight_integrable
energy_third_moment_pointwise
energy_third_moment_payments
energy_cutoff_mass_lower
energyNormalizer_bounds
energy_exp_remainder_bound
energyRemainder_measurable
energyRemainder_pointwise
energyRemainder_integral_bound
energyNormalizerErrorConstant_nonneg
energyNormalizer_expansion
```

全部28个helper亦实际逐项审计，没有只审公开定理；可精确归组为：

- `energyWeight.eq_1`、`energyNormalizer.eq_1`、`energyRemainder.eq_1`（3项）；
- `energyWeight._proof_1`、`energyNormalizerErrorConstant._proof_1`、`energyNormalizerErrorConstant._proof_2`（3项）；
- `energyRemainder_pointwise._simp_1_2`至`._simp_1_9`（连续8项）；
- `energyRemainder_integral_bound._simp_1_1`至`._simp_1_7`（连续7项）；
- `energyNormalizer_expansion._simp_1_4`至`._simp_1_10`（连续7项）。

本次实际新常量均在Shao.OQ4名称下，但这是无筛选遍历的结果；即使在导入名称下生成新helper，同一条件也会覆盖它们。

**真实24模块共存：** 同一输入import既有23模块及TruncatedEnergy，均为`Shao.OQ4.`前缀：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds、TruncatedEnergy。还实际检查两closedUpper可测性定理与N0主要结论可用；共存不是standalone检查的推测。

本机和服务器目标禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三项验证日志均0 warning/0 error。完整原始日志仅保留服务器`repro_outputs/oq4-energy/n0-independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 18237 | `cc01abf3ae8b45d6b68a5305e14fc553f4405246d430a5702ff439babb95108b` |
| `coexist-24.log` | 2574 | `ce5dfbb9005e8e8841837d6c6e96aa9235397517261b5aa82cbf3f87203435a6` |

## 最终裁决与范围

没有发现关键数学或形式缺口。冻结N0的全部结论、精确常数、真可积性与端点均得到覆盖；导数单调性版本保留匿名Taylor论证的精确系数且无前提漂移。

**只认证N0。归一化倾斜概率测度、倾斜均值与归一化矩、log Z精度、完整E1、E2精确再中心化、E3路径密度、E4、BE/SP、K/Kv、能量分母、完整OQ4及其他全部完整根仍OPEN。**
