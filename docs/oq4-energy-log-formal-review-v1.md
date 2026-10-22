# EnergyLogNormalizer N2 v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 真实N0归一化因子的有限log误差，T-only系数及显式共同矩类高度

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、26模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；服务器完成于2026-10-21T17:24:34.607054+00:00。实际检查HEAD为`28b459e8d6e30cc06c8402027c1a8ee18a08c5a7`。未读作者receipt、summary、ledger、译者票或其他审查；作者检查信息不作为独立认证替代。

## 冻结与最终版本

先只读冻结接口及匿名证明，冻结CORRECT / MATH_ONLY数学票为SHA256 `1dda233830aef08cfc0a0628b3562632f91d8408630c6ad290839f59a2f0ad7d`。最终源通知后才读取实现；数学票与匿名证明保持原字节。

| 文件 | SHA256 |
|---|---|
| `drafts/oq4/frozen-energy-log-normalizer-v1.md` | `74f05213e8332f7e7972fcfb8613fa51310e8365f1d24d41d2acaacde44bf399` |
| `drafts/oq4/energy-log/proof.md` | `10515d73e42d76df5788b85e45f1a914ce8bb0c4d1a2e569a44113a82c848cff` |
| 本机`drafts/oq4/energy-log/EnergyLogNormalizer.lean`及服务器`Shao/OQ4/EnergyLogNormalizer.lean` | `6bbf4093ed296e5fa40cc680f77670c5a3889d95a3679a1cfaf011a84efa6906` |
| 直接Shao依赖`TruncatedEnergy.lean` | `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` |
| 直接Shao依赖`IntervalConcentration.lean` | `491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875` |
| 共同`Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同`Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共同`Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同`Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |

最终源154行、8357字节，另import固定Mathlib Log.Basic；不import N1 EnergyTiltedLaw。表中本机目标及直接Shao依赖与服务器一致。服务器所有26个OQ4源和4项共同依赖前后SHA清单完全相同，完整清单留原始日志。未改旧源、公共定义、冻结、Git或缓存。

## 完整签名与证明核对

1. **精确阈值和T-only常数（第11–28行）。** `energyLogThreshold M T`恰为2(1+M+T+C_Z(T)M)；`energyLogErrorConstant T`恰为C_Z(T)+4T²+4C_Z(T)²，没有M、ν、β、h或s隐藏参数。非负性由M,T≥0及N0 C_Z非负推出；阈值界明确供应H≥2、M≤H和2(T+C_ZM)≤H。

2. **实际N0权重/归一化邻近1（第31–77行）。** 签名仅给任意实Borel概率ν、M,T≥0、h≥H、|s|≤T、平方/绝对立方真可积、二阶积分1及实际β≤M。结论同时返回真实权重Integrable、h≥2、β≤M≤h、精确原始误差界、|Z−1|≤1/2、Z∈[1/2,3/2]及Z>0。这里Z始终是实际`energyNormalizer ν h s`，没有抽象化或把所需误差作为前提。

   证明先由H取得h>0、h≥1和2(T+C_ZM)≤h，再实际调用N0 `energyNormalizer_expansion`，得到|Z−1|≤T/h²+C_Zβ/h³。T,C_Z,M非负和h≥1使该右侧≤(T+C_ZM)/h≤1/2。权重真可积单独由N0 `energyWeight_integrable`供应；因此是真实有限积分的控制。β≥1不是此处邻近1所需的额外条件，实际log误差中将从矩内部推出。

3. **双侧log界，无Z≤1限制（第80–92行）。** 纯实定理唯一域前提z≥1/2。内部得z>0，实际使用`Real.log_le_sub_one_of_pos`及`Real.one_sub_inv_le_log_of_pos`。上式给log z−(z−1)≤0，所以绝对值恰是(z−1)−log z；下式再给≤(z−1)²/z，最后用z≥1/2得≤2(z−1)²。分式恒等式在z>0后使用，没有额外z≤1，也不依赖total log的零/负值约定。z−1可以正、负或零，均被覆盖；校正项本身非正的符号也已正确处理。

4. **两个平方支付的精确4（第94–124行）。** 这个纯实辅助引理输入T,C≥0、β≥1、h≥1、β≤h及|v|≤T/h²+Cβ/h³。平方与2ab≤a²+b²给2v²≤4(T/h²)²+4(Cβ/h³)²，两个4完整保留。βh≥1给1/h⁴≤β/h³；又由β≤h≤h³得0≤β/h³≤1，平方不增，得到β²/h⁶≤β/h³。故结论恰为(4T²+4C²)β/h³，未引入M依赖。

   辅助纯实引理的β≥1、β≤h是明确标量条件；最终实际定理并没有把它们额外要求给分布，而是在内部供应。

5. **实际log-normalizer最终定理（第127–152行）。** 完整签名与冻结一致：实际概率ν、M,T≥0、显式H≤h、|s|≤T、平方/立方Integrable、二阶1、原ν实际β≤M。没有中心、id可积、β≥1、Z正性、Z误差或所需log结论作为附加前提。

   第134–140行调用真实邻近1定理，并通过`third_absolute_moment_ge_one ν hSq hCube hsecond`内部得到实际β≥1；β≤h由β≤M≤h供应。将纯实平方引理代入C=C_Z、v=实际Z−1后，最终分解log Z−s/h²=[log Z−(Z−1)]+[Z−1−s/h²]。对第一项用已证Z≥1/2的log引理，对第二项再次调用实际N0展开；精确合并为[C_Z+4T²+4C_Z²]β/h³。没有以纯实辅助结论替代实际归一化定理。

6. **端点、分布与依赖范围。** N0的闭截断包含±2h原子，严格尾及零点原子未改变。T=0、s=0与两种s符号都在范围内；s=0时实际Z可为小于1的闭截断质量，证明并未令log Z=0。没有对原law增加中心、第四/指数矩、密度、对称性或有界支撑。M只限制共同高度；M<1时类可能因实际β≥1为空，不需新增M≥1或M>0。N1不在证明依赖中。

## 独立服务器执行与全部新常量

通过正常`tools/server.py` broker，先source固定activate.sh再cd指定worktree。三个正式验证均指定服务器`taskset -c 0-3`、单进程顺序运行、无`-o`，不发射目标olean、不重编旧目标、不写共享缓存；无不确定操作重放或旁路回退。

```text
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 17
ACCEPTED_26_MODULE_COEXIST_EXIT=0
ALL_26_SOURCE_AND_4_COMMON_HASHES_UNCHANGED=True
```

无-o目标实际运行`lake env lean Shao/OQ4/EnergyLogNormalizer.lean`。完整源审计将服务器最终源直接接附录送`lake env lean --stdin`，打印两个定义，核对六个显式定理全部签名及实际使用的N0、矩与log API。随后遍历`env.constants.toList`，对每一个`env.getModuleIdxFor? declName`为`none`的新常量调用`Lean.collectAxioms`并拒绝非标准三公理。没有namespace、root、声明名或作者清单过滤。

实际17项为以下8个显式声明及9个helper（均`Shao.OQ4.`前缀）：

```text
energyLogThreshold
energyLogErrorConstant
energyLog_constants_nonneg
energyLog_threshold_bounds
energyLog_normalizer_close
energyLog_quadratic_bound
energyLog_square_payment
energyLog_normalizer_error
energyLogThreshold._proof_1
energyLogErrorConstant._proof_1
energyLog_quadratic_bound._simp_1_1
energyLog_quadratic_bound._simp_1_2
energyLog_quadratic_bound._simp_1_3
energyLog_quadratic_bound._simp_1_4
energyLog_quadratic_bound._simp_1_5
energyLog_quadratic_bound._simp_1_6
energyLog_quadratic_bound._simp_1_7
```

全部17项传递公理均为`propext`、`Classical.choice`、`Quot.sound`的子集；部分helper只用propext，其余用标准三项，没有sorryAx。所有实际新增helper均包含；本次名称恰在当前namespace下只是遍历结果，筛选并未限名。

同一Lean输入真实import以下26模块（均`Shao.OQ4.`前缀）：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds、TruncatedEnergy、EnergyTiltedLaw、EnergyLogNormalizer。额外检查两个旧closedUpper可测性定理以及N2主要实际与纯实接口可用，共存成功。

本机及服务器最终源禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三份独立日志均0 warning/0 error。完整原始日志仅留服务器`repro_outputs/oq4-energy-log/n2-independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 9125 | `ddca03558fb6fce3024b6b75fc6089ddf8ab2ee24d55d70e406c2416e5ee5a19` |
| `coexist-26.log` | 2151 | `1c4efab704d17d62975da5f28fd14a8c73e7bfcf16e905ad4cde6559c02f3866` |

## 裁决

没有关键数学或形式缺口。精确H、T-only C_log、内部实际Z的正邻域、两侧log处理及两个4的平方支付均覆盖冻结接口，无前提漂移。

**只认证有限N2。完整E1、E2精确线性再中心化、E3路径密度、E4能量集中、B1、BE/SP、K/Kv、随机分母、完整OQ4及其他全部完整根仍OPEN；本模块不构造或认证N1。**
