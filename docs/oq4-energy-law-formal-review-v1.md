# EnergyTiltedLaw N1 v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 实际归一化能量密度概率law、Borel质量与积分接口、有限分子和精确归一化矩界

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、25模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；本轮服务器完成于2026-10-21T17:17:22.106004+00:00，实际HEAD为`28b459e8d6e30cc06c8402027c1a8ee18a08c5a7`。未读作者receipt、summary、ledger、译者票或其他审稿票；本票依据最终源及本轮独立执行。

## 冻结与版本绑定

先只读N1冻结接口及匿名证明，冻结CORRECT / MATH_ONLY数学票为SHA256 `de284b4cd14b26d0b1f96063faef430b9c11b1b240b74a539be0ce0861070211`。收到最终SHA后才读取完整实现；数学票与匿名证明未改变。

| 文件 | SHA256 |
|---|---|
| `drafts/oq4/frozen-energy-tilted-law-v1.md` | `2b8b3761e1e0d6d2f78bd913c9db9f67d6484c7fcb266af99cc95c1bf7b7e0f2` |
| `drafts/oq4/energy-law/proof.md` | `3788a0145dddbbc47bb9bddcea5151eab5e11a574a84d2c2066c54fb8667c507` |
| 本机`drafts/oq4/energy-law/EnergyTiltedLaw.lean`及服务器`Shao/OQ4/EnergyTiltedLaw.lean` | `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` |
| 直接Shao依赖`TruncatedEnergy.lean` | `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` |
| 直接Shao依赖`IntervalConcentration.lean` | `491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875` |
| 共同`Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同`Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共同`Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同`Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |

最终源432行、24984字节。上述可读本机源与对应服务器源逐项一致。服务器25个OQ4源和4项共同依赖前后SHA清单完全一致，完整清单留服务器。没有修改N0或任何旧模块、冻结、公共文件、Git或缓存。

## 完整签名与实现覆盖

### 实际密度law、概率性与所有Borel集质量

第11–12行`energyTiltedLaw ν h s`就是实际`ν.withDensity (fun x => ENNReal.ofReal (energyWeight h s x / energyNormalizer ν h s))`，定义不含T，也不是只定义期望或假设存在概率law。第14–31行六个常数精确为冻结C_1、C_2、D_T、C_μ、C_m2、C_m3；C_m2的括号明确包含C_2+T+C_Z。

第33–35行对任意ν,h,s证明实际ENNReal密度可测。第37–41行只从N0归一化下界推0<Z，没有将Z正性列为前提。第43–55行在概率ν、T≥0、h≥1、|s|≤T、平方可积及单位二阶矩下，取得N0权重真实可积性，证明w/Z非负，合法将实际withDensity质量转成非负可积函数积分，得到ofReal(Z/Z)=1。平方以外不必提前加立方或中心条件，属于比完整冻结前提更强的辅助结论。

第57–68行对**任意**`A : Set ℝ`且`MeasurableSet A`证明真实实质量公式ν̃.real A=(∫_A w)/Z。所用`(hw.div_const Z).restrict`明确保证限制密度真可积，非负性保证ofReal/toReal转换合法。没有以无穷质量除法、未证有限性或不可积实积分默认值替代所需公式。

第70–76行由可测密度的`ae_withDensity_iff`直接证明ν̃-a.e. |x|≤2h：在严格补集上原权重恒零。这项甚至对任意参数成立，不意味着非适用参数下也声称概率性。原ν无需闭支撑；截断边界原子未删除。

### Borel测试换测度与真实可积性

第79–104行公开接口完整保留Borel f及`Integrable (fun x => f x * w x) ν`前提，同时返回`Integrable f ν̃`及真实Bochner积分公式。密度ofReal取值点态有限，且因Z>0、w≥0，其toReal恰为w/Z。证明用`integrable_withDensity_iff`将倾斜可积性化到可积的(fw)/Z，代数换序合法；随后用实际`integral_withDensity_eq_integral_toReal_smul`及线性分母提出得到∫f dν̃=(∫fw)/Z。

这里不要求f先在ν下可积，亦未把结论扩到任意不可积f。证明中`_hf`未参与进一步推导，不是缺口：withDensity可积性准则及已给加权Integrable已供应必要的加权可测信息，而公开接口仍有冻结要求的Borel前提。第一合取明确证明真可积性，故后一积分公式不依赖不可积积分的默认值。

### 内部id、实际β与两个law的矩可积性

第106–115行只用概率ν、平方/立方Integrable及二阶1，内部由|x|≤x²+1支配推出id真可积，调用既审实际矩定理推出β≥1。两者均是输出，不是额外分布限制；β总是原ν的`∫|x|³`。

第117–126行对任意可测且原ν可积的f，用0≤w≤exp(4T)证明fw真可积。第205–216行将其实际应用到内部推出的id及已给平方、立方，公开返回三种加权原函数的Integrable。第218–228行再逐个调用一般测试桥，公开返回id、平方和绝对立方对真实ν̃的Integrable。所有这些定理均无原中心条件。

### 截断内指数差分与三个真实分子

第128–155行不把指数差分当作前提：令F(v)=exp(4T)v−exp v，在[-4T,4T]上实际导数exp(4T)−exp v≥0，故F单调；比较u与0并按正负号去绝对值得|exp u−1|≤exp(4T)|u|。第157–172行只在|x|≤2h内代入N0实际argument bounds，得到|w−1|≤(exp(4T)T/h²)x²，没有将该界错误用于全实线或要求指数矩。

第175–203行构造两项全球包络，严格尾分别支付|x|、x²，截断内差分分别以立方和闭截断四次方支付；保留弱截断/严格补集。第230–255行只在均值分子多给原`∫x=0`：先用已证weighted-id及id可积性合法作积分差，再对N0可积尾绝对值加K|x|³进行真实积分比较，得到C_1β/h²，K=exp(4T)T/h²。

第257–283行二阶分子使用单位二阶矩和已证weighted-square可积性，尾平方由β/(2h)支付，修正由N0真可积闭截断x⁴及其2hβ支付，精确得到C_2β/h，C_2=1/2+2exp(4T)T。第285–300行三阶分子在双方真可积的前提下由0≤w≤exp(4T)证明0≤M_3≤exp(4T)β。第二和第三分子没有原中心、第四矩、有界支撑或额外高度阈值。

### 归一化常数与三项矩结论

第302–313行由N0正下界合法反转并用exp(−4T)倒数恒等式得Z⁻¹≤D_T=(4/3)exp(4T)，不是额外假设。第315–346行从N0精确一阶展开得到

```text
|Z−1| ≤ C_Z β/h³ + T/h² ≤ (T+C_Z)β/h.
```

内部β≥1、h≥1用来支付1/h²≤β/h，β≥0和h≤h³支付β/h³≤β/h；C_Z非负从N0供应。没有漏项、β≤M或更大高度门槛。第348–354行显式证明所有六个常数非负，只依赖T。

第356–376行真实倾斜均值通过测试桥、Z>0、分子C_1界和D_T倒数界给C_μ β/h²，并在签名明确保留原中心。第378–412行二阶矩**先比较M₂−Z**：点态实数恒等式M₂/Z−1=(M₂−Z)/Z，且|M₂−Z|≤|M₂−1|+|Z−1|。因此最终系数正是D_T(C_2+T+C_Z)，不把M₂−1除Z误当归一化误差。第414–430行三阶矩由真实换测度与分子/倒数界得到D_T exp(4T)β。各积分真实可积性已经在公开定理中证明。

完整实现只有第一分子及最终均值两项使用`hmean`；概率、支持、一般换测度、第二和第三矩均无中心前提。最终第二矩是原点二阶矩，与单位方差或精确中心化无混同。

### 原子和零参数

所有最终矩及概率结论保留T≥0、h≥1、|s|≤T的弱端点，涵盖T=s=0、h=1、零点原子及±2h原子。s=0时通过真实密度及N0的Z质量恒等式得到归一化闭截断law，一般不等于ν。任意Borel质量公式可直接给B内原子exp(sa²/h²)ν.real{a}/Z及B外零，无需新增单点假设。原law可不对称、有无界支撑且无密度。

## 独立服务器证据及全部新常量

所有Lean只在指定服务器执行，`tools/server.py`正常broker，先source固定activate.sh再cd lead-oq4 worktree；三个正式验证均`taskset -c 0-3`、一进程顺序运行、无`-o`，不重编旧目标，不写缓存或发射新目标olean。无不确定调用重放或旁路回退。

```text
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 54
ACCEPTED_25_MODULE_COEXIST_EXIT=0
ALL_25_SOURCE_AND_4_COMMON_HASHES_UNCHANGED=True
```

实际无-o目标为`lake env lean Shao/OQ4/EnergyTiltedLaw.lean`。另一命令把服务器最终完整源码直接接审计附录送`lake env lean --stdin`：打印7个真实定义、检查22个显式定理完整签名，然后对全部`env.constants.toList`遍历，以唯一条件`env.getModuleIdxFor? declName`为`none`选择全部新常量。每项执行`Lean.collectAxioms`并拒绝标准`propext`、`Classical.choice`、`Quot.sound`之外任何项。无namespace、root名、声明名或作者清单过滤。

实际54项包括以下29个显式声明（均`Shao.OQ4.`前缀）：

```text
energyTiltedLaw
energyTiltFirstNumeratorConstant
energyTiltSecondNumeratorConstant
energyTiltInverseNormalizerBound
energyTiltMeanConstant
energyTiltSecondMomentConstant
energyTiltThirdMomentConstant
energyTiltedLaw_density_measurable
energyTiltedLaw_normalizer_pos
energyTiltedLaw_isProbabilityMeasure
energyTiltedLaw_real_apply
energyTiltedLaw_ae_support
energyTiltedLaw_integral
energyTilt_original_moment_inputs
energyTilt_weighted_integrable
energyTilt_exp_difference_bound
energyTilt_weight_difference_inside
energyTilt_moment_pointwise
energyTilt_weighted_moment_integrability
energyTiltedLaw_moment_integrability
energyTilt_first_numerator_bound
energyTilt_second_numerator_bound
energyTilt_third_numerator_bound
energyTilt_inverse_normalizer_le
energyTilt_normalizer_difference_bound
energyTilt_constants_nonneg
energyTiltedLaw_mean_bound
energyTiltedLaw_second_moment_bound
energyTiltedLaw_third_moment_bound
```

其余25个生成helper全部包含在实际审计，可精确归组为：

- `energyTiltedLaw.eq_1`（1项）；
- `energyTiltFirstNumeratorConstant._proof_1`、`energyTiltSecondNumeratorConstant._proof_1`、`energyTiltInverseNormalizerBound._proof_1`（3项）；
- `energyTilt_first_numerator_bound._simp_1_1`至`._simp_1_7`（连续7项）；
- `energyTilt_second_numerator_bound._simp_1_1`至`._simp_1_7`（连续7项）；
- `energyTiltedLaw_second_moment_bound._simp_1_1`至`._simp_1_7`（连续7项）。

54项传递公理均为标准三项的子集，无sorryAx；部分helper仅`[propext]`，其余为白名单三项。本次所有新项恰在当前名称下，但筛选没有这一限制，同样可捕获导入名称下生成helper。

实际同一Lean输入import全部25模块（均`Shao.OQ4.`前缀）：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds、TruncatedEnergy、EnergyTiltedLaw。额外实际检查两个旧closedUpper可测性定理及N1主要概率/质量/支持/积分/矩接口可用，共存exit 0。

本机及服务器最终源禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三份日志均0 warning/0 error。完整原始日志仅留服务器`repro_outputs/oq4-energy-law/n1-independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 28979 | `0edf5cb3f5bb66b0af4bd78fe969143eec65e009f6909230979a1c4094edac8b` |
| `coexist-25.log` | 4024 | `c0128d23c76c4c9b914db6834b9007458c7bc6844d0b3e7c8eb5c4c4ff1cef51` |

## 裁决与边界

没有发现关键数学或形式缺口。N1实际测度、真积分与可积性接口以及全部分子和精确归一化矩常数覆盖冻结声明，无前提或端点漂移。

**只认证N1。完整E1、log Z精度、E2线性倾斜/精确再中心化、E3路径密度、E4、K/Kv、B1、BE/SP、随机分母、完整OQ4及其他全部完整根仍OPEN。**
