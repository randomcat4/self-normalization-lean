# ReflectedSurvival v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 唯一ν-CDF输入与ν/ν⁻两个原始SP输入下的真实上/下侧生存及区间集中接口

LEAN_STATUS: 独立服务器无-o目标、完整源码全部新增常量传递公理审计、指定22模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；服务器完成时间2026-10-21T16:19:38.873706+00:00。审查时实际服务器HEAD为`f46ee95e7ecbac3686caae481c9a03fd6bad96f7`。本票以实际源、独立运行及冻结数学票为依据；未读作者收据、摘要、声明清单、会话、语义票或其他审稿票。

## 数学票与最终源绑定

先只读冻结接口及匿名证明完成独立数学审查，冻结`reflected-survival-math-review-v1.md`，SHA256为`0289954a28a1d3e9a8475b716ee84bd2025cef22a8eae1ce3ce50809ae3b0d00`，STATUS CORRECT / MATH_ONLY。该票随后保持字节不变，才读取实现并进行本形式审查。

| 文件 | 审查时SHA256 |
|---|---|
| `drafts/oq4/frozen-reflected-survival-v1.md` | `d70163cb3114dcf35787d6ab1159b80ca67ba6dc2598613ae252e3ec1126f2dc` |
| `drafts/oq4/reflected/proof.md` | `25574bf05ec2e02b9a064762d2ca7565ae611aae2a3be3432876ec52d03ab266` |
| 本机`drafts/oq4/reflected/ReflectedSurvival.lean`及服务器`Shao/OQ4/ReflectedSurvival.lean` | `b54b2300ef77375782e60a541bcffd6bed05ac4de61a776c6e0fd5e189568809` |
| 直接import `FiniteSurvivalLaplace.lean` | `49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb` |
| 直接import `KilledBlockBounds.lean` | `cc46dc9257cc89d6e31139a60593a419d296fd5f691f10eb565d6310d9dd2408` |
| 使用的`BoundaryOccupation.lean` | `1568e5514fc4ca8053ccd9b0f123f86e61cc294df0f6de199c8a688b9d7de8a6` |
| 使用的`IntervalConcentration.lean` | `491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875` |
| `LaplaceTail.lean` | `664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2` |
| `LaplaceGenerating.lean` | `eab53afb87248fc0f9b94ddf84e986eedae51f2446e9b7ea176e517c4a861ed8` |
| 共同`Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |
| 共同`Shao/Basic/FinitePath.lean` | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` |
| 共同`Shao/Probability/FiniteIID.lean` | `d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b` |
| 共同`Shao/Probability/MeasurablePath.lean` | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` |

上述本机可读副本与服务器对应源逐项一致。最终目标12725字节、235行。全部22个OQ4源及4项共同依赖均在服务器检查前后逐字节SHA一致；完整清单只留服务器日志。

## 逐项签名与证明语义

1. **真实反射law与概率性（第10–26行）。** `reflectedLaw ν`就是`ν.map (fun x => -x)`，不是抽象比较law。概率实例用可测反射的map_apply在univ上证质量1。`iid_reflected_product_law`对所有自然t，恰证Π_t(ν⁻)=map(path neg)Π_t(ν)，由真实`Measure.pi_map_pi`逐坐标推送，无生存条件化。空Fin 0不需额外假设。

2. **前缀、闭下事件和概率恒等式（第28–61行）。** `reflected_prefixSum`对任意k成立；两个反射原像定理对任意t,d成立。`lowerBlockSurvival_eq_closed_lower_prefixes`展开为全部k≤t的`-d ≤ prefixSum a k`，即冻结所称闭下侧事件；共同接口没有另一个需改写的`closedLower`定义。公共`closedUpper`及既有`lowerBlockSurvival`均包含k=0；等号、原子、t=0和d<0的空事件均保留。第46、54行的真实Π概率等式通过可测集合的map_apply给出，两方向均有，并非仅某测试积分的类比。

3. **实际高斯反射（第64–90行）。** `standardNormalCDF`由既有第62行`standardNormalCDF_eq_real`绑定到实际`gaussianReal 0 1`的Iic质量。此处用实际`gaussianReal_map_neg`与方差1的`NullSingletonClass`：反射Iic(−x)精确为Ici x，再仅对高斯去掉单点，转成Ioi x。最后用概率测度闭集补质量公式得Φ(−x)=1−Φ(x)。没有把任意ν声明成无原子。

4. **严格CDF序极限（第93–109行）。** 上界由{X<x}⊆{X≤x}与有限测度的实质量单调性，下界对所有δ>0用{X≤x−δ}⊆{X<x}及实际Φ的1-Lipschitz界，再`le_of_forall_pos_le_add`。并未等同严格/非严格事件。辅助定理甚至对任意函数X成立，因为这一部分只用有限测度的集合单调性；实际后续X明确可测，补质量及推送没有不合法应用。

5. **反射BE由唯一原BE推出（第112–145行）。** 签名只有ν的全t≥1、全x闭CDF误差，无第二BE、矩或对称条件。实际X=prefixSum/√t由可测前缀和构造。反射后的闭事件精确等于{X<−x}的补集；第142行在可测严格事件上用概率补质量公式，转成1−P(X<−x)。用第93行严格CDF界与Φ反射，保持同β、同C_BE。这里未把<替成≤；t≥1量词保留。

6. **现有区间谓词，无矩假设（第148–188行）。** 只有β≥1、C_BE≥0与唯一ν-CDF。对t≥1证√t>0，构造实际可测X的推送概率μ，推送Iic恰为给定CDF事件。闭单位间隔精确等于μ的闭区间[a/√t,(a+1)/√t]质量。实际调用的是任意law的`closed_interval_mass_bound_from_cdf`与真实Φ的1-Lipschitz界；保留两端原子，未调用二阶/三阶矩高层定理。最终(1+2C_BEβ)/√t≤(1+2C_BE)β/√t只用β≥1。结论是既有`iidIntervalConcentration ν β (1+2*C_BE)`。

7. **两侧生存（第191–208行）。** 签名分别明确输入ν及`reflectedLaw ν`的全L>0、0<s<1原始式`laplaceG(maxLaplaceMean)=exp(laplaceW(endpointLaplaceMean))`。没有归一化式、S、非增性或可和性输入。对ν直接调用既审有限Laplace闭上侧定理；对ν⁻用本模块刚推出的CDF与独立hSPneg再调用同一定理，最后真实反射概率恒等式转成原ν闭下侧。所有自然t≥1、实d≥0及同一常数√2 exp(6+3C_BE)完整保留。

8. **常数与联合输出（第210–233行）。** C_S非负证明甚至不需C_BE≥0；C_q非负由该显式假设。最终签名输出两个常数非负和既有S/AC谓词，参数只有任意ℝ Borel概率ν、β≥1、C_BE≥0、唯一ν-CDF和两law各原始SP。β没有被暗中定义成某个矩。t=1、d=0、大跳、不对称、全部原子与全零路径无排除条件。

**冻结文字参数顺序事项已解决。** 服务器实际`#print`既有定义：`iidOneSidedSurvival (ν) (β Cs)`与`iidIntervalConcentration (ν) (β Cq)`。因此实现写`ν β C_S`和`ν β C_q`，展开分别正是冻结第12–15行要求的`C_S*(d+β)/√t`及`C_q*β/√t`。冻结第14–15行简写`ν C_S β`/`ν C_q β`是与实际API次序不符的记号，不改变其已写明的自然数学界。本票没有改动冻结、前提或证明；数学票第7项的原始记号记录保留。

**真实积分/级数承接。** 本模块新增部分只用有限概率质量、可测推送及实代数，没有用默认实积分0替代实际积分。两个原始SP中的`maxLaplaceMean`/`endpointLaplaceMean`及相关实级数为已审有限Laplace模块的实际对象；调用的`closedUpper_bound_of_cdf_and_original_sp`内部已经供应真实可积性、三项Summable、实际跨维非增性与SP归一化。本模块未把这些已证步骤重设成额外前提。

## 实际服务器验证

所有运行均通过`tools/server.py`当前broker，在指定worktree执行；先source指定activate.sh，再cd。使用固定Lean 4.36.0-rc1/mathlib807d3836版本与只读公共缓存；每次`taskset -c 0-3`单进程，三个Lean命令顺序执行，均无`-o`，没有生成目标olean、修改源或写缓存。本次broker均成功，无不确定操作重放或旁路回退。

1. **目标：** `lake env lean Shao/OQ4/ReflectedSurvival.lean`，exit 0，日志0字节。
2. **完整源码审计：** 将服务器最终完整源直接接审计附录送入`lake env lean --stdin`，exit 0。附录独立`#check`全部显式新项、所用高斯/产品/既审辅助API，并打印既有谓词与最终完整签名。动态遍历`env.constants.toList`，对每一个`env.getModuleIdxFor? declName`为`none`的常量都执行`Lean.collectAxioms`；不按namespace、root名或作者清单过滤。任何非`propext`、`Classical.choice`、`Quot.sound`公理会直接报错。
3. **22模块共存：** 实际同一Lean输入import全部下列既有21模块及ReflectedSurvival，exit 0；同时核对旧`measurableSet_closedUpper`与唯一名`measurableSet_closedUpper_laplace`可用、最终联合签名及其传递公理。没有只检查两个新模块或以standalone编译替代共存。

实际动态输出：

```text
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 29
ACCEPTED_22_MODULE_COEXIST_EXIT=0
ALL_22_SOURCE_AND_4_COMMON_HASHES_UNCHANGED=True
```

实际29项为以下17个显式声明和12个生成声明；全部传递公理均为标准三项白名单的子集，无sorryAx：

```text
reflectedLaw
reflectedLaw_isProbabilityMeasure
iid_reflected_product_law
reflected_prefixSum
reflection_preimage_closedUpper
reflection_preimage_lowerBlockSurvival
lowerBlockSurvival_eq_closed_lower_prefixes
reflected_closedUpper_probability
reflected_lowerBlockSurvival_probability
standardNormalCDF_reflection
strict_cdf_error_of_standardNormalCDF_error
iid_reflected_cdf_error
iidIntervalConcentration_of_standardNormalCDF_error
iidOneSidedSurvival_of_cdf_and_two_original_sp
reflected_survival_constant_nonneg
reflected_concentration_constant_nonneg
iid_survival_and_concentration_of_cdf_and_two_original_sp
reflectedLaw.eq_1
lowerBlockSurvival.eq_1
standardNormalCDF_reflection._simp_1_1
standardNormalCDF_reflection._simp_1_2
standardNormalCDF_reflection._simp_1_3
standardNormalCDF_reflection._simp_1_4
iid_reflected_cdf_error._simp_1_1
iid_reflected_cdf_error._simp_1_2
iid_reflected_cdf_error._simp_1_3
iidIntervalConcentration_of_standardNormalCDF_error._simp_1_2
iidIntervalConcentration_of_standardNormalCDF_error._simp_1_3
iidIntervalConcentration_of_standardNormalCDF_error._proof_1_1
```

上述名称均以`Shao.OQ4.`为完整前缀；这是实际无namespace过滤遍历的结果，不是遍历过滤条件。其中`lowerBlockSurvival.eq_1`是在导入名称下新生成的helper，亦在审计内。部分helper只依赖`[propext]`或`[propext, Quot.sound]`；其余依赖白名单三项。

22模块（均`Shao.OQ4.`前缀）：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival。

本机及服务器最终目标的独立禁用token扫描均为0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三个服务器日志均0 warning/0 error。

完整原始日志仅留服务器worktree的`repro_outputs/oq4-reflected/independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 20331 | `ab928a8287711727dca8df36d3ae03ff16da212cf939211d98cbc074aa83f080` |
| `coexist-22.log` | 2331 | `dc8856ffe45aa977b622709e94275ac36b04a130f153061d1d371ab964133975` |

## 最终裁决

没有关键数学或形式缺口。认证范围是给定唯一ν-CDF误差及ν/ν⁻各原始SP后，为现有KilledBlockBounds提供实际S/AC谓词及显式非负常数。常数依赖C_BE；只有外部BE指定通用数值C_BE后，它们才成为通用数值常数。

**外部BE、两个原始SP、无条件S/AC/O0、B1、长期K/Kv、能量分母、4/π、完整OQ4及其他全部完整根仍OPEN。**
