# EnergyLinearTiltLaw v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 实际能量law上的全实参数线性倾斜族、真积分与概率/矩接口

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、28模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；正式检查完成于2026-10-21T17:48:36.794123+00:00，实际HEAD为`2380a8e5798e848f3c9d644ff09e83a90194fd38`。未读作者receipt、summary、ledger、译者票或其他审稿票。

## 冻结与源绑定

先只读冻结接口及匿名证明，冻结CORRECT / MATH_ONLY数学票SHA256为`ddab2def53b6a73a974f7f4a0b0cef6f7e7dc44b56e33cacaf523b60bebbaad8`，最终源通知后才读取完整实现；数学票及原证明未改变。

| 文件 | SHA256 |
|---|---|
| `drafts/oq4/frozen-energy-linear-tilt-law-v1.md` | `28cb39d67500ae660d1eb2efa5f2aad0bae58896207ab853f8a5c0e530b91cd6` |
| `drafts/oq4/energy-linear/proof.md` | `a246e6290d2db021aa9ae0e667b2752392f64d5dfa90954c6a55c953c40887a0` |
| 本机`drafts/oq4/energy-linear/EnergyLinearTiltLaw.lean`及服务器`Shao/OQ4/EnergyLinearTiltLaw.lean` | `63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78` |
| 唯一直接Shao依赖`EnergyTiltedLaw.lean` | `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` |
| 共同N0依赖`TruncatedEnergy.lean` | `bd8015535312de5812ccca340e5bb6e7dd2d1c55a8da1e627f6aa228500495c0` |

最终源187行、10550字节。目标与上述依赖本机副本和服务器一致。服务器全部28个OQ4源及全部32项`Shao/Basic`、`Shao/Probability`共同Lean源在正式检查前后SHA清单完全相同；完整清单只留服务器。未改任何旧源、公共文件、冻结、证明、Git或缓存。

## 完整实际签名与实现

1. **真实定义且不含T/M/K（第9–26行）。** L、A1、A2、B3分别是exp(tx)、x exp(tx)、x²exp(tx)、|x|³exp(tx)对同一实际`energyTiltedLaw ν h s`的实积分。`energyLinearTiltLaw`是该同一μ的真实withDensity(ofReal(exp(tx)/L))测度；mean恰为实际A1/L。所有定义只含ν,h,s,t，没有替代μ、T、M、K、θ或预设均值。

2. **域与省略原cube前提（第51–55行）。** 实际主/辅助定理在section中保留概率ν、T≥0、h≥1、|s|≤T、原平方Integrable及二阶积分1；显式`include`使这些前提进入相关最终签名。本轮实际`#check`核对了展开后的全部签名。原cube前提被省略，因为N1的概率/支持已足够；这严格覆盖冻结完整域，且没有增加中心、id、M、K、θ、方差或指数矩条件。并非遗漏需要的分布限制。

3. **a.e.支持而非全球界（第28–47行）。** 线性密度对任意ν,h,s,t可测。纯实指数界以明确|x|≤2h为前提，给−2h|t|≤tx≤2h|t|，未声称全实轴exp(tx)有界。新law的ae闭支持经withDensity准则从同一N1 μ的ae支持转移，甚至无需参数适用条件；没有改成原ν逐点有界支撑。

4. **任意实t与自然次幂的真可积（第58–83行）。** 先内部调用N1实际概率定理给μ有限概率性。在μ满测集|x|≤2h上，|x|^k exp(tx)的范数受常数(2h)^k exp(2h|t|)支配；所有函数可测，h≥1保证半径非负，`Integrable.of_bound`给每个自然k、每个实t真正可积。k=0、1、2、3分别供应四个冻结函数；signed x项用可积|x|exp作范数支配，平方用sq_abs转化。没有将a.e.界用作全实轴界，没有原ν指数矩或第四矩假设。

5. **精确normalizer界和正性（第85–103行）。** 实际N1概率性和四项可积性内部供应；把同一μ-a.e. exp上下界通过`integral_mono_ae`与可积常数比较，给精确exp(−2h|t|)≤L(t)≤exp(2h|t|)，再由指数正性得到L>0。t未限制大小或符号；没有把L正性、界、μ概率或支持作为新输入。

6. **实际概率law（第105–114行）。** exp(tx)/L非负、真μ可积，使用真实withDensity质量及ofReal积分公式，归一化质量恰为ofReal(L/L)=1。该结论是构造测度的IsProbabilityMeasure，不是仅有期望公式或假设存在某law。闭支持由前述实际ae定理直接可用。

7. **所有Borel质量及测试桥（第116–151行）。** 对任意可测A，限制的exp/L由已证Integrable.restrict保证真可积，因此ν̃_t.real A=(∫_A exp(tx)dμ)/L是实际有限实质量。一般接口对Borel f且fw=f exp(tx)真μ可积，同时返回f真μ_t可积和真实积分比。密度点态有限，ofReal.toReal在L>0后化为正密度，`integrable_withDensity_iff`将可积性化成(f exp(tx))/L；随后Bochner密度公式合法换测度。没有要求f原ν或原μ可积，没有∞除法或依赖不可积实积分默认值。`_hf`保留冻结的Borel前提；加权可积性准则提供实际证明所需信息。

8. **真实矩与m（第153–168行）。** 公开合取明确返回id、平方、绝对立方对μ_t的三项Integrable，外加均值=A1/L、均值=m、二阶=A2/L、第三绝对矩=B3/L。四个等式都通过已证明加权可积性的同一测试桥得到，law和原μ保持一致。没有中心或正方差下界。

9. **t=0真实测度等式（第170–183行）。** 内部N1概率给L(0)=∫1dμ=1；把它代回真实withDensity定义后密度恒1，证明μ_0=μ作为测度等式，非仅同矩。m(0)=∫x dμ的身份亦精确；id真可积可由已证moments/加权可积性在t=0调用。名字中的zero表示参数0，不声称均值为零。s=0时μ一般仍为归一化闭截断law而非ν。

全实t、h=1、T=s=0、零点和±2h原子均保留。μ可能退化，证明没有从概率/支持推导正方差。原ν仍可不对称、无密度、非格点或有无界支撑。

## 服务器执行与全新常量审计

通过`tools/server.py`使用指定服务器；先source固定activate.sh再cd worktree。三个正式验证均`taskset -c 0-3`、单进程顺序运行、无`-o`，不重编旧target、不发射目标olean或写缓存。

首次只读文件清单预检因服务器未安装rg，在Lean启动及SHA快照之前明确exit 127；仅创建了日志目录。确认该已结束执行的效果后，改用Python只读目录枚举，正式三项检查才开始。未重放未知操作、未修改源或安装工具；这不是Lean证明失败。该历史已留服务器`inventory-history.txt`。

```text
COMMON_BASIC_PROBABILITY_SOURCE_COUNT=32
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 24
ACCEPTED_28_MODULE_COEXIST_EXIT=0
ALL_28_OQ4_AND_BASIC_PROBABILITY_SOURCE_HASHES_UNCHANGED=True
```

无-o实际目标为`lake env lean Shao/OQ4/EnergyLinearTiltLaw.lean`。另将服务器最终完整source直接接审计附录送`lake env lean --stdin`，打印6个定义并核对14个显式定理及N1概率/支持接口；随后遍历`env.constants.toList`，以唯一条件`env.getModuleIdxFor? declName`为`none`选出所有实际新常量。每项执行`Lean.collectAxioms`，拒绝标准三项之外任何公理；无namespace、root、声明名或作者清单过滤。

实际24项为以下20个显式声明和4个helper（均`Shao.OQ4.`前缀）：

```text
energyLinearNormalizer
energyLinearFirstNumerator
energyLinearSecondNumerator
energyLinearThirdNumerator
energyLinearTiltLaw
energyLinearMean
energyLinear_density_measurable
energyLinear_exponent_bounds
energyLinearTiltLaw_ae_support
energyLinear_power_exp_integrable
energyLinear_integrability
energyLinearNormalizer_bounds
energyLinearNormalizer_pos
energyLinearTiltLaw_isProbabilityMeasure
energyLinearTiltLaw_real_apply
energyLinearTiltLaw_integral
energyLinearTiltLaw_moments
energyLinearNormalizer_zero
energyLinearTiltLaw_zero
energyLinearMean_zero
energyLinearFirstNumerator.eq_1
energyLinearNormalizer.eq_1
energyLinearTiltLaw.eq_1
energyLinear_integrability._simp_1_1
```

前23项传递公理为`[propext, Classical.choice, Quot.sound]`，最后simp helper只用`[propext]`。没有sorryAx或非白名单公理；所有helper均实际覆盖。筛选同样会包含导入名称下生成的新项，本次并无这类额外名称。

真实同一Lean输入import以下28模块（均`Shao.OQ4.`前缀）：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds、TruncatedEnergy、EnergyTiltedLaw、EnergyLogNormalizer、EnergyE1Bounds、EnergyLinearTiltLaw。额外检查旧两个closedUpper可测性名字及新族主要可积/概率/质量/矩/t0接口可用，共存成功。

本机与服务器最终源禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三份正式日志均0 warning/0 error。完整原始日志只在服务器`repro_outputs/oq4-energy-linear/independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 18404 | `e80bf2c6980f87b0f24d198e7d7d9694462c44270f324ed7551c92f78056ed9d` |
| `coexist-28.log` | 4859 | `c56a6ead5ad3f469413f4f9372109a1a18966ab1d21d97f376b2e71d64edd801` |

## 裁决及范围

没有关键数学或形式缺口。省略不需的原cube前提是覆盖冻结域的加强，所有实际对象、全实参数、真可积性、归一化界与t0测度等式均完整。

**只认证E2首叶对象/积分接口。参数导数、共同方差区间、端点异号、θ存在、精确均值零、选定θ处的log/矩误差均未在本叶证明。E2、E3、E4、K/Kv、随机分母、完整OQ4及其他全部完整根仍OPEN。**
