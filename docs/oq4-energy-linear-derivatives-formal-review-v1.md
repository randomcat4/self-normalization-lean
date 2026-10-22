# EnergyLinearTiltDerivatives v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 同一实际线性倾斜积分族的全实参数导数、真实中心平方积分及连续性

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、29模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；正式服务器检查完成于2026-10-21T17:58:52.489309+00:00，实际HEAD为`2380a8e5798e848f3c9d644ff09e83a90194fd38`。未读作者receipt、summary、ledger、译者票或其他审稿票。

## 冻结与最终版本

先只读本叶冻结接口及匿名证明，冻结CORRECT / MATH_ONLY数学票SHA256为`ebc2bbb688dec06fff5df123e6834ea6675d1c8658f89d39e51ee434d8a83ac5`。最终源通知后才读取完整实现；数学票及匿名证明保持字节不变。

| 文件 | SHA256 |
|---|---|
| `drafts/oq4/frozen-energy-linear-derivatives-v1.md` | `45e9d3e76d5ce15cfbfa947198489ccf9c70b36cba14ce9d78014d68e202dd56` |
| `drafts/oq4/energy-linear-derivatives/proof.md` | `9edcf7be76ace16c1bab921c0b9c094caea0ba493032fd3479a7ae217c05bb16` |
| 本机`drafts/oq4/energy-linear-derivatives/EnergyLinearTiltDerivatives.lean`及服务器`Shao/OQ4/EnergyLinearTiltDerivatives.lean` | `f84467d102660c9abfa09062d1dbe8b3c499058b9960d779aa86fcd653b9a6b2` |
| 唯一直接Shao依赖`EnergyLinearTiltLaw.lean` | `63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78` |
| 共同实际μ依赖`EnergyTiltedLaw.lean` | `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` |

最终源173行、10286字节，另import固定Mathlib ParametricIntegral。上述本机目标、直接依赖及实际μ依赖与服务器一致。全部29个OQ4源和全部32项`Shao/Basic`/`Shao/Probability`共同Lean源在正式检查前后SHA清单完全一致，完整清单只留服务器。没有修改源、冻结、原证明、公共文件、Git或缓存。

## 完整实际签名与积分求导义务

第29–34行的section显式保留任意实Borel概率ν、T≥0、h≥1、|s|≤T、原平方Integrable及单位二阶矩。四个主导数及连续性定理另保留冻结的原绝对立方Integrable参数`_hCube`；该参数未用于主要计算不构成缺口，且属于原冻结域。中心平方身份和非负性省略不需要的cube前提，属于加强。实际展开后的所有签名已在独立source检查中核对，无中心、M、K、θ、可交换假设、方差下界或原指数矩前提。

第12–25行局部辅助界在明确|x|≤2h、|u−t|≤1、h≥0下，先证|u|≤|t|+1，再给

```text
‖x^k exp(ux)‖ ≤ (2h)^k exp(2h(|t|+1)).
```

使用的是范数中的abs_pow与实际指数上界，对任意自然k。它不是全实线无条件指数界。后续两次积分求导只在同一实际μ=energyTiltedLaw ν h s的满测集上调用，固定中心t的包络不依赖邻域u。

独立审计实际`#check`了Mathlib `hasDerivAt_integral_of_dominated_loc_of_deriv_le`：其前提是邻域s∈nhds(t)、邻域内原函数a.e.强可测、中心原函数Integrable、中心导函数a.e.强可测、同一μ-a.e.点上所有u∈s的导数范数支配、包络Integrable及同一μ-a.e.点上所有u∈s的HasDerivAt；结论包含导函数中心Integrable及实际积分函数的HasDerivAt。本源两次应用逐项对应：

| API义务 | L的求导（第36–60行） | A1的求导（第62–88行） |
|---|---|---|
| 固定基础测度 | 同一实际μ | 同一实际μ |
| 参数邻域 | (t−1,t+1)∈nhds(t) | 同一开邻域 |
| F(u,x) | exp(ux) | x exp(ux) |
| F′(u,x) | x exp(ux) | x²exp(ux) |
| 邻域可测性 | 每个u实际Borel→AEStronglyMeasurable | 同样实际Borel |
| 中心原函数真可积 | 首叶四项可积性的第一项 | 首叶四项可积性的第二项 |
| 中心导函数可测 | x exp(tx)实际Borel | x²exp(tx)实际Borel |
| 统一a.e.导数包络 | k=1的(2h)exp(2h(|t|+1)) | k=2的(2h)²exp(2h(|t|+1)) |
| 包络真可积 | 内部N1供应μ概率后integrable_const | 同样内部概率 |
| 被积参数HasDerivAt | 实际id×常数的exp链式法则 | 在前者上const_mul x |

其中hB的量词明确为`∀ᵐ x ∂μ, ∀ u∈邻域`，不是逐u选择不一致零测集。hD由每个实x上全实参数的真实导数供应；未将交换结论当作前提。API结果`.2`恰为实际HasDerivAt，L′=实际A1、A1′=实际A2，覆盖全部实t和原子测度。

## log、mean、中心平方与连续性

1. **log及商导数（第90–110行）。** 首叶内部供应实际L(t)>0；log规则使用其非零性给HasDerivAt(log L) m(t)。mean商规则使用刚证A1′、L′和L≠0，得到[A2 L−A1²]/L²；实际函数通过energyLinearMean定义及非零分母代数转换成A2/L−m²。没有total log/除零约定，也没有不同的mean或measure替代。

2. **真实中心平方可积（第113–146行）。** 内部取得同一实际μ_t=energyLinearTiltLaw ν h s t的概率、id和平方真可积及两个真实矩身份。先用x²−2mx+m²的可积加减与可积常数证明(x−m)²真正μ_t可积，再合法作积分线性。原点二阶=A2/L、实际均值=m、概率质量1给∫(x−m)²=A2/L−m²。不是只写抽象variance或依赖不可积积分默认值。

3. **积分版本导数及非负（第148–157行）。** 用上述实际积分身份转换已证商导数，公开HasDerivAt m (真实中心平方积分) t；非负性由可积中心平方的逐点非负积分给出。没有假设μ_t已中心化，亦不声称严格正、方差≥1/2或唯一参数。退化law可以给零导数。

4. **连续性内部供应（第159–169行）。** 对每个实t的四个实际HasDerivAt分别取continuousAt，构造L、A1、m、log L的全实Continuous合取。未在端点论证前额外输入连续假设，不要求A2连续来证明当前商导数。

所有函数均是首叶同一μ、L/A1/A2/μ_t/m，基础μ在积分求导时固定；只有完成商法则后才用μ_t的真实矩解释导数。h=1、T=s=0、t=0、正负t、零和±2h原子均保留。原ν不必全局有界、有密度、无原子或有指数/第四矩。

## 独立服务器检查及全部新常量

使用正常`tools/server.py` broker，先source固定activate.sh再cd指定worktree。三个正式验证均在指定服务器`taskset -c 0-3`、单进程顺序运行、无`-o`，不重编旧target、不发射目标olean、不写共享缓存。无不确定调用重放、安装或旁路回退。

```text
COMMON_BASIC_PROBABILITY_SOURCE_COUNT=32
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 17
ACCEPTED_29_MODULE_COEXIST_EXIT=0
ALL_29_OQ4_AND_BASIC_PROBABILITY_SOURCE_HASHES_UNCHANGED=True
```

独立无-o目标为`lake env lean Shao/OQ4/EnergyLinearTiltDerivatives.lean`。完整source审计将服务器最终完整源直接接附录送`lake env lean --stdin`，核对9个显式定理全部签名、真实求导积分API及首叶矩/正性接口。随后遍历全部`env.constants.toList`，只以`env.getModuleIdxFor? declName`为`none`选择全部新项，逐项`Lean.collectAxioms`并拒绝非标准公理，无namespace/root/声明名过滤。

实际17项包括9个显式定理：

```text
Shao.OQ4.energyLinear_local_power_bound
Shao.OQ4.energyLinearNormalizer_hasDerivAt
Shao.OQ4.energyLinearFirstNumerator_hasDerivAt
Shao.OQ4.energyLinear_logNormalizer_hasDerivAt
Shao.OQ4.energyLinearMean_hasDerivAt
Shao.OQ4.energyLinear_centeredSquare_integral
Shao.OQ4.energyLinearMean_hasDerivAt_centeredSquare
Shao.OQ4.energyLinearMean_derivative_nonneg
Shao.OQ4.energyLinear_family_continuous
```

以及导入名称下新生成的`Shao.OQ4.energyLinearMean.eq_1`和`Shao.OQ4.energyLinearMean_hasDerivAt._simp_1_2`至`._simp_1_8`共7个连续编号helper。九显式项及导入名eq_1均为标准`[propext, Classical.choice, Quot.sound]`；simp_1_7也为该三项，其余6个simp helper仅依赖propext。全部都在本次动态审计内，无sorryAx或其他公理；没有只按新root名筛选而漏掉导入名helper。

同一Lean输入真实import全部29模块（均`Shao.OQ4.`前缀）：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds、TruncatedEnergy、EnergyTiltedLaw、EnergyLogNormalizer、EnergyE1Bounds、EnergyLinearTiltLaw、EnergyLinearTiltDerivatives。额外检查两个旧closedUpper可测性名字及所有主要新接口可用，共存成功。

本机与服务器目标禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三个正式日志均0 warning/0 error。完整原始日志仅在服务器`repro_outputs/oq4-energy-linear-derivatives/independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 13636 | `6a0c76bb5fc2827695b5b8bb211cbeffcce7a8e7a0607099d391677872c3de97` |
| `coexist-29.log` | 4436 | `2f44d3e702f230a24bd47a984cdb108470e49a49fca99d1959f87bfb8eae8b6f` |

## 裁决与范围

没有关键数学或形式缺口。实际局部支配求导、log/商导数、真实中心平方可积与身份、非负性及连续性完整覆盖冻结接口，无额外分布或方差假设。

**只认证导数/中心平方叶。共同方差区间、端点异号、θ存在/唯一、精确中心化、选定θ处h⁻⁴ logL或最终矩界未证；E2、E3、E4、K/Kv、随机分母、完整OQ4及其他全部完整根仍OPEN。**
