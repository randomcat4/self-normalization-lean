# EnergyLinearTiltComparisons v1 独立最终形式审查

STATUS: CORRECT

SCOPE: FULLY_CHECKED — 同一实际线性倾斜族的七项全实参数raw/normalized有限矩比较

LEAN_STATUS: 指定服务器独立无-o目标、完整源码全部新常量传递公理审计、30模块真实import共存均exit 0，无警告。

审查日期：2026-10-22（Asia/Singapore）；正式服务器检查完成于2026-10-21T18:16:23.338127+00:00，实际HEAD为`ae4b9c3865e33e231252693e23ff0338ead29b16`。未读作者receipt、summary、ledger、checkpoint、译者票或其他审稿票；声明数量与认证以本轮实际源码及环境遍历为准。

## 冻结与版本绑定

先只读冻结声明与匿名证明，冻结CORRECT / MATH_ONLY数学票SHA256为`4ac1f3000ed8ff577a83592e228a6d9d9e4728bf84d81d3ce4ea76883e414887`。收到最终source后才读取完整实现；数学票及匿名证明保持不变。

| 文件 | SHA256 |
|---|---|
| `drafts/oq4/frozen-energy-linear-comparisons-v1.md` | `b9e406597da74e5cbb9b0f021ba536b6bc9949e358986f290d7a7cb192de97da` |
| `drafts/oq4/energy-linear-comparisons/proof.md` | `d052c6eeb1c52dc81266d4e601d301a5b21536149117d9f401c3e6807b061f30` |
| 本机`drafts/oq4/energy-linear-comparisons/EnergyLinearTiltComparisons.lean`及服务器`Shao/OQ4/EnergyLinearTiltComparisons.lean` | `f1aa93d33998f5365d236b9f96e2e04cab4e6235672a7b634988cd2330497cd4` |
| 唯一直接Shao依赖`EnergyLinearTiltLaw.lean` | `63cf342dcbe3cce728a42b283a539b8a56043f74a23f6f888ef94df378dcde78` |
| 实际μ依赖`EnergyTiltedLaw.lean` | `ea13bcf07671ee77a90910807f09f6c1c1deb95e1834f0715bcc042ab5ecbddd` |

最终源204行、11459字节。上述本机副本与服务器一致。正式检查前后全部30个OQ4源及全部32项`Shao/Basic`/`Shao/Probability`共同Lean源SHA清单完全一致。完整清单只留服务器，未改作者源、原证明、冻结、公共文件、Git或缓存。本叶不import或使用导数叶。

## 完整签名与七项语义

**实际对象与范围。** 两个Admissible section（第44–49、162–167行）完整保留概率ν、T≥0、h≥1、|s|≤T、原平方Integrable和二阶积分1，所有实t。原cube前提省略，因为只需已审第一叶内部供应的实际μ概率/闭支持；这是覆盖冻结域的加强，不是遗漏必要假设或增加新条件。没有原中心、M、K、θ、已中心化、方差下界、原ν支撑或指数/第四矩前提。所有积分均明确写在同一实际`energyTiltedLaw ν h s`或`energyLinearTiltLaw ν h s t`下；原点矩q,r没有换成原ν的β、单位二阶或方差。

1. **两种符号指数差分（第10–40行）。** 实现用exp的真实切线不等式替代匿名MVT：y≥0时由(1−y)exp y≤exp(−y)exp y=1得exp y−1≤exp y*y；y≤0时1−exp y≤−y≤exp(−y)(−y)。按符号去绝对值得全实|exp y−1|≤exp(|y|)|y|。再以明确|x|≤2h前提得到|exp(tx)−1|≤D|t||x|，D=exp(2h|t|)。此步没有global原ν支撑或参数符号假设。

2. **差函数真可积与合法积分差（第51–95行）。** `energyLinearComparison_power_integrable`从第一叶真可积的|x|^k exp(tx)以精确范数支配推出signed x^k exp(tx)真可积。对任意自然k，t=0给原x^k真μ可积；第一叶绝对幂次在t=0又给|x|^(k+1)真可积，特别包括u1。第70–74行实际证明差函数x^k(exp(tx)−1) Integrable，第75–82行才使用`integral_sub`。第85–95行用差的绝对值可积性与可积majorant，且只在实际μ-a.e.闭支持集上使用指数差分，得到通用幂次偏差界。没有用不可积总积分默认值。

3. **raw四界（第98–126行）。** 内部N1实际概率性令∫1dμ=1，通用偏差k=0、1、2分别给|L−1|≤D|t|u1、|A1−m0|≤D|t|q、|A2−q|≤D|t|r。k=1中的abs平方依法化为x²；各矩都是原μ下实际真可积矩。B3的逐点非负与第一叶加权cube真可积给0≤B3；上界对两侧真可积函数实际作a.e.积分比较，给B3≤Dr。四界完整，不假设m0=0、q=1或任何矩正下界。

4. **正L与精确倒数界（第128–136行）。** 直接调用第一叶实际L>0及下界exp(−2h|t|)≤L；用exp(−a)exp(a)=1，乘正D得到1≤LD，再合法除L得1/L≤D。没有额外L正性/误差假设，也不要求L≤1。

5. **归一化标量代数（第141–158行）。** 纯实helper在正L下用精确身份A/L−b=[(A−b)+b(1−L)]/L。三角不等式保留|A−b|和|b||L−1|，代两个误差后为[D(1/L)]τ(v+|b|u)。因D,τ,u,v非负及1/L≤D，输出精确D²τ(v+|b|u)。helper的误差输入是纯代数条件，实际主定理将本模块已证raw界传入，不是重新假设待证概率比较。

6. **normalized三界（第170–200行）。** 主定理内部取得raw四界、正L、倒数界、实际u1/q/r非负及第一叶μ_t真实三矩可积/积分比身份。均值以A=A1、b=m0、v=q、u=u1代入，得到精确D²|t|(q+|m0|u1)。二阶先用真实q_t=A2/L，再以b=q、v=r代入；q≥0令|q|=q，得到D²|t|(r+qu1)。第三先用真实r_t=B3/L，以B3≤Dr及1/L≤D两次乘非负数，得到D²r。两个额外项均未丢失；没有以中心化二阶、原ν矩或形式variance替换实际矩。

七项对应关系在完整实际声明中为：`energyLinear_raw_comparisons`返回前三偏差及(0≤B3∧B3≤Dr)，`energyLinear_normalized_comparisons`返回m、q_t、r_t三项。公开声明不必机械一项一条，但数学内容恰为冻结七式；独立`#check`已经核对其完整签名。

**真可积性与边界。** μ下id、平方、绝对立方及u1均从第一叶t=0的真实可积函数供给；新通用幂次引理另公开供应所有signed powers。μ_t下三矩由第一叶实际moments定理供给，不作附加前提。t=0时D=L=1、A1=m0、A2=q、B3=r及μ_0=μ，偏差界均0，第三矩比较为等式。正负t、h=1、T=s=0、零点及±2h原子、退化μ、不对称和原ν无界支撑全部保留。无除q、r、m0，故零矩情形不被排除。

## 独立服务器执行及全新常量

使用正常`tools/server.py` broker，先source固定activate.sh再cd指定worktree；三个正式验证均指定服务器`taskset -c 0-3`、一进程顺序运行、无`-o`，不发射目标olean、不重编旧target、不写共享缓存。无不确定调用重放或旁路回退。

```text
COMMON_BASIC_PROBABILITY_SOURCE_COUNT=32
TARGET_CHECK_EXIT=0
SOURCE_ALLNEW_AUDIT_EXIT=0
ALL_NEW_DECL_COUNT_NO_NAMESPACE_FILTER 10
ACCEPTED_30_MODULE_COEXIST_EXIT=0
ALL_30_OQ4_AND_BASIC_PROBABILITY_SOURCE_HASHES_UNCHANGED=True
```

实际无-o目标为`lake env lean Shao/OQ4/EnergyLinearTiltComparisons.lean`。独立完整source审计将服务器最终source直接接附录送`lake env lean --stdin`，核对源码全部8个显式声明及首叶可积/矩/normalizer接口。随后遍历`env.constants.toList`，仅以`env.getModuleIdxFor? declName`为`none`选择全部新项，对每项`Lean.collectAxioms`并拒绝非标准三公理；无namespace、root或声明名过滤，实际数量不依赖作者报数。

实际枚举10项：

```text
Shao.OQ4.energyLinearComparison_abs_exp_sub_one
Shao.OQ4.energyLinearComparison_exp_sub_one_bound
Shao.OQ4.energyLinearComparison_power_integrable
Shao.OQ4.energyLinearComparison_power_deviation
Shao.OQ4.energyLinear_raw_comparisons
Shao.OQ4.energyLinearComparison_reciprocal_bound
Shao.OQ4.energyLinearComparison_div_deviation
Shao.OQ4.energyLinear_normalized_comparisons
Shao.OQ4.energyLinearSecondNumerator.eq_1
Shao.OQ4.energyLinearComparison_power_integrable._simp_1_1
```

前8项是实际显式定理，第9项在导入名称下新生成，亦全量包含；它们的传递公理均为`[propext, Classical.choice, Quot.sound]`。最后simp helper只依赖propext。没有sorryAx或任何非白名单公理，没有按新root名漏审导入名helper。

同一Lean输入真实import全部30模块（均`Shao.OQ4.`前缀）：DelayedRecurrence、OvershootSum、OvershootMoment、VarianceScaling、Foundations、CosineCoefficients、KilledCosine、OccupationPayment、AveragedResidual、KilledKernel、KilledIteration、KernelRecurrence、CosinePowers、KilledPathLaw、KernelAbsorption、BoundaryOccupation、KilledBlockBounds、IntervalConcentration、LaplaceTail、LaplaceGenerating、FiniteSurvivalLaplace、ReflectedSurvival、SpitzerKernelBounds、TruncatedEnergy、EnergyTiltedLaw、EnergyLogNormalizer、EnergyE1Bounds、EnergyLinearTiltLaw、EnergyLinearTiltDerivatives、EnergyLinearTiltComparisons。额外检查两个旧closedUpper可测性名称和新主要偏差/归一化接口可用，共存成功。

本机及服务器目标禁用token扫描均0命中：`sorry`、`admit`、`axiom`、`unsafe`、`native_decide`、`sorryAx`。三份正式日志均0 warning/0 error；完整原始日志仅在服务器`repro_outputs/oq4-energy-linear-comparisons/independent-review-v1/`：

| 日志 | 字节 | SHA256 |
|---|---:|---|
| `target.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source-allnew-audit.log` | 12615 | `7f6d645e75a96d99fbf32cf7053900203408c0b87d468a558b64e922b219f721` |
| `coexist-30.log` | 3557 | `aa7cb3e046b42428c6f3def3afeef4098f68e9a1163ab932103cd802fea3bbec` |

## 裁决与边界

没有关键数学或形式缺口。真实七项比较、所有积分差真可积性、内部正L/倒数界、精确D²及两个归一化附加项完整覆盖冻结接口；省去原cube只构成合法加强。

**只认证有限比较叶。共同正方差窗口、端点异号、θ存在/选择、精确中心化、所选θ处log界及最终E2共同常数未证；E2、E3、E4、K/Kv、随机分母、完整OQ4及其他全部完整根仍OPEN。**
