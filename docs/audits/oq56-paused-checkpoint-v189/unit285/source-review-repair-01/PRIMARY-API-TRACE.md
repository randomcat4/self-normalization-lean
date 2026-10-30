# repair01 独立受影响主接口审查

旧版39条主接口/11原文件的完整HEAD/body/环境证据按 exact source-review-01/PRIMARY-API-CONTEXTS.json 复用（SHA256 5e7524c4ec5b37dbf47e5e082dd9583227430578d3730f5ce09c983a57be053b，71497B）。本轮完整重读新265LF源码、两proof227LF和完整diff，并重读 integral_add、Integrable.add 的完整接口/证明与相关环境。两份新增原始主文件均完整阅读。

| 实际接口 | 原始位置 | 当前行与条件 |
| --- | --- | --- |
| MeasureTheory.integral_add | unit284/parent-api-02/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:239-242 | 新61-67两次显式指定原theorem隐式f/g；函数严格等于当前被积lambda，两份Integrable证明仅作函数点运算定义性归约。 |
| MeasureTheory.Integrable.add | unit284/parent-api-01/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:403-423 | 当前63/66传入已有可积函数的加法，域仍Omega/nu、值域Real；没有把未证可积性加入前提。 |
| Measurable.norm | parent-api-06/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean:233-243 | 新113-114的alpha=Real、beta=iota->Omega、f=S；原接口只要求域MeasurableSpace，值域Real的NormedAddCommGroup/MeasurableSpace/OpensMeasurableSpace均已存在。 |
| Real.norm_eq_abs | parent-api-07/Mathlib/Analysis/Normed/Group/Real.lean:50-62 | Real norm定义为abs，原等式由rfl证明，只转换norm(Sx)可测性到abs(Sx)可测性。 |

Metric.lean完整1-262行已读：SHA256 66e4b70ad7283f621495ad96d0329ba095bb71081a1c72a9bd25bee8f73e361e，10439B。
Real.lean完整1-143行已读：SHA256 235dd178401b9964e081ab97d238fd440807adc0f82e8d2cf46015278a13bd51，4373B。
完整精确原文/环境/文件绑定见CHANGED-PRIMARY-API-CONTEXTS.json。两条新增明确主接口连同旧39条，共41条记录/13原文件。

加法顺序修订直接针对旧native73完整actual typed diagnostic，以add_comm改变两边相加顺序。两处change仅展开原Set membership定义后再作原abs/linarith运算，没有新增数学接口。原事件、Chernoff门槛、均值与二阶矩保持。没有新import/option、Omega拓扑/StandardBorel或隐藏MGF合同。当前源码是否成功elaborate仍无新机器证据。
