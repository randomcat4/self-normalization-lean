# U16d 独立声明、来源与静态接口审查

STATUS: CORRECT

唯一审查 lease 1，仅拥有本新报告及服务器 statement-review.md；不修改 scope、实现、旧报告、共享文件或缓存，不 spawn，不运行 Lean/API probe/build。并非独占代码库，保留他人编辑。尚无本单元实现；先只读取冻结 Lean fence 的完整公开定义体及完整目标类型，独立翻译并先落盘，尚未读 scope 正文或本次作者数学路线。

## 第一阶段：完整定义体和完整类型盲译

输入 fortieth-unit-scope.md，SHA256 `54a2a3f9a6da1e56a1ff07e612c43c43088c32dc4b4b48f207e93db1449a6dbf`。

`centeredNormalLogMGF` 对任意实数测度 mu 和实参数 q/a/v/s，定义标准 Real.log 作用于真实 Bochner 实积分 ∫exp(centeredNormalProjection(q,a,v,s,x))dmu。定义没有 integrability 或 normalizer 正性门，故本身是 Lean 总函数；定理必须真实给可积和正性，不能依赖不可积实积分或 log0 的总化。既有投影与二次型的精确 actual 定义将在盲译后核对，不能仅由名称推断正态性或实际矩绑定。

`exists_centeredNormalLogMGF_cubic_upper`：输入真实实数概率测度 mu，同一 mu-AE |x|≤4+sqrt10，再输入实数 q/a 并要求真实 E(normalValue)=q、EX=a。之后存在同一实 C>0和delta>0，使对全部实 v/s，只要 |v|+|s|≤delta，就同时有：真实 x↦exp(centeredNormalProjection q a v s x) 对 mu 的 Integrable；其真实积分严格正；实际 centeredNormalLogMGF≤normalTangentQuadratic(mu,v,s)/2+C(|v|+|s|)³。C/delta选在全部 v/s之前，窗口是包含0的闭l1球，系数1/2及三次l1范数不能改变。

类型没有 S/D/行列式正性或非退化门，没有 q>0、ell、阶段J或有限支撑门。一般有界概率，包括退化单点律，均需适用；v=s=0必须得到真实exp0可积、积分1、log1=0以及实际Q0=0，而非从除0/总化产生结论。两个均值门保持同一 mu/中心，不能把实际积分二次项换成任意协方差矩阵。

独立初步数学检验：若 actual 投影确为v(Y−q)+s(X−a)，有界X给同一 M>0，所有参数下AE |投影|≤M(|v|+|s|)。统一delta可使整球内AE |投影|≤1，三阶指数余项积分后应为O((|v|+|s|)³)；真实均值0和实际二阶矩Q给normalizer≤1+Q/2+三次项，再在真实normalizer>0后用logZ≤Z−1即可得所需上界。此仅是从完整类型所作可行性初判，actual矩接口、真实可积/正性门、精确Real.exp_bound系数与公开导入仍待后核。

本段先保存，再读scope/R1、已接受实际前置和固定库。根A/B/C/D、实际Legendre/Fenchel/Chernoff、紧族统一及完整LLT/hW均保持OPEN。

## 第二阶段：冻结范围、真实来源与实际定义

盲译先落盘后才读取完整scope、真实R1及实际已接受前置/固定库。scope本地及实际远端 SHA256 均为 `54a2a3f9a6da1e56a1ff07e612c43c43088c32dc4b4b48f207e93db1449a6dbf`；拟CenteredLogMGF.lean，仅导入NormalTangentMoments、Complex.Exponential、SpecialFunctions.Log.Basic。一个公开定义、一个完整目标，尚未实现；本报告不把静态可行性当作内核检查。

真实只读R1路径 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，本次直接核350–371行。351行K_c(s,t)=log E exp(s(Y−q)+t(X−a))与当前定义一致，参数字母v/s只重命名，没有负相位或虚数单位。370–371行写的是实际Legendre率I的逆协方差二次展开，不是当前K_c上界的逐字公式；当前目标是由有界性导出的标准充分前置引理，二次项使用协方差而非其逆。它不能单独登记为实际I的三次minorant或完整(16)/(17)。

指定服务器实际 NormalTangentMoments.lean SHA256 `8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1` 全部127行已只读核对相关语义：18–19行actual centeredNormalProjection=v*(normalValue x−q)+s*(x−a)，normalValue=8x−x²；21–28行在真实hb概率门下给真正MemLp2；30–47行在同一mu真实两个均值门后给∫projection=0，先建立被积项可积再消费积分线性；49–87行同样先有真实平方/混合项可积，给∫projection²=actual normalTangentQuadratic。当前定理的hb/hq/ha正好提供这些完整前提。

actual NormalTangentGaussian.lean SHA256 `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39`19–22行的Q确为Var(Y)*v²+2Cov(Y,X)*v*s+Var(X)*s²，顺序和交叉系数正确。hb下的真实二阶矩绑定排除了variance.toReal不可积总化；Q=∫projection²≥0，不需正定、S>0或det>0。当前是任意有界概率mu，包括非原子或退化mu；不擅自限制为有限stage或实际π_J，也未断言给任意q/a都存在符合均值的mu。

## 第三阶段：统一参数球、真可积/正性和完整数学检验

令B0=4+sqrt10>0。在同一个hb的AE集合内，有|X|≤B0、|Y|=|8X−X²|≤8B0+B0²。因此例如选择

`K=1+(8B0+B0²+|q|)+(B0+|a|)`，

则K>0，并在同一个与v/s无关的AE集合内同时有|Y−q|≤K、|X−a|≤K。这个显式共同界不需要非空支撑提取、正协方差或逐方向紧性选择。对全部实v/s、L=|v|+|s|≥0，由三角与乘积绝对值得真实投影f=v(Y−q)+s(X−a)满足|f|≤K L。

一次性选择delta=1/K>0、C=K³>0，均在全部v/s之前；当L≤delta时，正K给AE |f|≤Kdelta=1。闭球边界同样是≤1，正好满足实际指数余项API。没有从旧固定方向u窗口或逐v/s常数推出错误的共同球。

先建立真实可积：对任意固定v/s，f是实多项式连续函数；exp f、f、f²、|f|³及1+f+f²/2+K³L³都连续。hb和真实概率使这些函数各自真Integrable，可用已接受实际 integrable_continuous_of_fixed_bounds；或者球内用exp f≤exp1加可测性给exp真可积。这里必须是实际实指数而非复相位模1，不能用特征函数的单位模界代替。平方可积也可直接消费实际projection MemLp2/二阶矩前置。

由于真实mu是概率，NeZero mu实际实例成立。只有在exp f的真Integrable之后，才用实际 integral_exp_pos 得Z=∫exp f>0。因此Real.log取的是真正正normalizer，既不是不可积Bochner积分返回0，也不是log0=0或log负值的总化。有限mu上这些被积项的积分均为有限实数。

在同一AE |f|≤1后，实际Real.exp_bound取n=3，有限和为1+f+f²/2，系数为(n+1)/(n!*n)=4/(6*3)=2/9，故

`|exp f−(1+f+f²/2)|≤(2/9)|f|³≤|f|³≤K³ L³`。

这是对任意有符号实f的界，不要求f≥0，不使用不适用的exp_bound'正变量版，也没有遗漏n>0门。于是AE exp f≤1+f+f²/2+K³L³。在比较积分之前已经建立左右两侧真正Integrable，才能用integral_mono_ae；再在真实积分线性门下逐项算出

`Z≤1+∫f+(∫f²)/2+K³L³=1+Q(mu,v,s)/2+C L³`。

常数积分为常数来自同一个mu的概率质量1；真实中心0和实际二阶矩Q从同一q/a/mu前置传入，不能混成另一mu或自由S/T/b。所有多项式、绝对值余项或其差/范数若用于积分估计，也都先有真可积；本目标不需Fubini或DCT。

最后在已经得到Z>0后，真实Real.log_le_sub_one_of_pos给logZ≤Z−1，从前式准确得到公开上界Q/2+C L³。它不需要预先证明Z≥1或Q严格正；实际Q非负由真实平方积分自动成立。不能把该上界升为双向三次展开、真实逆Hessian或Legendre下界。

边界检查：v=s=0时f恒0、exp f恒1，真概率给Z=1、logZ=0，actual Q(mu,0,0)=0且三次项0。若mu退化为单点且q/a是真实均值，则f=0 μ-AE、Q=0，仍由统一K≥1给正C/delta，不需要除Q或除方差。一般退化方向也一样，没有隐藏非退化归一化。q/a任意有符号真实均值只进入有限绝对值界；hb可取等号，参数球可取边界；输出量词保持同一C/delta在全部v/s之前。

## 第四阶段：实际固定API、公开导入与缓存

全部检查仅指定服务器只读源码/既有缓存/版本，无Lean/#check/API probe/build。实际固定Mathlib HEAD为 `807d3836b165983210ee2ecf3cd28f239436949c`，toolchain `leanprover/lean4:v4.36.0-rc1`；lean-toolchain SHA256 `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest.json SHA256 `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。

- `Mathlib/Analysis/Complex/Exponential.lean` SHA256 `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146`517–521行真实 `Real.exp_bound {x:ℝ}(hx:|x|≤1){n:ℕ}(hn:0<n)`，结论是实绝对余项≤|x|^n*(n.succ/(n.factorial*n))。n3系数明确是实数2/9而非自然除法0；上文已先提供同一个AE集合上的小球门。
- `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` SHA256 `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97`16–18行明确其全函数扩展log0=0、log(−x)=logx；307–310行真正 `Real.log_le_sub_one_of_pos`要求x>0。目标显式正normalizer和上文证明顺序真实消费此门，不借总化。
- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` SHA256 `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`792–798行integral_exp_pos要求[NeZero mu]和真实Integrable(exp f)。同文件662–667行integral_mono_ae要求左右两侧Integrable及AE逐点≤；前述路线真实提供，未把总化积分单调性误当无条件。
- `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` SHA256 `00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b`87–88行实际IsProbabilityMeasure.neZero实例提供NeZero mu，零测度被真实概率排除。
- 实际 `Shao/OQ3/InverseTilt.lean` SHA256 `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`26–34行 integrable_continuous_of_fixed_bounds 的完整接口正是mu概率、hb、f全局连续→真Integrable f；实际证明先在紧Icc上取连续有界，再用Integrable.of_bound和同一hb的AE支撑门。它不是假定任意全局连续函数在任意概率都可积。

三个直接import的既有olean实际存在：NormalTangentMoments为301880字节、Complex.Exponential为210592字节、Log.Basic为264384字节。实际公开导入图无缺失源码；Bochner.Basic可由NormalTangentMoments→NormalTangentGaussian→Lebesgue.Integral→Haar.Unique→Group.Integral公开到达；概率NeZero实例沿RegularCovariance/Variance/Covariance/Independence/ConditionalProbability的真实公开路径可见。Real.exp_bound与log接口由两个直接Mathlib import公开可见，不需额外未声明缓存。

当前实际Shao前置闭包为10份，全部沿已接受源码链读取并核hash如下：

| 实际前置 | SHA256 |
| --- | --- |
| NormalTangentMoments | `8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1` |
| NormalTangentGaussian | `d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39` |
| RegularCovariance | `0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853` |
| FiniteStageMeasure | `1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` |
| InverseTilt | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| AtomicMeasure | `59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39` |
| SummableAtoms | `0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` |
| FiniteConstraints | `800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0` |
| SourceStarter | `0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d` |
| PositiveRate | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |

没有消费U16c泛型I结论作为真实率生产者，也无未来common模块、实际Legendre/Fenchel或Chernoff代码依赖。namespace Shao.OQ3、open MeasureTheory、noncomputable section足以解释冻结完整类型中的现有名字和真实积分记法；没有默认volume、矩阵范数或额外实例缺口。尚未实施，故不声称任何新目标/Audit的编译成功。

## 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 完整定义是源中真实中心实对数矩母函数；目标同时输出真exp可积和严格正normalizer，排除了实积分/log总化漏洞。实际前置绑定同一mu/中心的真均值0及实际二阶矩Q，统一共同特征界给在全部v/s之前的正C/delta，Real.exp_bound n3的准确2/9余项在共同AE小球内可积比较，再于Z>0后用logZ≤Z−1得到所需Q/2+三次上界。闭参数球、零参数及退化mu均有效，无额外协方差正定假设。实际来源、完整量词、公开API与缓存均匹配，未发现需要修订的声明、数学或静态环境缺口，可进入实现；本票不是内核验收。

非声明：未生产真实Legendre率/Fenchel下界、I三次minorant、逆Hessian、紧倾斜族统一C/sqrt n、Chernoff(16)/(17)、远区gap、完整层和(19)、LLT、hW、全局唯一性、最优性或新颖性。根A/B/C/D、实际Legendre/Fenchel/Chernoff与紧族uniform均保持OPEN。未读未来实现/作者API笔记，未修改scope/实现/旧票/共享文件/缓存，未spawn、Lean/probe/build。
