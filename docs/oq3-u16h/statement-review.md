# U16h 独立声明、来源与静态接口审查

STATUS: CORRECT

唯一lease1，只拥有本新报告及remote run/statement-review.md。不独占代码库，保留他人更改；不修改source/scope/receipt/旧票/shared/cache，不spawn、Lean/probe/build/commit或下载raw完整日志。以下第一阶段先仅提取冻结Lean fence的完整公开定义体和三个完整类型，独立盲译并持久化，当时尚未读scope正文/作者路线或本次实际库。初次保存2851字节，SHA256 4c3da095ed2c0acd482ea756394c66a261ca93aab565708f6338a6532ed8fa9b；随后按阶段核对，当前仍无本单元实现。

## 第一阶段：完整定义体和三个完整类型盲译

输入forty-fourth-unit-scope.md，SHA256 `826ea1ced6f86e64e46962d685b75a079c85f0ecdbe91ea9288451ff177ff2a7`。

`centeredSampleProjection(q,a,v,s,n,z)` 的完整body是对全部i:Fin n，把真实已定义centeredNormalProjection(q,a,v,s,z_i)相加，输出实数。n0为空和0，不含除n/sqrt n。q/a/v/s均任意实，不能仅凭centered命名假设q/a是真均值；既有单点projection的实际body须下一阶段核。

`iid_centeredSample_tilt`：输入真实概率mu、同mu-AE |x|≤4+sqrt(10)、任意实q/a/v/s和任意自然n，输出三重合取：(1)真实样本exp(上述完整和)在Measure.pi(fun _:Fin n=>mu)上真Integrable；(2)其真实积分恰为同mu单点exp(centeredNormalProjection)积分的n次幂；(3)整个实际n产品被样本和倾斜的真实measure，等于每坐标同一个真实单点mu.tilted(centeredNormalProjection)的n产品。需真实单点/样本Z>0，不能用不可积tilt总化0或丢失归一化；n0的产品单位律/Z^0=1也须核。

`centeredProjection_tilt_eq_quadratic`：同一真实概率和AE有界输入，任意q/a/v/s下，mu被实际centeredNormalProjection倾斜，作为测度恰等于mu被((8v+s)x+(-v)x²)倾斜。q/a只可能贡献常数shift，但须用真实定义核代数和合法倾斜不变性，不能假设均值或先猜未核congr API。

`iid_centeredSample_event_bound`：同一真实概率/AE有界/任意q/a/v/s/n，任意可测路径事件E、任意实c，输入对每个z∈E有c≤真实sample projection。输出原真实n产品.real(E)≤exp(n*actual centeredNormalLogMGF(mu,q,a,v,s)−c)乘真实单点projection tilt的n产品.real(E)。函数下界是输入hlower，未声称任何特定尾事件满足；exp符号为−c。不能log0、把lognormalizer当自由假设，或在ENNReal∞转real后得到虚假不等式。

独立初判：AE有界基准应使任何固定实参数的连续单点exp真可积，不可由small-ball LogMGF目标直接扩大全参数。真实Z>0后有限iid因子化给样本Z=Z^n>0、真实产品倾斜；事件上exp(F)≥exp(c)给倾斜概率≥exp(c)原概率/Z^n，所以目标方向正确。n0/空E/c有符号/任意非均值q/a均需后验实际API和数学核查。当前仅盲译落盘，不预判CORRECT；根A/B/C/D、概率Chernoff、完整(19)/LLT/hW仍OPEN。

## 第二阶段：冻结定义、真实既有定义和来源

本地forty-fourth-unit-scope.md与remote run/scope.md实际SHA均为 `826ea1ced6f86e64e46962d685b75a079c85f0ecdbe91ea9288451ff177ff2a7`。完整definition body只是Fin n上单点actual projection之和；三个完整type均无hq/ha真实均值门、无v/s小球、无n>0、无原子/阶段/矩正定或参数符号假设。显式hb和真实概率足以保证所需任意固定实参数可积，不能自行加这些额外前提或靠名字默认中心。

actual NormalTangentMoments.lean18–19：centeredNormalProjection(q,a,v,s,x)=v*(normalValue(x)−q)+s*(x−a)，normalValue=8x−x²。actual CenteredLogMGF.lean11–12：centeredNormalLogMGF=Real.log(∫exp(centeredNormalProjection)dmu)。这是对真实normalizer取标准实log，定义本身会总化，当前目标必须以另证Z>0保证普通log语义；没有已给真实均值也不妨碍指数倾斜和本次类型。

真实只读R1 `C:/game/shao/current/oq3/proofs/r1/report.md`，SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，已实际读350–365。该处定义中心二元logMGF，对iid样本乘指数并倾斜，再结合事件约束和Fourier层估计。H给其实际产品测度恒等式和明确hlower下的一般指数事件比较，既是标准充分变测度基础，也没有把式(16)所有试验符号/Legendre优化/共同层界都声称已闭合。

按授权实际读已接受SampleChangeOfMeasure.lean28–84，SHA `d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134`，其中先真单点/产品可积、normalizer正，再Measure.pi_eq可测矩形与restrict_pi_pi/Fubini证明实际iid倾斜。这只用作已接受标准API模式核验；H imports不含该模块，也不能借其原子w/HasSum前提代替本目标一般mu的可积义务，未声称该模式新颖。

## 第三阶段：任意参数的真实可积与normalizer

actual `InverseTilt.lean`26–34的public `integrable_continuous_of_fixed_bounds (mu)[IsProbabilityMeasure mu] hb (f:ℝ→ℝ) (hf:Continuous f)` 输出真Integrable f mu。它用实际AE区间支持和紧区间连续norm有界再Integrable.of_bound，完全不要求原子性、q/a是均值或小v/s。本次实际H闭包经NormalTangentMoments→NormalTangentGaussian→既有基座可见该public theorem；不需要且不含U15a TiltedMeasureDomination模块。

固定任意q/a/v/s，f(x)=centeredNormalProjection(q,a,v,s,x)是实际二次多项式，exp(f)全局连续；上述接口给hf真Integrable。mu真实概率给NeZero，实际Bochner.Basic792–798 `integral_exp_pos hf` 给Z=∫exp(f)dmu>0，Z是真有限实数，不能通过integral_undef或exp/log总化定义假装正。对第二目标的g(x)=(8v+s)x−v*x²同样用这个一般连续可积接口给hg，不能错误调用没有在H imports闭包内的U15a，也不能把U16d仅小球的上界扩到所有参数。

对任意n，P_n=Measure.pi(fun _:Fin n=>mu)真实概率、有限、NeZero，SigmaFinite门齐备。真实F(z)=∑f(z_i)，Real.exp_sum给逐点exp(F)=∏exp(f(z_i))。actual `Integrable.fintype_prod` 对每坐标hf和SigmaFinite提供真实样本exp Integrable，然后才消费有限积积分Fubini公式；实际integral_fintype_prod_eq_pow给∫exp(F)dP_n=Z^n。因为Z>0，Z^n>0对所有n成立，n0时恰1。不能只读一个总化Fubini等式便宣称样本真可积。

single与sample都先有hf/hF及真实基准概率，actual isProbabilityMeasure_tilted因此给mu.tilted f、P_n.tilted F都是真概率；产品Q_n=Measure.pi(fun _:Fin n=>mu.tilted f)也真概率。所有实际测度总质量有限，后续.real不是∞.toReal=0。n0产品是唯一空路径上的单位概率，不是零测度；F0=0、expF0=1、Z^0=1，真实normalizer全保留。

## 第四阶段：真实iid产品倾斜measure等式

首目标第三项可在上述真可积/正Z后严格证明。对每个坐标ν=mu.tilted f、共同密度h(x)=exp(f(x))/Z≥0；真实样本密度exp(F(z))/Z^n=∏h(z_i)，来自exp_sum、prod_div_distrib和Fin n的card。所有归一化常数都明确是同一个mu/f的Z及Z^n，不能漏掉乘积normalizer。

actual `Measure.pi_eq`279–283输出方向是 `Measure.pi μ = μ'`，而冻结目标是P_n.tilted F=Q_n；未来实现必须先取对称或对其结论取.symm，不能逐字复制旧U9b原方向再期望类型自动相同。这是合法API选择，不改变任何完整type或构成声明阻塞。

对坐标可测矩形univ.pi A，actual tilted_apply'给样本tilt真实lintegral密度；substitute sample normalizer Z^n和上述密度逐点积等式。actual restrict_pi_pi把P_n的矩形限制化成∏(mu.restrict A_i)。每个受限坐标上h真Integrable：hf.integrableOn再div_const Z；这些受限测度有限/SigmaFinite，Integrable.fintype_prod给受限密度乘积真Integrable。h的非负性由exp>0和Z>0给出，才可用ofReal_integral_eq_lintegral_ofReal把真实lintegral改成ofReal实积分。

再用actual integral_fintype_prod_eq_prod、各非负积分的ENNReal.ofReal_prod_of_nonneg，和逐坐标 tilted_apply_eq_ofReal_integral'，得到矩形上真实P_n.tilted F与Q_n质量相同，Measure.pi_eq给整个measure相同。所有Fubini/实复合转换前的真实可积门都有可用publicAPI；没有假设mu是原子测度或遗漏矩形可测、限制测度有限、normalizer非零条件。n0空积=1和空矩形为全空路径空间，同一唯一性论证成立。

## 第五阶段：常数shift与实际二次倾斜

逐点展开真实normalValue/projection得f(x)=(8v+s)x+(-v)x²−(vq+sa)。令g(x)=(8v+s)x+(-v)x²，b=−vq−sa，则f=g+(fun _=>b)是函数外延后的真实环等式。hb给exp(g)真Integrable，mu概率给NeZero及Zg>0，先用isProbabilityMeasure_tilted建立nu_g=mu.tilted g真概率。

actual `tilted_tilted hg (fun _=>b)` 给(nu_g).tilted const_b=mu.tilted(g+const_b)；actual `tilted_const nu_g b` 在该真实概率门下给左侧=nu_g。再以f=g+const_b的真实函数等式替换，即得冻结第二目标。常数指数在nu_g有限概率上当然真可积且正normalizer；不是只凭“忽略常数”口号。无需猜未核tilted_congr API，函数外延/代数等式与实际现有tilted_tilted、tilted_const足够；scope路线提到congr并非冻结类型必要依赖。

v/s/q/a都可有任意实符号，v=s0时f=g=0和零shift，actual tilted_const给原mu，未除这些参数。常数shift虽从倾斜law中消失，却不可从第三目标的logMGF系数随意丢掉：logZ_f=logZ_g−vq−sa，冻结目标始终使用actual centeredNormalLogMGF，不错误把它替换成未中心化normalizer。

## 第六阶段：事件比较、实log与所有边界

首目标已给真实P_n.tilted F=Q_n及样本normalizerZ^n>0。对明确可测E，actual tilted_apply_eq_ofReal_integral'给Q_n(E)=ofReal(∫_E exp(F)/Z^n dP_n)。密度在限制measure上真实Integrable（hF.integrableOn.div_const），且非负，实积分非负；因此toReal_ofReal在该非负门下得到Q_n.real(E)=∫_E exp(F)/Z^n dP_n。P_n/Q_n本身真实概率保证两事件ENNReal质量有限，不把top.toReal的0作为事件质量。

hlower是所有z∈E的显式点态输入，实exp单调给exp(c)≤exp(F(z))。P_n.restrict E有限，常数exp(c)真可积，exp(F)受限真可积；actual setIntegral_mono_on需要并能同时消费这两IntegrableOn、hE和点态界，得到exp(c)*P_n.real(E)≤∫_E exp(F)dP_n。actual integral_div与真实归一化等式给右边=Z^n*Q_n.real(E)。exp(c)>0、Z^n>0，正量交叉乘法/乘exp(−c)可得P_n.real(E)≤Z^n*exp(−c)*Q_n.real(E)，方向与冻结目标一致。

先证Z>0之后才使用actual Real.exp_log hZ及Real.exp_nat_mul/exp_sub，得Z^n*exp(−c)=exp((n:ℝ)*logZ−c)。actual centeredNormalLogMGF恰logZ，故最后系数正确。没有用log0/负normalizer、没有除P_n(E)/Q_n(E)或n，也不要求E正概率。standard real log在此确实处于正域，非使用其总化值。

边界：E空时hlower真空且两质量0，任意c合法；c任意实不妨碍exp(c)>0；v=s0时Z=1、logZ=0，hlower按实际F=0限制非空E时c≤0，比较正确；n0时F0=0、Z^0=1、空产品真实概率，E若含唯一空路径则hlower迫使c≤0，若不含则零事件，目标两种都成立。q/a任意非均值仍可应用，无真实均值/方差或small-ball条件隐藏在事件法则内。

真实sample展开是v*normalDeviation q z+s*((∑z_i)−n*a)。actual SampleBoundary.tangentDeviation q的中心是n*q/4，不能把tangentDeviation a误当n*a；仅a=q/4时可进一步绑定。本目标未导出任一尾事件hlower，未来针对正负尾必须另证试验s符号并验证真实事件不等式。当前不直接完成sourceTail、负层概率或式(16)/(17)。

## 第七阶段：实际public API、导入与静态环境

冻结imports恰CenteredLogMGF、SampleBoundary、Mathlib.MeasureTheory.Measure.Tilted、Mathlib.MeasureTheory.Integral.Pi；namespace Shao.OQ3/open MeasureTheory/open scoped BigOperators/noncomputable section使完整definition中∑和全部类型可见。路径定义已有Shao.Path n=Fin n→ℝ，无默认volume积分、额外Matrix范数或新MeasureSpace实例门。此声明没有n的除法或sqrt，也不需Levy/root公共char/新cache。

实际InverseTilt26–34 public一般连续积分接口可在H实际闭包使用；U15a并不在闭包，本审查未将它算作可调用前置。actual Integral.Pi67–71的Integrable.fintype_prod需要每坐标真Integrable及SigmaFinite；106–108 integral_fintype_prod_eq_prod和119–122 integral_fintype_prod_eq_pow只给积分等式，不能单独免除可积义务。Integral.Pi显式public import Integral.Prod，已实际读其源码与现成olean；两坐标/有限积API可见。

actual Constructions.Pi279–283 pi_eq方向/坐标SigmaFinite门、417–421 restrict_pi_pi、311–313产品概率实例已核；有限概率和限制测度均满足相应SigmaFinite。Tilted101–124的apply/eq_ofReal_integral'实际上有不可积时0分支，所以本次另证hf/hF绝不可省；126–136概率构造用NeZero/hf及integral_exp_pos；251–252 tilted_tilted只要第一个exp真Integrable即可和任意后potential复合，74–75 tilted_const必须在真实概率下使用。均是实际MeasureTheory公开名，不假设一个不存在的pi_tilted封装。

Bochner.Basic737–742 ofReal_integral_eq_lintegral_ofReal明确要求真Integrable和AE非负；792–798 integral_exp_pos要求NeZero和真实exp可积；295–297 actual积分除常数API名是integral_div。Bochner.Set745–759的setIntegral_mono_on包含两个IntegrableOn、可测E和E上点态界，三门上文均补足。Log.Basic59–61 Real.exp_log严格要求Z>0，不是对所有实Z无条件成立。所有这些类型均在指定服务器实际只读核，未做Lean/API探针。

实际两个Shao直接olean已存在：CenteredLogMGF 392960字节、SampleBoundary 594096字节；两个Mathlib直接olean已存在：Tilted 78048字节、Integral.Pi 63624字节。实际Tilted SHA `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f`、Integral.Pi `43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9`、Constructions.Pi `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`、Bochner.Basic `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`、Bochner.Set `e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75`、Log.Basic `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97`，所需现成olean均只读核有。

## 第八阶段：17项实际Shao闭包与版本绑定

由两个实际Shao direct imports递归只读得到17项（15 OQ3+2 shared），全部source实际SHA和现成olean已核；没有U15a/U16g/SampleChangeOfMeasure实现依赖，后者仅授权参考旧标准证明模式。

|实际模块|SHA256|
|---|---|
|Shao.Basic.FinitePath|898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb|
|AtomProjection|0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22|
|AtomicMeasure|59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39|
|CenteredLogMGF|1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4|
|FiniteConstraints|800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0|
|FiniteNormalSpan|0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de|
|FiniteStageMeasure|1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1|
|InverseTilt|c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811|
|NormalTangentGaussian|d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39|
|NormalTangentMoments|8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1|
|PositiveRate|8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b|
|RegularCovariance|0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853|
|ResonanceArithmetic|cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b|
|SampleBoundary|7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2|
|SourceStarter|0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d|
|SummableAtoms|0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b|
|Shao.Probability.FiniteIID|d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b|

实际server worktree `/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3`；toolchain leanprover/lean4:v4.36.0-rc1，lean-toolchain SHA `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`，lake-manifest SHA `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`，实际mathlib HEAD `807d3836b165983210ee2ecf3cd28f239436949c`，只读核版本/缓存。实际CenteredSampleTilt.lean尚未创建；没有当前实现/receipt/build/Audit可判定。未读下一I候选或未来作者notes，scope中G排队状态只作冻结历史保留，实际G已被lead完整接受。

## 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 冻结sample定义与三个完整类型数学成立，真实单点projection/logMGF与任意q/a和全实v/s的量词一致。已有public一般连续AE有界支持积分接口直接给所有固定参数真exp Integrable，非小球扩张且不依赖未import的U15a；真实Z>0后有限积可积/Fubini给Z^n>0及实际iid产品倾斜测度等式。真正可测矩形限制可积与有限归一化门充足，pi_eq方向可取对称而无签名修复。常数shift通过真实quadratic tilt概率下的tilted_const、tilted_tilted及函数外延恒等式严格消去，不猜congrAPI。事件hlower经真可积的指数比较和正域log/exp恒等式给正确−c系数，保留空E/n0/v=s0/c有符号/零事件质量而不除这些量。静态import/publicAPI/17真实前置与缓存无声明阻塞。

这是完整独立声明/source/API门CORRECT，并非尚未存在的实现/proof/actualTYPE/Audit通过；批准后的actual proof仍须逐门建立这些义务。本单元给一般真实iid倾斜和明确hlower的事件指数比较，不自动给任何sourceTail/正负trial sign、实际probChernoff(16)/(17)、Legendre最优/全局远区gap、完整(19)/LLT/hW/WC/KL或根闭合，不作最弱/最优/新颖性主张。紧二次tilt质量由G另证，当前未import G去偷换证明。根A/B/C/D、probChernoff、完整(19)/LLT/hW仍OPEN。所有源/scope/旧票/receipt/shared/cache均未修改。
