# U13a v2 NormalLayerFourier 独立声明与来源审查

## 第一阶段：仅v2冻结Lean代码块重新盲译（先落盘）

本节只提取v2冻结Lean代码块，在读取v2scope说明之前先落盘。实测twenty-ninth-unit-scope-v2.md SHA256=`024110d50ff7fa8638a063be0ac0825c9b17b0259f95c23e694ea0f1cdc3695a`。v1的两定义/五完整类型先前已盲译落盘并开始独立来源/数学审查；v2只修复一个proof-only缓存import，本报告不虚称已失去此前上下文。代码块实测v1/v2逐字相同；旧v1scope与原盲译报告保留不覆盖。当前尚无最终v2判定。

定义normalLayerIntegrand(q,a,d,s,n,z)：实际normalDeviation(q,z)=d这一层上的exp(i s(∑z_i−n a)/sqrt(n))，层外0。未除层概率，n0除法总化。

定义normalLayerCharacteristic(mu,q,a,d,s,n)：在真实同一mu的Fin n坐标Measure.pi下积分上述实际层indicator乘复相位；是未归一化层特征积分，层质量可0。

1. 正h、整数k下，h/(2pi)乘真实Lebesgue闭基本区间[−pi/h,pi/h]的exp(i t h k)积分，精确等于k0时1、否则0。
2. 任意实际概率mu及任意q/a/t/s/n下，真实n重产品中exp(i[t normalDeviation(q,z)+s(∑z_i−n a)])积分=同一actual centered characteristic_mu,q,a(t,s)^n。无需中心等于均值；这里s未sqrt缩放。
3. 任意实际概率mu和任意q/a/d/s/n，实际层indicator相位对同一真实n重产品真Integrable。
4. 同一实际概率mu、任意q/a/h/d/s，h>0、Y实际mu-AE属于零offset hℤ，给n且d+nq实际属于hℤ，则未归一化层特征积分=h/(2pi)乘闭基本区间上的exp(−i t d)*actual characteristic_mu,q,a(t,s/sqrt(n))^n真实Lebesgue积分。相容门、负相位、系数和sqrt尺度明确，无矩/正协方差/正层质量/n>0门。
5. 同一ell/q/p/r/J实际矩阵非奇异、mulVec约束、finiteBase非负、r非负，给d/s/n及d+nq属于dyadicMesh(J)ℤ，则同一atomicMeasure(finiteMass ell p r J)在q/q4中心满足上述公式，h=actual dyadicMesh(J)。无需Summable r/严格正质量；全部对象保持同一有限律/参数。

待核actual Path/normalDeviation和真实产品语义、层可测/可积、整数正交/端点/归一化、AE逐坐标零offset网格与相容门、联合Fubini真可积、n0/零层质量、有限实际网格/J0/共同参数、v2显式缓存import的可见性。根A/B/C/D全部OPEN；精确有限样本反演不等于LLT或条件Lévy。

## 第二阶段：版本透明性、真实R1及承重定义

v1scope SHA=`1c2b098c06c66f579ec9fda025cafee256dee053056d3b4005c0e47a9ecabc2f`，v2scope SHA=`024110d50ff7fa8638a063be0ac0825c9b17b0259f95c23e694ea0f1cdc3695a`。本地两版Lean代码块逐字比较完全相同（不仅去空白）；两定义体、五完整类型、默认measure和全部假设未改。全文diff仅版本标记、拟import追加Mathlib.MeasureTheory.Integral.Pi及说明该变化的段落。旧v1scope/盲译报告不改；保留盲译报告SHA=`867dd28b579a6f40e5cf1f1b35c80a0e7d69cbe344684e1ab6f5386a773c9921`，其原状态仍待核，无追改历史裁决。

此修复来自本次独立静态检查：v1拟三import的public re-export图未到达Integral.Pi/Prod，所需olean虽存在，显式proof API可见性仍需透明绑定。协调者据此冻结v2，追加一个已cached Integral.Pi，它public import Integral.Prod。未发生Lean/API探针或编译失败，也不是修改数学前提；本票最终批准对象仅v2环境。

v2代码块先落盘后读取v2解释，沿用本次在v1盲译之后已独立读取的真实R1 309–345及同一actual前置。R1实测SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。源332–343只对Y作格点Fourier反演，并保留切向characteristic的sqrt尺度。两定义是未归一化层期望，不是除以层概率后的条件characteristic；s=0时即真实层概率的复嵌入。这里仅给有限样本精确恒等式，源的中心/远弧渐近及条件Lévy仍需后续工作。

实际Path n=Fin n→ℝ（共享FinitePath18），normalDeviation(q,z)=∑normalValue(z_i)−nq（SampleBoundary19–20），并非抽象替代能量；Y=8x−x²。actual centeredNormalTangentCharacteristic=∫exp(i[t(Y−q)+s(X−a)])dmu（FiniteFarArc21–23）。真实有限iid法就是Measure.pi(fun Fin n=>mu)，共享FiniteIID只作actual产品律接口，不改产品measure。

下列实际前置本地/真实服务器源码hash均重新核对一致：

|源|共同SHA256|
|---|---|
|SampleBoundary|`7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2`|
|FiniteFarArc|`3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71`|
|FiniteNormalSpan|`0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de`|
|FiniteStageMeasure|`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1`|
|AtomicMeasure|`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`|
|共享FinitePath|`898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb`|
|共享FiniteIID|`d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b`|

## 第三阶段：五目标的独立数学核对

### 1. 整数正交与真实归一化

令I=[−pi/h,pi/h]，h>0使端点有序且体积为2pi/h，真实Lebesgue积分有限。每个整数k的复指数连续、norm1，先在紧I上真可积。k=0时积分=2pi/h，乘h/(2pi)=1；h和2pi非零均来自严格正性。

k≠0时，c=(h*k:ℂ)*I非零；将真实闭Icc积分经Lebesgue单点无原子转为Ioc积分，再由端点有序转为有向intervalIntegral。实际integral_exp_mul_complex给积分=(exp(c*pi/h)−exp(c*(−pi/h)))/c。h非零后端点为exp(i*pi*k)、exp(−i*pi*k)，其指数之差是k*(2pi i)，真实整数周期定理给二者相等。因此积分0，正确得Kronecker项。不能对任意实k使用该结论；这里k:ℤ和c≠0的门都足够。闭区间两个端点没有额外质量或重复计数。

### 2. 真iid产品characteristic幂，任意代数中心

逐路径有限恒等式

t normalDeviation(q,z)+s(∑z_i−n a)=∑_i[t(Y(z_i)−q)+s(z_i−a)]

成立，q/a只是代数中心，无需真实均值或矩存在。复指数有限和化为各坐标phase乘积。每个单坐标phase连续、norm1，在概率mu下真Integrable；整体phase/乘积同样norm1、可测，在真实有限产品概率下先真Integrable。再用实际有限产品积分分解得到各相同一维characteristic积分的积，即其n次幂。mu为概率提供各坐标SigmaFinite等实际库门，没有以对不知可积函数成立的总化公式冒充真实可积。

n=0时Fin0上空和0、空积1，实际空产品measure质量1，双方都是1。所有n始终同一mu/q/a/t/s，未换成抽象“独立性”假设下的另一联合律。

### 3. 真实层事件及层相位可积

normalDeviation是有限坐标连续多项式，层{normalDeviation=d}是闭集，故真正MeasurableSet。切向相位是连续复函数，norm恒1；即使n0，除sqrt0按固定实除法定义为0，仍连续/可测。层indicator函数可测且norm≤1，在实际产品概率下Integrable.of_bound真可积。无需层概率正性；如果层为零质量，未归一化期望为0而不出现除0。若需要读成概率，s0时是真实层概率的嵌入，不是条件概率对象。

### 4. AE整数和、相容门、联合Fubini及精确反演

由真实hgrid通过有限产品的measurePreserving_eval，将各坐标mu-AE门提升到产品AE门；Fin n有限，所以可同时取得全部坐标Y(z_i)=h k_i。若需要可测集合版本，hℤ可数、Y连续，其原像是可测集合；不需可测地全局选择整数k_i，只需在已有AE事件上对每条有限路径逐点提取有限证人。hlayer给d+nq=h k0。因此实际

normalDeviation(q,z)−d = ∑Y(z_i)−(d+nq)=h(∑k_i−k0)。

这里整数差K=∑k_i−k0使第一目标适用。h≠0保证K=0恰等价于normalDeviation=d。若删去hlayer，则频率可能不是整数倍h，有限基本区间积分不再是层indicator；当前类型正确保留该必要相容门。此处明确是零offset hℤ，不把一般offset+hℤ擅自替换成零offset。

先把正交投影乘上真实切向phase，再交换t与样本z积分。必须先给真实联合Integrable：取nu=(volume.restrict I)，lambda=Measure.pi(fun Fin n=>mu)。nu真实有限（I紧、Lebesgue有限体积），lambda是真实概率；其乘积是有限measure。联合函数

F(t,z)=exp(i t(normalDeviation(q,z)−d))*exp(i s(∑z_i−n a)/sqrt(n))

是联合连续/可测函数，norm恒1，故在nu.prod lambda下真正Integrable；各slice和所需迭代积分也由实际Fubini接口得到。只有在此联合门之后，才可把h/(2pi)∫_z phase(z)∫_I exp(i t(M(z)−d))dt变为h/(2pi)∫_I exp(−i t d)∫_z exp(i[t M(z)+(s/sqrt(n))R(z)])dλ dt。

应用目标2，内层样本积分就是actual characteristic_mu,q,a(t,s/sqrt(n))^n。因此外层系数h/(2pi)、负层相位−t d、切向频率sqrt(n)⁻¹*s均准确；没有遗漏nq相位，因为actual characteristic已按q中心化，hlayer也按d+nq相容。s R/sqrt(n)=(sqrt(n)⁻¹*s)R只用总化除法的乘法恒等式，不需消sqrt，包含n0。

不要求网格最大、随机支撑有界、真实均值或协方差正性；任何包含实际Y支持的正网格hℤ都能给该精确投影。格距最大性服务后续远弧分析，不是此恒等式的假设。

### 5. 同一有限原子律、J0、零质量及n0

同一ell/q/p/r/J的finiteMass由四个finiteBase与j<J的r(j)组成，未来质量为0。hM/hc给真正四个有限HasSum约束，hp/hr给非负权重，第0约束给HasSum1，故同一actual atomicMeasure是概率。若作为源中心解释，实际约束也给同一pi_J的EX=q/4、EY=q；这里general精确反演本身只需代数中心，未另外挑选参数或使用原律P。

FiniteStageMeasure90–107的atomicMeasure_finiteMass_ae_range只把实际measure集中于Fin4⊕FinJ的活跃有限支撑：未来j≥J项因权重0不参与。FiniteNormalSpan26–34的stageAtom_normalValue_lattice对每个此stage原子给Y=dyadicMesh(J)*integer，故真实零offset hgrid成立，且dyadicMesh(J)>0。没有将整个无限AtomicIndex的每个原子错误地放进当前有限网格；也没有为此格点包含性套用需要严格正质量的最大格距定理。

J=0时h=1、新增项为空，四旧原子的Y均为整数，以上真实概率/网格证明仍有效。允许零质量、r不可和，因为只使用前J项。hlayer只要求相容，不要求实际可达或正层概率；相容但不可达时双方均0。n=0时M=R=0，层积分为d0时1、否则0；hlayer此时要求d∈hℤ，右侧的整数正交正好给同一值。sqrt0不会被消去，q/a在空样本中乘0，不出现新的n>0门。

## 第四阶段：v2实际固定库与缓存可见性

本次只在指定服务器只读实际源码/olean，没有Lean/API探针、构建或作者notes/receipt/log门。实际mathlib HEAD及manifest rev=`807d3836b165983210ee2ecf3cd28f239436949c`，lean-toolchain=`leanprover/lean4:v4.36.0-rc1`。真实run/scope.md仍为v1 SHA=`1c2b098c06c66f579ec9fda025cafee256dee053056d3b4005c0e47a9ecabc2f`，run/scope-v2.md与本地v2同SHA=`024110d50ff7fa8638a063be0ac0825c9b17b0259f95c23e694ea0f1cdc3695a`，旧稿未覆盖。

|实际源码/API|前提与实测SHA256|
|---|---|
|Integrals.Basic242–252|intervalIntegral.integral_exp_mul_complex需复系数c≠0；当前k≠0/h>0分支真实满足。`9f989cc31de77616c518e6b435d1af387596c6c6ab317b1c4b979c5f8f73f022`|
|Complex.Log172–173|exp x=exp y iff存在整数m使x=y+m*(2pi I)，与两个端点整数差相符。`991a8c873c89b62bd9724a88b91e7ca17f5947c736dd6b026b5fac0a5913dbeb`|
|Integral.Pi33–36、106–122|有限产品Integrable接口需各坐标真Integrable和SigmaFinite；积分prod/pow接口在Fintype及SigmaFinite下可用。当前phase有真实norm1概率可积门，Fin n含0。`43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9`|
|Constructions.Pi311–313、402–407|真实有限产品概率实例及概率坐标eval的MeasurePreserving，可提升AE坐标门。`bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef`|
|Integral.Prod443–478|真正Fubini/反向Fubini明确消费联合Integrable；当前限制volume×产品概率为有限/SFinite，ℂ完整，真实门满足。`8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05`|
|IntervalIntegral.Basic677–678；Bochner.Set669–700|端点有序时有向积分=Ioc积分，Lebesgue无原子给Icc=Ioc积分。SHA分别`bf8558a4cb789e3505cfb08a6712ce83017719be2523e862d5e52f082433814c`、`e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75`|

实际现成olean：Integral.Pi63624 bytes、Integral.Prod284712 bytes、Integrals.Basic95448 bytes、SampleBoundary594096 bytes、共享FinitePath284864 bytes、共享FiniteIID71032 bytes。未下载/写入缓存。v2的显式Integral.Pi8行是public import Integral.Prod；独立遍历v2 public图已到达Prod、Constructions.Pi、Lebesgue.Basic和Complex.Log，没有v1暴露的proof API可见性缺口。SampleBoundary→FiniteIID→Independence.Basic提供实际Constructions.Pi；FiniteFarArc显式Lebesgue.Basic绑定标准实volume；其JointNonlattice链提供Complex.Log。

拟namespace Shao.OQ3/open MeasureTheory/open scoped BigOperators Matrix提供两定义/五类型的样本和、矩阵mulVec与积分语法。Path是actual Fin n→ℝ，真实有限产品Borel/可测空间可用。外层Fourier积分显式volume，样本积分显式Measure.pi；追加proof-only import不改变默认measure/定义/类型。此为静态环境审查，未虚称这五个新目标已elaboration、实现或kernel通过。

STATUS: CORRECT

JUSTIFICATION: v2两定义与五完整类型先重新盲译落盘，代码块与v1逐字相同；唯一proof-only缓存import修复透明且实际public可见。真实整数正交、h/(2pi)系数、负层相位、切向sqrt尺度和d+nq格点相容门数学上正确。真实产品概率/可测层事件及有限区间×产品概率的联合norm1函数给可积后才可Fubini；iid幂与AE整数和可在现有真实API下建立。有限实例消费同一finiteMass的真实非负HasSum概率与活跃stage网格，J0/n0/零质量和任意r有限零延拓均覆盖。未发现需修订的来源、声明、量词或v2静态环境缺口。

本票仅批准v2声明/source/静态环境；旧v1scope及原盲译保留，不追改历史为已通过。本次未读取作者未来实现/notes或receipt/机械日志，未写实现、运行Lean/API探针、构建、修改共享文件/作者源/旧票/缓存、spawn或commit/PR。精确未归一化层反演不等于条件归一化、条件Lévy、Fourier渐近、混合LLT、实际hW或根闭合；根A/B/C/D全部OPEN。
