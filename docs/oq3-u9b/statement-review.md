# U9b 独立声明与来源审查

## 第一阶段：只读 Lean 代码块后的盲译

本节在读取scope解释、真实R1或本次实际依赖源之前落盘。只提取nineteenth-unit-scope.md的Lean代码块：两定义、五个完整目标。实测scope SHA256=`cac22df661588663b9fdcda118a1d71021df105867bc1545378f0c5dbf50a015`。未读作者API/其他notes，尚无SampleChangeOfMeasure实现或构建。

定义normalizedTailCoefficient为sqrt(2πn)乘exp(n·saddleRate(ell,q,w))乘真实originalMeasure(ell,w)的n重产品在sourceTail(q,n)上的实质量。定义tiltedTailCoefficient为同一sqrt因子乘真实atomicMeasure(w)的n重产品下，sourceTail指标乘exp(−ell normalDeviation(q,z))的期望。两个定义使用同一q/ell/w，实际法不同。

1. 非负HasSum w1、任意实ell及每个n下，真实π_w^n上的exp(−ellΣY)真正Integrable，其积分精确等于单坐标inverseNormalizer(ell,w)的n次方。
2. 同样前提，真实P(ell,w)^n测度恰等于真实π_w^n按−ellΣY作tilted得到的测度；是测度等式，不只是某个矩或事件值相等。
3. 任意实ell/q、上述真概率权重、每个n及任意可测路径事件E，exp(n·saddleRate)乘真实P^n(E)实质量，等于真实π^n下E指标乘exp(−ell normalDeviation)的积分。待核实际rate符号、Z正与限制事件后积分真实可积；未要求E=sourceTail。
4. 对真实sourceTail，两个系数定义精确相等，任意ell/q及全部n。
5. ell≥0、q≤2、非负可和r、阶段J、hM/hc和limit/finite旧质量非负时，两实际normalizedTailCoefficient的误差≤sqrt(2πn)·exp(11ell n)·n·C(ell)乘完整未来r尾。两项各使用其自身w对应的saddleRate和originalMeasure，不能暗换成共同rate。

待核n=0、首四项目标的任意ell/q弱门、每坐标与事件限制后的真实可积性、Z>0及消去、同一q与不同真实law的rate对应，不把精确换测度称为全局鞍点或(30)连续性完成。根A/B/C/D仍OPEN，当前尚无裁决。

## 第二阶段：真实来源与实际定义/API

盲译落盘后读取scope解释和真实R1 499–520，并为核rate补读146–159。R1实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。156行源率为ell q+log Z，501–507的倾斜期望系数等于真实原律归一化尾系数，509–520再接产品比较和尾质量误差。候选两定义准确保持同一sourceTail事件与同一q，两个实际概率律的方向也正确。

本次直接只读实际InverseTilt.lean SHA256=`c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811`：20–24行Z=∫π exp(−ell Y)，P=π.tilted(−ell Y)；36–49行对任意实ell、非负HasSum w1真实证明逆指数Integrable和Z>0；51–55行给P真概率；69–86行实际原子质量为w_i exp(−ell Y_i)/Z，实质量消去ofReal时明确非负。

实际PositiveRate.lean SHA256=`8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b`，20–21行saddleRate恰为ell*q+log Z，正号正确。当前泛化的任意q不自动表示均值、KL或全局Legendre极值，签名也没有这些结论。

实际U11c AtomicProductControl.lean SHA256=`6f886635f2201e04d1004a4f4b3b4058d406be3a283f716b70f1ce1cfaa5775f`，201–252行是已完整独立CORRECT的真实概率门及似然期望尾误差。其完整独立报告SHA256=`ad060d2a59f3a5da4a8ec379085771bb6b88c9da66cd56edbe2ac53c696739c4`，本候选只消费其最终真实结论。

指定服务器固定库只读核查，无构建：

| 实际库与SHA256 | 相关真实接口 |
| --- | --- |
| Integral/Pi.lean `43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9` | 33–49行Integrable.fin_nat_prod及53–71行fintype_prod要求每坐标Integrable与SigmaFinite；实际积分有限乘积公式79–98行可用于这些已真正可积的乘积。空产品分支也明确处理。 |
| Measure/Tilted.lean `355cce542b03dd9130d9511f80ae803cc11a12ba9e6a947e68402b124be2165f` | 94–107行tilted是以exp(f)/∫exp(f)的非负withDensity；109–124行tilted_apply_eq_ofReal_integral会区分真实可积与总化分支，126–130行真实Integrable与非零基测度给真概率。当前必须且能够用首目标和Z正性落在真实分支。 |
| Constructions/Pi.lean `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef` | 417–421行restrict_pi_pi精确将可测矩形限制的真实产品等同各坐标限制测度的产品，支持逐矩形比较；既有空产品定义为唯一空路径Dirac。 |

## 第三阶段：逐目标独立数学审查

记π=atomicMeasure(w)，P=originalMeasure(ell,w)，h(x)=exp(−ellY(x))，Z=∫h dπ。hw/hs先给π真概率；实际单坐标API对任意ell给h真Integrable、0<Z<∞以及P真概率。Z是有限实数且严格正，不能仅凭正exp逐点就跳过其积分有限门。

### 1：真实产品归一化

实数指数有限和恒等式给`exp(−ellΣ_iY(z_i))=Π_i h(z_i)`。每坐标h真Integrable，π概率提供SigmaFinite，固定库Integrable.fin_nat_prod/fintype_prod给该真实n重积函数Integrable。此时使用有限乘积积分公式得到`∫Π_i h(z_i)dπ^n=Π_i∫h dπ=Z^n`。不从不可积时可能偶合的总化乘积积分公式替代Integrable证明，也不把π^n写成一个随机变量重复n次的对角律。

### 2：实际测度等式与限制积分门

目标1给联合密度H(z)=exp(−ellΣY)的真实积分Z^n>0，因此π^n.tilted(−ellΣY)是真概率。对任意可测矩形R=Π_i s_i，P^n(R)=Π_i P(s_i)，每项由实际单坐标倾斜密度为`(∫_{s_i}h dπ)/Z`的非负实数对应的ENNReal。

这里每个坐标限制测度π.restrict(s_i)仍有限，h由原有Integrable限制后仍真正Integrable；所以在限制产品上，有限乘积密度再次真正可积，积分精确为Π_i∫_{s_i}h。由restrict_pi_pi和Z^n归一化，联合倾斜律在R上的质量同为上述乘积。无需任何单个事件积分严格正，也不除以某个限制事件的质量；只除以全局Z>0。两边有限概率在可测矩形上一致，真实产品测度唯一性给整个测度等式。由此可行路线的每次lintegral/ofReal实积分转换都已有非负且真正可积的密度支撑，不依赖tilted_of_not_integrable的零测度分支。

### 3：任意可测事件的精确率符号

对任意可测E，H因目标1可积，限制到E或乘1_E仍真可积；密度非负，故真实P^n实概率满足

`P^n.real(E) = (∫_E H dπ^n) / Z^n`。

实际I=saddleRate=ell q+log Z，且Z>0，故

`exp(nI) = exp(n ell q)·Z^n`。

相乘并合法消去正Z^n，得到`exp(n ell q)∫_E exp(−ellΣY)`。常数移入真实可积的事件积分后恰为`∫ 1_E exp(−ell(ΣY−nq))`，即候选的normalDeviation。负号、q平移方向与指数系数均正确，不是ell q−log Z，也没有把P和π互换。

首四项可以对任意ell/q成立：ell任意时单坐标支撑仍有界，真实逆指数可积；q在这里仅是确定性平移和率定义的参数。没有均值约束也能证明该代数换测度，不意味着任意q处率非负、等于KL或全局鞍点唯一。

### 4：实际尾系数及n=0

U9a已审sourceTail_measurable对任意实q和每个n成立，故目标3取E=sourceTail后乘同一个sqrt(2πn)得到两个定义精确相等。此事件有energy>0门，未被换成另一组平方后丢符号的路径事件。

n=0时π^0与P^0均为同一空路径Dirac，ΣY=0、H=1、Z^0=1，联合tilt为常数0倾斜且等于原空产品；任意事件E的等式就是同一空路径事件质量相等。两个尾系数的sqrt因子为0，sourceTail也因energy=0为空，所有目标一致。没有在消去中错误要求n>0。

### 5：两个各自归一化的原律与同一固定q

hl/hr给limitingMass非负，hj/hr及实际finiteMass零延拓给finiteMass非负。hM/hc与既有limit/finite约束HasSum的第0分量给两套完整权重各自HasSum1；因此目标4可分别用于两个真实law，不能省掉这里的概率门。

两个normalizedTailCoefficient各自含其实际w的`I_w=ell q+log Z_w`与实际P_w。分别转换成tiltedTailCoefficient后，两边变为同一q/ell下的似然指标函数，对应两个实际π产品的期望；无须、也不能假设Z_limit=Z_J或I_limit=I_J。由U11c最终似然尾界，乘非负sqrt(2πn)并用|c(a−b)|=c|a−b|得到所写精确系数顺序。

全部r/J/n仍在固定ell/q/p的族中，C只依赖ell；未来尾仍从Lean r_J开始。J=0由真实四基点有限概率门照常成立，n=0两端误差及右侧均0。这连接(27)与直接权重版比较误差，但不证明(30)常数连续性或按n重选最终P。

## 最终声明裁决

STATUS: CORRECT

JUSTIFICATION: 两定义五签名准确表达实际有限iid产品的精确逆倾斜换测度及其尾误差应用。真实单坐标/联合/限制指数密度可积与Z>0足以支持所有归一化、测度等式和real质量转换；实际rate=ell q+log Z给正确指数符号。首四项任意ell/q门、n=0、第五两law各自rate及共享q/概率门均无关键声明缺口。

这是仅声明/source gate。尚无SampleChangeOfMeasure.lean实现、完整证明审查或U9b构建/Audit成功声明，不能现在将源(27)记作实现完成。未读作者API/其他notes，未改实现/旧报告/cache或重编任何成功目标。不声称全局鞍点、TV等同、(30)连续性、LLT或对角闭合。根A/B/C/D全部OPEN。
