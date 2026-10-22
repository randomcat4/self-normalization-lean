# U12a v2 独立声明与实Lebesgue环境审查

## 第一阶段：仅v2 Lean代码块盲译（先落盘）

本节仅从twenty-third-unit-scope-v2.md的Lean代码块提取一个定义和六个完整类型，在读取v2解释、v1比较及本次环境源码之前落盘。实测v2 scope SHA256=`9482dfb3ec45d59c19200b20d81692773c033b06021a6855cccc7fe2c76d0da4`。未读当前实现、失败日志、作者API或receipt，未运行Lean。

定义：给任意实测度mu及实q/a/t/s，centeredNormalTangentCharacteristic是mu下实际复指数相位exp(i[t(normalValue(x)−q)+s(x−a)])的积分。q/a并未要求是均值。

1. 任意mu及q/a/t/s时，特征函数等于单位模中心相位exp(−i(tq+sa))乘jointCharacteristic(mu,8t+s,−t)。
2. 任意实际概率mu及q/a时，特征函数关于(t,s)∈ℝ²连续，无矩或有限支撑输入。
3. 任意概率mu/J/q/a/t，若mu真实AE支撑落在四旧原子加FinJ新增原子的stage范围，且所有活跃原子真实singleton实质量正，则s=0时模1当且仅当t*dyadicMesh(J)=2pi*m对某整数m成立。
4. 相同概率、AE范围及活跃正单点门下，0<|t|≤pi/dyadicMesh(J)推出s=0的模严格<1，含基本区间两个端点。
5. 相同门下，对紧K、0∉K且K包含于该基本区间，先存在eta>0及0<rho<1，再对全部t∈K和全部|s|<eta给模<rho。允许空K与J=0。
6. 相同门下，有共同eta/rho对所有|s|<eta及所有n:ℕ，特征函数的n次幂在K上真正IntegrableOn（此处默认测度须核为实际实Lebesgue）；其实际K限制积分范数≤volume.real K*rho^n。n=0及空K均包含，需真实有限Lebesgue质量与可积性。

待核v2声明/定义体是否与v1逐项保持，以及新增导入的真实MeasureSpace ℝ实例、volume含义、实积分默认测度、有限紧集质量。当前无最终裁决；根A/B/C/D全部OPEN。

## 第二阶段：历史保留、原样声明与来源绑定

盲译落盘后读取v2解释并比较v1/v2。实测v1 scope SHA=`1dddd27330a06202fa0c8fe924c4bb32cfd26fdef54b110aa89fa8168ff40d8b`，旧声明票SHA=`bb35c6145cf03ac92901f0bccd302296d4c497c112a63e7e7ed04ba6f04f5d35`，v2 scope SHA=`9482dfb3ec45d59c19200b20d81692773c033b06021a6855cccc7fe2c76d0da4`。提取的Lean代码块全文文本比较完全相同，故一个定义体及六个完整类型（含全部假设、量词、默认测度语法及端点条件）逐项保持。实质环境变动仅是在原JointNonlattice、FiniteNormalSpan、Topology.Order.Compact之后显式新增Mathlib.MeasureTheory.Measure.Lebesgue.Basic。

审查责任说明：v1旧票漏核原导入环境中MeasureSpace ℝ是否存在；其CORRECT不能视为v1声明环境或编译已通过。该环境遗漏属于独立审查缺漏，本次明确更正；不回写旧票/旧scope或倒改首轮失败历史。协调消息称首轮build未成功，本次没有读取其失败日志，也不把已修改的私有证明体当作已核实现。本票仅绑定新v2声明环境。

真实R1 SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`；重新核332–346相位与远弧步骤，309–348来源语义保持。当前六目标仍只处理实际有限阶段的法向精确共振、离零紧集严格收缩、小切向共同窗口及频率Lebesgue幂积分，不含中心弧二阶展开或完整LLT。

## 第三阶段：实际新增实例与默认测度语义

经指定服务器只读核固定mathlib源码，未运行Lean或目标：

1. MeasureTheory/Measure/Lebesgue/Basic.lean实际SHA=`4955d3400a03ba9d525206fcf1cff8592497dfff06674ca13d68d3bdcabb964d`。第10行是`public import Mathlib.MeasureTheory.Measure.Haar.OfBasis`，不是未公开的实现导入。Basic对应olean实际存在，153848字节。
2. Haar/OfBasis.lean实际SHA=`b243e3c02d446de7b0475db5a61405224c298ae134d4fe0e609cf55d5d874d07`。309–311行的measureSpaceOfInnerProductSpace将有限维实内积空间的volume定义为标准正交基对应的addHaar；319行实际声明公开instance `Real.measureSpace : MeasureSpace ℝ := by infer_instance`。实数的标准内积、有限维及Borel结构提供该实例的实际输入；这里并非凭“Lebesgue”文件名猜测存在实例。OfBasis对应olean亦实际存在，156024字节。
3. Basic.lean49–74行在namespace Real，实际`Real.volume_eq_stieltjes_id : (volume : Measure ℝ)=StieltjesFunction.id.measure`。因此新增volume是标准实Lebesgue测度，而非任意缩放Haar、计数测度或概率测度。77–93行给volume(Ico/Icc a b)=ofReal(b−a)及相应real长度，124行给singleton0质量，标准归一化明确。
4. Integral/IntegrableOn.lean92–93行（SHA=`d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2`）实际定义`IntegrableOn f s (mu : Measure α := by volume_tac) := Integrable f (mu.restrict s)`。v2作用域没有另设[MeasureSpace ℝ]参数或自定义局部volume；新增公开Real.measureSpace因此将最后目标的默认IntegrableOn测度、无显式测度的t积分、以及右端volume.real K绑定到同一真实Lebesgue测度。定义和前五目标中显式mu的随机变量积分仍使用传入mu，不会被新默认volume替换。
5. 紧K在实线上有界且可测，包含于某有限闭区间；Basic的实际区间体积公式与测度单调性给volume K<∞，所以volume.real K是真实有限体积。连续幂函数在紧K上真正可积；真实norm积分界仍是rho^n乘该同一有限Lebesgue体积。空K体积/积分0，n=0的积分常数1给体积本身，均不靠toReal(∞)或不可积积分总化。

这里验证的是公开导入链、实际实例定义和预期数学语义；没有新目标elaboration/编译通过的声称。后续build02仍须实际作者门及完整独立proof/TYPE/机械审查。

## 第四阶段：v2完整数学类型复核

- 首目标用actual normalValue=8x−x²得到(8t+s)x−tx²−(tq+sa)，常数相位模1；显式mu下积分恒等对任意mu有效。
- 概率下相位真实可测、参数逐点连续且模恒1，由真实可积常数1支配得到全参数连续，不需均值/矩。
- U6b的正单点模1等号桥与U8实际有限法向整数支撑给精确双向t*h_J∈2piℤ。J0使用旧基点法向差1，J+1使用活跃addedAtom J与baseAtom2差h_(J+1)；不套无限原子的全联合非格点目标。0<|t|≤pi/h_J时仅可能整数m=0，违背t非零，故含两个端点的严格收缩正确。
- 非空紧K的连续法向模最大值M<1，取rho∈(max(M,0),1)，对开集合norm<rho使用K×{0}的紧tube取得统一eta；空K取任意eta>0及rho∈(0,1)。q/a只作用于单位模中心相位，未暗加均值条件。
- 新增真实Lebesgue环境下，所有固定s的n次幂连续而在紧K上真IntegrableOn，逐点范数≤rho^n后取得真实频率积分界。eta/rho先于所有t/s/n，J0/空K/n0均保持。上述证明依据此前已核的Bochner continuous_of_dominated、generalized_tube_lemma及有限紧集可积接口，声明文本未改变其任何门。

STATUS: CORRECT

JUSTIFICATION: v2的一个定义体与六个完整声明原样保留；新增cached Basic通过公开OfBasis导入实际Real.measureSpace，且固定库将该volume证明为标准Lebesgue。最后目标默认IntegrableOn、频率积分和volume.real K因此具有一致且正确的实测度语义，紧K有限体积/真实可积支持其指数界；来源与其他数学类型无缺口。此为v2独立声明/environment gate，不是当前实现/首轮失败或build02成功的判定。未读实现、失败日志、API笔记或receipt，未运行目标/重编成功项，未改旧票或任何共享文件，未spawn。根A/B/C/D全部OPEN。
