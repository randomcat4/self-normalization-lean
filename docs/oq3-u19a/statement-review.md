# U19a SourceGlobalExponentialTests 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 一、先行独立盲译检查点

本节仅从冻结scope68的Lean fence读取两项完整TYPE；尚未读取scope说明、作者路线、原R1、本单元mechanical/graph材料或未来笔记。0公开DEF，以下完整代码块保留全部类型前提与量词。当前仅是盲译，不是批准。

```lean
theorem source_saddle_exponential_value_bound
    (q : ℝ) (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k)) :
    (∀ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      s * (q / 4) + t * q -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ≤
          saddleRate sourceEll q w) ∧
    (8 * sourceEll) * (q / 4) + (-sourceEll) * q -
      Real.log (∫ x : ℝ, Real.exp ((8 * sourceEll) * x + (-sourceEll) * x ^ 2)
        ∂originalMeasure sourceEll w) = saddleRate sourceEll q w

theorem exists_source_tail_exponential_separator
    (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : ∀ k : Fin 4,
      HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
        (constraintTarget q k))
    (a c : ℝ) (hc0 : 0 < c)
    (htail : (Real.sqrt q / 4) * Real.sqrt c ≤ a)
    (hne : a ≠ q / 4 ∨ c ≠ q) :
    ∃ s t : ℝ,
      Integrable (fun x : ℝ => Real.exp (s * x + t * x ^ 2))
        (originalMeasure sourceEll w) ∧
      0 < (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w) ∧
      saddleRate sourceEll q w < s * a + t * c -
        Real.log (∫ x : ℝ, Real.exp (s * x + t * x ^ 2) ∂originalMeasure sourceEll w)
```

第一目标 `source_saddle_exponential_value_bound`：任取实q与AtomicIndex→ℝ的w；假设每个w_i≥0，以及对全部k:Fin4，同fixedAtom和sourceEll的实际加权feature级数HasSum到constraintTarget q k。结论是一个合取：

- 对任意实s、t，函数x↦exp(sx+t x²)在同一个`originalMeasure sourceEll w`下真正Integrable，其实际实积分严格正，而且`s(q/4)+tq−log(该积分)≤saddleRate sourceEll q w`。s/t在该forall内部任意，q在本目标没有另加窗口或正性前提，w未假定全原子严格正。
- 在具体有限实参数s=8*sourceEll、t=−sourceEll处，上述测试值恰等于同一个saddleRate。没有新增定义globalRate／supremum，也没有在此type中给一般a/c点的结论。

第二目标 `exists_source_tail_exponential_separator`：任取实q∈(1,103/100)、同w≥0及完整4行实际HasSum；任取实a、c，只要求c>0，`(sqrt q/4)*sqrt c≤a`（含等号的弱尾域），并且`a≠q/4 ∨ c≠q`，则存在两个有限实s、t，使真实exp(sx+t x²)在同P下Integrable、其真积分>0，并有严格`saddleRate sourceEll q w < s*a+t*c−log(该积分)`。s/t允许依赖q/w/a/c，但不更换原w、q或法则。没有额外限定c属于支撑凸包、c∈[1,1+H]或a²≤c；支撑外参数也包含。没有假设w基点/全部原子严格正、非退化协方差、手工KL界或已知分离见证。端点、退化模型、off-support和所有c>0须由后续数学审查独立核。

必须随后独立核：全参数真实可积／正Z与标准实log合法；第一目标q无窗口是否仍由4约束充足；第二目标不许把严格结论限成c窗口或强尾不等号；a/c恰候选被显式排除，但其他边界不可省；有限实见证不能靠无穷参数或未证globalRate/entropy对偶。


## 二、盲译后独立核对来源与两项数学命题

本节在以上50行完整TYPE盲译已落盘后追加；未读取任何作者未来/implementation/candidate笔记或scanner JSON。随后已读完整57行scope68、真实R1 146–258和原fixed-moment构造18–109，以及root正式`coordination/integration-v36/OQ3_UNBLOCK.md`。本门只有声明与数学可实现性审查，没有U19a proof/source/Audit可供接受，以下不是kernelPASS预报。

### 原来源和root边界契约

R1 sourceEll=log(31/30)、Y=8X−X²，真实4行约束是质量1、E(X²−4X)=0、E[Xexp(−ellY)]=0、EX²=q。146–159给候选均值(q/4,q)及λ0=ell*q+logZ；161–237利用共同能量范围、binary gap和严格性讨论全局正尾最小。本文只产出真正有限实指数测试的上界/取等及严格分离，不声称一般ρ的KL恒等式或data-processing(9)/(10)已证明。

实际root行政契约明确允许OQ3-owned finite exponential separators，尚无冻结的通用globalRate/Legendre公共接口，domK/扩展实数supremum和off-support bridge由root协调。scope中“closed positive tail”必须按本type实际`c>0`且`a≥(√q/4)√c`解读；此集合在c>0相对域包含边界，但不是R²中的闭集（c可趋0）。本type不覆盖c=0，没有错误宣称ambient closedness；root后续必须保留真实domK/正配分/扩展值语义，不能直接把实数log总化当global rate。

两个type的直接消费性真实成立：对C已交付的固定q和w=limitingMass sourceEll p r，取hw=(全w正).le及完整hm即可，同一q/w/P不重选；C是未来consumer，不是本模块import依赖。不新增p/r/Q opaque-eps/局部rate-gap或手工KL前提。第一个type在候选点给所有 admissible real tests≤λ0且具体θ0取等；第二个给每个其他正尾点一个真admissible test>λ0。因此未来诚实扩展supremum可消费它们证明候选率值和严格大于，但本声明本身没有定义/宣称已闭root canonical supremum、一般KL或原根组。

### 共同模型和真配分函数门

由hm0的真实HasSum可公开推出HasSum w1。`atomicMeasure_isProbabilityMeasure`因此给π=atomicMeasure w真概率；`atomicMeasure_mean`给真Integrable X和EX=q/4，`atomicMeasure_constraints ... 3`给真Integrable X²和EX²=q。以上接口对任意实q均有效，不偷加第一type没有的qwindow、基点正或全w严格正。hm本身可能排除某些q，但证明不依赖虚假空前件。

公开`atomicMeasure_ae_bounds`给1≤|X|≤β=4+√10；`originalMeasure_isProbabilityMeasure`由真实inverse-exp可积建立P真概率，`originalMeasure_ae_bounds`给同P有界支持。`integrable_continuous_of_fixed_bounds mu hb f hf`对每个连续实f在真概率下给真实Integrable，所以对任意有限实s/t，exp(sX+tX²)、其平移/中心化指数及所需多项式都真可积。`integral_exp_pos`消费此Integrable和概率的NeZero实例，给所有分子、Z、P配分严格正，不能用tilted不可积时归0分支。

Z=inverseNormalizer sourceEll w>0由公开`inverseNormalizer_pos`；实际P=π.tilted(−ellY)。固定库`MeasureTheory/Measure/Tilted.lean236–249`的公开`integral_exp_tilted (f g)`给
`M_P(s,t)= Eπ exp((s−8ell)X+(t+ell)X²)/Z`。
它本身允许总化值，故上面真可积/正Z/正分子是必需门。使用标准Real.log_div前必须给两个非零参数，不能误用log0=0。对每个实s/t都满足这些门，因此真实domK中的测试资格不是额外未证输入。

### 第一target：所有实测试的候选点上界和精确取等

独立直接证明如下，完全不需一般KL/Jensen-duality：令α=s−8ell、β'=t+ell，h(X)=α(X−q/4)+β'(X²−q)。由已建立X/X²/常数真Integrable，积分线性给Eπh=0；h和exp(h)连续有界支持上真可积。公开`Real.add_one_le_exp`给1+h≤exp h，真实概率积分比较和线性给1≤Eπ exp h，故log(Eπ exp h)≥0。

精确指数拆分及真可积下常数因子移出给
`log M_P(s,t)=α(q/4)+β'q+log Eπ exp h−logZ`。
正的实指数因子、正Eπ exp h和Z非零允许log_mul/log_div。代数于是给
`s(q/4)+tq−log M_P(s,t)=ell*q+logZ−log Eπ exp h≤λ0`。
这个计算没有除q或取√q，所以确实覆盖第一个type的任意实q，不需要第二type窗口。

θ0=(8ell,−ell)时α=β'=0，Eπexp0=1；公开`originalMeasure_forward_normalizer`129–147也直接给真实`M_P(θ0)=Z⁻¹`和真Integrable。Y=8X−X²只是精确函数恒等式，标准log_inv使候选测试值`ell*q+logZ=λ0`。第一个目标的所有量词和取等成立；无需存在任意优化器或严格协方差，也不需要调用只对全w>0成立的originalAtomEntropy_hasSum。

### 第二target：全弱正尾域严格分离，所有c>0

固定q∈(1,103/100)和同π/P，令ell=sourceEll>0、H=25+8√10。由√10正、(√10)²=10可严格推出50<H<51；同AE支持平方给`1≤X²≤1+H`，并有真实EX²=q。z=(q−1)/H满足0<z<1，所有H/q分母门先明确正性。

任意c>0，令R=√c/√q>0。q>0且实sqrt平方恒等式给c=qR²，弱尾假设精确给δ=a−qR/4≥0（qR/4=(√q/4)√c）。这里不要求(a,c)实际可实现、a²≤c、c落在支撑能量区间或强尾不等号；所有在完整type内的点保留。

对任意有限实u，取s=8ell、t=−ell+u，真配分关系给精确式
`V_u(a,c)−λ0 = 8ell*δ − ell*q*(R−1)² + u*c − log Eπ exp(uX²)`。
实际EnergyBernoulliMGF的`bounded_energy_logMGF_le_bernoulli`在同π/q/H和上述真henergy/hsecond下，对所有正/负/零u给真实centered指数可积、正积分及log界。移出exp(uq)前已真可积，得`log Eπ exp(uX²)≤u+log(1−z+z exp(uH))`。因此
`V_u−λ0 ≥ 8ell*δ−ell*q*(R−1)² + theta*p−log(1−z+z exp theta)`，其中theta=uH，p=(c−1)/H。

情况A：`1≤c≤1+H`且R≠1。此时0≤p≤1，binaryRelativeEntropy_source_gap给`(7/200)(R−1)²<binaryD(p,z)`。公开`sourceEll_lt_one_div_thirty`是真log(31/30)<1/30，配q正且q<103/100给`ell*q<103/3000<7/200`；R≠1才有(R−1)²>0。故L=ell*q*(R−1)²严格小于binaryD。公开`exists_binary_exponential_test p z L`产生一个有限实theta及正binary partition，使binary测试>L；取u=theta/H即可使V_u−λ0>8ellδ≥0，得到所需严格分离。

情况B：R=1。此时c=q，且hne与δ≥0强制a>q/4。θ0本身的测试值减λ0为`8ell*(a−q/4)>0`；不需要任何energy Bernoulli优化器。特别弱边界的唯一排除点恰是候选(q/4,q)，没有把尾域偷偷改成强不等式；c=q而a>q/4仍严格处理。

情况C：`0<c<1`，真实off-support也必须覆盖。令B0=8ell*a−ell*c+logZ，T=|λ0−B0|+1>0。有限实u=T/(c−1)<0，分母c−1严格负/非零；由X²≥1乘负u、exp单调和两侧真Integrable/概率积分比较，`Eπexp(uX²)≤exp u`。正分子才取log，得log≤u。故`V_u≥B0+u(c−1)=B0+T>λ0`。不存在用“此点不可实现”直接略掉结论，或把u=−∞作为见证。

情况D：`c>1+H`。同T和B0，取有限实u=T/(c−(1+H))>0，分母真正；X²≤1+H给logEπexp(uX²)≤u(1+H)，所以`V_u≥B0+T>λ0`。同样全是实际有限参数与真实正配分函数，不诉诸人为定义的∞ rate。

四种情况穷尽全部c>0：端点c=1、c=1+H由A保留。p=0/1时binaryD的sup常需无限参数，但accepted `exists_binary_exponential_test`只求严格L<binaryD，已经分别用有限log(u)／−log(u)的正delta构造给见证；此处不要求binary端点精确attainment，也不除p或1−p。c越接近端点或R越接近1，参数可以很大但仍是有限实数，type没有统一参数界承诺。

数学独立结论：两项冻结命题均为真，直接路线在当前接受的实际API下可行；没有发现需要新增假设、修改域或引用尚未证明generalKL/entropy-duality的缺口。实现时仍须逐门给出上述Integrable、概率、正分母/正配分、积分线性与精确log恒等式；声明批准不预先认可未来证明体或kernel结果。

## 三、实际主API与公开路径语义（机械图核验之前）

已完整读EnergyBernoulliMGF13–97和99–173的真实公开types/proof，SourceBinaryEntropyGap46–51的完整接口及其p0/p1条件，RegularCovariance200–205的sourceEll真严格界，PositiveRate31–55和AtomicMeasure78–109的真实moment/Integrable接口，InverseTilt26–67及129–147的actual probability/normalizer接口。它们没有需要未声明的全原子正性或extra hbase/S/det；本module尽管import RegularCovariance，只用sourceEll标量界，无需协方差正定作为隐藏前提。

固定Mathlib实际语义已server只读核：`MeasureTheory.integral_exp_tilted`236是MeasureTheory全局命名空间下的真实f/g比值公式；标准log Basic133/138的log_mul/log_div均需两个非零；151的log_le_log要求正左参数且真实积分比较；210/213的log_nonneg由Eexp≥1适用。`Analysis.Complex.Exponential.lean633`公开Real.add_one_le_exp适用于所有实h；`MeasureTheory.Integral.Bochner.Basic.lean792`的integral_exp_pos需要真Integrable及NeZero measure，概率会提供后者。所有数学门已在上面的可实现性论证中明确生产。禁止把这些总化API单独当作真实有限率证明。


## 四、数学核验完成后的冻结／公开图／环境证据

最后才作本节实际hash、定向图/cache存在性及Git绑定。没有读取作者candidatecache/scanner/implementation/future JSON或笔记，没有U19a Lean/probe/source/Audit可读，未重复root两root smoke或旧目标成功构建。定向图由reviewer在指定server独立从这三个精确import做源码只读扫描，含嵌套注释/字符串剥离、module默认可见性、public/private和meta import；没有把作者candidate计数当证明。

本地/远端scope.md均57行10676B，SHA256=`03237ffc5dba9ed8e3d25d65cbc1d2ebae9f3e14431fc415e28afdb81deaec2c`。唯一Lean fence含2完整theorem、0DEF；其量词/实参顺序见第一节完整保留，没有声明版本修订或静默增前提。R1真实report.md SHA=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。

独立实际闭包：physical11Shao+2776Mathlib=2787内部节点，211外部停止叶；public11Shao+2512Mathlib=2523内部，189外部停止叶，总2712。所有内部source缺项0、olean不存在项0；外部Lean/其他package叶按停止边界计，不宣称已遍历它们内部。必要actual公共模块AtomicMeasure/InverseTilt/SourceStarter/BinaryEntropyBounds/SourceBinaryEntropyGap和Real.Exp/Log/Sqrt/Tilted/Bochner.Basic均在公开可达图中。真正正性sourceEll_pos位于SourceStarter45–46，确是log(31/30)>0；不是把ell换成1/30。

当前11项目源fresh server hash与本地accepted draft逐项一致，canonical相对路径键、排序紧凑JSON的map SHA为`8238b008f0d69333bbd4a891d836c26b6e5d997325d2fe396696bd7017934783`：

| 项目源码（Shao/OQ3/下） | SHA256 |
| --- | --- |
| AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| BinaryEntropyBounds.lean | 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228 |
| EnergyBernoulliMGF.lean | e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad |
| FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| FiniteStageMeasure.lean | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |
| RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| SourceBinaryEntropyGap.lean | f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9 |
| SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |

这三个accepted import自身实际直接路径已核：EnergyBernoulliMGF普通public可见转入SourceBinaryEntropyGap/InverseTilt/Convex.SpecificFunctions.Basic；PositiveRate转入InverseTilt/Convex.Integral/Convex.SpecificFunctions.Basic；RegularCovariance转入FiniteStageMeasure/PositiveRate/Probability.Moments.Variance。当前所需真实exp切线、积分比较/线性、log_mul/div/monotonicity、sqrt平方、二元有限指数测试都经这些公开图可达；无需新增缓存模块或额外未冻import。

精确API名称透明记录：实际Tilted.lean34为`namespace MeasureTheory`，直到377才结束，中间没有`namespace Measure`；故236正确全名是`MeasureTheory.integral_exp_tilted`，只有定义`Measure.tilted`用显式Measure前缀。本票只使用实际全名，不把文件路径Measure/误作namespace。scope路线本身使用无误的公开短名integral_exp_tilted，不需改冻结文件。EnergyBernoulliMGF当前真实总长176行，其第二目标99–173；scope说明“99–184”是范围文字不精确，完整目标和实际公开接口无变化，不是环境阻塞。

当前指定server mathlib实际Git HEAD=`807d3836b165983210ee2ecf3cd28f239436949c`；lean-toolchain为`leanprover/lean4:v4.36.0-rc1`、文件SHA=`d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4`；lake-manifest SHA=`40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e`。本门仅cache存在性/readiness静态证据，不声称U19a已elaborate/构建/Audit。

最后实际Git为`feat/oq3-source-fixed-law-remainder`，HEAD=`f69807c8fbae2875e5cb6d6f704e7ca1c63085d7`，status干净；local和remote的SourceGlobalExponentialTests.lean均不存在，U19a run中Audit.lean/Audit.log/receipt.json均不存在。尚未U19a新branch/source/probe，与声明门顺序相符。scope未来新branch的策略是root/lead权限，本review没有branch/source/cache写入。

行政基线区分：scope冻结时rootv35，审查中lead通知rootv36已通过PR145整合A139/B141，main82294da791784f3ac34ca52b96e21ef23f8a5329/acceptedf2a39a09ebd50648bd61d68d7018aa01a9810ea0、同树b6e72c992deceb0df88e772e50b2c42ba58ac4b4，receipt7d76700e85b2b495b7d1f0ba771f7029682c999eab062fbebb31a9acc3fe6b35；C144是批冻结后发布的下一队列，当前lane仍Chead未改。本票未fetch/rebase/merge/reset/重跑整合门，没有把行政推进当源漂移。lead同时报告旧256源/1033对象不变，这是root行政证据，不冒称本人重新hash旧对象。实际本门11源已如上fresh独立核，pins/数学接口未变。

root此前新增15个KL/Bernoulli cache模块、保持39871旧shared文件不变的e5a25f97收据为root行政readiness；本门实际三个imports不消费新generalKL API。未重复root成功import/check或做whole-cache-directory哈希冻结，没有以cache绿灯当数学结论。所有server项目只读命令CPU14–17，无Lean/#check/probe/build/rebuild/Audit/cachewrite/spawn/commit/pub或raw完整log下载，未触外部CPU0–9/80GiB任务；只新建本报告和授权上传。

## 五、最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 冻结scope68的两个完整type数学正确且在当前指定server接受接口下可实现。第一目标只需真实π/P概率、4约束产生的可积均值、全实二次exp可积/正配分，以及exp≥1+h给候选上界和θ0精确取等；没有第一type未写的qwindow/全原子正性。第二目标从真实能量支持与q窗口，四情形覆盖所有c>0/弱尾域：区间内非R1消费真binary有限指数测试及严格7/200 gap，R1尾内直接θ0，区间外显式有限正负u；p0/p1、支撑外点、实际非零分母/log正域和同w/q法则均保留。没有输入generalKL/entropy-duality/手工rate-gap/局部优化或新增代理globalRate。

这只是完整独立声明／来源／API准许，U19a实现、全部private/generated、actualTYPE与传递公理和真正目标构建仍须后续完整独立proof门；本票不预报Lean kernelPASS。未来root真实domK/扩展实数supremum仍须单独对接，尤其不能把c>0的相对闭尾域误写成R²闭集、不能以log0总化代替admissibility。一般KL(9)/(10)、原source saddle导数/常数及剩余根装配均未因此自动关闭，无最优性或新颖性声明。

所有根A/B/C/D保持OPEN。完整先行50行盲译字节前缀保留；前部IN_PROGRESS是历史检查点，最终状态以本节为准。作者未来/implementation/candidate/scanner笔记和JSON未被读取作为数学依据，未以作者路线代替上述独立推导。等lead全文读取本final后才由作者实施；本review未修改任何旧票、源或冻结scope。
