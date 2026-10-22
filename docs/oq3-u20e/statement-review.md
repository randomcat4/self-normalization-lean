# U20e declaration review history

The v1 environment gap was deferred without implementation. The focused v2 explicitly activates the ContDiff scope and preserves both Lean fences. Both complete original reports follow verbatim.

## Original v1 report: CRITICAL GAPS, unimplemented

# U20e SourceSmoothMeanMap 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 不可改写完整TYPE盲审前缀

先仅读冻结scope76的两个Lean代码块，保全完整TYPE及独立量词／对象翻译，尚未读取scope说明、本轮原文／库API／行政凭据。
本轮0公开DEF／1公开THM，为声明门；没有本模块实施或proof验收。

```lean
import Shao.OQ3.InverseTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
```

```lean
theorem source_log_partition_and_tilted_mean_smooth
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let Z : (Fin 2 → ℝ) → ℝ := fun theta =>
      ∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P
    let K : (Fin 2 → ℝ) → ℝ := fun theta => Real.log (Z theta)
    let tilt : (Fin 2 → ℝ) → Measure ℝ := fun theta =>
      P.tilted (fun x => theta 0 * x + theta 1 * x ^ 2)
    let mean : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun theta =>
      ![∫ x : ℝ, x ∂tilt theta, ∫ x : ℝ, x ^ 2 ∂tilt theta]
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    IsProbabilityMeasure P ∧
      (∀ theta : Fin 2 → ℝ,
        Integrable (fun x : ℝ => Real.exp (theta 0 * x + theta 1 * x ^ 2)) P ∧
        0 < Z theta ∧ IsProbabilityMeasure (tilt theta) ∧
        Integrable (fun x : ℝ => x) (tilt theta) ∧
        Integrable (fun x : ℝ => x ^ 2) (tilt theta)) ∧
      ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ mean ∧
      ∀ theta : Fin 2 → ℝ,
        HasFDerivAt K
          ((pr 0).smulRight (mean theta 0) + (pr 1).smulRight (mean theta 1)) theta
```

### 独立完整翻译及疑点

1. 任给同一AtomicIndex→ℝ权重w，全权重非负，并有真实HasSum w 1。
2. TYPE没有q、全四矩约束或基点正质量假设，也不从调用者索取原P概率。
3. P固定为originalMeasure sourceEll w，使用同一个实际原律。
4. Z(theta)是同P下exp(theta0*x+theta1*x²)的真实实积分，theta为整个Fin2实参数空间。
5. K(theta)=Real.log(Z(theta))，是字面ambient函数，不引入新的公开canonical定义。
6. tilt(theta)是P的实际二次指数tilted测度，不是未绑定的归一化权重代理。
7. mean(theta)为两项真实积分组成的Fin2向量：(E_tilt X,E_tilt X²)。
8. pr_i为真实连续线性坐标投影，导数输出类型是CLM。
9. 结论首先生产IsProbabilityMeasure P，不靠零测度总化或caller实例。
10. 对全部实theta同时给exp真Integrable、Z(theta)>0、tilt真概率、X和X²在该tilt下真Integrable。
11. Z正性必须在使用log／除法前建立，排除不可积exp导致的tilted=0。
12. 不限theta小球或一个鞍点邻域；每个theta都要求真实结论。
13. 还给ContDiff ℝ ∞ K，含整个ambient参数域的所有有限阶导数连续性。
14. ∞不等于解析ω；TYPE未要求实解析，也没有给出均值映射逆。
15. 对真实mean函数同样要求ContDiff ℝ ∞，不是只对归一化矩代理给光滑性。
16. 最后对每个theta给HasFDerivAt K，导数h↦mean(theta)_0*h0+mean(theta)_1*h1。
17. 这是真Fréchet梯度，并非某个指定theta0处的一阶／二阶数值公式。
18. 仅已有点态导数／Hessian结论不能自动推出全参数C∞。
19. 必须实际对所有多项式指数矩建立共同局部参数主控、真积分可积及完整求导公式。
20. 一个可核方向是M_k(theta)=∫x^k exp(theta·W)dP，导数由M_{k+1}和M_{k+2}给出。
21. 全阶结论需要对所有k同时作自然数阶归纳；不能在高阶步骤循环假设自身光滑。
22. 该递推须来自真实可积的参数积分导数，而非对总化积分形式微分。
23. 将所有有限自然阶合成∞，必须核实际ContDiff API中阶数类型／∞和局部／全局量词。
24. mean需与M1/Z、M2/Z真实相等；必须先证明相应weighted exp Integrable及实际tilt积分API门。
25. 实际tilt的X／X²可积可用绝对连续继承原AE界后bounded-continuous积分门，但两者概率应先产生。
26. 不可跨模块调用PR151私有weightedMoment等名字；只能局部诚实重建或用真正公开库API。
27. M0/Z正，所有theta分母非零；ContDiff.log／div不能忽略正域／非零前提。
28. CLM投影与标量／加法构造的导数函数光滑性必须核实际公开接口或等价有限维表达式。
29. 退化w（只有少数正原子）、真概率离散支撑、任意实theta均允许；无需协方差正定。
30. 本TYPE没有hcont／C2／导数可积／局部逆等手工分析假设，不容在实现中暗加。
31. 待核四精确imports下所有必要导数／ContDiff／tilt API是否公开可见及现有环境是否可执行。
32. 本轮不输出正定、localinverse或原A/B/C/D闭合；不因名称MeanMap而误记均值逆完成。
33. 本前缀不预报elaboration／kernel／完整proof结论。

--- END IMMUTABLE BLIND PREFIX ---

## 独立声明／来源／API终票（冻结v1）

STATUS: CRITICAL GAPS

REASON: 预期的数学C∞命题成立且有真实公开API生产路径，但冻结scope第16行没有开启ContDiff作用域。第36行两个∞不能在该header下被认证为所需C∞阶数。必须另立透明的环境修订；本v1不能直接批准实施。未运行Lean，因此这里报告静态确定的作用域缺口，不伪称已观察到某条实际elaboration错误。

本报告只审声明／来源／API可消费性，不是实现证明终审。开头IN_PROGRESS是当时盲译检查点原字节；本节为最终裁决。先保存完整TYPE和独立翻译，随后才读scope正文、来源及库API，最后核对机械绑定。

盲审前缀保全：前77行／5125字节，SHA256 `2b6da1a7cf0db5aeaf5a57ea3eba7d4e154ebf85f6f72c8f10cf99562fcce00d`。本终票仅追加，前缀未改。前缀13–15项是对作者预期C∞语义的独立翻译；后续固定库核对发现，冻结header尚未把该预期绑定为实际记号，不能倒改前缀隐藏发现。

### 1. 精确阻塞及最小修复边界

1. 冻结scope第16行仅列`open MeasureTheory`、`open scoped Matrix Topology BigOperators`及`noncomputable section`。第36行使用`ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ mean`。四个imports提供相关定义，但提供定义不等于激活scoped notation。
2. 固定Mathlib `Analysis/Calculus/ContDiff/FTaylorSeries.lean`116–120实际定义：
   - `scoped[ContDiff] notation "ℕ∞ω" => WithTop ℕ∞`；
   - `scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)`；
   - `scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)`。
3. C∞的阶数是内层ENat无穷嵌入外层WithTop，并非外层top。不能用裸`⊤`代替来修复，否则会变成解析ω要求。本单元未审也未声称解析性。
4. 固定Lean `Lean/ScopedEnvExtension.lean`102–115的`addImportedFn`只把`Entry.scoped`存入`scopedEntries`，与立即加入有效状态的`Entry.global`分开。导入模块内部开过scope不会自动使新文件处于该scope。
5. 同文件287–304的`activateScoped`才将指定namespace的scoped项加入当前状态；`Lean/Elab/Open.lean`74–89中普通namespace open及`open scoped`显式调用该过程。当前header所开Matrix／Topology／BigOperators／MeasureTheory没有打开ContDiff。
6. 实际`ContDiff/Operations.lean`34、`Log/Deriv.lean`33、`ContDiff/Comp.lean`39自身均显式开启ContDiff；不能把这些文件内的命令当作本模块header。
7. 为排除另一个通用∞记号覆盖该缺口，独立只读检索固定Mathlib及Lean Init中声明字面∞的notation／syntax。有效候选只有ContDiff-scoped、ENNReal-scoped、OnePoint-scoped，另有Adele后缀及局部范畴例子；没有可把当前两个位置静态认证为C∞的全局通用∞定义。该查询不是重新扫描import图或运行Lean。
8. 最小建议：保留v1字节／哈希／本票，另立修订scope，在header显式增加`open scoped ContDiff`。等价无歧义修复是把阶数写成实际内层top嵌入式；若用后者也须独立核其真实类型。不要静默在未来实现中加header后仍称当前冻结环境完全获批。
9. 四imports不必为此增加新模块／缓存；缺的是已导入记号的激活。本票不修改scope、不写实现、不运行验证探针。修订版应经独立focused声明门后才声称环境获批。

### 2. 原文对应及量词判断

R1原件`current/oq3/proofs/r1/report.md`137–145定义同一逆倾斜P并给有界、离0支持及反向倾斜；147–159进一步用完整矩约束产生鞍点与正率。当前TYPE只需非负w和真实HasSum w 1来产生有界概率P，因此不要求q／其余三矩约束是合理的加强，不是漏门。它不以这两个输入声称均值0、特定鞍点或正率。

R2原件`current/oq3/proofs/r2/report.md`38–45的W=(X,X²)、真实log母函数和真实倾斜律，与本TYPE的坐标次序完全相符。50–60的均值逆邻域、协方差谱界及统一矩条件是后续消费者需要的额外义务。全参数C∞可为其提供正则性，不能代替逆、非退化或紧族谱结论。

`drafts/oq3/root-contract.md`26–30要求固定同P、真实配分可积及严格正性，不能把域外总化积分0的log当成真正K。本TYPE在有界同P下显式生产每个实theta的可积和正Z，因而可合法输出整个ambient参数域的literal K。它没有创建另一个公开canonical K或声称扩展率函数已被该正则性结论取代。

所有P／Z／K／tilt／mean／pr均为同一结论内部的let，按出现次序依赖同一w。Z和K在原P下；mean在该P的实际theta倾斜下。没有另取law、theta依赖w或调用者预给光滑性。最后梯度是h↦mean(theta)0*h0+mean(theta)1*h1；与W坐标相符。

### 3. 从实际公开API生产概率、所有矩及正配分

实际`Shao/OQ3/InverseTilt.lean`51–55公开`originalMeasure_isProbabilityMeasure ell w hw hs`。代ell=sourceEll可建立P的真实概率实例。该实例不是零测度的真空性质；其生产者先有逆指数可积与严格正normalizer。

同源57–60公开`originalMeasure_ae_bounds`，得到同P下AE |x|≤B，其中B=4+sqrt10。26–34公开`integrable_continuous_of_fixed_bounds`：对真实概率mu、该AE界和任意连续实函数给Integrable。该API不要求全正原子、q或协方差非退化。

定义仅供此独立数学论证的M_k(theta)=∫x^k exp(theta0*x+theta1*x²)dP（不是建议增加公开DEF）。对每个自然k和全部实theta，被积函数连续，所以上述公开门给真实Integrable；k=0给真实Z。不存在先对总化积分形式微分再补可积的步骤。

固定库`MeasureTheory/Measure/Tilted.lean`126的`isProbabilityMeasure_tilted`以真实exp可积为门；实际`integral_exp_pos`在概率非零实例下给Z>0。先得到这两项再使用log／逆数。任意大实参数只改变有界支撑上有限连续函数的界，不破坏可积性。

`tilted_absolutelyContinuous`280把同P的AE支撑界传给每个实际tilt；在真实tilt概率实例下，再用相同bounded-continuous公开API给x与x²真Integrable。也可用293的`integrable_tilted_iff`与真实加权矩，但不能省略其exp可积门。

退化权重同样允许：例如只一个原子正质量时，均值映射可能常数／不可逆，本TYPE仍成立。没有任何一步需要全四矩、q窗口、正基点质量或正定Hessian。没有把全参数结论误用为全参数一致的数值界。

### 4. 全阶参数求导的实际可实现路径

对每个k和参数theta，候选CLM导数是
`D_k(theta)=M_(k+1)(theta) • pr0 + M_(k+2)(theta) • pr1`。
这是有限维实参数到实数的真实Fréchet导数表达式，不是只有两个形式偏导。

为证明该公式，取theta的固定正半径闭球，与固定支撑区间Icc(-B,B)作紧积。相应被积CLM导数
`x^(k+1)*exp(t0*x+t1*x²) • pr0 + x^(k+2)*exp(t0*x+t1*x²) • pr1`
在(t,x)上连续，故其operator norm在该紧积有有限共同界C。这里的C可依赖k、theta和所选邻域；对AE x之后的全部邻域参数使用同C，而非逐t临时选择主控。

真概率P下常数C可积。F(t,·)及F'(theta,·)由连续性给AEStronglyMeasurable，F(theta,·)已有加权矩可积；点态参数链式求导给每个x、每个邻域t的HasFDerivAt。因此实际`Analysis/Calculus/ParametricIntegral.lean`206–212的`hasFDerivAt_integral_of_dominated_of_fderiv_le`全部门可满足：
- 邻域集合真实属于nhds theta；
- eventually参数的F可测；中心F真可积；
- 中心F'可测；
- AE x后∀邻域t的同一operator norm可积主控；
- AE x后∀邻域t的真实HasFDerivAt。

最后先对M_(k+1)、M_(k+2)确认真实可积，才把CLM积分拆为两项并提出常CLM，得到D_k。旧PR151实际私有weightedMoment证明可供对照这些原库门，但本单元四imports不公开其private名字；未来实现必须局部诚实重建或调用真正公开原库，不能跨私有调用。

将所有k同时作自然阶n归纳，避免循环：
1. 每个M_k在所有theta可微，故全局连续，再由`contDiff_zero`得到阶0。
2. 假设对全部k都有阶n；于是M_(k+1)、M_(k+2)的固定CLM倍与和构成阶n导数函数D_k。
3. 实际`ContDiff/Defs.lean`1171的自然n版`contDiff_succ_iff_hasFDerivAt`恰要求存在阶n的导数函数且∀x HasFDerivAt；用已得D_k得到M_k阶n+1。
4. `ContDiff/Operations.lean`643的`ContDiff.smul_const`及197的add适用于上述CLM值函数；不需把高阶向量值求导再从头建立不同阶API。
5. 全部自然阶后，`ContDiff/Defs.lean`1114的`contDiff_infty`合成真正C∞。该推理仅在明确激活正确∞记号或写无歧义阶数后使用。

这是完整无额外分析假设的生产路径，不把已有鞍点一阶／二阶数值结论当作全阶证明。现有imports中Operations经Comp／Basic公开提供Defs／相应ContDiff接口；ParametricIntegral提供真实主控求导接口。无需缺失的FiniteDimension或InverseFunction模块。

### 5. 绑定真实倾斜均值、K及梯度

Z=M_0，在全部theta严格正。实际`Log/Deriv.lean`182的ContDiff.log消费函数光滑和∀theta非零，给K的全参数C∞；不是对log0应用链式法则。

实际`Tilted.lean`230的`integral_tilted`把两个真实tilt积分写成P下exp密度乘x／x²。该原库公式可对总化积分陈述，但本上下文已独立生产全部相关真实可积、真实概率和Z>0，不以其无条件形式绕开这些门。由实数smul=乘法、乘法交换及`integral_div`，对每个theta有actual mean0=M_1/Z、mean1=M_2/Z。

这个身份必须对整个参数函数成立，再用`ContDiff.div`（Operations835，所有theta分母非零）、`contDiff_pi`（Operations113）与两坐标有限向量身份转移C∞。只在theta0匹配两个值，不足以转移均值映射光滑性。

最后对Z的真实D_0用log链式求导；Z非零后导数等于Z^-1*(M_1*pr0+M_2*pr1)。利用上面的actual mean身份与CLM extensionality／smulRight展开，得到冻结最后一项的精确CLM。两个坐标不转置、不交换；从caller没有输入m=gradient。

这些参数积分、有限维紧性、ContDiff归纳、正log和真实倾斜公式的数学门均可在四imports下实现；唯一当前阻塞是冻结header未显式绑定ContDiff-scoped ∞。声明门不等于已经完成未来实现／内核验收。

### 6. 行政／环境绑定（数学与API审查之后）

独立只读核scope两端：54行／7096字节，SHA256 `439e2740c2968acda75ceb7b980a27554e6d72a498e1268913c78ea00e3300da`，与本门绑定一致。没有修改冻结header或TYPE。

五个真实项目源的当前SHA及own olean存在性已定向核查，未重扫整图、未重编旧门：

| 实际相对路径 | SHA256 | own olean |
| --- | --- | --- |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 | 存在 |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d | 存在 |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b | 存在 |
| Shao/OQ3/AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 | 存在 |
| Shao/OQ3/InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 | 存在 |

canonical source-relative path-key JSON compact SHA256独立复现为`5d1b1c34f11a05f81e8636f3809e739b4942d03d2d5f7f82dabbb7fff8e28307`。链为InverseTilt→AtomicMeasure→SummableAtoms→SourceStarter→FiniteConstraints，与实际import行一致。没有读取作者candidate扫描器／JSON正文来建立数学结论。

本轮不重复已完成的5Shao／2501Mathlib物理图、公开2458Mathlib+189外部叶计数、pins／缓存或成功smoke；这些scope中的既有环境记录不替代本票对新作用域门的独立检查。候选文件只核字节hash，得到`5da34cadad30873e42e6d0cb038c5e3036582d04d1a3986cf9d3b6f578808d83`；不读其正文，不把它当证明。

实际只读git观察：branch `feat/oq3-compact-tilt-weak-cramer`；HEAD `53694dec89a2834522e48ab36954fc4528cfee06`；status clean。目标`Shao/OQ3/SourceSmoothMeanMap.lean`不存在。未有本单元source／build／Audit／receipt／新branch，不能报告kernel PASS或完整证明已验收。

固定原件R1 SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`；R2 SHA `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。原件只读，未改来源或旧接受源。

root v39 checkpoint交接属于parent提供的行政更新；五个前置旧源不变，本票没有重跑root成功检查／大图／稳定对象hash。当前检查是声明/API门，不以新root交接自动覆盖新TYPE作用域缺口。

所有remote项目读取经共享server broker并置CPU14–17；未运行任何Lean／probe／Audit／smoke，未写cache／pins，未接触外部CPU0–9任务，无新agent／commit／pub。仅写本新报告及授权远端报告。所有作者future／candidate／implementation笔记均未读。

### 7. 消除义务、直接consumer与剩余

本v1消除了“数学命题是否需要额外q／正定／手工C2输入”的疑虑，核实有界概率、全参数加权矩主控、全阶归纳及真实mean绑定的实际公开路径；但未消除冻结header的ContDiff∞环境缺口，因此不能计为CORRECT声明／实现／proof接受。

恢复正则性路线时，先保留本v1并冻结最小显式作用域修订，focused独立核对后再实施、首strict build、完整module-owner TYPE／公理Audit、独立完整proof门。不能用本票的数学路径代替未来proof。

实际直接consumer为同w/q的均值映射邻域正则性／逆路线；本TYPE没有输出均值导数可逆、局部逆或紧族Hessian谱界。root当前优先的A最后同律／正能量／ratio事件／系数装配可消费已有接受接口，是否暂存本节点是调度决定，不改变本冻结v1的裁决。

FINAL STATUS: CRITICAL GAPS — 数学C∞结论与来源匹配；冻结v1缺少显式ContDiff作用域绑定。最小修复是独立新版header加`open scoped ContDiff`，不改数学输入／输出。当前保留未实现，不接受、不编译、不发布。均值inverse、无界根B、谱标准化、原A装配及所有原根A/B/C/D仍OPEN。

## Focused v2 report: CORRECT declaration, no proof acceptance

# U20e v2 全参数光滑均值映射独立focused声明审查

STATUS: IN_PROGRESS

唯一reviewer lease1；只拥有本新报告及授权remote报告。先仅读取新冻结Lean fences及显式header环境约定，独立翻译并持久化；随后才比较版本／原文／原库／行政绑定。旧v1 scope及CRITICAL票不改。本轮没有实现proof可审，也不运行Lean。

## 新冻结完整imports／TYPE及环境约定

```lean
import Shao.OQ3.InverseTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
```

冻结header显式约定：`open MeasureTheory`；`open scoped Matrix Topology BigOperators ContDiff`；`noncomputable section`。以下∞应按显式ContDiff作用域解释，仍须独立核固定库定义。

```lean
theorem source_log_partition_and_tilted_mean_smooth
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) :
    let P : Measure ℝ := originalMeasure sourceEll w
    let Z : (Fin 2 → ℝ) → ℝ := fun theta =>
      ∫ x : ℝ, Real.exp (theta 0 * x + theta 1 * x ^ 2) ∂P
    let K : (Fin 2 → ℝ) → ℝ := fun theta => Real.log (Z theta)
    let tilt : (Fin 2 → ℝ) → Measure ℝ := fun theta =>
      P.tilted (fun x => theta 0 * x + theta 1 * x ^ 2)
    let mean : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun theta =>
      ![∫ x : ℝ, x ∂tilt theta, ∫ x : ℝ, x ^ 2 ∂tilt theta]
    let pr : Fin 2 → ((Fin 2 → ℝ) →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
    IsProbabilityMeasure P ∧
      (∀ theta : Fin 2 → ℝ,
        Integrable (fun x : ℝ => Real.exp (theta 0 * x + theta 1 * x ^ 2)) P ∧
        0 < Z theta ∧ IsProbabilityMeasure (tilt theta) ∧
        Integrable (fun x : ℝ => x) (tilt theta) ∧
        Integrable (fun x : ℝ => x ^ 2) (tilt theta)) ∧
      ContDiff ℝ ∞ K ∧ ContDiff ℝ ∞ mean ∧
      ∀ theta : Fin 2 → ℝ,
        HasFDerivAt K
          ((pr 0).smulRight (mean theta 0) + (pr 1).smulRight (mean theta 1)) theta
```

## 完整独立翻译与focused疑点

1. 任意同一AtomicIndex权w，仅输入逐项非负和真实HasSum w 1，没有q／完整四矩／正基点／caller概率或光滑性输入。
2. P=originalMeasure sourceEll w固定为实际原逆倾斜律，不能改成atomicMeasure或另取一个存在law。
3. Z(theta)为同P下实际二次指数积分，theta遍历整个Fin2实空间；K就是其真实实log。
4. tilt(theta)是同P的实际quadratic tilted测度，mean(theta)是该测度下X和X²两个实际积分组成的向量。
5. pr_i是真连续线性坐标投影；不是形式导数符号或单坐标差分。
6. 结论先生产P真概率，再对每一个实theta生产exp真Integrable、Z严格正、tilt真概率及该tilt下X/X²真Integrable。
7. 必须先排除不可积exp使tilted=0／log0的总化，再使用归一化密度与log／逆数。
8. ContDiff ℝ ∞ K和ContDiff ℝ ∞ mean要求所有有限阶全局连续可微；显式ContDiff应绑定内层ENat top，不是外层ω解析性。
9. 本门需核新header确实激活该scoped notation，而非只导入含记号定义的模块。
10. ∞含义须与实际contDiff_infty／自然n successor criterion匹配，不可用裸外层top替换。
11. 最后对全部theta的HasFDerivAt K输出h↦mean(theta)0*h0+mean(theta)1*h1，坐标次序为(X,X²)。
12. 真实mean函数必须与归一化矩函数在全部theta相同，不能只在source鞍点匹配一个值再迁移光滑性。
13. 有界P允许每个theta及每个多项式阶k的加权指数矩真可积，但不能把旧点态Hessian直接升级为C∞。
14. 独立可核路径是对全部k的M_k(theta)=∫x^k exp(theta·W)dP建立真实全参数一阶公式，再对所有k同时归纳自然光滑阶n。
15. 导数CLM由M_(k+1)*pr0与M_(k+2)*pr1组成，须先真可积、共同局部参数主控和AE可测，再拆分积分。
16. 共同常数可依赖k／参数中心，但必须在AE x之后覆盖整个参数邻域，不是逐参数临选主控。
17. 自然n归纳的IH应包含全部k，避免以更高k的同阶结论循环证明自身。
18. 实际Operations.smul_const／add／pi与log／div接口须公开可达，所有分母Z非零门由真实正性消去。
19. 同tilt的真概率与绝对连续继承AE界可给X/X²真Integrable；actual integral_tilted才将mean与M1/Z、M2/Z绑定。
20. 当前没有正定性、均值映射局部逆、统一数值导数界或解析ω输出；允许退化原子law和零方向。
21. 只修header不等于实现／kernel通过；四imports／唯一完整TYPE是否逐字保留将在本前缀之后独立比较。
22. 已有v1数学路径可在精确版本对比后带证据复用，不能把v1拒绝自动倒改成通过。
23. 本门不导入PR161原A根或其他pending叶；未来同w/q消费者可用hm0给当前hs，但本TYPE不依赖那些构造。
24. 先核声明语义和原库，再核hash／当前git；不读作者implementation／future／candidate笔记或JSON正文来证明数学。

--- END IMMUTABLE BLIND PREFIX ---

## U20e v2 focused独立声明终票

STATUS: CORRECT

JUSTIFICATION: 两个Lean fences（四imports及唯一完整TYPE）与v1逐字不变；显式`open scoped ContDiff`确实激活固定库中表示C∞的内层ENat top嵌入，关闭v1唯一环境缺口。实际自然阶Fréchet导数判据／contDiff_infty与Operations、log／div／真实tilted积分API支持全参数／全部有限阶数学路径，无需新增caller分析假设。此为声明／环境批准，不是未来实现／kernel／完整proof或均值inverse验收。

盲前缀69行／5136字节，SHA256 `5b340acd14522ffdbe5c17ddc06961bb969305d42ef3200538ac2f79092f31f2`。先完整读v2 TYPE及header、独立翻译并持久化，再比较旧版本／读原库，最后核行政绑定。本节仅追加，未倒改前缀或旧v1票。

### 1. 版本边界：精确修订而非静默修复

独立按原字节比较v1、v2的两个`lean` fences，数量均为2、逐字相同；两文件均LF无CR。四imports没有变化，TYPE所有w/hw/HasSum、P/Z/K/tilt/mean/pr lets、真概率／可积／正Z、C∞及全theta梯度合取均保持原字节。

唯一Lean环境变化在header：旧`open scoped Matrix Topology BigOperators`增加ContDiff。正文另更新标题／版本状态、原A161已发布但待root验收、消费者范围、沿用v39及未来分支说明。这些行政文字差异确有存在，不误称整个scope除一个词外逐字相同；它们没有增加数学输入／改变输出。

旧v1 scope：54行／7096B，SHA `439e2740c2968acda75ceb7b980a27554e6d72a498e1268913c78ea00e3300da`。旧v1完整票202行／19618B，SHA `20484a5393042bacdb8606c839cddda9deb3fce56f6ae9d4fc2beb306546bc47`；其77行／5125B前缀SHA `2b6da1a7cf0db5aeaf5a57ea3eba7d4e154ebf85f6f72c8f10cf99562fcce00d`。本次定向核这两个历史hash仍相同，保留其CRITICAL GAPS历史；不将v2通过追记成v1已通过或曾实施。

新v2 scope两端54行／7574B，SHA `f2daa316ffcbb81fd564f4bdc51f5e991818af98449bb4b3ca8a83609f3d3c8e`。本票所有裁决仅绑定该版本。

### 2. 固定记号及Lean激活机制，缺口确已关闭

实际Mathlib `Analysis/Calculus/ContDiff/FTaylorSeries.lean`112–120：光滑阶类型为WithTop ℕ∞；scoped[ContDiff]的ω是`(⊤ : WithTop ℕ∞)`，scoped[ContDiff]的∞是`((⊤ : ℕ∞) : WithTop ℕ∞)`。两者不同，不能以裸外层top替换来“修复”C∞。

实际固定Lean `Lean/Elab/Open.lean`84–89对`open scoped`逐namespace解析并调用`activateScoped`。本header明确写ContDiff，因而不再依赖被导入模块内部的open命令传播，也不依赖不存在的通用∞记号。ContDiff scope在四imports的公开链上已注册；该新命令只激活记号，不产生新实例／新拓扑／新公理或强弱不同的命题。

因此两处`ContDiff ℝ ∞`现在是所需所有有限阶连续可微，未升级解析ω。无需新import／新缓存／新共享定义；本轮未以Lean probe作“验证”或预报elaboration成功。

### 3. 真实阶数与公开API focused复核

以下固定库实际声明已定向重读，不凭scope中的API名字猜测适用性：

| API／位置 | 精确门与当前适用性 |
| --- | --- |
| ContDiff/Defs.lean1114 `contDiff_infty` | `ContDiff 𝕜 ∞ f ↔ ∀ n:ℕ, ContDiff 𝕜 n f`；同内层∞，正好合成全部有限自然阶 |
| 同源1125 `contDiff_zero` | 阶0 iff全局Continuous，可由所有theta的HasFDerivAt先得连续 |
| 同源1171–1173 `contDiff_succ_iff_hasFDerivAt {n:ℕ}` | 阶n+1 iff存在阶n的真实CLM导数函数且∀x HasFDerivAt；用自然n避免解析阶额外条件 |
| Operations.lean643–645 `ContDiff.smul_const` | 标量C^n函数乘固定向量／CLM仍C^n，用于M_(k+1)*pr0及M_(k+2)*pr1 |
| 同源197–199 `ContDiff.add` | 同域／同值空间的C^n函数相加，用于整个导数CLM函数 |
| 同源113–118 `contDiff_pi`／pi' | Pi值函数光滑iff全部坐标光滑；适用真实Fin2 mean |
| 同源835–838 `ContDiff.div` | 分子分母C^n且∀theta分母≠0；Z>0真实消去此门 |
| Log/Deriv.lean182–184 `ContDiff.log` | 实函数C^n且处处非零；不是可对log0使用的无条件接口 |

Operations实际public import Comp、Deriv.Inverse等；其自身34行也显式open scoped ContDiff，说明导入定义与当前header激活是两个不同层面。实际contDiff_succ criterion输出的CLM类型与pr_i及smulRight表达相容，不是标量方向二阶或Peano展开替代真正全阶Fréchet光滑。

### 4. 来源／真实对象／概率与正配分仍完整

沿用v1已经独立实读并通过的R1 report137–159、R2 report38–60及root-contract26–30的来源判断。R1 SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`；R2 SHA `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`。同P的W=(X,X²)、真实log配分和真实tilt mean对应原文。当前只有质量约束，不声称原P中心化、正率／正定或特定q鞍点。

`InverseTilt.lean`51–55的公开originalMeasure_isProbabilityMeasure从hw≥0及hs真实生产P概率；57–60给同P AE |x|≤B=4+sqrt10。26–34的公开integrable_continuous_of_fixed_bounds给该真实概率下任意连续实函数真Integrable。此路径对允许退化的非负w成立，不暗加正基点／四矩／P概率输入。

所以对全部自然k与所有实theta，M_k(theta)=∫x^k exp(theta0*x+theta1*x²)dP均真可积。Z=M0，真实概率非零后integral_exp_pos给Z>0。先有这些事实，才可使用log／分母和实际tilted概率；不以不可积倾斜总化为0制造输出。

实际Tilted.lean126–131的isProbabilityMeasure_tilted消费exp真Integrable及NeZero原P。280–281的tilted_absolutelyContinuous把P的同AE界传给各实际tilt；真实tilt概率下再对连续x／x²用有界积分门，得TYPE要求的两个真Integrable。也可用293–295的integrable_tilted_iff，但不能省略其exp可积门。

TYPE的P、所有theta的tilt和mean始终来自同w，不是未绑定normalized proxy。q和完整四矩确非此正则性所需；以后同q/w消费者可从hm0得到hs，但不能将当前单元说成依赖原A161或U20c/20d叶。

### 5. 全参数／全阶路径可实现性（自包含复述）

M_k对参数的真实导数CLM为`M_(k+1)(theta) • pr0 + M_(k+2)(theta) • pr1`。这里对参数theta1求导产生x²，而不是对样本x求导的2x；坐标次序与TYPE一致。

对每个固定k、theta，取参数固定正半径闭球及样本固定紧支撑区间的积。相应CLM被积导数在二者上联合连续，故有同一有限operator norm界C。AE x后∀邻域参数均受该C控制；C可依赖k／中心，不要求全参数统一数值界。

实际ParametricIntegral的`hasFDerivAt_integral_of_dominated_of_fderiv_le`所需门是：真实参数邻域、eventual F可测、中心F真Integrable、中心F'可测、AE样本后全邻域参数的共同可积operator norm主控、AE样本后全邻域的真实点态HasFDerivAt。上述有界性／连续性与有限概率满足这些门；再在加权矩真可积后拆CLM积分，得到该D_k公式。

必须在本新模块诚实重证必要private辅助，不能跨调用PR151的private weightedMoment等名字。该生产路径不依赖仅有的鞍点一／二阶公开结论，也不以它们自动推出邻域C2。

共同归纳的命题为“对全部k，M_k是C^n”：n0由全点真实导数给连续；n+1时IH已经同时提供M_(k+1)、M_(k+2)的C^n，smul_const/add使D_k为C^n，配合∀theta真实HasFDerivAt套自然n successor criterion。不存在以待证更高k同阶光滑循环证明自身的步骤。

对所有自然n完成后套contDiff_infty，得到M0／M1／M2乃至全部M_k的真正C∞。这条路径可覆盖每个theta而常数仅局部选取；没有要求参数空间紧，也没有把逐点主控误作全参数共同数值界。现在header已把最后∞与该实际API同义绑定。

### 6. 实际mean全函数身份与最终梯度

实际Tilted.lean230–232的integral_tilted对每个theta把真实tilt积分改写为P下exp密度除真实Z后的加权积分。该公式可对totalized积分无条件陈述，但本上下文已先生产相关真实可积与正Z，因此不是总化捷径。

用smul=实乘法、交换乘积及integral_div得到对全部theta的actual mean0=M1/Z、mean1=M2/Z。只有这个全参数函数身份建立后，才由M1/M2/Z的光滑及Z处处非零，用ContDiff.div和contDiff_pi转移整个mean的C∞。

Z=M0光滑且严格正，ContDiff.log给literal K的C∞；对M0的真实一阶公式作log链式求导，再用actual mean身份和CLM外延／smulRight展开，得到最后∀theta的准确梯度。该过程未在单个theta0比较值后错误迁移导数，没有假设m=∇K作为caller前提。

退化law、零方向以及任意大实参数均保留。均值映射可常数或不可逆；当前只给真实mean光滑，不给正定／局部逆／紧族谱下界／解析ω。

### 7. 定向metadata与现状（最后）

scope-v2两端SHA／行字节均为本票绑定的新值，旧scope及旧202行票hash保持。新scope对四imports与唯一TYPE的原字节比较为真；本门未修改任何版本。

从刚经本review完整核验的U22a正式74项目字典中独立取五个核心条目：FiniteConstraints、SourceStarter、SummableAtoms、AtomicMeasure、InverseTilt，canonical subset SHA复现`5d1b1c34f11a05f81e8636f3809e739b4942d03d2d5f7f82dabbb7fff8e28307`。它们与v1已核接受源、v39同条目相同；本轮没有再读所有源／对象重算hash或重跑大图。

既有candidate-cache.json仅核文件hash `5da34cadad30873e42e6d0cb038c5e3036582d04d1a3986cf9d3b6f578808d83`（2168B）；不读其正文／作者扫描器，不以候选标签证明数学。四imports既有5Shao/2501Mathlib物理、2458公开Mathlib+189外部叶记录沿用，不重新扫描／声称本focused门重新认证整图。五核心源／对象及原库readiness已在接受链独立核过，修订无新依赖。

实际当前branch是`feat/oq3-source-counterexample-root`，HEAD `293d3394546eaec284d39b86ed1f6449af7f70c8`，status clean；U20e `Shao/OQ3/SourceSmoothMeanMap.lean`不存在。没有U20e源码／probe／build／Audit／新branch，也不预报实际elaboration／kernel PASS。未来正常从accepted v39新branch属于后续实施，不回写旧heads。

本轮仅CPU14–17的轻量server读取，无Lean／probe／smoke／旧Audit或成功门重复、无cache／pins／source／旧票写入、无新agent／chat／commit／pub；外部CPU0–9／80GiB任务未触。root独占共享定义、缓存、版本、集成和根验收。

### 8. 最终裁决与边界

v2修复了v1明确指出的notation环境缺口，并完整保留已独立核通的真实概率／所有指数矩可积／正配分／全阶递推／实际mean身份／真实梯度数学。没有新关键缺口，因此此冻结v2声明可进入后续实施门；不能仅加scope就把未来proof计为完成。

未来仍须新源诚实实现所有k/alltheta的真实求导与全阶归纳、首严格server检查、actual module-owner全TYPE／公理Audit及独立完整proof终审。当前未闭合均值inverse、任何全族标准化／谱结论或原B/C/D；原A161的正式root验收另属root流程，本声明不给A添加新前提，也不宣告任何根关闭。

FINAL STATUS: CORRECT — 绑定scope-v2 SHA f2daa316ffcbb81fd564f4bdc51f5e991818af98449bb4b3ca8a83609f3d3c8e；focused声明／环境门通过，0实现／0proof验收／0均值inverse闭合。旧v1 CRITICAL票及其盲前缀保持历史原字节。
