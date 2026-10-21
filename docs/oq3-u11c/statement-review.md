# U11c 独立声明与来源审查

## 第一阶段：只读 Lean 代码块后的逐类型盲译

本节在读取scope解释、R1及本次实际依赖源之前落盘。本次仅提取eighteenth-unit-scope.md的Lean代码块：零定义、五个完整目标签名。实测scope SHA256=`7308b8a152c069b947ec8e26d7d9cc4524e8711b9893b7bb8d9e05a8354ccf11`。未读作者API/其他notes，尚无实现或构建。

1. 任意非负真实Summable权重w、B≥0，实函数f只需在每个真实fixedAtom上满足|f|≤B，就对atomicMeasure(w)真正Integrable。签名不要求f全局可测，须独立核原子支撑是否足以保证AE可测及有限积分。

2. 两组非负可和权重w/v，同一f只在全部fixedAtom上有|f|≤B，则两个真实单点律积分差的绝对值≤B·整个AtomicIndex权重L1。没有概率归一化或f全局可测门，须由可和质量与原子求和解释支持，不能仅靠总化积分。

3. 两组非负真实HasSum到1的权重给真实概率律。任意n、B≥0、全局可测路径函数f，只需对每个原子索引tuple z:Fin n→AtomicIndex，在实际样本路径fixedAtom∘z上有|f|≤B，即得真实n重Measure.pi积分差≤B·n·atomicMassL1(w,v)。界并非要求所有实路径全局有界，必须提升共同原子tuple支撑，并对混合乘积/Fubini有真正可积性；n=0也包括。

4. 任意ell≥0、q/p、非负可和r、阶段J，加实际M非奇异、M p=target q，以及极限/有限四旧权重均非负，给同一原子tuple有界可测f的极限与有限实际n重π积分差≤B·n·C(ell)·整个未来r尾。须真实建立两律概率门，再接权重L1尾界。

5. 再给q≤2，用真正sourceTail(q,n)的指标乘exp(−ell·normalDeviation(q,z))作路径函数；极限与有限实际n重π下的期望差≤exp(11ell n)·n·C(ell)·整个未来质量尾。没有归一化sqrt(2πn)系数，也没有P换测度等式或常数连续性结论。

后续重点核原子AE可测/可积、真实路径乘积及逐坐标混合支撑、n=0、矩阵/约束消费和同一固定q/p/r/ell的全部n/J应用。所有根仍OPEN，当前尚无裁决。

## 第二阶段：真实来源、实际原子API与固定乘积库

盲译落盘后读取scope解释和真实R1 499–520。R1实测SHA256=`3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。501–502定义sqrt(2πn)乘实际π^n似然指标期望；509–513给Y≥−9产生的exp(11ell n)界与有限产品比较；516–520接固定线性补偿尾质量界。候选五项只证明直接权重L1比较及其尾量应用，期望中未漏换成另一个法或对角样本，也没有声称504–507的精确P换测度已由这些目标证明。

直接只读实际已审AtomicMeasure.lean SHA256=`59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39`：21–22行atomicMeasure为同一fixedAtom上的Σ ofReal(w_i)·dirac；39–42行非负HasSum w1给真概率；44–49行无条件AE在共同fixedAtom范围；57–64行integrable_atomicMeasure_iff对任意f明确等价于Summable(w_i‖f(atom_i)‖)，没有全局可测前提；66–75行integral_atomicMeasure在真实Integrable门后给精确原子积分级数。故前两个候选不要求全局可测与实际API一致，不是省掉一个不可替代的测度前提。

指定服务器固定库实际SumMeasure.lean SHA256=`b4f63c8acdd8f1c15e4762497def59cf9073063759726a113121fd219a53098a`，103–107行integrable_sum_dirac_iff与168–171行integral_sum_dirac_eq_tsum确认上述任意原子值函数语义。可数原子支撑允许任意f与其在该支撑上的可测延拓AE相等，真实可积性仍需加权范数可和，候选恰能从有界原子值与Summable w给出。

实际固定Integral/Pi.lean SHA256=`43c50a9d9a683b2050e145154410a7260c3dd84f3ec3010630cc6b90572afcd9`，第8行public import Integral.Prod；指定Pi.olean实际存在。本次只读，没有下载/改cache或构建。Pi中的有限产品对象是真Measure.pi，并有有限乘积积分/坐标积分接口；任意路径f的Fubini必须另外消费真实可积性，不能把特殊可分离乘积公式当成任意f定理。

实际Integral/Prod.lean SHA256=`8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05`：65–76行在SFinite下给强可测参数积分，230–243行integrable_prod_iff明确要求AE强可测与可积门，334–343行真实可积联合函数给可积参数积分，443–444行integral_prod明确要求Integrable f。这些API支持下述合法逐坐标路线；不会自动允许对不可积函数交换积分。

## 第三阶段：逐目标独立数学审查

### 1–2：一般有限原子测度，真实可积后比较

由w_i≥0、|f(atom_i)|≤B有`0≤w_i‖f(atom_i)‖≤B w_i`。Summable w给B w可和，实非负级数比较得到真实加权范数Summable；实际integrable_atomicMeasure_iff因此给Integrable f。无概率门的测度总质量可为任意有限非负数，论证仍成立；B=0或w全0也成立，不靠积分总化零分支。

第二目标分别对w/v应用第一目标，才用实际原子积分级数。两条加权f值级数均真实绝对可和，可合法相减：积分差为Σ'(w_i−v_i) f(atom_i)。又有Summable(w−v)，所以Σ'|w−v|是真实可和的L1。逐项`|(w_i−v_i)f(atom_i)|≤B|w_i−v_i|`与无限三角不等式给所写界。这个系数正是B，没有额外概率归一化或系数2要求，也没有把weight L1命名为TV。

### 3：atomtuple界足够支持混合乘积与逐坐标替换

由hw/hv与HasSum各到1，实际atomicMeasure_isProbabilityMeasure建立μ/ν是真概率。对任意每坐标从μ或ν选择的混合有限产品ρ，每个坐标都AE在同一fixedAtom范围；通过实际产品评估的AE拉回及有限坐标全称组合，ρ-AE路径可以写成fixedAtom∘z，z:Fin n→AtomicIndex。hbound遂给|f|≤B的ρ-AE界。hf给ℝ值函数的AE强可测，ρ有限概率，所以每个混合产品下f真正Integrable。这里没有要求或推断全实路径上|f|≤B。

令ρ_k前k个坐标取ν、其余取μ，从ρ₀=μ^n到ρ_n=ν^n。相邻两律只在一个坐标不同，其余坐标的共同乘积仍是真概率并AE有原子tuple表示。对每个这样的其余原子tuple，冻结它后的单坐标函数在全部fixedAtom上仍被B界住，前两目标给单坐标积分差≤B·L1(w,v)。两条联合函数在各自混合产品下已真正可积，所以Fubini、参数积分可测/可积与积分相减均合法；非原子其余tuple只占零集，不需要假设所有切片都可积。

对其余坐标的概率律积分，单步差仍≤B·L1。再用n次有限三角不等式得到B·n·L1，与签名系数一致。该路线明确分开真实联合可积、AE切片正当性及参数积分，未从不可积的总化积分制造等式。固定库已有上述Fubini和参数可测API，实际有限产品的测度保持重排可以隔离被替换坐标，不需新增TVcache。

n=0时只有唯一空路径，两个Measure.pi都是相同空乘积概率，两个积分完全相等；右侧n因子0，界成立。hbound此时只约束该唯一tuple处的f值，与一般量词兼容。没有把n重积换成一个变量重复n次的对角推前。

### 4：实际limit/finite概率门与权重尾界

本次实际读取U3a SummableAtoms.lean SHA256=`0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b` 107–129行limitingMoment_hasSum，明确消费ell≥0、hM、hc、r非负及Summable r；取feature分量0（恒为1、target分量0为1）得到HasSum limitingMass 1。实际U3c FiniteStageMeasure.lean SHA256=`1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1` 21–31行finiteMass_constraints消费hM/hc，分量0同样给HasSum finiteMass 1。

hl/hr按Sum两侧给limit全部权重非负，hj/hr及j<J零延拓给finite全部权重非负。因此两律是真概率，第三目标可真实应用。U11b AtomicTailControl.lean实测SHA256=`ec528d9af8b475f1db8a78c93ab917d754365d280027a86be2823825b19c2f79`，其已完整独立CORRECT的全AtomicIndex L1尾界给L1≤C(ell)·T_J，乘以非负B·n得到第四签名的确切系数与乘法结合。hM此时真实用于质量1，不能沿用U11b纯线性目标无需hM的理由将这里的概率门删除。

允许hr零项与旧质量仅非负都足够，不需全严格正。J=0时finite只有四旧点；两律仍由同一矩阵/约束门保证概率，尾量为全部r，比较适用。参数ell/q/p/r先固定，J/n均是同一族中的输入；源族既有统一p/q/eps门可在它们外选择，不须重选随n变化的P。

### 5：真实似然指标的可测性与原子tuple有界

实际SampleBoundary.lean SHA256=`7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2`：19–27行是实际有限和normalDeviation和有正energy门的sourceTail；41–50行sourceTail_measurable对任意实q成立；104–115行fixedAtom_normalValue_lower给每个原子Y≥−9；128–142行normal_likelihood_weight_bound对ell≥0、q≤2给每条满足该逐坐标下界的路径exp(−ell d)≤exp(11ell n)。

normalDeviation是实际坐标多项式有限和，连续可测；exp复合与可测sourceTail指标给当前f真正Measurable。每个原子tuple都有逐坐标Y≥−9，所以其非负似然指数≤B_n=exp(11ell n)，指标只能将非负值变成0。因此|指标·指数|≤B_n在真实原子tuple上成立，可直接应用第四目标，B_n>0自动给hB。并未错误地声称exp(−ell d)在所有实路径上全局有界，也没有以|Y|≤9代替单边支撑界。

n=0时energy=0，sourceTail为空，两个期望都是0，右侧亦0；q≤2而无q>0也正确，因为可测性和指数界不需几何平方化的q>0门。当前函数与R1的实际似然指标一致，尚未乘sqrt(2πn)；该固定非负因子可另乘，但精确换测度(27)、连续性(30)和实际LLT/witness均不由本签名推出。

## 最终声明裁决

STATUS: CORRECT

JUSTIFICATION: 零定义五目标在准确输入下成立。前两条的任意f原子可积性与实际已审API一致；第三条仅atomtuple有界已足以保证所有真实混合有限产品的AE界、可积性及合法Fubini，逐坐标差系数为B·n·L1且包括n=0。第四条实际消费非负性、hM/hc和约束HasSum来建立两律概率；第五条使用真实可测尾事件和Y≥−9的原子似然界。固定参数、J=0与全索引L1尾接合无关键声明缺口。

这是仅声明/source gate，尚无AtomicProductControl.lean实现、完整证明审查或U11c构建/Audit成功声明。未读作者API/其他notes、未改共享cache/源/旧报告或运行任何成功目标。当前不证明源(27)精确换测度、测度TV/逆倾斜TV、(30)常数连续性、LLT或最终对角。根A/B/C/D全部OPEN。
