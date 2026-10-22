# U19a SourceGlobalExponentialTests 完整独立证明审查

STATUS: IN_PROGRESS

## 一、actual公开类型的独立盲译检查点

本轮承认先前声明审查上下文存在，但先重新仅从实际source提取两个完整公开TYPE并独立翻译；未读取本次实现proof、private/helper/生成项、作者receipt或成功日志。0公开DEF，下面完整保留两项类型及全部长续行。此检查点不是本轮CORRECT裁定。

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

第一项实际TYPE逐量词重译：

1. 任取实q和w:AtomicIndex→ℝ；每个w_i≥0，未要求严格正。
2. 对每个k:Fin4，实际级数w_i*constraintFeature sourceEll (fixedAtom i) k有真正HasSum到constraintTarget q k。
3. type没有qwindow、hbase正性或协方差正定假设。
4. 结论第一合取项先对所有有限实s/t量化；同一个originalMeasure sourceEll w始终不换。
5. exp(sx+t x²)在该真实measure下Integrable，实际实积分严格正。
6. 测试值s(q/4)+tq−log(该积分)≤同一个saddleRate sourceEll q w。
7. 第二合取项在特定实参数(8sourceEll,−sourceEll)精确取等。
8. 没有把saddleRate定义成supremum或新增globalRate；未来proof必须从实际法则证明上界与取等。

第二项实际TYPE逐量词重译：

1. 任取实q且1<q<103/100，同w≥0及完整4行HasSum；q/w/law先固定。
2. 任取实a、c，仅c>0，不限制c在支撑能量区间。
3. 弱尾门为(√q/4)*√c≤a，保留等号边界。
4. 仅排除(a,c)=(q/4,q)，形式为a≠q/4∨c≠q。
5. 结论存在两个有限实s/t，可依赖该固定q/w/a/c，但不得重选q或w。
6. 同P上的exp(sx+t x²)真Integrable，其实际配分积分>0。
7. 该真实测试值s*a+t*c−log积分严格大于同saddleRate。
8. c<1、c>1+H、p=0/1、c=q但a>q/4，以及a²>c等不可实现矩点均未被删除；proof必须覆盖。
9. 没有手工KL界、rate-gap、已知优化器、entropy-duality、可积性或正配分作为额外输入。

本轮后续检查必须区分：类型为真、当前具体proof完整、内核既有证据三层；不能把本盲译或旧声明CORRECT作为完整proof接受。


## 二、真实来源／冻结类型和全部324行proof语义

本节在本轮66行实际公开TYPE独立盲译已落盘之后追加。已重新读冻结scope68与R1真实146–237及当前完整324行source，包括所有3个private theorem与每个local；随后已读全部12个actual DECL/TYPE的所有长续行与公理行。尚未读取作者本单元receipt、Audit实现/计数绿灯或build日志作证据。以下首先给独立数学判断。

### 来源及实际对象

R1真实sourceEll=log(31/30)>0、Y=8X−X²、π的四约束给E1=1、E(X²−4X)=0、E[Xexp(−ellY)]=0、EX²=q；所以EX=q/4。P是π反向指数倾斜，Z=Eπexp(−ellY)，λ0=ell*q+logZ。原161–237的目标是固定候选全局正尾最小；本模块通过真实指数测试完成候选上界／取等和其他正尾矩点严格分离，不证明一般ρ-KL恒等式／Markov data-processing(9)/(10)。

两actual完整公开TYPE与冻结scope68语义逐量词一致：第一项q全实，无qwindow/hbase；第二项q窗口、c>0和弱尾不等号及唯一候选点排除均完整。所有s/t的配分属于同一个actual originalMeasure sourceEll w。没有新public或private DEF、globalRate、domK、扩展supremum、代理law或外加手工gap。有限测试意味着参数是实数，不是要求w仅有限支撑。

实际已接受定义核对：atomicMeasure w是ofReal(w_i)加权fixedAtom Dirac和，originalMeasure ell w=(atomicMeasure w).tilted(−ell*normalValue)，inverseNormalizer是其实际反向exp积分；saddleRate=ell*q+Real.log Z。hw/hm不能被裸tsum=1代替。本proof每处先由hm0得到真实HasSum w1，正确提供两种概率的生成门。

### Private 1：original_quadratic_exp_log，源16–44

1. 输入任意实ell、w≥0、真HasSum1及任意实s/t；ell无需正或固定sourceEll。源23–24先分别建立真实atomicMeasure与originalMeasure概率实例，后者沿已接受InverseTilt由bounded inverse-exp真Integrable产生，不是tilted不可积时的零测度。
2. 源25–34分别用真实AE界和连续性给P上的exp(sX+tX²)及π上的exp((s−8ell)X+(t+ell)X²)真Integrable。源41由integral_exp_pos hi给P真实配分>0；源44另由hj给真实分子>0，再由inverseNormalizer_pos给Z>0。
3. 源35–40完整函数外延展开Y，精确得到负tilt加测试指数=(s−8ell)X+(t+ell)X²。没有错号或另一倾斜law。
4. 源42实调公开全名`MeasureTheory.integral_exp_tilted`（Tilted.lean236–249）得到实际分子/Z，源44在两个正数的ne'下才用Real.log_div。此API本身总定义，但当前proof已真排除积分未定义0和log0。该private完整type交付Integrable、正分配函数、精确log式三合取；所有后续hprovide与第一public都消费此实际同law引理。

### Private 2：atomic_quadratic_log_lower，源46–101

5. hm0给HasSum1并建立π真概率；atomicMeasure_mean给真实Integrable X和EX=q/4，atomicMeasure_constraints row3给真实Integrable X²和EX²=q。没有使用只适用于全w>0的熵接口或假定q正。
6. h=s(X−q/4)+t(X²−q)。源62–64先由两个真实可积中心化函数构造hh；65–68由连续有界支撑给exp(h)真Integrable。69–82还显式绑定hxs/hx2s/hss/htt，在integral_add、两次const_mul和integral_sub前逐项供给Integrable，严格得Eπh=0。
7. 源83–91给1+h真Integrable，调用integral_mono_ae hlin he及全实Real.add_one_le_exp，在真概率下积分得到1≤Eπ exp h；不诉诸未证Jensen/entropy-duality。
8. 源92–97逐点指数函数恒等式为exp(sX+tX²)=exp(sq/4+tq)*exp h。右侧由he真Integrable且常数有限，因此原raw指数也真Integrable；不需要额外积分假设。源98–100移出常数并用exp因子>0、Eπexp h>0才用log_mul，log_exp真实还原线性常数。Real.log_nonneg hge给所需下界。
9. 因而这个private对全实q/s/t都成立，无协方差非退化、全原子正性或小球门。它只给本π的标准指数下界，不把任何优化器或全局率定义作为前提。

### Private 3：raw_energy_log_upper，源103–117

10. 输入任意真概率mu、实际固定AE有界、H>0、真实能量双界及实际EX²=q，对每个实u调用已完整独立接受的bounded_energy_logMGF_le_bernoulli。该API给centered exp真Integrable hi、实际积分>0 hp及真实log界，正/负/零u都可用。
11. 源110–114精确exp(uX²)=exp(uq)*exp(u(X²−q))，右侧由hi真Integrable，故raw同样真Integrable。116在正exp因子及hp非零下用integral_const_mul/log_mul/log_exp，将centered上界转成`log E exp(uX²)≤u+log(1−z+zexp(uH))`。
12. z此private未额外假定在(0,1)，其所用accepted Energy API通过真能量积分比较先证明binary partition>0，非靠log总化。因此private量词没有隐藏qwindow；主proof实际还有hz0/hz1可供binary test。主proof另192–197显式构造每个raw指数的hrawi/hrawp再消费不等式。

### Public 1：全实s/t候选上界和精确取等，源119–151

13. 由hm0真实HasSum建立π概率后，对每个任意实s/t实调Private1，得到P真Integrable和正配分。把其精确log式代入后，对同π实调Private2于α=s−8ell、β'=t+ell，得到`log N≥(s−8ell)q/4+(t+ell)q`。
14. 代数给`s q/4+tq−logMP≤ell*q+logZ`，就是实际saddleRate。这个计算没有除q、取√q、使用q窗口或任何先假定的globalRate；第一actualTYPE覆盖全实q真实成立。
15. 第二合取项又实调Private1于θ0=(8ell,−ell)，正确将π分子简为Eπexp0=1（π概率已建立），得到logMP(θ0)=−logZ。随后neg_mul和ring仅作精确代数，测试值=ell*q+logZ。取等属于同actual P；未只证明“存在别的测试近似候选值”。

### Public 2准备：实际概率／能量范围／所有u的证人搬运，源153–227

16. 完整public前提中w仅非负，hm0给真实HasSum与π概率；row3给EX²=q，AE界来自actual atomicMeasure_ae_bounds。q>1才推出q>0，ell正来自公开sourceEll_pos，未将ell改成1/30。
17. H=25+8√10。源178–182用真实(√10)²=10和√10≥0严格证明50<H<51与H>0（25/8<√10<13/4的等价有理平方界）；不是小数近似。183–191对1≤|x|≤4+√10分别平方，借sq_abs精确得到1≤x²≤1+H；上界(4+√10)²=26+8√10。hw零项/缺失基点不影响这条支持AE事实。
18. 192–197先对所有实u由连续有界给hrawi，再integral_exp_pos给hrawp。每个之后被log的raw numerator都真实正且可积，无需重新选择法则。
19. B=8ell*a−ell*c+logZ。局部hprovide 199–221对于任意实u，若证明`λ0<B+u c−log Eπexp(uX²)`，就实调Private1于(8ell,−ell+u)，显式函数外延he消去多余项并给同P真Integrable和正配分，严格导出实际公开证人(s,t)。不是只给未归一化π上的代理测试。
20. T=|λ0−B|+1>0，源224–227由le_abs_self严格得λ0<B+T。所有量均是有限实数；此处没有假定λ0本身正，证明严格T余量仍成立。

### Public 2支撑外低能量，源228–241

21. c<1时u=T/(c−1)，hden严格负且非零，hu严格负，field_simp在此ne后精确给u(c−1)=T；参数虽可能很大仍是有限实数。
22. X²≥1乘u≤0正确反向给uX²≤u，再exp单调；实际integral_mono_ae以hrawi和π上真可积常数为门，π质量1后给Eπexp(uX²)≤exp u。hrawp>0之后才Real.log_le_log，再log_exp给log≤u。
23. 因而`B+u c−lograw≥B+u(c−1)=B+T>λ0`，hprovide交付同P的实际有限测试。未因不可实现矩点直接声称空结论，也未用u=−∞。hc0仍全局保留但这一分支不需额外能量可行性。

### Public 2支撑外高能量，源242–255

24. c>1+H时u=T/(c−(1+H))>0，正分母ne'之后精确约掉给u(c−(1+H))=T。X²≤1+H乘u≥0，实际两侧可积比较给raw≤exp(u(1+H))。
25. 正raw取log得lograw≤u(1+H)，所以同样B+u c−lograw≥B+T>λ0，hprovide给有限实s/t。所有c>1+H包括任意远off-support点；没有删成仅“可实现矩点上的分离”。

### Public 2闭能量区间及R=1，源256–285

26. 两支撑外分支的否定真实给1≤c≤1+H，包含两个端点。此时仍用原hc0和q>0得√c、√q严格正，R=√c/√q>0；平方恒等式及q.ne'之后清分母证明c=qR²。
27. 源268–275先证明qR/4=(√q/4)√c（用√q²=q和√q.ne'），才将原弱tail门改为qR/4≤a。没有把一般a改成边界等号，或强加a²≤c。
28. R=1时c=q，hne真实排除a=q/4；由弱tail与hne推出a>q/4。真π概率给raw u0的积分1，hprovide 0配log1=0和c=q，最后ell>0使增量8ell(a−q/4)>0。候选点本身恰被显式排除；同c=q而更大的a完整处理，未丢失尾内点。

### Public 2闭区间且R≠1，源286–321

29. 从真实1≤c≤1+H和c=qR²/H>0得到p=(qR²−1)/H∈[0,1]；qwindow/H>50给z=(q−1)/H∈(0,1)。这些正性和端点门在调用binary API之前明确提供。
30. 实调binaryRelativeEntropy_source_gap同q/H/R（hR>0、hRone≠1、hp0/hp1齐全），得到(7/200)(R−1)²<binaryD(p,z)。源295–298用真实sourceEll<1/30、q>0和q<1.03得到ell*q<103/3000<7/200；只有R≠1才给平方严格>0，故L=ell*q*(R−1)²<binaryD。
31. 实调exists_binary_exponential_test，在p=0/1仍仅需要严格L<binaryD，不要求端点sup由有限theta精确达到；已接受API的两端点显式有限log见证有效。当前obtain得到theta/htheta（binary partition正性分量虽不再使用，API仍真实交付）；没有无限参数或一般KL对偶假设。
32. u=theta/H，H.ne'之后huH=uH=theta。实调Private3于同π/q/H/u，rw huH后得到lograw≤u+logBbinary。htprod在同c=qR²下精确把theta*p改为u(c−1)；不改变概率或中心。
33. 弱tail给hdelta=8ell(a−qR/4)≥0。源316–320的精确函数/代数身份为`B+u c−λ0 = hdelta−ell*q*(R−1)²+u c`。与htheta的严格`L<u(c−1)−logBbinary`和Private3上界相加，得到`B+u c−lograw>λ0`；严格性来源binary-test余量，不需要δ>0。hprovide再真实输出公开测试与Integrable/正partition。
34. 因此四种情形穷尽所有c>0。c=1、c=1+H在闭区间被保留，p0/p1不除p/1−p，a²>c等不可实现点也由相同不等式处理。没有调用hbase正、协方差严格性、原C law重新选q/w、generalKL或root globalRate。

### 当前数学裁定及原义务边界

实际全部324行每一步有上述门支撑，三个private引理没有把目标重新作为输入；公有两结论均已由当前proof完整产生，无实质缺口。第一目标θ0是真的候选点所有有限测试的最大值；第二目标只在目标实际正尾点域产出真测试。未来canonical扩展supremum仍由root从这些admissible证人对接，不在本模块私定义。

D_x此处c>0且a≥(√q/4)√c，是c>0相对域中的弱尾边界，不能误称R²闭集；c=0明确不在type。该结果消除root真实全局率函数消费的候选上界/取等/严格offcandidate分离义务，不等同于证明一般ρ-law KL唯一性、(9)/(10)或所有源根装配。未声称原24exactζ、literalPhi、其他局部saddle常数或根A–D自动闭合。

## 三、全部12 actual DECL/TYPE与传递公理

在完整proof/实际API语义检查之后，server读取actual-declarations.txt全部94行、所有长续行，非仅grep首行。两个公有完整TYPE与第一节actual源签名逐项相符；三个private完整实际类型没有额外遗漏前提；七个生成项的真实universe/typeclass/非零条件逐项如下。

名称约定：T=`Shao.OQ3.exists_source_tail_exponential_separator`；私有PFX=`_private.Shao.OQ3.SourceGlobalExponentialTests.0.Shao.OQ3.`。public第一目标完整名`Shao.OQ3.source_saddle_exponential_value_bound`，无generated子项被隐藏到别的公共目标。

| 实际Audit次序/DECL | 完整TYPE的独立核验 | 实际AXIOMS |
| --- | --- | --- |
| 1 source_saddle_exponential_value_bound | 第一节完整q/w/hw/hm；∀实s/t真实P指数可积/正积分/候选值≤λ0，且θ0精确等于λ0；无qwindow | propext, Classical.choice, Quot.sound |
| 2 T._simp_1_5 | ∀{M₀:Type u₁}[MonoidWithZero M₀]{a}[IsReduced M₀](n:ℕ)，a≠0→(a^n=0)=False。IsReduced不能删 | propext |
| 3 PFX atomic_quadratic_log_lower | ∀q实,w，w≥0→完整sourceEll4HasSum→∀实s/t，sq/4+tq≤log E_atomic exp(sX+tX²)；无额外q或非退化前提 | propext, Classical.choice, Quot.sound |
| 4 T._simp_1_1 | ∀{α:Type u₂}[Zero α][OfNat α 2][NeZero 2]，(2=0)=False | propext |
| 5 PFX original_quadratic_exp_log | ∀ell实,w，w≥0→HasSum w1→∀s/t实，真实originalMeasure ell w上的Integrable∧正partition∧logMP=logE_atomic exp((s−8ell)X+(t+ell)X²)−logZ；ell全实 | propext, Classical.choice, Quot.sound |
| 6 T._simp_1_4 | ∀{M₀:Type u₁}[Mul M₀][Zero M₀][NoZeroDivisors M₀]{a b}，a≠0→b≠0→(a*b=0)=False | propext |
| 7 T._simp_1_7 | ∀{R:Type u₁}[AddMonoidWithOne R][CharZero R](n:ℕ)，(↑n+1=0)=False | propext |
| 8 T._simp_1_6 | ∀{G₀:Type u₃}[GroupWithZero G₀]{a}(n:ℤ)，a≠0→(a^n=0)=False，保留整数幂和非零门 | propext, Classical.choice, Quot.sound |
| 9 T._simp_1_3 | ∀{α:Type u₂}[Zero α][OfNat α 4][NeZero 4]，(4=0)=False | propext |
| 10 T._simp_1_2 | ∀{α:Type u₂}[Zero α][OfNat α 3][NeZero 3]，(3=0)=False | propext |
| 11 T | 第二节完整qwindow/w≥0/4HasSum/全a,c>0/弱tail/hne，产生同真实P真Integrable/正配分的有限s/t且值>λ0；无漏off-support | propext, Classical.choice, Quot.sound |
| 12 PFX raw_energy_log_upper | ∀mu实measure[IsProbabilityMeasure]，真实AE固定界→∀实q/H/u，H>0→AE1≤X²≤1+H→实际EX²=q→logE_mu exp(uX²)≤u+log(1−(q−1)/H+((q−1)/H)exp(uH))；没有未写z∈(0,1)门 | propext, Classical.choice, Quot.sound |

实际共12THM=2public+3authoredprivate+7generated，0DEF。公理精确是6项完整标准三公理、6项仅propext；不是每项都含三公理。没有sorryAx、项目新axiom或不允许的传递公理。七生成TYPE是数值/乘法/幂非零命题等式，所有实例门真实保留，不是隐藏分析假设。尚待下节最后检查Audit选择器与当前源的覆盖/机械绑定，不能仅凭计数当全模块证明。


## 四、最后核对的Audit覆盖／机械证据／冻结绑定

独立proof与全部实际TYPE审完后，才读取本单元正式receipt、40行Audit.lean、必要日志诊断/metadata、build-history与正式11源字典。receipt的`AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW`是作者机械状态，不是本票独立裁决；本票不以它的implementation叙述作数学依据。

Audit实际targets数组只含两个冻结公开名，defs空；先验证两名确为theorem，再遍历env.constants，选择两个target stem的所有后继以及本模块`_private.Shao.OQ3.SourceGlobalExponentialTests`前缀，逐项拒绝新增axiom并Lean.collectAxioms核传递白名单，输出完整TYPE/axiom。当前完整324行source独立只含2publicTHM和3privateTHM、0DEF；联合全部12 actual类型足以覆盖这份实现及7生成项。选择器不是module-index枚举，本报告不虚称用了全模块索引工具。

Audit.log的实际DECL/TYPE/AXIOMS和完整缩进行在server重新选块，逐字等于actual-declarations.txt。实际摘要是FROZEN_DEFINITIONS0、FROZEN_THEOREMS2、ALL_THEOREMS12、ALL_DECLARATIONS12、AXIOM_GATE PASS，首Audit正式exit0。只读取选块与计数，raw完整日志没有下载到本地或写入额外新文件。

### 真实hash和成功／失败历史

| 工件 | 行数/字节 | SHA256 |
| --- | --- | --- |
| actual source local/worktree/run/source-03四端一致 | 324 /14847 | 24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df |
| scope68 local /run scope.md一致 | 57 /10676 | 03237ffc5dba9ed8e3d25d65cbc1d2ebae9f3e14431fc415e28afdb81deaec2c |
| 先前独立声明final local/remote一致 | 161 /20481 | 7edb796bff491afa3ace735588dc2e5a59f95871281dd60c43ec39a07b3edf97 |
| R1真实原件report.md | 只读来源 | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |
| source-01完整失败版本 | 310 /14427 | af3701f86f57bf8850d2685ab34c52c3bf3d952ee45cadb641ae329e8a457f41 |
| source-02完整失败版本 | 323 /14821 | 76ace8dde3637d8cb2971f9031af6b4135c1564dbdd630e43f61bff56e9473eb |
| build-01.log（raw留server） | 259 /12460 | 928ff68e11ce470b07c4fa8a1b4e1374876ed9b6d2c86d09630c8ce72464dce3 |
| build-02.log（raw留server） | 71 /3436 | 5250459594f72c03925d1b5830333ad724b8fef4d0b4ce540abd7f6ff7df5431 |
| build-03.log 首次完整成功 | 0 /0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| build-history.json | 68 /1778 | 2dce551a77d12d36e26ea5590fca3fa35a44cd754c4322f99b7ba0096dd672e7 |
| Audit.lean local/remote一致 | 40 /1741 | 13a1239ea5d22d8dda7fee45fb9254ab83d4d8cde0d9e3226c6cbd04d3583ede |
| Audit.log | 99 /5778 | 71edce47a286f5678f5c8f18ba5875124f5a33d41cf581154d608e46c3feb6a4 |
| actual-declarations.txt local/remote一致 | 94 /5662 | 37c55eb82cbf85ff728655666f5113acd3e7fe1a55eb780d932b9487adf8f3f2 |
| 正式receipt local/remote一致 | 299 /11832 | 6e71abfc34ca2ecf0b4a0abf1d28e590fa39538ee499e79b0c32a26597ef931f |
| 正式prerequisite-hashes.json local/remote一致 | 13 /1144 | 238155e80b5fc25d04159f3c9dee3e591fa0137ae7de9799ecf3b30de577c35b |

本review独立去空白比较两个actual公有完整type与scope fence，合取、量词及所有长参数均匹配；01和02两份历史source的这两个type及三imports也与冻结scope相同。当前5个authored声明的实际名/分类与全部TYPE吻合。剥注释后禁止项sorry/admit/axiom/unsafe/native_decide/implemented_by/set_option扫描无命中，CR字节0、尾空白0。

正式history确有且仅有三个不同完整source尝试：01 exit1，02 exit1，03 exit0。server仅选取失败诊断行独立核：01包含积分rewrite／表达式类型匹配、错误旧simp名measureReal_univ_eq_one、parser与无进展dsimp等；02包含已规范neg_mul后rewrite、目标已结束后多余ring、c=q的等式与否定不等式方向匹配错误。这些版本均完整但失败，不是partial通过。当前完整proof修复表达式后03首次成功（14.965382秒），真实build-03.log为空且0error/0warning，之后没有重编未改成功源或重复Audit。历史全源/日志保留，不用失败kernel状态掩盖当前源验收。

作者实际target命令是指定server `taskset -c 14-17 lake env lean -M8192 -j4 -DautoImplicit=false -o .../SourceGlobalExponentialTests.olean Shao/OQ3/SourceGlobalExponentialTests.lean`，首Audit用相同CPU/native内存/jobs/strict autoImplicit读取本run Audit.lean；没有心跳、证明强度或设置弱化。本独立review没有执行任何Lean/#check/probe/target/Audit/build/import smoke，机械结论仅是对既有真实成功证据及冻结hash的只读验收。

### 依赖、pins与新的root接受基线

正式11项当前项目源在最后逐项fresh SHA核验：11/11与正式prerequisite表及receipt map相同、0 mismatch，canonical相对路径键排序紧凑map SHA=`8238b008f0d69333bbd4a891d836c26b6e5d997325d2fe396696bd7017934783`，恰与本人声明终票独立图相同。关键EnergyBernoulliMGF e3bb038b...、PositiveRate 8e727078...、RegularCovariance 0add3476...及AtomicMeasure/InverseTilt/SourceBinaryEntropyGap等均为已接受未改接口；没有新分析缓存或generalKL依赖。

按parent要求复用本人的已完成声明图/pin/cache核验，未重扫大图/对象/cache：物理11Shao/2776Mathlib、211外部停止叶；公开2523内部+189外部停止叶=2712，之前独立核source/olean缺0。真实std API的namespace仍是全局MeasureTheory.integral_exp_tilted（不是MeasureTheory.Measure）、Real.add_one_le_exp、Real.log_div/Real.log_mul两个nonzero门、Real.log_le_log正左参、integral_mono_ae真Integrable；当前proof均正确消费，无缺import/实例环境修复。

pins复用同声明证据并与当前正式receipt一致：leanprover/lean4:v4.36.0-rc1，Mathlib807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4、lake-manifest SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。没有为此目标升级packages、复制缓存、重验稳定51对象或重复root成功KL smoke。

最后实际Git为`feat/oq3-source-global-exponential-tests`，HEAD=`f2a39a09ebd50648bd61d68d7018aa01a9810ea0`，HEAD tree=`b6e72c992deceb0df88e772e50b2c42ba58ac4b4`，唯一status为`?? Shao/OQ3/SourceGlobalExponentialTests.lean`。它使用rootv36 accepted checkpoint，树与main82294da791784f3ac34ca52b96e21ef23f8a5329相同；这是声明终票后正常创建的新分支，非C frozen源漂移。C144 f698旧分支保持，C不是本模块import dependency。当前U19a尚无accept/commit/PR，review没有fetch/rebase/reset/merge/retarget或任何branch/source/shared/cache/旧票写入。

所有远端review命令只读且taskset CPU14–17，未启动heavy、未使用ulimit-v、未改pins/心跳/全局资源，外部CPU0–9/80GiB任务未触。只新写本地u19a-proof-review.md及授权对应remote report，原始完整logs留server，所有作者implementation/future/candidate/scanner笔记/JSON未读。

## 五、完整独立最终裁决

STATUS: CORRECT

JUSTIFICATION: 对scope68两完整target，actual324行proof、3authored private及全部locals、7生成项／12actualTYPE和传递公理已完成独立审查。候选全实测试上界来自同π真实中心均值、exp切线不等式和可积积分；精确θ0取等由真实log配分换测度产生。全c>0弱正尾域的严格分离真实覆盖低/高off-support、R=1尾内和R≠1闭能量区间含p0/p1，所有输出都是同原P上真Integrable、正配分的有限实指数测试。真概率、log非零、积分线性、sqrt/清分母和严格gap门逐项满足，没有手工globalRate/KL/entropy-duality/局部优化假设或更换law/q。既有首次完整strict03和首Audit的真实成功及冻结hash相符；不是只根据绿灯作语义接受。

原义务→消除义务→直接consumer→剩余：R1 section3在固定源法则上的候选点有限指数测试最大值／取等，以及其他全部正尾矩点的真实严格admissible separator已证明；直接consumer为root canonical domK上诚实扩展Legendre supremum的候选率值和全局严格offcandidate比较，随后才是同C最终law的rootA装配。这里0DEF，没有自建竞争globalRate，也不完成root的扩展值/边界/supremum桥；不声称一般ρ的KL(9)/(10)、saddle导数/曲率/常数装配、其他源根、新颖性或最优beta。

所有根A/B/C/D保持OPEN。作者机械状态与本完整独立CORRECT分开；只在lead全文读取本final之后才可由其接受/提交/发布。本轮先行66行盲译检查点原字节前缀完整保留，前部IN_PROGRESS是历史状态，最终以本节为准；没有更改冻结scope、原source、receipt、旧票或他人文件。
