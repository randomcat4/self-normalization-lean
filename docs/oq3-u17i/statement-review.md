# U17i StageCurvedLayerLimit 独立声明 / 来源 / API 审查

STATUS: CORRECT

## 1. 两项完整类型独立盲译（先持久化）

先只读冻结Lean fence两项完整类型；没有新定义。此时不读scope解释、作者路线/笔记或机械结果；尚无实际实现可作证明审查。

```lean
theorem stage_source_layer_conditional_factorization (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q d : ℝ) (hq : 0 < q)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (n : ℕ) (hn : 0 < n)
    (hmass : 0 < (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = d}) :
    (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = d ∧ z ∈ sourceTail q n} =
      (Measure.pi (fun _ : Fin n => mu)).real
          {z : Shao.Path n | normalDeviation q z = d} *
        (normalLayerConditionalLaw mu q (q / 4) d n).real
          {x : ℝ | -((q / 16) * d) ≤ x ^ 2 ∧
            -(Real.sqrt (n : ℝ) * q / 4) < x}

theorem stage_source_weighted_layer_subsequence_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ) (hq : 0 < q)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M)
    (hlayer : ∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
      d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (d0 : ℝ)
    (hd0 : Tendsto (fun j : ℕ => d (m j)) atTop (nhds d0))
    (hcont : ∀ A : Set ℝ,
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu)))
          (frontier A) = 0 →
      Tendsto (fun n : ℕ => (normalLayerConditionalLaw mu q (q / 4) (d n) n).real A)
        atTop (nhds ((ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance mu))).real A))) :
    Tendsto (fun j : ℕ => Real.sqrt (m j : ℝ) * Real.exp (-ell * d (m j)) *
        (Measure.pi (fun _ : Fin (m j) => mu)).real
          {z : Shao.Path (m j) | normalDeviation q z = d (m j) ∧
            z ∈ sourceTail q (m j)})
      atTop (nhds (((dyadicMesh J / (2 * Real.pi)) *
          Real.sqrt (2 * Real.pi / normalVariance mu)) * Real.exp (-ell * d0) *
        (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))).real
          {x : ℝ | -((q / 16) * d0) ≤ x ^ 2}))
```

第一目标独立翻译：固定实数轴概率μ、有限阶段J、正实数q和任意实层位移d，假定μ几乎处处位于实际有限阶段点像。对每个正整数n，若同一真实μ^n的层{normalDeviation q=d}具有严格正实质量，则该层与真实sourceTail交集的质量，等于层本身质量乘实际normalLayerConditionalLaw μ q (q/4) d n 对集合{x²≥−qd/16 且 x>−sqrt(n)q/4}的实质量。这里统计量、条件归一化、map和strict符号门必须与已有实际定义一致，不能把零质量回退律当正层条件律。

第二目标独立翻译：固定同一概率μ/J/q/ell，q>0，真实EY=q和EX=q/4，真实stage AE支持与每个活跃索引实际单点正性。给定全序列实有界层位移d(n)，其层最终与同一格距及nq相容。给定自然数重索引m(j)→∞，只要求d(m(j))→d0，不要求d全序列收敛或全n相位趋0。

另有显式外部输入hcont：对每个边界在实际Gaussian N(0,Real.toNNReal(transverseVariance μ))下为零的实数集合A，同一个实际normalLayerConditionalLaw μ q (q/4) (d n) n 的A质量沿全部n趋Gaussian的A质量。该输入本身没有在此目标中被证明，必须保持为待接的连续集收敛门，不能误称已证明Lévy或弱收敛。

在这些前提下，沿m(j)的真实加权sourceTail交层质量 sqrt(m(j))·exp(−ell d(m(j)))·μ^{m(j)}(层∩sourceTail) 趋于 [(h/(2π))·sqrt(2π/normalVariance μ)]·exp(−ell d0)，再乘同一实际Gaussian对{x²≥−qd0/16}的实质量。

量词/边界：ell任意固定实数；两个真实均值与所有同μ方差参数不得换测度或重新选择。首目标明确n>0、层质量>0；次目标须从给定前提取得最终正n/正层质量与非退化Gaussian，再处理移动二次阈值、d0=0交界和符号阈值趋−∞。结论只有固定有界层的子列极限，不是共同尾、完整19、conditional Lévy、hW/generalKL或根闭合。

## 2. 来源与本单元实际范围

盲译62行/4697字节已先持久化，阶段SHA256=6e7274cd529b6df2aaba4a48f68c8f34e4131060408e94100800873e52dd946f；随后才读取scope56解释、R1和实际前置/API。本票是冻结声明/source/API门，未读取或编写尚不存在的实现，也未读作者future/candidate/implementation notes。

R1 314–344的有限法向格点、实际中心R_n=∑X−na、层质量Gaussian系数与条件方差，是本单元承重对象。R1 400–409的实际相位、曲边恒等式(18)及正和符号条件，解释目标一的准确事件。R1 411–429的g_J与原(19)需要进一步将固定层结果和共同尾接合；本声明只处理hcont之后的固定有界层子列，不证明整个(15)或(19)。

两个目标均使用同一实际μ^n、真实normalDeviation和sourceTail；统计量明确用a=q/4。SampleBoundary的tangentDeviation q=∑X−nq/4，而不是tangentDeviation(q/4)。目标中的normalLayerConditionalLaw μ q (q/4) d n是其实际居中统计量除sqrt(n)的条件推送，参数顺序准确。

hcont是明确待接U18a的证明接口：本单元形式上证明带此显式输入的蕴含，绝不把连续集概率收敛隐藏为源模型已有事实。实际characteristic函数收敛已由U13c独立接受，但从中生产此hcont所需的Lévy/Portmanteau连接仍未由本单元证明。移除本假设须有后续真实生产者，不能加入新公理替代。

## 3. 第一目标：实际条件因子恒等式

### 3.1 真产品概率、energy正性与可测性

记ν=Measure.pi(fun _:Fin n=>μ)、A={M_n=d}、R=tangentDeviation q、T(z)=R(z)/sqrt(n)。ν是真概率，故所有事件质量有限。A由M_n连续而闭可测；T是有限坐标和减常数再除固定实sqrt(n)的连续函数。目标集合B={x²≥−qd/16 且 x>−sqrt(n)q/4}是闭平方阈值集与开半线之交，真实Borel可测。

真实stage range的inl/inr分支分别映到fixedAtom(Sum.inl i)与fixedAtom(Sum.inr j.val)。公开fixedAtom_bounds给每坐标1≤|X|。通过Measure.tendsto_eval_ae_ae和有限ae_all_iff取得同一ν-AE全部坐标界，再在非负两边平方得到X_i²≥1。实际Shao.energy=∑X_i²，故ν-AE energy≥n>0；这里先用明确hn:0<n，不从普通上界hb猜下能量界。

不存在必须访问的私有API：NormalLayerConditionalLaw的normalLayerSet_measurable/normalLayerStatistic_continuous是private，不能直接调用；本目标可由上面的实际有限和连续性重新建立同样可测事实。G的stage_abs_bounds_ae也不是本imports可用公开辅助，stage双界须从公开fixedAtom_bounds真实取得。

### 3.2 准确曲边与严格符号门

已接受公开sourceTail_on_normal_layer的完整真实类型是：q>0、n>0及实际M_n(z)=d时，sourceTail当且仅当energy>0、∑X>0且R²≥−nq d/16。它由实际curved_sample_identity和真实sqrt平方构造，未丢失正和符号。

令u=sqrt(n)>0，先有u²=n与n>0，才可将R²≥−nqd/16除以n，得到(R/u)²≥−qd/16。又∑X=R+nq/4，u²=n给∑X>0当且仅当R/u>−uq/4。两次比例都用同一个真实正u，无错误sqrt消元、n=0总化除法或二次方不保符号的问题。

因此在真实ν-AE的energy>0集合上，A∩sourceTail与A∩T⁻¹B等价。只要求AE事件相等并用measure_congr/measureReal_congr，不把全部path的energy都断言严格正。q>0正是公开sourceTail等价式和原尾几何所需门，第一目标没有隐含均值或协方差假设。

### 3.3 正层质量、实际cond-map与ENNReal→Real

实际normalLayerConditionalLaw定义（12–18）检查的是νA=0；为零时回退dirac0，否则map T (cond ν A)。本目标hmass:0<ν.real A，加真ν有限，给νA严格非零且不为top，所以实际正层分支确被激活。不能把real正性和ENNReal零/无限分支混淆。

由T、B真实可测，Measure.map_apply给law(B)=cond ν A (T⁻¹B)。实际ProbabilityTheory.cond_mul_eq_inter的类型在有限ν和可测A下给cond ν A (T⁻¹B)·νA=ν(A∩T⁻¹B)；不需猜条件独立或RN导数，也不需额外假设T⁻¹B有正质量。

再用上面的AE事件相等、ENNReal.toReal_mul及实乘法交换，正好得到ν.real(A∩sourceTail)=ν.real A·law.real B。ν与cond/map均是真有限概率，所有toReal均代表真实有限质量，没有top.toReal默认0。这个乘法路径也避免对事件概率作不必要的实除法。

目标一的n0与零层质量已明确排除；正层、空交事件、r=0式二次边界都合法。无须ell或ell符号条件，因为它不出现在该目标。

## 4. 第二目标：先恢复真实层，再处理移动事件

### 4.1 同一μ上的S/D/T与Gaussian非退化

从阶段range的公开fixedAtom_bounds得到同一μ的hb:AE |X|≤4+sqrt10；hpos(Sum.inl i)给同一μ四个实际baseAtom单点严格正实质量。已完整接受的一般μ公开normalVariance_pos、parabolaCovariance_det_pos、transverseVariance_pos的完整门就是概率μ、hb、base正性，因此给S=normalVariance μ>0、D=det(parabolaCovariance μ)>0及T=D/S>0。未将仅atomicMeasure版本套一般μ。

S、D、T是真实可积居中二次型/协方差给出的参数：前置一般μ证明在实际紧支撑下先保证相关多项式可积，通过三个正基点排除非零二次式AE为0，再得正定性；这里不把variance的toReal总化当正方差。

Real.toNNReal T由于T>0而严格正、非零，并且其强制实数值等于T。Gaussian.Real的参数v明确是方差，故Γ=gaussianReal 0 (Real.toNNReal T)是真N(0,T)，不是把T当标准差或把τ²写成τ。实际nullSingletonClass_gaussianReal需要v≠0，本门先建立该条件才可用其无原子结论。

### 4.2 真实层质量最终正与准确s=0常数

已接受NormalLayerConditionalLaw的公开eventually_stage_normalLayer_mass_pos完整前提是同μ概率、hb、实际EY=q、EX=a、S>0、D>0、阶段AE range、每阶段正单点、全n有界d和最终格层相容。本候选取a=q/4，所有门由原输入或上段推导；不要求q∈(1,1.03)、ell≥0或d全n收敛。

同样，公开stage_normalLayerCharacteristic_scaled_tendsto在s=0给全n的真实复数scaled层特征极限；normalLayerCharacteristic_zero_eq_mass把s0特征精确识别为实际层实质量的复嵌入，取实部后得到sqrt(n)·ν_n.real{M_n=d n}→C，其中C=(h/(2π))sqrt(2π/S)>0。它就是声明常数，没有遗漏h、2π或sqrt(n)。

层质量最终正来自此真实正C及sqrt(n)≥0，而不是来自hcont的假设，也不是先假定条件律分支可用。结合m→∞，这些eventual事实拉回到j；再并入最终m(j)≥1才可调用第一目标与消去sqrt(m(j))。没有要求m单调或单射；Tendsto m atTop atTop足够。

hcont全n测试概率收敛通过Tendsto.comp hm给同一实际子列条件律ρ_j=normalLayerConditionalLaw μ q (q/4) (d(mj)) (mj)的固定连续集门。实际公开normalLayerConditionalLaw_isProbabilityMeasure对所有n/d都成立，包含初始dirac回退，故ρ_j是真概率；最终正层时它又与真实cond-map一致。两个层次没有循环论证。

### 4.3 每个固定平方阈值都是Gaussian连续集

设A_a={x:ℝ|a≤x²}。连续常数与连续平方给frontier A_a⊆{x|x²=a}（实际frontier_le_subset_eq）。a<0时等值集为空；a≥0时至多包含sqrt(a)和−sqrt(a)，a=0时就是{0}。T>0后的Γ无原子与Set.Finite.measure_zero给所有这些边界真Γ零质量。

因此hcont可逐个用于每个固定A_a。固定Iic(−K)的frontier也包含于单点{−K}，同样是Γ连续集。这里实际使用的集合都是Borel；hcont的形式对任意边界零质量集合更强，但本证明无需对不可测移动集合偷用map_apply。

必须保留T>0：d0=0时仅知道A_0=univ并不足以控制从负d逼近形成的小孔；真正Γ{0}=0才保证该孔概率消失。候选通过真实阶段正基点已提供这一门，不用假设条件二阶矩或条件Gaussian密度。

### 4.4 移动二次阈值的固定集合夹逼（含d0=0）

令a_j=−(q/16)d(mj)，a0=−(q/16)d0。由hd0的真实实数Tendsto得a_j→a0。固定任何ε>0，最终有A_(a0+ε)⊆{x|a_j≤x²}⊆A_(a0−ε)。只能把两端固定集合代入hcont，不能直接将中间随j变化事件当作hcont的固定A。

取ε_l=1/(l+1)递减趋0：A_(a0+ε_l)递增到{x²>a0}，A_(a0−ε_l)递减到A_a0。Γ有限概率，实际测度从下/上连续性（上连续先有闭集可测与一项有限）给对应ENNReal概率极限，有限limit后再用ENNReal.tendsto_toReal转为实概率。

Γ{x²=a0}=0使Γ{x²>a0}=Γ(A_a0)，因此两侧实概率趋于同一值。a0<0（d0>0）时目标集合本来全空间；a0=0（d0=0）时下侧union=ℝ 去掉 {0}，无原子门真实补上零点；a0>0（d0<0）是两条真正非退化Gaussian尾。没有将零交界当作可忽略但未经证明。

### 4.5 严格正和的远条件尾：先固定K再取极限

实际符号阈值b_j=−sqrt(mj)q/4；q>0和m→∞给b_j→−∞。固定正K，最终b_j≤−K，因此被严格符号门删掉的{x≤b_j}包含于固定Iic(−K)。此处不能对移动Iic(b_j)直接用hcont。

对该固定Iic(−K)，先用hcont.comp hm取条件概率极限Γ.real(Iic(−K))。随后K沿Nat趋∞，这些闭半线递减、交为空；Γ有限概率且各集合可测，真实上连续性给该尾趋0。没有使用未证明的条件独立性、条件Chebyshev/二阶矩、指数矩或概率密度。

将两步统一，设C_j={x|a_j≤x² 且 b_j<x}，固定ε>0、K后最终有A_(a0+ε) ∖ Iic(−K)⊆C_j⊆A_(a0−ε)。由于ρ_j真有限概率，真实measureReal_mono与并集次可加给
ρ_j.real(A_(a0+ε))−ρ_j.real(Iic(−K))≤ρ_j.real C_j≤ρ_j.real(A_(a0−ε))。

先对j取固定集合概率极限，再令ε↓0、K→∞，第4.4节和真实Gaussian尾给ρ_j.real C_j→Γ.real A_a0。也可用等价ε-邻域论证而不依赖额外limsup模块。所有real概率比较均有实际有限概率门，没有把ENNReal.toReal无条件当单调。

### 4.6 乘回真实层与任意ell的有界层权重

最终m(j)>0且真实层mass>0后，第一目标给joint层质量=layer质量·ρ_j.real C_j。乘sqrt(mj)与exp(−ell d(mj))并交换实乘法顺序，表达式恰为三因子：真实scaled层质量、真实exp权重、真实条件事件概率。

第一因子沿m趋C，第二因子由hd0和实指数连续性趋exp(−ell d0)，第三因子由上述夹逼趋Γ.real A_a0。全部是有限实数，所以乘法Tendsto直接给冻结右侧C·exp(−ell d0)·Γ.real A_a0。这里ell可以负/零/正，仅固定有界层收敛，不宣称该权重对全部层共同支配。

全序列hd为真实层质量前置提供显式O(1)界；hd0只在子列上使用，hlayer也只需最终成立。没有假定全n相位趋0、d全序列收敛或m严格增长。J0仍由base正性给S/D/T>0、h=1；初始零mass/n0允许存在，但由已证明的eventual事实排除在本极限的归一化操作之外。

## 5. 固定库实际主API读核（无Lean/API探针）

在指定服务器只读实际源码；以下是实际完整门，不是照抄scope中的索引文字。

| 实际API及位置 | 完整关键门 / 本候选满足情况 |
| --- | --- |
| Probability.ConditionalProbability153–164 | cond_isProbabilityMeasure需νA≠0及有限质量；第一目标hmass与真ν概率给出 |
| 同文件263–264 | ProbabilityTheory.cond_mul_eq_inter (A可测)(t)(ν)[IsFiniteMeasure ν]：condνA(t)·νA=ν(A∩t)；实际没有额外正t质量要求 |
| MeasureTheory/Measure/Map170–172 | Measure.map_apply需统计量Measurable和测试集合MeasurableSet；T与B已逐项建立 |
| Basic/ENNReal/Real337–338 | ENNReal.toReal_mul为真实乘法同态；同时本问题各概率质量均有限，不能借此掩盖top |
| Basic/NNReal/Defs161、551–556 | T≥0时Real.coe_toNNReal=T，Real.toNNReal_pos↔T>0；用真实T>0取得非零NNReal方差 |
| Probability/Distributions/Gaussian/Real220–236 | gaussianReal参数是均值/方差，零方差为dirac；nonzero v后nullSingletonClass_gaussianReal才给无原子；所有v均有真概率实例 |
| MeasureTheory/Measure/Typeclasses/NullSingletonClass80–82 | Set.Finite.measure_zero要实际NullSingletonClass实例，正T后合法 |
| Topology/Order/OrderClosed648–657 | frontier_le_subset_eq需两Continuous；frontier_Iic_subset给半线边界单点控制 |
| MeasureTheory/Measure/Continuity198–203 | tendsto_measure_iUnion_atTop需真实Monotone与可数生成atTop，Nat满足 |
| 同文件220–227 | tendsto_measure_iInter_atTop需各NullMeasurableSet、Antitone和一项≠∞；闭Gaussian测试集+真概率满足 |
| Topology/Instances/ENNReal/Lemmas102–103 | ENNReal.tendsto_toReal必须limit≠∞；Γ的所有事件≤1，limit有限 |
| MeasureTheory/Measure/Real88–90 | measureReal_mono先真实包含，另要上集质量≠∞（默认finiteness也须真概率）；本题ρ_j/Γ均真概率 |
| Analysis/Real/Sqrt139 | Real.tendsto_sqrt_atTop支持正q下符号阈值退向−∞，n正后才用sqrt平方/除法 |

已接受实际NormalLayerConditionalLaw12–18、103–138和FundamentalFourierAsymptotic242–278全文相应部分已读：实际均值/有界d/最终格层/一般μ S/D门与本候选逐项匹配。其已有characteristic结论未被误当成本单元已经证明hcont。

数学/source/API语义至此未发现声明阻塞。下面才进行冻结hash、public import图、cache与pins的机械只读重核；尚无本单元实现、receipt或编译门可签。

## 6. 最后进行的冻结与实际环境重核

本轮数学、来源、真实前置与主API语义先于机械检查。最后所有远端项目读取均通过共享server.py、taskset -c 14-17；没有Lean/#check/API probe/build/rebuild/cachewrite/spawn/commit/raw完整日志复制，没有修改source/scope/receipt/旧票/shared或回退他人编辑，没有触外部CPU0–9/80GiB及全局资源，没有使用ulimit-v。

实际worktree=/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3；branch=feat/oq3-stage-curved-layer-limit；HEAD=18d47cde0e9408700a91cd0814f947cb2b8b646d，git status为空。H正常发布后的HEAD推进与其冻结源未冲突。两端StageCurvedLayerLimit.lean都不存在，本单元没有target/Audit/receipt可作证明成功依据，本票也未作这种声称。

| 冻结对象 / pins | 实核SHA256 |
| --- | --- |
| 本地fifty-sixth-unit-scope.md与remote run/scope.md，7615字节/66行 | f2a28b6f6c06b03dc8c571232ba0b4f61445af97fcd766b69f4325f74abb20fc |
| 原始只读R1 report.md | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |
| lean-toolchain，29字节/1行 | d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4 |
| lake-manifest.json，3541字节/117行 | 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e |

冻结fence独立枚举确为0定义/2完整theorem类型，当前实际导入项目源中无这两个新名字冲突。拟imports恰为实际H加Mathlib.Probability.Distributions.Gaussian.Real；不加入Levy/Portmanteau或下一单元为隐含依赖。

### 6.1 全部45份实际项目闭包

从实际H源及其imports递归取得45份项目源，逐份实算SHA，与已接受H的44前置加H冻结源码的基线完全一致，45个现成项目olean均存在。以下是本轮重核完整清单，不是仅照抄candidate cache metadata。

| 实际前置源 | SHA256 |
| --- | --- |
| Shao/OQ3/BinaryEntropyBounds.lean | 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228 |
| Shao/OQ3/SourceBinaryEntropyGap.lean | f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9 |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| Shao/OQ3/AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| Shao/OQ3/InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| Shao/OQ3/EnergyBernoulliMGF.lean | e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad |
| Shao/OQ3/FiniteStageMeasure.lean | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| Shao/OQ3/AtomProjection.lean | 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22 |
| Shao/OQ3/ResonanceArithmetic.lean | cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b |
| Shao/OQ3/FiniteNormalSpan.lean | 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de |
| Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb |
| Shao/Probability/FiniteIID.lean | d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b |
| Shao/OQ3/SampleBoundary.lean | 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2 |
| Shao/OQ3/SourceEnergyGeometry.lean | 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a |
| Shao/OQ3/FarEnergyExponentialCover.lean | 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d |
| Shao/OQ3/PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |
| Shao/OQ3/RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| Shao/OQ3/NormalTangentGaussian.lean | d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39 |
| Shao/OQ3/NormalTangentMoments.lean | 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1 |
| Shao/OQ3/CenteredLogMGF.lean | 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4 |
| Shao/OQ3/CenteredSampleTilt.lean | d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501 |
| Shao/OQ3/SourceFarWeightedTail.lean | c9e4c14af297353c5358da6d3e75d72f712649e535102ba18297fc00a0e5261f |
| Shao/OQ3/LocalRateMargin.lean | 5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77 |
| Shao/OQ3/NormalTrialCost.lean | 8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895 |
| Shao/OQ3/JointNonlattice.lean | 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559 |
| Shao/OQ3/FiniteFarArc.lean | 3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71 |
| Shao/OQ3/TiltedMeasureDomination.lean | 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b |
| Shao/OQ3/ProductMeasureDomination.lean | 9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f |
| Shao/OQ3/CompactTiltDomination.lean | 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623 |
| Shao/OQ3/CharacteristicMeasureDomination.lean | ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb |
| Shao/OQ3/NormalTangentPowerLimit.lean | 819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457 |
| Shao/OQ3/NormalTangentDomination.lean | b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90 |
| Shao/OQ3/CentralFourierIntegral.lean | 4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93 |
| Shao/OQ3/NormalLayerFourier.lean | 063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3 |
| Shao/OQ3/FundamentalFourierAsymptotic.lean | aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1 |
| Shao/OQ3/NormalLayerConditionalLaw.lean | 94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a |
| Shao/OQ3/NormalLayerMassBound.lean | 66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1 |
| Shao/OQ3/CompactTiltLayerMassBound.lean | 5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7 |
| Shao/OQ3/LocalNegativeLayerTail.lean | 049361c77716896922fb1d7cd3e6abf84515b76a99103c597d8d74b63a2f1856 |
| Shao/OQ3/LocalNegativeLayerControl.lean | e94a5a8e82d2a69a946a12e16f3fb2a58b174fb036becce5632d7c600b796f01 |
| Shao/OQ3/GlobalNegativeLayerBound.lean | 57b61e6e3bfd184586083e55633a563e4176cbfcf16def62a7d860d92b5c01d8 |
| Shao/OQ3/NegativeLayerGeometricTail.lean | 8077cfb97547c4a8c5b22da6ed17a58168a6ca1f6b2654f6799292a06a8b23f4 |
| Shao/OQ3/StageLayerDecomposition.lean | b6204bbbc39d029e221e473c76e8ebe34a42cf4765f4c3f7ccbd657d6311a8de |

本地被直接语义核读的H、NormalLayerConditionalLaw、RegularCovariance与实际远端SHA相同。公开sample/curve/cond-law/一般μ协方差接口都沿这条实际闭包可达；本门没有调用不可见的private helper。

### 6.2 真实public图、Gaussian导入与缓存

独立从45项目前置的实际Mathlib import再加Gaussian.Real出发，52个直接Mathlib根模块的递归源码闭包为2905份。逐个对应源码/现成olean均存在，missing清单为空；没有读取作者candidate cache metadata来替代该枚举，也没有下载或写缓存。

再按实际module的public import图追踪，下面所有主API owner均公开可达。实际Gauss方差/无原子/finite measure连续性、cond-map与toReal接口不只是磁盘上有源码。

| 真实Mathlib API源 | 实核SHA256 |
| --- | --- |
| Probability/ConditionalProbability.lean | 4245cc130e59294fadd87a6b011273c010bf3a21fd3395b8a3fe0f8a749f3f8c |
| MeasureTheory/Measure/Map.lean | 7bae8f174146d4ef4055f79757c2a0a3af6a9090dda3d28ea17fbd54540e9593 |
| Probability/Distributions/Gaussian/Real.lean | 9edebfff169cb577b6dab1a7912f2e8fec0e70a8dac39db105263e1a0f31b383 |
| Topology/Order/OrderClosed.lean | 011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e |
| MeasureTheory/Measure/Continuity.lean | efb3bc5e7fefb246225d56685023674a2c32e844e72e0d03dff5df12750c8009 |
| Topology/Instances/ENNReal/Lemmas.lean | 5fd3057f9d8e1e912b64dc09a09fd05f7e999745dc7f5fd28d960630957b8691 |
| MeasureTheory/Measure/Real.lean | 1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d |
| MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean | 571b68b8c23c35a977c2f9435d5bbe6bf0aa8f7e24b99420260b929a06ac3cd7 |
| Basic/NNReal/Defs.lean | 250d8ef69dc5cca301cd7f02a1521fa21614794b602ddd99ac2cb1e1da8beeae |
| Basic/ENNReal/Real.lean | da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf |
| Analysis/Real/Sqrt.lean | 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204 |

真实toolchain文本是leanprover/lean4:v4.36.0-rc1，实际Mathlib HEAD=807d3836b165983210ee2ecf3cd28f239436949c。只读静态检查没有新scope实例/导入阻塞；该结论不是本单元未来Lean elaboration或proof内核成功。

## 7. 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 第一完整类型在明确q>0、n>0和真实正层质量下，stage产品AE给energy>0；实际曲边恒等式经正sqrt(n)消元精确得到同一统计量的平方阈值与严格符号阈值。实际cond-map正分支、真实可测性、有限ENNReal质量和cond_mul_eq_inter→toReal乘法共同支持准确因子恒等式，未偷用零质量回退或归一化默认值。

第二完整类型从同一μ的阶段双界/正基点可真实推出S/D/T>0和非退化Gaussian，已有准确s0层系数及最终正mass API与全部原前提匹配。显式hcont只作用于同一实际条件律的固定连续集合；移动平方阈值用固定两端夹逼，零交界由真正Gaussian无原子处理；符号远尾先固定K取条件概率极限、再令K趋∞。最后实际因子化、scaled层质量和任意固定ell的连续指数三因子相乘，给冻结子列常数。只需d(mj)→d0、m→∞，不暗加d全序列/相位收敛或m单调条件。

因此冻结声明的数学/source/API和当前静态环境无已知阻塞，可进入独立实现阶段。本票不签署尚不存在的具体proof/build，后续完整审查须核全部实际locals/private/generated与机械凭据。尤其hcont只是明确待接接口，Levy/Portmanteau生产者仍未由此声明或本票证明；不可把条件蕴含当成源模型已完成(15)。

固定层moving曲边/sign远尾是本候选待实现的输出，当前只有声明批准；共同层tail、Phi改写、完整series limit19、conditional Lévy、LLT、hW、generalKL、全局极小/最优/新颖性及根A/B/C/D继续OPEN。
