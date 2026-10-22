# U17i StageCurvedLayerLimit 完整独立证明审查

STATUS: CORRECT

## 1. 实际两项完整公开类型独立盲译（先持久化）

承认已有声明审查历史上下文；本轮仍从实际实现重新提取两项完整公开类型。先持久化此盲译，再读本轮证明/private/generated、scope解释或receipt/机械结果。实际没有公开定义体。

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

第一目标独立翻译：同一真实概率μ、阶段J、正q、任意层d，给真实阶段AE范围。正整数n且μ^n的真实M_n=d层质量严格正时，sourceTail交该层的实质量，精确等于层本身质量乘实际normalLayerConditionalLaw μ q (q/4) d n对{x²≥−qd/16 且 x>−sqrt(n)q/4}的实质量。应核实际条件律正分支、真实有限质量、energy>0与正sqrt(n)下的平方/符号消元。

第二目标独立翻译：固定同一概率μ/J/q/ell，q>0、真实EY=q/EX=q/4、阶段AE范围和活跃有限索引单点正性。全序列d显式有界并最终同格距/nq相容；自然数重索引m→∞，只有d(mj)→d0。另输入hcont：同一实际条件律沿全部n对实际Gaussian N(0,Real.toNNReal(transverseVariance μ))的每个边界零质量集合的实概率趋于该Gaussian实概率。

则沿该子列，真实sqrt(mj)·exp(−ell d(mj))·μ^{mj}(M=d(mj)交sourceTail)趋于C·exp(−ell d0)·Gaussian{x²≥−qd0/16}，其中C=(dyadicMesh J/(2π))sqrt(2π/normalVariance μ)。ell任意固定实，μ/q/中心/方差和实际law不能替换。

hcont是显式未在本目标中生产的输入，不能误记为本单元已证明Lévy/弱收敛。实际实现须核四个私有辅助及所有生成项，真实非退化Gaussian、固定阈值夹逼、d0=0交界、先固定K再取极限的sign远尾，以及最终正n/层质量后真实因子化。没有全n相位收敛或m单调要求，也没有共同层尾或全19/根闭合结论。

## 2. 冻结声明、来源与范围

盲译已先持久化60行/4306字节，阶段SHA256=ef8650e74d653b43e4394cfe66d63f8f8a11b20a89dfae9dad64c6c8599dfc71。随后才读scope56解释、真实R1、全部实际源码和固定库；本轮未读作者candidate/future/implementation notes或下一scope。

R1 314–344的实际Y/X中心、层质量系数及条件方差，对应本单元的同μ层概率与Gaussian；400–409的实际格层和曲边恒等式及正和条件，对应首目标的准确事件。原文344的Lévy步骤没有在此实现中生产：第二目标hcont仍是公开完整类型中的显式输入。421–429的全层极限也没有因为得到固定层子列而闭合。

实际源没有公开DEF；两项public类型以真实μ^n和normalLayerConditionalLaw μ q (q/4) d n为对象，未改为替代measure、未引入全n相位收敛。统计量是R_n=∑X−nq/4再除sqrt(n)，不能把tangentDeviation的参数误写成q/4。ell只作固定有界层连续权重，不承担共同层尾估计。

## 3. 第一公开证明全部locals（11–126）

### 3.1 真实概率、正sqrt与产品AE能量（25–60）

25–32固定真实ν=Measure.pi(fun _:Fin n=>μ)、层A、统计量T、目标集合B、r=sqrt(n)。ν由原概率μ的有限产品构成，是真有限概率；并未用总化tilt或改变law。33–35先由hn给实n>0、r>0、r²=n，后续所有r/n消元都在这些门之后。

36–41对每个Fin n坐标通过Measure.tendsto_eval_ae_ae.eventually hrange，再用ae_all_iff合并同一ν-AE全部阶段支持。42–60逐坐标从公开fixedAtom_bounds的inl/inr真实映射取1≤|z_i|，sq_le_sq₀要求的双方非负均显式给出，再用sq_abs得1≤z_i²。真实energy=∑z_i²≥∑1=n>0，故hE是同一产品概率下真AE正能量。未从普通上界猜下能量，也未把AE当所有path点态。

### 3.2 实际可测与正层分支（61–74）

hMc由实际normalDeviation/normalValue的有限和多项式给连续性；hA是层等值闭集可测。hT直接由实际有限和/固定sqrt分母函数给Measurable；hB由闭平方阈值集与严格开半线相交给真Borel可测。没有调用前置中的private可测helper。

hmass是真ν.real A>0。69通过ENNReal.toReal_pos_iff取νA>0，得到hA0:νA≠0；ν是实际有限概率还独立保证νA≠∞。70–74才将实际normalLayerConditionalLaw的if分支化为map T (cond ν A)，没有在Dirac回退时错误认为是真正条件law。

### 3.3 AE事件等价、平方与符号（75–114）

hset只在hE给出的ν-AE正能量上建立。对层外hz不成立的路径，两事件都false；对层内hz，先有hR:r·T=实际tangentDeviation q（83–87），其中n*(q/4)=nq/4仅作实环代数。r≠0来自hr>0后才用mul_div_cancel₀。

88–89由hR和r²=n得R²=n·T²。90–95由同一个R关系得真实∑X=r·(T+rq/4)。96–98用r>0先消去严格乘法符号，得到∑X>0 ↔ −rq/4<T；保留了严格不等号，没有把平方后的条件当充分条件。

99–110的hcurve在hnR>0后才用mul_le_mul_iff_of_pos_left，将−nqd/16≤R²等价为−qd/16≤T²。两个方向的convert/ring只是重排同一正n因子，没有对n0、负分母、q或ell非法消元。

111消费公开sourceTail_on_normal_layer的真实q>0/n>0/实际层等式门。hE除去能量条件后，剩余sign和curve与B中的curve/sign顺序由and_comm等价。故hset精确是原sourceTail交层与A∩T⁻¹B的AE相等；不是偷删sign或构造点态全路径energy正性。

承重公开曲边API来源是实际SampleBoundary 34–86：先有S²−n(q/16)energy=(nq/16)M+R²，再在q/n/energy正时真实sqrt平方，并保持S>0。实际Shao.energy是样本平方和，未替换为方差。

### 3.4 真cond-map、有限ENNReal乘法与real质量（115–126）

115–118先用已建立的Measurable T与B套实际Measure.map_apply，再调用ProbabilityTheory.cond_mul_eq_inter hA (T⁻¹B) ν；该API需要可测层A与有限ν，均真满足，给law(B)·νA=ν(A∩T⁻¹B)。没有条件独立、RN或概率可积性假设被暗用。

119–120只对真实ENNReal乘法恒等式取toReal并使用toReal_mul。124先由measure_congr hset换成实际交事件，125反向用该乘法恒等式，126交换实乘法顺序，正好输出第一完整类型。这里ν/cond/map是真有限概率，所有real质量均有真实有限含义，不是top.toReal默认0；未除事件概率，也未用log0。

首目标明确排除n0和零层mass；任意空交事件、任意实d和没有正原子前提都合法。q>0没有被暗中加强为源q区间。

## 4. 四个authored private证明的全部门（128–326）

### 4.1 square_level_null（128–143）

该helper只需实际G的NullSingletonClass，不要求G概率或有限。对任何成员x²=a，先从平方非负得到a≥0，才用sq_sqrt取得sqrt(a)²=a。因式分解(x−sqrt a)(x+sqrt a)=0给x=sqrt a或x=−sqrt a，故等值集真包含两点集；a<0时不存在成员，证明没有对负a错误使用sqrt平方公式。

两点Finset由真实NullSingletonClass得到G质量0，再measure_mono_null给全等值集质量0。a=0时两个点合并为0仍是有限零质量集，未遗漏关键零交界。

### 4.2 square_threshold_frontier_null（145–149）

frontier_le_subset_eq消费常数与平方函数的真实Continuous，给frontier{a≤x²}⊆{a=x²}。翻转等式后包含于上一helper的{x²=a}，measure_mono_null给边界0。无隐藏概率/矩或Gaussian专用假设，后续需先提供真实NullSingletonClass实例。

### 4.3 square_threshold_mass_limits（151–227）

G是真概率且无原子。157–166定义C(b)={b≤x²}与delta_k=1/(k+1)，真实delta_k>0；hdanti用正分母的一除法单调性和Nat有序实嵌入给delta反单调。hCm对每个b给闭平方阈值Borel可测。

167–178由delta反单调分别取得C(a+delta_k)递增、C(a−delta_k)递减；方向逐行正确。179–189的union精确为{a<x²}：forward用delta>0取得严格，reverse由正gap x²−a的exists_nat_one_div_lt选实际k。190–206的intersection精确为C(a)：若x²<a，先从正gap a−x²选delta_k<gap，与该k成员条件矛盾；反向直接用delta_k>0。

207–214不是把严格/非严格阈值点态等同，而是从square_level_null和measure_eq_zero_iff_ae_notMem取得x²≠a的G-AE门，再得严格集与C(a)的AE相等及真实measure_congr。零交界a=0的可能差集{0}恰由此无原子门消去。

215–217使用真正Monotone union测度连续性得上移阈值概率极限，先以实际union和AE等质量改写。218–222使用每个C可测→NullMeasurable、真实Antitone和G的一项有限质量，才用inter测度上连续性。223–227在G(Ca)≠∞后用ENNReal.tendsto_toReal转为目标实概率两极限；没有对∞极限的toReal假连续。

### 4.4 moving_curved_probability_tendsto（229–326）

完整输入是每个rho_j真概率、G真概率且无原子、同G边界零集合的显式hcont、a_j→a0、b_j→−∞。它不假设rho_j有矩或密度；不是Gaussian弱收敛生产者。

241–264先独立建立固定G的尾G.real(Iic(−k))→0。半线族反单调；交集为空通过exists_nat_gt(−x)逐点反证。所有Iic可测，G概率给一项≠∞，实际inter连续性后在0≠∞下toReal转实。265–266用frontier_Iic_subset与真实measure_singleton=0取得每条固定半线的连续集门。

267–269建立正delta及上一helper两端平方阈值概率极限。270按真实tendsto_order分成任意c<L与c>L的eventual严格界，L=G.real C(a0)，不以主张移动事件本身是固定连续集来替代。

下界272–304先固定e=(L−c)/5>0，再选一个固定k使G(C(a0+delta_k))>L−e，另选固定K使G(Iic(−K))<e。这些选择都在全部后续j之外。之后才对这两个固定集合使用hcont，得到rho_j(Cplus)>G(Cplus)−e及rho_j(Iic−K)<Gtail+e；a_j→a0给最终a_j<a0+delta_k，b_j→−∞给最终b_j≤−K。

293–297真实集合包含Cplus⊆E_j∪Iic(−K)：若x≤−K进入tail，否则x>−K≥b_j且平方阈值满足E_j。292先安装hprob j为实际有限概率，再用measureReal_mono和measureReal_union_le给rho(Cplus)≤rho(E_j)+rho(tail)。独立数值核算为rho(E_j)>L−4e>c；e取1/5保留严格余量。未对未证有限的measure.real作无条件单调比较。

上界305–326先固定e=(c−L)/3>0，选固定k使G(C(a0−delta_k))<L+e，再用固定集合hcont得到rho_j(Cminus)<G(Cminus)+e。a_j→a0给最终a_j>a0−delta_k，于是E_j⊆Cminus；320先装真概率后用real单调，得rho(E_j)<L+2e<c。这里舍弃sign只作上界，没有假称sign事件质量1。

该helper实际按“先固定阈值与K、再取j极限，且固定G尾先已证明趋0”的顺序工作。它没有调用移动事件版Portmanteau、条件Chebyshev/二阶或指数矩。平方边界包括a0=0，a0<0的全空间与a0>0的两尾同样处理。

## 5. 第二公开证明与实际前置（355–424）

355–360从同一μ的stage range按fixedAtom两个分支取得真实hb；361–362从hpos(inl i)取得同一μ实际base点正性。363–365调用已完整接受的一般μ normalVariance_pos/parabolaCovariance_det_pos/transverseVariance_pos，得S>0、D>0、T>0。未使用仅atomicMeasure公式或把variance.toReal总化当正方差。

实际定义Δ=Cov(X,X²)、S=Var(Y)、T=detΔ/S=τ²。前置一般μ证明先真可积实际居中多项式，再在正基点排除非零二次式取零，给正定性/S/D/T正。本实现消费的hb、basepos与其真实公开类型逐项匹配，没有转到另一law。

366的G是真GaussianReal 0 (Real.toNNReal T)，NNReal参数是方差而非标准差。368先真概率；369–370先由实际hT>0得toNNReal T>0、非零，才取得nullSingletonClass_gaussianReal实例。未把零方差dirac误作无原子Gaussian。

367/371–372的rho_j精确是same μ/q/a=q4/d(mj)/mj的normalLayerConditionalLaw；公开probability定理保证每个j包括初始Dirac回退都是真概率。373–375只把公开输入hcont A hA沿hm复合，真实生产hcont的Lévy步骤仍未证明；此依赖在最终公开类型中完整保留。

376–378由hd0及固定q/16给实际负平方阈值a_j→a0。379–386由m→∞的Nat实嵌入与sqrt_atTop，再乘严格负常数−q/4（hq>0），取得b_j=−sqrt(mj)q/4→−∞。没有假定m单调或使用q的源区间上界。387–389才消费完整moving helper门，得真实rho_j曲边/符号事件概率趋G(Ca0)。

390–400定义准确C=(h/(2π))sqrt(2π/S)。实际stage_normalLayerCharacteristic_scaled_tendsto在s=0接受同μ的hb、真实EY/EX、S/D正、range/pos、全n有界d和最终格层门，给scaled复层特征趋C。再取真实复数实部并消费normalLayerCharacteristic_zero_eq_mass，得到sqrt(n)乘真实层实质量趋C；不是由复范数或取消相位推断质量。

401–404只从hd0和实指数连续性得exp(−ell d(mj))→exp(−ell d0)，ell可负/零/正。405取真实scaled层质量、权重及hcurve的三因子极限；没有把固定有界层结论提升为共同尾。

406–407独立消费实际eventually_stage_normalLayer_mass_pos，全部一般μ门同上。其前置证明由真实正C和sqrt(n)≥0推出层mass最终正，不依赖hcont。418将此eventual门与最终n≥1沿hm拉回；420先取得0<mj，才422套第一公开因子化。421精确展开rho，ring只重排有限实乘法因子，heq即真实sourceTail交层的最终等式。424用congr'完成同一子列真实表达式的极限。

所有n0和零层mass分支在第二目标函数中定义良好，但除sqrt/真实条件化只在最终正n/正mass后使用；J0仍有四个正基点，S/D/T与格距h=1合法。d0=0的零交界由真实G无原子helper处理。μ/q/ell不随J/n重选，d只沿m收敛，不暗加全n相位趋0或d全n收敛。

## 6. 本轮实际固定库主API门（只读）

| 实际库接口 | 真实门及本实现消费 |
| --- | --- |
| ConditionalProbability263–264 cond_mul_eq_inter | 可测A、有限ν；115–118在真ν概率下调用 |
| Measure/Map170–172 map_apply | 真实Measurable T与B；65–68先建，117消费 |
| Basic/ENNReal/Real130–131/337–338 | toReal_pos_iff给非零层门；toReal_mul给真实乘法，同题各概率有限 |
| Gaussian/Real220–236 | v=0为dirac，概率全v成立，NullSingletonClass必须v≠0；370先用真实T>0 |
| Typeclasses/NullSingletonClass80–86 | 有限点集零质量只在真NullSingletonClass下使用，142显式消费 |
| OrderClosed648–657 | frontier_le_subset_eq要两Continuous，frontier_Iic_subset给单点边界 |
| Measure/Continuity198–203/220–227 | union需Monotone；inter另需NullMeasurable和一项有限，215–222/258–264均真给出 |
| ENNReal/Lemmas102–103 | tendsto_toReal需有限limit；225/227/264使用G概率或0≠∞ |
| Measure/Real88–90/137–144 | real_mono需上集非top，局部安装rho_j概率后合法；union_le实际支持该真实包含估计 |
| Archimedean/Basic211–217 | exists_nat_one_div_lt要严格正gap并输出1/(k+1)<gap；188/197使用实际严格gap |
| Topology/Order/Basic139–141 | tendsto_order恰为全部严格下/上邻域eventual界；270两方向完整证明 |
| AtTopBot/Field272–274 | 趋atTop函数右乘负常数趋atBot；383显式−q/4<0 |
| Real/Sqrt139/177、NNReal/Defs551–556 | sqrt_atTop、正n平方公式，toNNReal_pos与T>0对应，按先后顺序消费 |

实际前置normalLayerConditionalLaw定义12–18和公开42–50/103–138、FundamentalFourierAsymptotic242–259、SampleBoundary53–86及一般μ协方差接口均已重新核对实际定义/完整门。已接受前置proof/build不重跑。本轮到此未发现数学或来源缺口；接下来读取全部actual DECL/TYPE，receipt/机械绿灯仍后置。

## 7. 全部10项actual DECL / TYPE（全部长续行）

先只读实际Audit.log的DECL/TYPE和全部续行、完成语义判断，之后才读receipt、Audit源及机械公理行。以下逐项覆盖真实枚举顺序；没有只核2个公开目标或按作者预估猜生成项。

```text
DECL Shao.OQ3.stage_source_layer_conditional_factorization
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (J : ℕ) (q d : ℝ),
  0 < q →
    (∀ᵐ (x : ℝ) ∂mu, x ∈ Set.range fun i => Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i) →
      ∀ (n : ℕ),
        0 < n →
          0 < (MeasureTheory.Measure.pi fun x => mu).real {z | Shao.OQ3.normalDeviation q z = d} →
            (MeasureTheory.Measure.pi fun x => mu).real
                {z | Shao.OQ3.normalDeviation q z = d ∧ z ∈ Shao.OQ3.sourceTail q n} =
              (MeasureTheory.Measure.pi fun x => mu).real {z | Shao.OQ3.normalDeviation q z = d} *
                (Shao.OQ3.normalLayerConditionalLaw mu q (q / 4) d n).real
                  {x | -(q / 16 * d) ≤ x ^ 2 ∧ -(√↑n * q / 4) < x}
DECL Shao.OQ3.stage_source_weighted_layer_subsequence_tendsto
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ),
  0 < q →
    ∫ (x : ℝ), Shao.OQ3.normalValue x ∂mu = q →
      ∫ (x : ℝ), x ∂mu = q / 4 →
        (∀ᵐ (x : ℝ) ∂mu, x ∈ Set.range fun i => Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i) →
          (∀ (i : Fin 4 ⊕ Fin J), 0 < mu.real {Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i}) →
            ∀ (d : ℕ → ℝ),
              (∃ M, ∀ (n : ℕ), |d n| ≤ M) →
                (∀ᶠ (n : ℕ) in Filter.atTop, ∃ k, d n + ↑n * q = Shao.OQ3.dyadicMesh J * ↑k) →
                  ∀ (m : ℕ → ℕ),
                    Filter.Tendsto m Filter.atTop Filter.atTop →
                      ∀ (d0 : ℝ),
                        Filter.Tendsto (fun j => d (m j)) Filter.atTop (nhds d0) →
                          (∀ (A : Set ℝ),
                              (ProbabilityTheory.gaussianReal 0 (Shao.OQ3.transverseVariance mu).toNNReal)
                                    (frontier A) =
                                  0 →
                                Filter.Tendsto
                                  (fun n => (Shao.OQ3.normalLayerConditionalLaw mu q (q / 4) (d n) n).real A)
                                  Filter.atTop
                                  (nhds
                                    ((ProbabilityTheory.gaussianReal 0 (Shao.OQ3.transverseVariance mu).toNNReal).real
                                      A))) →
                            Filter.Tendsto
                              (fun j =>
                                √↑(m j) * Real.exp (-ell * d (m j)) *
                                  (MeasureTheory.Measure.pi fun x => mu).real
                                    {z | Shao.OQ3.normalDeviation q z = d (m j) ∧ z ∈ Shao.OQ3.sourceTail q (m j)})
                              Filter.atTop
                              (nhds
                                (Shao.OQ3.dyadicMesh J / (2 * Real.pi) * √(2 * Real.pi / Shao.OQ3.normalVariance mu) *
                                    Real.exp (-ell * d0) *
                                  (ProbabilityTheory.gaussianReal 0 (Shao.OQ3.transverseVariance mu).toNNReal).real
                                    {x | -(q / 16 * d0) ≤ x ^ 2}))
DECL _private.Shao.OQ3.StageCurvedLayerLimit.0.Shao.OQ3.square_level_null._simp_1_1
TYPE ∀ {α : Type u_1} {a b : α}, (a ∈ {b}) = (a = b)
DECL _private.Shao.OQ3.StageCurvedLayerLimit.0.Shao.OQ3.square_threshold_frontier_null
TYPE ∀ (G : MeasureTheory.Measure ℝ) [MeasureTheory.NullSingletonClass G] (a : ℝ), G (frontier {x | a ≤ x ^ 2}) = 0
DECL _private.Shao.OQ3.StageCurvedLayerLimit.0.Shao.OQ3.square_threshold_mass_limits._simp_1_1
TYPE ∀ {α : Type u} {ι : Sort v} {x : α} {s : ι → Set α}, (x ∈ ⋃ i, s i) = ∃ i, x ∈ s i
DECL Shao.OQ3.stage_source_weighted_layer_subsequence_tendsto._proof_1_1
TYPE ∀ (m : ℕ → ℕ) (j : ℕ), 1 ≤ m j → ¬0 < m j → False
DECL _private.Shao.OQ3.StageCurvedLayerLimit.0.Shao.OQ3.square_threshold_mass_limits._simp_1_2
TYPE ∀ {α : Type u} {ι : Sort v} {x : α} {s : ι → Set α}, (x ∈ ⋂ i, s i) = ∀ (i : ι), x ∈ s i
DECL _private.Shao.OQ3.StageCurvedLayerLimit.0.Shao.OQ3.square_level_null
TYPE ∀ (G : MeasureTheory.Measure ℝ) [MeasureTheory.NullSingletonClass G] (a : ℝ), G {x | x ^ 2 = a} = 0
DECL _private.Shao.OQ3.StageCurvedLayerLimit.0.Shao.OQ3.square_threshold_mass_limits
TYPE ∀ (G : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure G] [MeasureTheory.NullSingletonClass G]
  (a : ℝ),
  Filter.Tendsto (fun k => G.real {x | a + 1 / (↑k + 1) ≤ x ^ 2}) Filter.atTop (nhds (G.real {x | a ≤ x ^ 2})) ∧
    Filter.Tendsto (fun k => G.real {x | a - 1 / (↑k + 1) ≤ x ^ 2}) Filter.atTop (nhds (G.real {x | a ≤ x ^ 2}))
DECL _private.Shao.OQ3.StageCurvedLayerLimit.0.Shao.OQ3.moving_curved_probability_tendsto
TYPE ∀ (rho : ℕ → MeasureTheory.Measure ℝ),
  (∀ (j : ℕ), MeasureTheory.IsProbabilityMeasure (rho j)) →
    ∀ (G : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure G] [MeasureTheory.NullSingletonClass G],
      (∀ (A : Set ℝ), G (frontier A) = 0 → Filter.Tendsto (fun j => (rho j).real A) Filter.atTop (nhds (G.real A))) →
        ∀ (a b : ℕ → ℝ) (a0 : ℝ),
          Filter.Tendsto a Filter.atTop (nhds a0) →
            Filter.Tendsto b Filter.atTop Filter.atBot →
              Filter.Tendsto (fun j => (rho j).real {x | a j ≤ x ^ 2 ∧ b j < x}) Filter.atTop
                (nhds (G.real {x | a0 ≤ x ^ 2}))
```

两项公开完整类型与实际源保持同μ、q/4中心、正n/正层mass门、任意ell和显式hcont。四private类型与第4节证明一致：level/frontier只需实际NullSingletonClass；threshold mass另需真概率；moving helper明确每个rho_j真概率及G真概率/无原子、同G连续集门和两真实Tendsto。没有丢失这些必要门。

四generated逐项独立判定：单点成员Prop等式、iUnion成员存在式、iInter成员全称式均为真实集合成员定义等式，包含空/任意Sort索引时仍正确；Nat辅助的前提1≤mj与¬0<mj确实矛盾，恰覆盖420的omega证明，没有加入原数学中额外假设或断言False。它们不是未检查的私有宏。

独立实际枚举为10 owned、10 theorem：2public+4authored private+4generated，0DEF。源码authored六项与真实owned差额四项完全由上述实际proof helpers解释；不存在只按计数猜测覆盖。

## 8. 最后读取的机械证据与绑定

数学、全部427行实现/locals、四private和全部10TYPE判断完成后，才读作者receipt、Audit源及既有build/Audit/deps/pins/hash。所有远端项目命令以taskset -c 14-17开始；未Lean/#check/API probe/build/rebuild/cachewrite/spawn/commit/raw完整日志复制，未改source/scope/receipt/旧票/shared或回退他人修改，未用ulimit-v，未触外部CPU0–9/80GiB或全局资源。

实际worktree=/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3；branch=feat/oq3-stage-curved-layer-limit；HEAD=18d47cde0e9408700a91cd0814f947cb2b8b646d。git status仅?? Shao/OQ3/StageCurvedLayerLimit.lean，与author-check时未commit/PR记录相符。

| 对象 | 实核字节/行 | SHA256 |
| --- | --- | --- |
| 本地draft、远端worktree、run源码快照（三端一致） | 20637/427 | 71c85b128101af074034f454f40d25405b6898624989d464a69a73cc19db4d60 |
| scope56本地与run/scope.md | 7615/66 | f2a28b6f6c06b03dc8c571232ba0b4f61445af97fcd766b69f4325f74abb20fc |
| 既有声明票本地与run/statement-review.md | 28826/282 | 95ccfa4d414f339971022f30ad0f3f8c2edf27765645ca8f02982f9984d86bb1 |
| 作者receipt本地U17i-receipt.json与run/receipt.json | 11739/167 | 261beb8ec46b36a245a2c385b64fafc98de56504c49d14b60342be033adfd7fd |
| 本地U17i-Audit.lean与run/Audit.lean | 1741/40 | bb3838b4e7248306090e8c4d001b94c324bc00b832065baa01978547aa6e5eb8 |
| 真实远端Audit.log | 6000/89 | f6c190d3b3d2342cd55df11a7ecd0e30fac527f42dc8923ae6b0fc1eb11c7085 |
| 前置JSON本地与run/prerequisite-hashes.json | 4827/47 | 95ea7907db310414e325cae677ba2b86efad99317390574385a631099ba342da |
| 完整冻结source的真实build-10.log | 0/0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| 原始只读R1 report.md | 19420/575 | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |
| lean-toolchain | 29/1 | d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4 |
| lake-manifest.json | 3541/117 | 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e |

独立提取两项实际完整类型，与scope fence逐项去空白比较均相同；实际imports恰H+Gaussian.Real，0公开DEF。源扫描无CR、尾空白、sorry/admit/axiom/unsafe/native_decide/implemented_by。

### 8.1 历史分段检查与完整冻结首成功，分类不混淆

receipt记录完整427行冻结源码首次成功是build10 exit0、日志空；首Audit exit0。实际远端空build10及其SHA如上只读核实，未重跑。空日志本身不独立编码历史退出码，exit值和当时阶段分类明确来自hash绑定receipt/恢复派工记录。

不能将01–09统称失败：03/06/08是逐段增添源码时成功的未完整模块检查，分别只有首公开目标、首目标+三个private、首目标+四个private；它们不是两目标完整验收。01/02/04/05/07/09是失败增量检查。每次之间源码被增加/修复，当前完整冻结成功10之后没有重复target/Audit。该历史分类被透明保留，未用旧partial成功替代本次完整source的审查。

| attempt | receipt记录exit/阶段 | 实核日志字节/行 | 实核SHA256 |
| --- | --- | --- | --- |
| 01 | 1，失败增量检查 | 110/3 | 6a8213345906a7c5bd09628925e06a9c71f94097f8cf977439346398d9b14236 |
| 02 | 1，失败增量检查 | 3028/72 | 2919d78d85165bd6e9a099999cd34dfab33259fa82df74ae861b66bb640e95e9 |
| 03 | 0，仅首公开因子化，带样式警告 | 997/16 | ba875f200b9a8509ac6ff64d3b73a1247feebf48573ccaf2211400d7bdf10c19 |
| 04 | 1，失败增量检查 | 1367/43 | 8cfb4e680a8fcf02b256a5fadfda3cb0312e68f34fb93121ed9fa43f84c02c07 |
| 05 | 1，失败增量检查 | 75/1 | a719576fbc25884b91abe9d7854ccde3398cddca0ff6c0e092ecce5c1693cdbc |
| 06 | 0，首目标+三个平方阈值private，空日志 | 0/0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| 07 | 1，失败增量检查 | 1474/28 | abf9dee47d1d9ed10ad65f67a5972df828a4782cfb6f673543797e920c0a1e0e |
| 08 | 0，首目标+四个private，带样式警告 | 714/16 | e4d776e3d3707ccd54fdcd11196d82ac9ceab36147132724d8da4cc3c6580f91 |
| 09 | 1，首个完整两目标版本，hbot化简前失败 | 3573/76 | cdf5a39d7f0c7a4627f80d786fee1a7eaf70ca0ce9b1dbcf2ac829c595d124be |
| 10 | 0，当前完整冻结source首次成功 | 0/0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |

各历史文件实际hash与receipt记录逐项相同；两个空日志有相同SHA不表示当时源码相同。本票审的是当前三端一致427行，未重建历史源，也未下载raw完整日志。所有记录命令均为CPU14–17、native -M8192 -j4、严格-DautoImplicit=false；无证明语义/心跳弱化或ulimit-v。

### 8.2 实际Audit全覆盖与公理

最后全文读取Audit.lean：先验证两个冻结目标为theorem、defs为空；遍历两个public stem及整个_private.Shao.OQ3.StageCurvedLayerLimit前缀，逐项collectAxioms并拒绝新增project axiom/非白名单传递公理。它捕获了public stem下Nat辅助及private stem下三个simp项。结合源码六authored和实际10TYPE，覆盖不留未解释差项。

实际每项AXIOMS为标准白名单的子集：单点/并/交成员三个simp项只有propext；Nat反证辅助为propext、Quot.sound；其余六authored均为propext、Classical.choice、Quot.sound。最终日志记录U17I_FROZEN_DEFINITIONS 0、U17I_FROZEN_THEOREMS 2、U17I_ALL_THEOREMS 10、U17I_ALL_DECLARATIONS 10、U17I_AXIOM_GATE PASS。

作者状态AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW及当时终审pending/未commitPR的nonclaims是正确历史时点；本票独立数学判定是现在的新裁决，不倒改旧receipt。公理PASS也不把公开参数hcont自动生产为源模型事实：其条件依赖已在类型和第5节明确检查。

### 8.3 全部45个实际项目依赖hash

独立递归actual imports，剔除本模块后45份Shao前置；每份真实SHA字典与本地JSON、run JSON、receipt imported_project_sources三方完全一致，45个现成项目olean均存在。

| 实际前置源 | 实核SHA256 |
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

对应Mathlib直接根52、全递归Mathlib模块2905，源码/现成olean缺失清单为空；没有下载或写缓存、没有为旧成功模块重编。只证明本单元实际闭包齐全，不声称U18a的另一个闭包已就绪。

### 8.4 真实public可达API源与pins

实际toolchain=leanprover/lean4:v4.36.0-rc1；Mathlib HEAD=807d3836b165983210ee2ecf3cd28f239436949c。主API owners按实际module/public import图均公开可达；以下hash在最后重算，而非只据scope文字确认。

| 实际Mathlib源 | SHA256 |
| --- | --- |
| Probability/ConditionalProbability.lean | 4245cc130e59294fadd87a6b011273c010bf3a21fd3395b8a3fe0f8a749f3f8c |
| MeasureTheory/Measure/Map.lean | 7bae8f174146d4ef4055f79757c2a0a3af6a9090dda3d28ea17fbd54540e9593 |
| Basic/ENNReal/Real.lean | da5573e6bb7b196bd109724302c3db8eda3a3efab72c8db958ce2ddbf643cecf |
| Probability/Distributions/Gaussian/Real.lean | 9edebfff169cb577b6dab1a7912f2e8fec0e70a8dac39db105263e1a0f31b383 |
| MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean | 571b68b8c23c35a977c2f9435d5bbe6bf0aa8f7e24b99420260b929a06ac3cd7 |
| Topology/Order/OrderClosed.lean | 011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e |
| MeasureTheory/Measure/Continuity.lean | efb3bc5e7fefb246225d56685023674a2c32e844e72e0d03dff5df12750c8009 |
| Topology/Instances/ENNReal/Lemmas.lean | 5fd3057f9d8e1e912b64dc09a09fd05f7e999745dc7f5fd28d960630957b8691 |
| MeasureTheory/Measure/Real.lean | 1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d |
| Algebra/Order/Archimedean/Basic.lean | 0fef31980e08533e08d3bbc67747d1c702c0b9287fe38e4f7018657441340176 |
| Topology/Order/Basic.lean | 3602a21a0c9138a3256249ea1cfd2279e6bfd0459272a6f03e0c52d8326aa82f |
| Order/Filter/AtTopBot/Field.lean | b6ce875ac37da2745d10f0b6460f3fee16f326dc2824652e1c537fba95725b33 |
| Analysis/Real/Sqrt.lean | 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204 |
| Basic/NNReal/Defs.lean | 250d8ef69dc5cca301cd7f02a1521fa21614794b602ddd99ac2cb1e1da8beeae |

## 9. 最终独立完整裁决

STATUS: CORRECT

JUSTIFICATION: 当前实际427行全部proof/locals、四authored private及四generated已独立核读，两个完整公开类型与冻结scope相同。首目标从真实产品AE stage能量正性开始，在正n/sqrt门后精确保留曲边和strict sign，并在真实非零层分支、实际map/cond/有限ENNReal乘法后恢复原real交质量。四private完整证明了无原子平方边界、两端阈值有限测度连续性以及先固定阈值/K后取序列极限的移动事件夹逼，a0=0没有遗漏。

第二目标从同μ一般协方差公开门真得S/D/T>0，再构造实际非退化Gaussian与真实条件概率族。hcont始终是同一actual family的显式输入，未被当成已证Lévy；实际s0层系数与最终正mass来自已接受公开层定理。m→∞、任意ell连续权重和最终正n/层mass后的第一目标精确因子化，完整给冻结weighted子列极限。没有条件矩、假独立、全n相位收敛或全局rate假设被暗加。

全部10actualTYPE与源码/生成枚举一致；三端源、45前置、pins、完整首成功build10空日志及10声明标准公理门都已最后只读绑定。历史03/06/08只记partial成功，未当失败或完整验收；没有重跑未改成功source或Audit。本独立数学裁决不依赖作者PASS替代语义。

本轮只写此新报告及指定remote副本，等待lead全文读取后决定发布。所证是带显式待接hcont的固定层curved/sign/weighted子列结论；hcont生产者、conditional Lévy/完整15、共同层尾组合、Phi改写、完整series limit19、LLT/hW/generalKL、全局极小/最优/新颖性及根A/B/C/D仍OPEN。
