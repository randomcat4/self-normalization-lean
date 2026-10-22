# U20a SourceFixedLawCounterexample 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 不可改写盲译前缀：冻结唯一完整TYPE

先仅提取scope71的Lean fence完整TYPE，尚未读其说明、作者路线、候选图或新机械证据。已有前置审查上下文存在，但不把前置已接受误作本合取声明自动成立。0publicDEF／1publicTHM。

```lean
theorem exists_source_fixed_law_counterexample :
    ∃ (q : ℝ) (w : AtomicIndex → ℝ),
      1 < q ∧ q < 103 / 100 ∧ (∀ i, 0 < w i) ∧
      (∀ k : Fin 4,
        HasSum (fun i => w i * constraintFeature sourceEll (fixedAtom i) k)
          (constraintTarget q k)) ∧
      let P : Measure ℝ := originalMeasure sourceEll w
      let x0 : ℝ := Real.sqrt q / 4
      IsProbabilityMeasure P ∧
      (Integrable (fun x : ℝ => x) P ∧ (∫ x : ℝ, x ∂P) = 0) ∧
      (∀ᵐ x ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + Real.sqrt 10) ∧
      0 < P.real (Set.Ioi 0) ∧
      (∀ xi eta : ℝ, xi ≠ 0 ∨ eta ≠ 0 → ‖jointCharacteristic P xi eta‖ < 1) ∧
      Filter.Tendsto (fun J => |resonanceXi J| + |resonanceEta J|)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun J => ‖jointCharacteristic P (resonanceXi J) (resonanceEta J)‖)
        Filter.atTop (nhds (1 : ℝ)) ∧
      0 < x0 ∧ x0 < 1 / 2 ∧ 0 < saddleRate sourceEll q w ∧
      0 < correctedInverseScale sourceEll q (atomicMeasure w) ∧
      ∃ nseq : ℕ → ℕ, StrictMono nseq ∧
        Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
        ∀ J : ℕ, 0 < nseq J ∧
          (J : ℝ) < Real.sqrt (nseq J : ℝ) *
            (normalizedTailCoefficient sourceEll q w (nseq J) -
              correctedInverseScale sourceEll q (atomicMeasure w))
```

独立量词／let／全部条件与结论翻译：

1. 结论直接存在一个实q及一个全AtomicIndex实权重函数w，没有caller提供的解析前提。
2. 同q必须满足1<q<103/100，不能在不同性质之间重择q。
3. 同w的每个AtomicIndex权重都严格正，包括四基点及全部新增索引。
4. 同w对sourceEll的全部四条真实feature行满足实际HasSum到同q的target。
5. 此处严格正与HasSum是无条件存在交付的一部分，不是仅藏在蕴含前件。
6. P在最后合取内let为originalMeasure sourceEll w，所有原律性质与样本量系数都必须绑定它。
7. x0在结论内let为sqrt(q)/4，不是另一个存在阈值。
8. P为真正IsProbabilityMeasure，而不是总化tilted=0或另选概率law。
9. x在P上真实Integrable且积分严格等于0。
10. 同P的AE样本满足1≤|x|≤4+sqrt10，含有界且与0分离两侧。
11. P.real(Ioi0)>0是实际正半轴概率，不只是支持集存在一个正数。
12. 对所有实xi/eta，只要至少一个非零，同P的jointCharacteristic范数严格小于1。
13. 它是联合非格点严格模界，不应只证明单一X方向或使用另一个opaque family的w。
14. resonanceXi/J及resonanceEta/J是指定公开频率函数，不可按P另选频率。
15. 指定频率两分量绝对值之和沿自然J趋于+∞。
16. 同P沿同频率的jointCharacteristic范数沿J趋于实1。
17. 这与非零固定频率严格小于1并存，表达非强非格点逃逸序列。
18. 同x0必须严格在(0,1/2)内；须先q>0才解释sqrt和窗口。
19. 同q/w/sourceEll的实际saddleRate严格正，不能只给形式率常数或无关KL代理。
20. 同atomicMeasure w上的实际correctedInverseScale严格正。
21. 最后存在一条自然数序列nseq；这个存在在同q/w/P/x0及所有上述性质之后。
22. nseq严格递增，并显式趋于atTop；不能只给无穷多个无排序见证。
23. 对所有自然J，nseq J>0，尤其J0不能落在n0总化边界。
24. 对每个J，同一实际normalizedTailCoefficient在nseq J的偏差乘sqrt(nseq J)严格大于实J。
25. nseq的递归选择应只选样本量，不能为每个J重选w/q/P。
26. 公开TYPE没有手工gap／hcont／hW／Levy／W／概率存在性输入，须由已接受生产者实际消去。
27. 需核arbitrary-late见证给阈值K=J及N至少previous+1时能同时满足晚到和原gap，不假设原见证序列本来单调。
28. 同原律产品样本及归一化系数必须保持现有真实定义，不能换成自由序列来制造增长。
29. 需核实际正原子P质量／全部正w／约束对joint严格性与共振极限的公开接口足够，无跨privatehelper。
30. 声明不定义canonical K／domK／EReal sup，不声称全局最优性或root A/B/C/D闭合；此门须明确剩余桥接。

以上仅为新完整TYPE的独立盲译及待核疑点，后续审查只能追加；当前检查点不是批准。

## 一、冻结范围及原始来源对应

以上70行4713B盲译前缀原字节保留，SHA256=6e4ece82f09fc54bcd28a0c5dabd259d059894ba2061dec4bfd5d2ed0ab7d4f8；页首IN_PROGRESS只记录先行检查点，末节为本门最终裁决。
本轮严格在完整TYPE盲译落盘后才全文读scope71、R1实际原文、实际已接受公开生产者及固定库；再最后作一次新exact2import静态图与机械绑定。
这是0publicDEF／1publicTHM的声明／来源／API门，尚无实现。既有前置独立CORRECT是可消费的生产者证据，不等于本新声明已elaborate或kernel/Audit通过。

R1真实137–145行定义同π反向指数倾斜P，给中心化及有界／离0支持，正向exp(8ellX−ellX²)重倾斜回同π。
149–159行给同固定q的x0=sqrtq/4及正的source率；259–277行给所有非零联合频率严格模小于1；279–292行给指定逃逸频率上模趋1。
486–497行先选样本量再限制未来尾，539–550行明确“one final fixed law P”的sqrt(n)尺度余项无界，而非一列随n改变的law。
554–558行再次明确P、x0及所有质量固定，样本量变化时不换law，并保持有界且与0分离。
公开新TYPE忠实组合这些已分别生产的实际性质，并加强输出一个真实StrictMono时间序列；没有把原global rate／鞍点假设偷偷写成自由输入。
R1可选(14a)的超多项式共振速率没有出现在此TYPE，本票也不把单纯模趋1声称为已经导出的每个多项式弱Cramér速率结论。

## 二、一次固定实际C生产者，禁止换w／q／P

实际SourceFixedLawRemainder.lean139–154的公开exists_source_fixed_law_unbounded_scaled_remainder是无输入存在命题。
它一次生产p:Fin4→ℝ、q、eps及r:ℕ→ℝ；p全正、1<q<103/100、eps>0、原矩阵约束成立、r全正真Summable且总和<eps。
结论继续交付同w=limitingMass sourceEll p r的每个AtomicIndex质量严格正，以及同sourceEll／fixedAtom／q的全部四条真实HasSum。
它同时交付同P=originalMeasure sourceEll w的真概率、真Integrable X且EX=0，及实际
∀(K:ℝ)(N:ℕ),∃n:ℕ,N≤n∧0<n∧K<sqrt(n)*(normalizedTailCoefficient sourceEll q w n−correctedInverseScale sourceEll q(atomicMeasure w))。
这不是输入hcont／hW／W／手工gap之后的条件式；实际公开TYPE已消去这些假设，存在的r在全部K/N/n之前固定。
本新声明可只destruct这条C存在一次，令同w为其limitingMass，保留q/w/约束/概率/中心化/U，再忘去不需要公开的p/eps/r细节；不重新调用一个opaque family来取得另一个w。
全部后续支持、单点、特征函数、率、scale与nseq均从这个固定w推导。没有按n、频率J或时间索引J重选q、r、w或P。
从hm0可真实得到HasSum w1；hw严格正给非负，后续原律概率与积分API使用的正是这两个真实门。
这里没有消费Q的opaque eps、跨模块private helper或通过“存在另一个非格点family”偷换最终law。

## 三、同一个P的支持、正半轴质量及联合非格点

原律概率与Integrable X／EX=0直接由C保留；亦与公开InverseTilt.lean51–55、94–114的同w接口一致。
InverseTilt.lean57–60的originalMeasure_ae_bounds在同sourceEll/w上给AE 1≤|x|≤4+sqrt10；倾斜绝对连续把实际atomic支持传给同P。
不是从另一个概率law的有界性借来支持；1≤|x|含真实离0，不能只给|x|上界。

InverseTilt.lean88–92的originalMeasure_atom_pos完整输入ell、w、hw≥0、真实HasSum w1、索引i及0<w_i。
其结论P.real{fixedAtom i}>0来自准确单点公式w_i exp(−ellY_i)/Z；exp正且inverseNormalizer_pos真严格正，非ENNReal.toReal总化假阳性。
C给所有w_i>0，所以同P的每个fixedAtom均有真实正单点质量。
取i=Sum.inl(1:Fin4)，实际fixedAtom=baseAtom1=1，故{1}⊆Ioi0。
真实MeasureTheory.measureReal_mono在Measure/Real.lean88–90先取集合包含，另有μ(Ioi0)≠∞门；它的默认finiteness也必须由已建立的IsProbabilityMeasure P满足。
因此0<P.real{1}≤P.real(Ioi0)，得到准确正半轴质量。没有把任意支持点的存在当成正质量，也没有忽略有限ENNReal转实门。

JointNonlattice.lean97–115的公开jointCharacteristic_norm_lt_one_of_positive_atoms适用于任意真概率mu，只需全部fixedAtom实际正单点质量。
它完整结论是∀xi eta，xi≠0∨eta≠0→‖jointCharacteristic mu xi eta‖<1，恰好匹配新TYPE的联合两频率量词。
实际jointCharacteristic是∫ exp(i(xiX+etaX²))，不是X单变量characteristic或CenteredNormal代理；公开integrable_jointPhase以真实连续及norm=1在概率下给真可积。
既有该定理经严格凸模等号→所有正原子相位相同→实际fixedAtom_no_projection_lattice迫使xi=eta=0，适用于此同P。
其private strictConvexSpace证明只在原module内消费；本新模块直接调用公开定理，无需复制／公开一个新共享instance或跨private引用。
尤其不能消费exists_source_weakly_nonlattice_family的另一个存在p/q来替换C的law；本目标已有足够的任意mu公开API。

## 四、同显式频率共振与所有正性门

PositiveRate.lean26–29的公开originalMeasure_ae_range（实际在PositiveRate，不在InverseTilt定义）直接给同P AE属于range fixedAtom；该定理经倾斜绝对连续获得，不要求调用另一个family。
ResonantLimit.lean62–66的公开jointCharacteristic_resonance_norm_tendsto_one完整输入同mu真概率及该AE实际原子range，输出新TYPE所需norm趋实1。
其上游49–60先以每原子最终相位=1、同mu上的norm1可积主控和真正DCT证明复杂积分趋1，再取norm；不是由特征函数模小于1直接猜极限。
实际指定频率为ResonanceArithmetic.lean18–20：resonanceXi J=16π2^J，resonanceEta J=−2π2^J。
该文件64–77的resonance_frequency_escape给同一对频率L1范数趋+∞，不依赖q/w且没有另择P相关频率；58–62相位恒等式为2π2^J normalValue x。
故两个共振结论与所有非零固定频率严格模小于1真正属于同P，可以同时成立，且J0频率亦由公开定义合法。

实际sourceEll_pos给sourceEll=log(31/30)>0，因此非零；PositiveRate.lean142–154的公开saddleRate_pos消费同w全部严格正及完整hm，给真实saddleRate sourceEll q w>0。
没有把sourceEll当成1/30，也没有输入另一KL／全局rate代理来替代此实际定义ell*q+logZ。
CorrectedScaleContinuity.lean138–155的公开source_atomic_corrected_radicand_pos消费同qwindow、hw≥0、四基点w(Sum.inl i)>0与全部hm。
这些门均由同C输出成立，故R=normalVariance π−(32sourceEll/q)*det(parabolaCovariance π)>0，π=atomicMeasure w。
已有correctedInverseScale的真实定义为(sourceEll*sqrt R)^-1；先sourceEll>0、R>0，再sqrt正和乘积正／逆数正，严格得到目标scale>0。
这一步不依赖U19b SourceGeometricScale或U19c SourceLogPartitionDerivatives，也没有只凭det>0而忽略减去项来断言radicand正。

由1<q得到q>0，再Real.sqrt_pos给sqrtq>0；q<103/100<4，配Real.sq_sqrt(q≥0)及sqrt非负得sqrtq<2，除正4给0<x0<1/2。
实际Analysis/Real/Sqrt.lean177的sq_sqrt及285–286的sqrt_pos是当前公开接口；不需要新cache或任意归一化假设。
所有实乘除分母4、原Normalizer及sqrtR均有真实门；本声明无n0的逆sqrt约分，最后序列每项另保证n>0。

## 五、任意晚实际见证到StrictMono真实时间序列

固定上节所有q/w/P/scale，记G(n)=sqrt(n)*(normalizedTailCoefficient sourceEll q w n−correctedInverseScale sourceEll q(atomicMeasure w))。
C给U(K,N):∃n,N≤n∧0<n∧K<G(n)，对全部实K及自然N，且同law已在这些量词之外固定。
按Classical.choose，在每个自然J/N定义pick(J,N)为U((J:ℝ),N)中的一个真实见证；choose_spec同时保留late、positive与原J严格gap。
只选择自然数见证，绝不重新解整个C的存在p/q/r；也不要求C原本的阶段序列单调。
递归设nseq0=pick(0,1)，nseq(J+1)=pick(J+1,nseqJ+1)，这是Nat.rec在同pick函数上的普通自然数递归。
初项nseq0≥1且0<nseq0，gap为0<G(nseq0)；因此J0/N0边界不落在n=0的总化概率表达式。
每一步choose_spec给nseqJ+1≤nseq(J+1)，由自然数后继严格性得nseqJ<nseq(J+1)，并同时给0<nseq(J+1)及(J+1:ℝ)<G(nseq(J+1))。
固定J的gap并不是由单调性传过去：它是在该步阈值K=J处实际重新选择满足原U的n；所以每J精确保留目标严格界。
归纳／cases J可完整交付∀J,0<nseqJ∧(J:ℝ)<G(nseqJ)，严格不等号没有弱化成≤。
实际Order/Monotone/Basic.lean577–578的strictMono_nat_of_lt_succ由全部相邻严格不等式给StrictMono nseq。
实际Order/Filter/AtTopBot/Tendsto.lean84–85的StrictMono.tendsto_atTop专用于φ:ℕ→ℕ，由其id_le推出Tendsto atTop atTop；不是错误套用到可能有上界的实严格增序列。
因此TYPE中StrictMono、Tendsto和全J偏差这三项均可由当前公开C实际生产，不需新增选择／增长／单调见证前提。
同一个阶段字母J在两频率极限和时间序列中不要求额外对齐条件；TYPE没有把频率J误当样本量n，也不需要nseqJ与2^J的算术相容。

## 六、实际系数与原概率事件未被替换

SampleChangeOfMeasure.lean19–21的normalizedTailCoefficient ell q w n，真实为sqrt(2πn)*exp(n*saddleRate ell q w)乘Measure.pi(fun _:Fin n=>originalMeasure ell w).real(sourceTail q n)。
它是同一P的实际n重有限产品概率，而不是caller给定的实序列或另一个measure；C公开gap已使用该实际定义。
SampleBoundary.lean25–27的sourceTail q n要求实际energy>0且(sqrtq/4)*sqrt(n*energy)≤sumX，正是同x0下源尾事件，41–45给真实可测门的公开证明。
本新TYPE没有改变归一系数、law或x0，也没有把saddleRate与correctedInverseScale自定义为能使G增长的任意常数。
声明保留完整四HasSum和同w/q，供root以后将canonical对象及U19c解析身份接到这个精确法则；本门只确认该可消费性，不替root完成桥接。

## 七、数学后核的静态图／缓存／版本／冻结行政事实

本审查独立一次扫描实际exact2imports SourceFixedLawRemainder／ResonantLimit：剥除注释／字符串，识别普通import与public/private及meta modifier；非module传统import按公开处理。
physical遍历全部内部边，public只遍历公开边；只展开Shao／Mathlib，Lean/Batteries等外部节点停止且单列，不冒称其内部已展开。
独立physical=66Shao＋2973Mathlib＋211外部停止=3250节点；public=2711内部＋189外部停止=2900节点。
全部66＋2973内部source和对应olean存在，缺0；这只是静态存在性，不是本target的Lean成功，也不是全共享cache hash不变假设。
66canonical源相对路径键sorted compact SHA256=58e653fb52d5e8da7a8f35ad6fbeb5c33ff0416ea46ba6cef7d6447dd28e81de。
实际公开可达C／ResonantLimit／JointNonlattice／ResonanceArithmetic／InverseTilt／PositiveRate／CorrectedScaleContinuity，及Measure.Real／Order.Monotone.Basic／AtTopBot.Tendsto／Analysis.Real.Sqrt。
SourceGeometricScale与SourceLogPartitionDerivatives不在此图，符合本门不以148／151为import依赖；C144实际生产者本身在图并保持冻结源。

关键实际源本地／server SHA一致：
- SourceFixedLawRemainder.lean d935445d9a9ba3a524273b35986cbd0e6371faa1cd93295c42c205ec80a55696（235行12309B）。
- ResonantLimit.lean 2823af057a916aceb09aa68bb098af030c757f7d1e3b33040095b6c528516b57（99行4932B）。
- JointNonlattice.lean 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559。
- InverseTilt.lean c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811。
- PositiveRate.lean 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b。
- CorrectedScaleContinuity.lean b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8。
- ResonanceArithmetic.lean cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b。
真实R1原件SHA256=3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662；新scope71本地／remote同43行7320B，SHA256=baf7463955fcf1cb3ae1d7211fa6167346b6469cde93a67fa51265f99f3a81e3。
本报告完整fence与scope逐字相同；namespace Shao.OQ3／open MeasureTheory／scoped Matrix Topology BigOperators／noncomputable及这两个imports提供所需记号与标准实例。
实际Mathlib HEAD=807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA256=d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4；lake-manifest.json SHA256=40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。
实际worktree仍branch feat/oq3-source-log-partition-derivatives，HEAD a8991280cab24bd1fdd25d97d2404e414f5b9bce，status--short为空；未提前说新U20a分支已经建立。
server实际SourceFixedLawCounterexample.lean／U20a Audit.lean／receipt.json均不存在；本声明不预报未来elaboration、target／Audit或内核PASS。
所有server读取taskset -c 14-17；本轮未启动Lean／#check／probe／build／Audit／root smoke，未重扫旧图或重跑任何已成功门，未写cache/pins/source/旧票，也未触CPU0–9／80GiB外部任务。

## 八、最终独立裁决及承重边界

STATUS: CORRECT

JUSTIFICATION: 完整TYPE无隐藏手工gap／hcont／law输入。现有无条件C公开定理一次固定实际q/w/P并交付全部严格权重、真实HasSum、概率／中心化及任意实阈值任意晚实际系数见证。其同w可逐项生产所有正单点、支持、联合严格模界、同指定逃逸共振极限、q窗口下x0、正率及真正正corrected scale；不消费另一个opaque family或跨privatehelper。选择函数与自然递归可严格保持同law并同时给每项正、相邻严格增长和当前J实际gap，标准自然严格增趋atTop接口公开可达。精确新imports静态source／olean无缺项，未发现声明或环境阻塞；actual实现／全部生成TYPE／公理仍须后续独立proof门。

原target→消除义务：将R1固定最终法则的premise audit／真实弱非格点与任意晚scaled remainder失败合并为同一w/q/P，并生产真实StrictMono见证时间序列。
直接consumer→root使用此公开w/q/full4HasSum在同law上接canonical rate／K／鞍点／Hessian／常数适配，再处理原根A最终陈述；不能因本定理名含counterexample就跳过这些接口。
仍OPEN→本声明门不定义或证明root canonical K／domK／EReal sup、全局鞍点／最优性、general KL9/10、完整原始根反例组装或可选多项式共振速率。全部原根A/B/C/D仍OPEN。本票是声明CORRECT，不是尚不存在实现的proof验收；lead全文读后才可实施。
