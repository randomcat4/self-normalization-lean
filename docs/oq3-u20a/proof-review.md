# U20a SourceFixedLawCounterexample 完整独立证明审查

STATUS: IN_PROGRESS

## 不可改写盲审前缀：actual唯一公开完整TYPE

本轮先仅读取actual公开TYPE，未读该源private／proof体、作者路线／future笔记或receipt／build／Audit。此前声明审查上下文存在，但不把声明CORRECT当作实际证明正确。0publicDEF，完整TYPE如下。

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

本轮独立量词／对象／疑点翻译：

1. 不输入law或解析假设，而直接存在一个实q及一个全AtomicIndex实权重w。
2. q固定在(1,103/100)，同w全部索引严格正。
3. 同q/w/sourceEll满足全部四行真实HasSum约束。
4. 这些条件在存在交付的合取中，不能被移动到可真空成立的蕴含前件。
5. P结论内let精确为originalMeasure sourceEll w，不是另选概率law。
6. x0结论内let精确为sqrtq/4，不是自由阈值。
7. 同P必须为真正概率，X真Integrable且EX=0。
8. 同P的AE支持满足1≤|x|≤4+sqrt10，既有上界又离0。
9. 同P在Ioi0有真实正实质量，不能仅从支持存在正数推出。
10. 对全部非零联合实频率对(xi,eta)，同P actualjointCharacteristic范数严格小于1。
11. 它不是只证明单变量非格点，也不能换用另一个非格点family的w。
12. 指定resonanceXi／Eta频率之L1大小沿自然J趋+∞。
13. 同P在同一指定频率对上的characteristic范数趋实1。
14. 固定频率严格模小于1与逃逸频率模趋1必须同时属于同P。
15. 同sqrtq/4严格位于(0,1/2)。
16. 同sourceEll/q/w的实际saddleRate严格正。
17. 同atomicMeasure w上实际correctedInverseScale严格正。
18. 这些正性必须从已有公开生产者实际得到，不能借另一law或手工正数代替。
19. 在同q/w/P固定之后，存在一条nseq:ℕ→ℕ。
20. nseq须真正StrictMono，并另有Tendsto atTop atTop。
21. 全J包括0，样本量nseqJ严格正。
22. 全J，当前J的实值严格小于sqrt(nseqJ)乘实际同law尾系数偏差。
23. 不能只证明无穷多无排序见证，或给nseqJ≥J但漏掉相邻严格增长。
24. 若私有helper假设泛型G的任意晚大值，main必须用实际C为同w/q消去该假设。
25. 应从一次固定C存在取得所有性质，而不是为nonlattice／rate／gap各选不同存在见证。
26. 递归choice每步要同时保留当前J gap、positive和previous+1的late，不假设G随n单调。
27. 真单点到Ioi0的measureReal_mono需要同P有限质量，不能在toReal中漏掉非top门。
28. 正scale应由实际radicand正、ell正、sqrt正再逆正，不凭det>0或总化sqrt。
29. actual tail coefficient使用同P的真正n重有限产品概率，不是任意G序列定义成期望结果。
30. 输出不定义rootcanonicalK／domK／EReal sup，不证明全局最小或原根A/B/C/D闭合。

当前仅为实际公开TYPE的独立盲审检查点；后续只追加，不改写此历史前缀。

## 盲审前缀续：R1独立语义重建，仍未读实际proof

真实R1 137–159行要求同原P为inverse tilt，中心／有界离0且同q确定x0；259–292行要求同P的联合非格点严格模界与同指定逃逸共振模趋1；539–558行明确同一个最终固定P有sqrt(n)尺度余项无界，支持与质量不随样本量变化。
因此这个存在合取必须从一次固定q/w/P生产全部性质，公开full4HasSum是后续root在同law接解析接口的必要输出。序列StrictMono仅应选择样本时间，不能改变最终法则或把归一化尾概率换成任意数列。
独立可行性预期为：取C的无条件∃p/q/eps/r及全部∀K/N实际gap一次；固定w/P后从正权重给正P原子，逐一调用任意mu的nonlattice／resonance API；另以generic U(K,N)递归选择当前J gap且late≥previous+1，最后main真实消去U假设。所有正性须在清分母前生产。
本轮已逐字核actual唯一public TYPE与冻结scope71 fence相同；上述盲审疑点不因此前statement CORRECT而省略。完整盲审前缀此后不可改写。

## 一、范围、顺序与真实来源

前77行5410B为不可改写盲审前缀，SHA256=51e64fb1c5e80d200a1b1821ff717cb3a40fab0865dc1a1077b6719cbb95b2b3；其中最先独立持久化的actual TYPE盲译为70行4312B，SHA256=444ae99eacd5b1dd7bbd7f56b3820e67eeb115a651fa341d6319eab5532e31e4。页首IN_PROGRESS保留为历史状态，末节是最终裁决。
本轮实际顺序为：仅读actual完整public TYPE并落盘→R1／scope语义重建并追加来源盲审→完整103行proof及固定API→全部2 actual TYPE和公理→最后receipt／Audit程序／build／依赖／pins／Git等机械。
本票没有读作者implementation／candidate／future／scanner笔记，也没有从receipt数学说明建立证明路线。先前声明CORRECT只固定接口，不替实际proof背书。
公开TYPE与scope71唯一fence逐字相同；全部q/w/P/x0、两条特征函数结论、实际系数偏差、StrictMono及Tendsto量词均未改变。
R1真实137–159、259–292、539–558的同一个最终原律、支持、弱非格点和余项失败含义已在盲审前缀重建。实际proof消除的是同law组合与递增见证序列的接口义务，不把R1全局最优／root canonical叙述当成已证明输入。

## 二、唯一私有引理 increasing_remainder_witnesses（19–35）

实际完整输入为任意G:ℕ→ℝ及h:∀K:ℝ,N:ℕ,∃n,N≤n∧0<n∧K<G n；输出存在自然序列，StrictMono、Tendsto atTop atTop及∀J正样本量／实J严格gap。
这是一个泛型数列选择引理，本身不代表counterexample；main必须对真实P系数函数实际消去h，见下节。
24启用classical，25的choose只对fun(J N:ℕ)=>h(J:ℝ)N选择自然数pick J N，同时保留hpick_ge、hpick_pos、hpick_gap三条规格。
没有选择p/q/w或改变G，也没有把“存在晚见证”弱化成一个未带规格的任意数列。
26的实际Nat.rec初值pick 0 1、步函数pick(J+1)(prev+1)，在同pick函数上形成nseq。
27–29把nseq(J+1)按递归定义展开为pick(J+1)(nseqJ+1)，先Nat.lt_succ_self给nseqJ<nseqJ+1，再用该步hpick_ge给≤pick，严格增长方向正确。
30用Order/Monotone/Basic.lean577–578的strictMono_nat_of_lt_succ，真正从所有相邻严格增长得到StrictMono；没有假设原C时间序列或G单调。
31使用Order/Filter/AtTopBot/Tendsto.lean84–85的StrictMono.tendsto_atTop，此API精确是φ:ℕ→ℕ，由id_le与tendsto_id推出趋atTop，不会误用到可能有界的实严格增序列。
32–35对当前J作zero／succ cases：zero精确使用hpick_pos0 1及hpick_gap0 1，succ精确使用hpick_pos(J+1)(nseqJ+1)与相同hpick_gap。
所以每项的正性和当前实J gap来自同一次真实choose_spec，与晚到门同时保留；不是由G的假定单调性把前项gap传过去。
J0已要求晚到至少1且hpick_pos为严格正，排除n0总化边界；此引理对负K的更强h虽可用，构造只消费合法K=(J:ℝ)，无额外正K假设。
代码没有私有DEF或递归axiom；nseq是引理内正常Nat.rec let，所有规格在真实递归展开后证明。

## 三、主证明只取一次同一最终法则（62–71）

62–63唯一一次destruct公开exists_source_fixed_law_unbounded_scaled_remainder，保留p/q/eps、正p、qwindow、真实矩阵约束、r全正真可和／小总和、最终w全正、full4HasSum、同原律概率／中心化及任意晚gap。
该已完整独立接受的C公开TYPE（SourceFixedLawRemainder.lean139–154）是无输入存在命题，不输入hcont／hW／W／手工gap或代理law。
64令w=limitingMass sourceEll p r，65令P=originalMeasure sourceEll w，只是同C见证的定义别名；没有再次调用任何存在family重选参数。
66 letI : IsProbabilityMeasure P:=hprob让后续有限测度／联合特征函数API使用真实同P概率；这不是新probability假设。
67–68从同hm0的feature0=1／target0=1真实取得HasSum w1；69把C的全部严格正hw转成所需非负hnonneg。
70–71对全部AtomicIndex i以originalMeasure_atom_pos sourceEll w hnonneg hmass i(hw i)证明实际P.real{fixedAtom i}>0。
InverseTilt.lean88–92该公开API经真实单点公式w_i exp(−ellY_i)/Z及Z>0得到严格正，既没有把负权重ofReal截断当质量，也没有漏掉不可积倾斜归0的门。
这里正概率、可和性及全部单点属于同一C的w；没有使用opaque的另一个nonlattice-family存在law。

## 四、正P(X>0)、x0、正率与正scale（72–90）

73–74选Sum.inl1，由实际fixedAtom／baseAtom化简到实原子1，故hsingle是同P.real{1}>0。
75–78逐点证明{1}⊆Ioi0；79用真实measureReal_mono hsub，隐含非top门由66的概率实例满足，再lt_of_lt_of_le给目标严格正实质量。
原库Measure/Real.lean88–90完整类型为measureReal_mono(h:s1⊆s2)(h2:mu s2≠∞:=by finiteness)，证明是ENNReal.toReal_mono h2(measure_mono h)；本context具备必要有限性，不是对任意toReal无条件单调。
80由1<q先给q>0；81先Real.sqrt_pos和正4，得到x0>0；82–83以Real.sq_sqrt hqpos.le、sqrt非负及q<103/100<4推出sqrtq/4<1/2，未对非法sqrt或q作清分母。
84–85实际saddleRate_pos消费sourceEll_pos.ne'、同hw全部严格正与同hm，得到实际ell*q+logZ正；sourceEll始终为log(31/30)，没有当成1/30或输入自由rate。
86–87实际source_atomic_corrected_radicand_pos消费同qwindow、hnonneg、四基点hw(Sum.inl i)及hm；输出actual atomicMeasure w上R=S−(32sourceEll/q)detD>0。
88–90展开correctedInverseScale，先真实ell>0及sqrtR>0、乘积正，再inv_pos，精确得到同π/q的目标正scale。
这是使用公开CorrectedScaleContinuity接口的实际减项radicand正，不是凭detD>0或平方根总化猜正；没有U19b148／U19c151 private或新接口依赖。
全部q/w在上节一次固定；这里没有因正率或正scale重新选择另一个q或概率law。

## 五、泛型helper假设的真实消去及其余输出（91–100）

91–94传给increasing_remainder_witnesses的G完整字面表达式是
G(n)=sqrt(n:ℝ)*(normalizedTailCoefficient sourceEll q w n−correctedInverseScale sourceEll q(atomicMeasure w))。
传入的hgap就是62–63从同C获得的∀实K／自然N任意晚严格偏差命题；w别名与C的limitingMass定义相等，故不是caller手工输入或自由数列性质。
此处真正把generic helper的前提由无条件最终法则构造消去，返回nseq/hmono/htop/hn都已绑定同q/w/P。
95先输出同q/w及其qwindow、全正质量和full4HasSum；96保留原hprob/hcenter，并用originalMeasure_ae_bounds sourceEll w给同P真实AE 1≤|x|≤4+sqrt10。
97的联合严格模界直接调用任意mu公开jointCharacteristic_norm_lt_one_of_positive_atoms P hpos xi eta hne；当前概率实例和全部正原子都由这个P实际生产。
JointNonlattice.lean97–115的类型与每个xi/eta量词吻合，证明经模等号迫使正原子同相位、actual fixedAtom不落非零投影格，得到严格<1；不是只证明X单频率非格点。
98使用同显式resonance_frequency_escape，频率实际为Xi_J=16π2^J、Eta_J=−2π2^J，其绝对值和趋+∞。
99对同P调用generic jointCharacteristic_resonance_norm_tendsto_one，实际hsupp来自PositiveRate.lean26–29公开originalMeasure_ae_range sourceEll w。
ResonantLimit.lean49–66的概率＋AE实际原子range→每原子最终相位1、norm1真实DCT→同积分模趋1，完整接口不另选p/q/r，也不要求caller输入未来尾极限。
100把hxpos/hxupper/hrate/hscale与同G的nseq三项组入冻结合取，所有public let均只按定义相等消去，没有改law／阈值／rate／scale。

实际normalizedTailCoefficient仍是SampleChangeOfMeasure.lean19–21定义的sqrt(2πn)*exp(nI)乘Measure.pi(fun _:Fin n=>同P).real(sourceTail q n)。
sourceTail q n仍是同x0=sqrtq/4的真实energy>0及尾事件，公开sourceTail_measurable已生产可测门；本proof没有把G定义成无关任意序列来制造偏差。
因此每个J实际偏差>J是在同P真实有限n重产品概率上取得，序列只选择样本量；固定law不依赖n或J。
本模块没有新公开DEF、没有全局最优／canonical rate结论；定理名counterexample不等于原root完整陈述已经组装。

## 六、全部actual DECL／TYPE、公理和归属覆盖

完整proof与主API核查后，我实际读完actual-declarations.txt40行所有续行；公开TYPE保留全部合取／lets／∀xi eta及∀J，privateTYPE保留全部G／∀K,N假设。
只有两项owned且均为theorem：唯一公开exists_source_fixed_law_counterexample与private increasing_remainder_witnesses；无public/privateDEF或生成项。
这不是按名字预猜：最后才读的实际Audit程序对env.constants逐项用env.getModuleIdxFor?取模块索引，再用env.header.moduleNames精确比较owner==Shao.OQ3.SourceFixedLawCounterexample。
该程序检查非空实际归属集合、target确为theorem、targetCount=1，并对每owned条目拒绝axiom且collectAxioms逐项限制白名单；真实模块索引枚举输出2owned／2THM。
两个条目的传递公理均恰为[propext,Classical.choice,Quot.sound]，无sorryAx／自定义公理。完整103行source也仅有这两个authored theorem，与owner枚举联合覆盖全部声明。
以下原样保留全部实际TYPE／公理选块，其40行2562B SHA256=4e0f9ed3416336bcc50e2ac252928ac70ae887676585493ede00f762df440ac2：

```text
DECL Shao.OQ3.exists_source_fixed_law_counterexample
TYPE ∃ q w,
  1 < q ∧
    q < 103 / 100 ∧
      (∀ (i : Shao.OQ3.AtomicIndex), 0 < w i) ∧
        (∀ (k : Fin 4),
            HasSum (fun i => w i * Shao.OQ3.constraintFeature Shao.OQ3.sourceEll (Shao.OQ3.fixedAtom i) k)
              (Shao.OQ3.constraintTarget q k)) ∧
          have P := Shao.OQ3.originalMeasure Shao.OQ3.sourceEll w;
          have x0 := √q / 4;
          MeasureTheory.IsProbabilityMeasure P ∧
            (MeasureTheory.Integrable (fun x => x) P ∧ ∫ (x : ℝ), x ∂P = 0) ∧
              (∀ᵐ (x : ℝ) ∂P, 1 ≤ |x| ∧ |x| ≤ 4 + √10) ∧
                0 < P.real (Set.Ioi 0) ∧
                  (∀ (xi eta : ℝ), xi ≠ 0 ∨ eta ≠ 0 → ‖Shao.OQ3.jointCharacteristic P xi eta‖ < 1) ∧
                    Filter.Tendsto (fun J => |Shao.OQ3.resonanceXi J| + |Shao.OQ3.resonanceEta J|) Filter.atTop
                        Filter.atTop ∧
                      Filter.Tendsto
                          (fun J => ‖Shao.OQ3.jointCharacteristic P (Shao.OQ3.resonanceXi J) (Shao.OQ3.resonanceEta J)‖)
                          Filter.atTop (nhds 1) ∧
                        0 < x0 ∧
                          x0 < 1 / 2 ∧
                            0 < Shao.OQ3.saddleRate Shao.OQ3.sourceEll q w ∧
                              0 < Shao.OQ3.correctedInverseScale Shao.OQ3.sourceEll q (Shao.OQ3.atomicMeasure w) ∧
                                ∃ nseq,
                                  StrictMono nseq ∧
                                    Filter.Tendsto nseq Filter.atTop Filter.atTop ∧
                                      ∀ (J : ℕ),
                                        0 < nseq J ∧
                                          ↑J <
                                            √↑(nseq J) *
                                              (Shao.OQ3.normalizedTailCoefficient Shao.OQ3.sourceEll q w (nseq J) -
                                                Shao.OQ3.correctedInverseScale Shao.OQ3.sourceEll q
                                                  (Shao.OQ3.atomicMeasure w))
AXIOMS [propext, Classical.choice, Quot.sound]
DECL _private.Shao.OQ3.SourceFixedLawCounterexample.0.Shao.OQ3.increasing_remainder_witnesses
TYPE ∀ (G : ℕ → ℝ),
  (∀ (K : ℝ) (N : ℕ), ∃ n, N ≤ n ∧ 0 < n ∧ K < G n) →
    ∃ nseq, StrictMono nseq ∧ Filter.Tendsto nseq Filter.atTop Filter.atTop ∧ ∀ (J : ℕ), 0 < nseq J ∧ ↑J < G (nseq J)
AXIOMS [propext, Classical.choice, Quot.sound]
```

## 七、最后读取的机械证据及精确绑定

本地actual源、server worktree、run快照同103行5065B，SHA256=3d402b62362c4394eb50a6ade2f512ab90c3d19982ce19ca143c706257c5c571；完整publicTYPE与scope71 fence逐字相同，exact2imports未改。
local／remote scope71同43行7320B，SHA256=baf7463955fcf1cb3ae1d7211fa6167346b6469cde93a67fa51265f99f3a81e3；已接受声明终票195行19582B SHA256=8772c37411d5b4c78d500ba01050935e7638f64a7332491ab078b2309aa85efa原字节保留。
正式receipt local／remote同249行14852B，SHA256=e69f55873e4dca2f9c981de398ec83c0916eb7c8244818596436dd28c1d4e74f；其状态正确为AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW，作者数学叙述在本轮proof／TYPE审查后才读，不用作证明。
首次完整strict build01 exit0／4.5294684805秒；日志8行363B，SHA256=2ee1b5947d0462ab569dd7523dcb6216e528e49f62be333d844d6e0a54865972。
日志不是空文件，server独立选必要诊断核得1条line66 Try-this let-instance风格建议、0actual error；无repair／partial／失败／成功重跑记录，成功后源未变化。
正式命令为taskset -c 14-17 lake env lean -M8192 -j4 -DautoImplicit=false；本票不修改风格warning清理冻源，不减弱任何证明设置。
首Audit exit0，Audit.lean41行1791B SHA256=b797ef3b097f8c0019fa285b8eeb6f20b20c8a43ea83d9aa93be7f061c8b53ea；Audit.log45行2676B SHA256=33b738bde270930847abf38e65550d397d9f2d760220171b3e48c69592e8219f。
actual-declarations40行选块与真实Audit.log前40行逐字相同；日志摘要为0publicDEF／1target／2THM／2owned／AXIOM_GATE PASS；target olean实际存在。作者门是本轮数学审查后的机械确认，不替代逐行proof。

正式prerequisite-hashes.json68行7118B，SHA256=8ac31143691d49f01f4282818e19eb2167156fa27ac7cade67741e07cba7fdd4；本门fresh逐项核66个当前server项目源SHA与正式字典全部匹配。
其canonical相对路径键sorted compact SHA256=58e653fb52d5e8da7a8f35ad6fbeb5c33ff0416ea46ba6cef7d6447dd28e81de，与本审查者声明门独立扫描的exact2import图一致。
本proof门只复用已有图／pins／cache证据，不重新扫graph、不哈希稳定51缓存对象、不重跑成功import smoke／Lean／target／Audit；不把全共享cache目录hash冻结当作前提。
关键承重C SourceFixedLawRemainderd935445d、ResonantLimit2823af05、InverseTiltc7e7d19e、PositiveRate8e727078、JointNonlattice51ce9392、CorrectedScaleContinuityb0391976和ResonanceArithmeticcd21a264保持相同已接受源。
Mathlib实际HEAD=807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA256=d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4；lake-manifest.json SHA256=40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。
实际Git branch=feat/oq3-source-fixed-law-counterexample，HEAD=ded5b45059cf80861712f61c86170243d5e87fc2；status仅?? Shao/OQ3/SourceFixedLawCounterexample.lean，尚无本单元commit／PR。
这属于在root批准v37 accepted正常新建分支，151／148／146／144冻结head保留；本票未merge／rebase／reset／fetch或retarget。
源无CR、尾空白、sorry／admit／axiom／unsafe／set_option字样。所有本轮server项目读取taskset -c 14-17，未触CPU0–9／80GiB外部任务、ulimit-v、共享cache／pins或其他作者编辑；只新写本报告及授权远端报告，未复制完整raw日志到本地。

## 八、最终完整独立裁决与剩余义务

STATUS: CORRECT

JUSTIFICATION: 已完整审actual103行proof、唯一private helper的全部递归／choice步骤、main全部locals及精确module-owner枚举的2个实际TYPE和传递公理。C只destruct一次，固定同q/w/P后实际生产所有正单点、正半轴概率、支持、联合严格模界及共振极限、x0／rate／scale正性；generic G前提在main由同law无条件C真实消去。Nat.rec每一步同时保留当前J真实gap／正样本量／previous+1晚到，StrictMono与自然趋atTop均准确，未假设G或旧时间见证单调。全部冻结合取与actual finite-product尾系数保持原义，未发现数学／声明／公理缺口。首strict build及首Audit仅作末阶段绑定确认，1条非阻塞风格建议透明保留。

原target→本次消除：R1同一个最终固定法则的概率／中心／支持／正半轴／弱非格点／共振／正率和正常数，与真实sqrt(n)尺度余项失败现组合在同w/q/P，并有真正StrictMono且趋无穷的正样本量序列，逐J实际偏差严格大于J。
直接consumer→root可在此公开同w/q/full4HasSum上接canonical K／domK／扩展rate／鞍点／Hessian及常数适配，随后对原根最终声明作独立组装；本模块0publicDEF，不创竞争root对象。
仍OPEN→本票不自动证明canonical EReal supremum或globalmin／全局鞍点唯一性、general KL9/10、可选多项式共振速率或完整原根反例陈述。全部原根A/B/C/D仍OPEN。独立CORRECT供lead全文读后决定接受／提交／发布，本审查不执行commit或PR。
