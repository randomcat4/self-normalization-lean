# U18b StageSourceAsymptotic 完整独立证明审查

STATUS: IN_PROGRESS

## 1. actual唯一完整DECL／TYPE的先行盲译

首先只读server正式actual-declarations.txt的DECL／TYPE全部长续行，公理与机械摘要未读；本地同名mirror不存在，因此没有依赖假定的本地副本。尚未读本轮46行实现或receipt。已有声明审查背景不替代实际proof。以下原样保存实际类型选块，未创建其他本地导出／cache文件。

```text
DECL Shao.OQ3.normalizedTailCoefficient_stage_subsequence_tendsto_of_stage
TYPE ∀ (w : Shao.OQ3.AtomicIndex → ℝ),
  (∀ (i : Shao.OQ3.AtomicIndex), 0 ≤ w i) →
    HasSum w 1 →
      ∀ (J : ℕ) (q : ℝ),
        1 < q →
          q < 103 / 100 →
            ∫ (x : ℝ), Shao.OQ3.normalValue x ∂Shao.OQ3.atomicMeasure w = q →
              ∫ (x : ℝ), x ∂Shao.OQ3.atomicMeasure w = q / 4 →
                (∀ᵐ (x : ℝ) ∂Shao.OQ3.atomicMeasure w,
                    x ∈ Set.range fun i => Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i) →
                  (∀ (i : Fin 4 ⊕ Fin J),
                      0 < (Shao.OQ3.atomicMeasure w).real {Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i}) →
                    ∀ (m : ℕ → ℕ),
                      Filter.Tendsto m Filter.atTop Filter.atTop →
                        Filter.Tendsto (fun j => Int.fract (↑(m j) * q / Shao.OQ3.dyadicMesh J)) Filter.atTop (nhds 0) →
                          (Summable fun k =>
                              Shao.OQ3.sourceGaussianLayerWeight (Shao.OQ3.atomicMeasure w) q Shao.OQ3.sourceEll
                                (Shao.OQ3.dyadicMesh J * ↑k)) ∧
                            Filter.Tendsto (fun j => Shao.OQ3.normalizedTailCoefficient Shao.OQ3.sourceEll q w (m j))
                              Filter.atTop
                              (nhds
                                (Shao.OQ3.dyadicMesh J / √(Shao.OQ3.normalVariance (Shao.OQ3.atomicMeasure w)) *
                                  ∑' (k : ℤ),
                                    Shao.OQ3.sourceGaussianLayerWeight (Shao.OQ3.atomicMeasure w) q Shao.OQ3.sourceEll
                                      (Shao.OQ3.dyadicMesh J * ↑k)))
```

完整量词盲译：先给同一个AtomicIndex上的实函数w，输入逐项非负与真实HasSum w 1；随后固定自然数J、实q并要求1<q<103/100。同一个实际atomicMeasure w的真实E[normalValue]=q、E[X]=q/4；该测度AE属于Fin4⊕FinJ对应的实际stageAtom范围，而且每个该活跃索引的真实单点.real质量严格正。

再给任意m:ℕ→ℕ，要求m沿atTop趋atTop，以及同q/J的真实Int.fract((mⱼ:ℝ)*q/h_J)沿j→∞趋0。不要求m StrictMono，不把圆商距离或相位趋1替换实fract趋0；w/q/J不随j或层索引重选。

结论为两项合取：同μ=atomicMeasure w的整数函数k↦sourceGaussianLayerWeight μ q sourceEll (h_J*k)真正Summable；沿同m的实际normalizedTailCoefficient sourceEll q w(mⱼ)趋于(h_J/√normalVariance μ)乘同一整数函数的tsum。实际TYPE没有hcont族、手工hb/S/det正、阈值可测、代理law或其他新增analytic前提，必须从现有模型门生产。Summable不能用real tsum总化掩盖；q/4真实中心和same sourceEll／same law完整保留。

边界：J0／早期m0／非活跃零权不被删除；概率需要从hw和真HasSum解释，不能由类型打印中没有显式class就假定真概率。该TYPE比旧J的强化是否确实完成，留待全proof与公开API审查，不凭此前声明CORRECT或作者PASS预批。

## 2. 完整actual源码／冻结类型与R1(19)

实际唯一TYPE的盲译先于本轮源码／receipt落盘，44行／3622字节／SHA256 ac866962cf0dbaa05eca448a06dff66c9edbbdf6e74cf82e8797d297a2ddd204。后文仅追加，不改首段历史。完整读指定server StageSourceAsymptotic.lean1–46行：两imports为NormalLayerWeakConvergence与StageLayerSeriesLimit，namespace／open／noncomputable与冻结scope66一致；11–28行完整public签名去空白后与scope唯一完整fence精确一致。没有公开DEF、手工hcont／hb／方差／det前提或另一个law。

实际TYPE全部长续行已首读：w→逐项非负→真HasSum1→J/q严格窗口→同μ两均值→AE有限stage范围→每活跃单点正→m atTop／真fract phase趋0→整个Summable∧actual coefficient Tendsto。pretty-printer第一Summable的k没有重复打印类型，源码23行明确k:ℤ；stage索引源码明确Fin4⊕FinJ，m为ℕ→ℕ。全链是普通全称与箭头条件，不存在存在参数可以靠坏前件真空满足的类型漏洞。

R1第400–429行明确phase θ_{n,J}=fract(nq/h_J)、曲边层identity和(19)沿每个phase趋0序列的Cn极限。sourceGaussianLayerWeight（旧J15–18行）是exp(−ell*d)乘同Gaussian.real{x:−(q/16)d≤x²}；normalizedTailCoefficient（SampleChangeOfMeasure19–21行）是√(2πn)*exp(n*saddleRate)*同w的originalMeasure真实iid sourceTail实质量。本结论仍为(h_J/√S)Σℤ同真实层函数，不是用代理函数、Phi名义CDF或缺实际概率的数列替代来源。

旧J真实公开目标 normalizedTailCoefficient_stage_subsequence_tendsto的全部类型已再次读完：本actual类型精确保留其所有模型门／m／phase和完整结论，实际唯一被消去的前提是对任意whole d／全n有界／eventual整数格相容／任意目标frontier-null A的real条件概率收敛族。本轮必须检查该族确被生产，而不是以声明批准或作者PASS预设它。

## 3. 逐行proof29–43：真模型门全部在同atomicMeasure上产生

29–30行 `letI : IsProbabilityMeasure (atomicMeasure w) := atomicMeasure_isProbabilityMeasure w hw hs`。实际AtomicMeasure.lean21–22行以ofReal w_i乘dirac(fixedAtom i)求和；公开39–42行以真实hw和HasSum w1证明该同一measure概率。letI是现成证明在本proof上下文的局部class使用，不是新增假设、全局实例、拓扑或代理law；无全w>0输入、无对概率总化或归一化系数的猜测。

31–33行hb只从公开atomicMeasure_ae_bounds w的第二分量取值。该公开51–55行结果是∀ᵐx,1≤|x|∧|x|≤4+√10，由真实sum-dirac的AE fixedAtom范围与公开fixedAtom_bounds推得。因此 `filter_upwards ... exact hx.2` 合法给同μ的AE绝对值上界；不是使用未公开private stage_abs helper，也不是从AE支持随意推逐点界。actual proof选择了比scope说明的stage-case拆分更直接的同law公开充分入口，数学量词与类型没有改动；hrange仍原样传入J/U18a。

34–35行hbase取hpos(Sum.inl i)。实际FiniteConstraints57–58行stageAtom=Sum.elim baseAtom新增点函数，所以该分支定义性等于baseAtom i；真实单点集合与μ.real完全同一个。严格性来自活跃有限单点质量，不是只用非负权重／正总mass或假设无限索引全正。J0时Sum.inl仍有四基点，无需非空FinJ；w的非活跃零权仍合法。

36行hS是同μ的一般公开normalVariance_pos μ hb hbase；37行hD是同μ的公开parabolaCovariance_det_pos μ hb hbase。这两个RegularCovariance public接口分别157–164行、109–130行，均要求真概率、真实AE有限界和实际四基点正质量，没有手工hsecond／energy／Gaussian方差或另一个mu。已有完整独立U7终审的语义是先连续多项式真实可积／L2，再以正原子将AE零平方提升到−1／1／2真基点排除非零二次式；绝非variance.toReal总化或任意矩阵det>0冒作正协方差。hS>0保证结论√S正，hD/hS先使真实T=det/S>0，随后U18a合法还原toNNReal；本proof没有靠NNReal夹0隐藏负variance。

38–39行 apply旧J真实public theorem，传入同w/hw/hs、同J/q/qwindow、原真实E[Y]／E[X]=q/4、原hrange/hpos以及同m/hm/hphase。新目标的整项Summable∧Tendsto与其结论精确匹配，没有改h_J／√S或丢负层／整数零层。此处真正唯一余下goal是旧J完整hcont；没有访问其private term／count-DCT helper，亦没有借同名目标递归：所调用旧名称无 `_of_stage` 后缀。

40行 `intro d hd hlayer A hfrontier` 逐个引入完整hcont族的whole sequence及全部门；41–43行 exact实际已接受U18a public `stage_normalLayerConditionalLaw_real_tendsto (atomicMeasure w) J q (q/4) hb hmeanY hmeanX hS hD hrange hpos d hd hlayer A hfrontier`。每个对象／中心／目标Gaussian原样对应；局部probability实例由29行真实生产。任意d和A在固定同w/J/q及模型之后，无m、层索引或A内重选law。没有额外d收敛、A可测／有界、每早期n层正或正目标A质量前提。

所以这里不是假设hcont后重新包装旧J：旧J留下的族由U18a已经实际证明的弱收敛／连续集接口生成。hmeanX=q/4确作为U18a的一般a实例，恰为同normalLayerConditionalLaw里的统计量(ΣX−nq/4)/√n。没有把一般a路径误当tangentDeviation q，亦没有替换其条件measure。

## 4. 继承的真实分析门、边界与原系数同一性

U18a当前9ffb…生产源及其完整c9c87bfb…独立终票已接受，本轮消费公开定理而不重复其成功检查。其真实proof先由hD/hS给T非负、合法Real.toNNReal复coercion，再以相同actual U13c charFun逐点极限接Gaussian charFun和Lévy，使用标准ProbabilityMeasure弱拓扑；prime Portmanteau对任意frontier-null A给ENNReal质量，再以真Gaussian有限质量门接toReal。`ProbabilityMeasure.coe_mk`只还原底层measure，Gaussian和条件法则均未换。

因此本actual 41–43行消费的是实际.real概率收敛，不是仅特征函数收敛、NNRealapply或手工hcont假设；有限概率、真可测／可积和层归一化的门由实际U13c/U18a已证明。全n条件律的零原层dirac0fallback保留，晚期层正、n≥1与sqrt非零约分已在U13c先证明后使用。B没有新除n、除层质量或非法sqrt0消元，早期m_j=0只为合法all-n定义。

旧J完整API提供真整数Summable及actual系数极限。其已接受proof的count可积、eventual统一几何支配、两侧序列及Gaussian极限可和、真实层分解与零层只计一次，不被本B重新当作未证假设。B的角色是合法补全它的唯一分析输入，并传所有其他足够门；不能在结论处因real tsum总化而取消Summable。量词始终fixed w/J/q，m只需趋∞而无StrictMono，新proof原样传递phase真Int.fract趋0，不将接近1或circle距离替代它。

J0／m早期0／inactive零权／单点正性只有活跃Fin4⊕FinJ全被保留。q严格窗口不扩大到端点，sourceEll仍真实既有常数；B未输入或输出triangular-array统一速率、重新选p/q/eps/law，亦未产生最终diagonal或root闭合结论。

## 5. 全部声明与local／private／generated的语义覆盖

完整46行源码仅有1public theorem；没有public DEF、authored private theorem／DEF、local helper声明、instance命令、设置／attribute／宏生成命令。全部local项只letI真实概率、hb、hbase、hS、hD和intro的d/hd/hlayer/A/hfrontier，逐项如上核查。type已首读全部长续行，参数强度与source／scope一致。是否存在tactic生成常量仍留最后读取actual Audit枚举与计数核对，不能仅从源短或内核通过就预猜为0。

数学阶段独立结论：该proof完整生产原J所需全族，对同实际有限stage模型完成原R1(19)声明的hcont去假设化；没有发现数学／API／类型不符。下一节才核正式receipt、实际Audit／公理与构建／source／53前置／pins等机械证据，不以作者绿灯代替上述步骤。

## 6. 最后actual Audit全量TYPE／公理／隐藏声明核验

数学proof阶段写入报告后，才完整读取server正式receipt、39行Audit.lean，并从Audit.log选择全部实际DECL／TYPE所有续行／AXIOMS与计数。该唯一actual类型已在第1节首读完整保存，末阶段再次逐项核对，整个forall／箭头链没有新增hcont／手工方差／law输入，也没有只摘要首行。实际名称唯一为 `Shao.OQ3.normalizedTailCoefficient_stage_subsequence_tendsto_of_stage`。

Audit.lean7–10行冻结一个target、空defs；11–18行验证theorem存在及isTheorem。22–24行遍历env.constants，用完整target stem后代及 `_private.Shao.OQ3.StageSourceAsymptotic` 前缀筛选；25–29行拒绝新axiom并以Lean.collectAxioms逐项拒绝标准白名单外依赖；30行打印完整实际TYPE。34–39行核targetCount1并给计数。该机制是stem+privateprefix，不是module-index归属枚举；结合实际46行完整源码只有一个theorem、无其他命令／私有定义，覆盖实际本单元公开与可能生成项，不能误称扫过所有模块索引。

实际导出：FROZEN_DEFINITIONS0、FROZEN_THEOREMS1、ALL_THEOREMS1、ALL_DECLARATIONS1、AXIOM_GATE PASS；唯一THM实际传递AXIOMS恰为[propext, Classical.choice, Quot.sound]。从实际TYPE、完整源码与该枚举共同核明0publicDEF、1publicTHM、0authored private、0generated；不是因作者说“1owned”就预猜无helper。没有sorryAx／新axiom或其他非白名单传递依赖。

Audit源39行／1694字节／SHA256117304884aea02d9d5886a8f53eb9208f977f872812dd715332f21a91d15ee77；Audit.log32行／1935字节／SHA256 f2fd7b9072ed73ebc613b3cc4f50372c9f577eb60941f0fbee7143607829e140。所选actual DECL／TYPE／AXIOMS块27行／1821字节／SHA256 b0443e894835aa0ddba6d53ac445ba9c49f99cfc056d5c589f4c21ff82a9f0bf，按实际日志选择规则重新计算，与run actual-declarations.txt完整字节一致；首读与末核绑定同一个类型artifact。没有复制完整rawlog到本地。

## 7. 最后source／receipt／build／依赖与版本绑定

指定server工作树Shao/OQ3/StageSourceAsymptotic.lean、run同名snapshot及source-01.lean三份均46行／2139字节／SHA256905f5287250e4ef52cdd0fb7dbcd7823bbd6ceda6ac1de1ee3b82e7959580c8e。本轮读取remote实际source，无需或创建本地源mirror；只创建拥有写权的本报告。源LF无CR、无尾空白；独立顶层声明扫描只得该1theorem，sorry／admit／axiom／unsafe／native_decide／implemented_by／set_option均无命中，全源没有设置弱化或别的局部实例命令，唯一letI是29行真实概率证明。

正式receipt203行／12082字节／SHA2568763bd2321957f27cf9f6871874e2406d051c33d06d7526770b201c42aa44d78，实际状态AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW，正确把作者门与本独立终审分开。其source／scope／声明票／build／Audit／53前置字段均与本轮独立实际绑定吻合；收据的implementation叙述在本数学阶段之后才读取，未用作证明路线或批准理由。

首次完整strict build01实际exit0，既有命令为taskset -c14–17（实际命令空格为`taskset -c 14-17`）下lake env lean -M8192 -j4 -DautoImplicit=false，输出本目标olean。日志实际356字节／SHA2562c7d1766bb746b33760d12d811cab4c0602731f9ce7eaa17444f1870c3e894c4，非空。只选错误／warning摘要，真实0error、一个源29:2的warning头；正式receipt标明style.haveILetI，建议let写法而非语义问题。本报告没有把它记作空日志／0warning，也没有修改冻源消警告或重编成功源。run现存build日志只有build-01.log，receipt只有这一完整尝试、无partial／失败／重复成功记录；source-01与当前成功source精确同字节。首Audit正式exit0且无重复运行记录，本review也未启动任何target或Audit。

既有本目标olean实际42784字节／SHA256cbade741b198bc406d406956ca8f2fdba2ee9e9390df8fa412ef2c40df895c01，作为已有artifact附加绑定，不以object存在替代proof语义。旧U18a成功build／root两import smoke／稳定51对象均未重复运行或重验。

formal prerequisite-hashes.json55行／5697字节／SHA256ab6219a874756b1ba7763797437e8be0a6beb6b9ec34f434ec0b38b2623c5300，canonical53路径字典完整等于receipt对应map；排序紧凑JSON独立复算SHA25664b2df2d535f500ead30cf7d5d3bfd8b66016f9fd15c154e2f8254b138a031fb。对这正式字典逐项fresh读实际53源hash，0缺／0不符。关键U18a仍9ffb7595…、旧J仍4c797f9f…，与本轮实际公开接口读取及已独立接受版本相同。

本轮按要求沿用自己114行声明终票04099472…中的独立两import图，不重新扫描：物理53Shao／2973Mathlib，公开2696内部+189外部停止叶=2885，内部source／olean无缺。自己当时物理外部停止叶211；receipt透明另记作者扫描为208，本review保留211口径，不读取作者scanner／candidateJSON或为这不影响内部map、公开图及实际编译的行政计数差重扫／重编。没有以外部停止叶数量代替缺项验证。

冻结scope两端36行／6141字节／SHA256dd5a8aa972b0adc3aea0bb089b8e22caf0c1a71cf50f42c4555978d19fe06db8；对应声明终票两端114行／17616字节／SHA2560409947250890b0ea22f1d340f76624e4c9fa3e848c68ceb569c32944653d1de，实际完整public签名与该scope去空白一致。R1本地原件fresh SHA2563473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662；U18a完整接受终票仍162行／26441字节／SHAc9c87bfbf424a2ee5f94cbe7a474d317844903cb331772e75bd27e8ee8192cea，未倒改旧票。

fresh实际分支feat/oq3-stage-source-asymptotic，HEAD468fcefcf6205827a9551cba39b4c5afaf959150，status仅本B source untracked；作者尚无本目标commit／PR。Mathlib HEAD807d3836b165983210ee2ecf3cd28f239436949c、status干净；lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4，lake-manifest SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。当前stack接受U18a parent，未为root v35 baseline作lane merge／rebase／reset或改变冻结source。

本review仅写local drafts/oq3/u18b-proof-review.md与授权run/proof-review.md，server命令均taskset -c 14-17；实际只读进程affinity=[14,15,16,17]。没有Lean／#check／probe／build／rebuild／Audit、cachewrite、spawn、commit／pub、源／scope／receipt／旧票／shared／pins／heartbeat修改，无完整rawlog下载，不碰外部CPU0–9／80GiB或全局资源。未读作者implementation／future／actual-diagonal／candidatecache／scanner或其JSON正文，只读本门正式receipt与prereq字典。

## 8. 最终完整独立裁决与剩余原义务

STATUS: CORRECT

JUSTIFICATION: 对冻结905f5287…完整46行实际实现完成先actual唯一完整TYPE盲译、再scope/R1、全部local proof与公开API、最后实际ownedTYPE／Audit／公理及真实source/build/pins绑定。proof确由hw+HasSum生产同atomicMeasure真概率，公开AE真实原子界给hb，活跃inl点真单点正质量给hbase，再由一般公开variance／det正性接口产生全部U18a门。它保留同q/4中心、同Gaussian variance、同μ及任意whole d／A，用真实已接受U18a定理逐个构造旧J完整hcont，而非假设所需族；旧J返回同actual系数与真整数Summable。J0／早期m0／非StrictMono m／零inactive权与真实phase趋0全部保留，未换law或增加解析前提。

实际1owned＝1THM、0DEF/private/generated，完整TYPE与首读artifact一致，传递公理恰标准3；首完整build01非空仅1style警告exit0、首AuditPASS及53源绑定相符。作者内核门和本独立数学CORRECT是分开核实的两阶段，本判定不由绿灯直接推出；无成功检查重复运行。

本模块实际消除原R1(19)固定真实finite-stage coefficient极限里旧J的显式hcont分析缺口，得到所述完整Summable与相位子列极限；直接消费者是原26的任意晚阶段见证和原31固定律生产链。它未独立输出“对全部合法prefix”的组装接口、最终同一law diagonal／unbounded remainder、hW／generalKL／literalPhi／原24exactζ或全局root结论，根A/B/C/D仍OPEN。接受和发布仍须lead逐字读本完整终票后另行进行；未宣称优化性、最弱条件或新颖性。
