# U18b StageSourceAsymptotic 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 1. 冻结唯一完整类型的先行盲译

先仅提取 scope66 唯一 Lean fence 的完整类型，未读本 scope 正文、作者路线或本轮依赖／缓存材料；零公开定义。已有 U18a 与旧条件链的审查背景存在，但不据此默认新声明成立。

```lean
theorem normalizedTailCoefficient_stage_subsequence_tendsto_of_stage
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hphase : Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
      atTop (nhds 0)) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
        (dyadicMesh J * (k : ℝ))) ∧
      Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
        atTop (nhds ((dyadicMesh J / Real.sqrt (normalVariance (atomicMeasure w))) *
          ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
            (dyadicMesh J * (k : ℝ))))
```

完整量词：先给同一个全局原子索引上的实权重 w，逐项非负 hw，且真实 HasSum w 1（不是仅以总和符号的总化等式代替可和）。随后固定自然数 J 与实数 q，要求1<q<103/100。对同一个实际 atomicMeasure w，真实积分 E[Y]=q、E[X]=q/4；该测度几乎处处落在 Fin4⊕FinJ 索引的真实 stageAtom 范围内，且每个该活跃有限索引对应的实际单点实质量严格正。

在 w/J/q 及全部上述模型门固定后，再给任意自然数函数 m:ℕ→ℕ，只要求 m 沿 atTop 趋 atTop，不要求它严格递增；另要求同一 q/J 的实数相位 Int.fract((mⱼ:ℝ)*q/dyadicMesh J)沿 j→∞真正趋0。不是只要求圆商距离趋0，也不是对全部原n已输入相位趋0。

结论是同一实际 atomicMeasure w 的两项合取：第一，整数 k 上的真实函数 sourceGaussianLayerWeight(atomicMeasure w,q,sourceEll,h_J*k) 真正 Summable；第二，沿上述同一个m序列的实际 normalizedTailCoefficient(sourceEll,q,w,mⱼ) 趋于 (h_J/√normalVariance(atomicMeasure w)) 乘同一整数函数的真实 tsum。sourceEll 是既有固定常数，h_J=dyadicMesh J；量词未允许按j/k重选w/q/J或代理法则。该类型未新增手工方差／行列式正性、AE有界、hcont家族、可测阈值或额外解析极限假设，后续必须从现有真实模型门及公开接口推出所需条件。

边界保留：J=0；w只需非负而非全索引严格正；早期mⱼ可以为0，极限门仅排除最终停留有限n；源索引上的零权／重复原子及真实stage支持不由本盲译擅改成全w>0。两个结论必须同law、同w和同sourceGaussianLayerWeight系数，不能把Summable当作实tsum默认0或另加hcont。以上只是实际冻结类型的数学翻译，尚未判新强化可由库证明。

## 2. 与真实 J 接口的完整强化边界及原义务

盲译已先行持久化为36行／3370字节／SHA256 b7e7d2af1c0d1feee0055628739f00300a72cc9479dc362f5796b1ab5d8dd5fb，后文只追加，未覆盖首读历史。随后完整读取36行scope正文及accepted StageLayerSeriesLimit.lean的真实定义／唯一public完整类型，亦重新读取已完整终审的U18a当前88行生产源。

独立按括号层级提取 J 完整公有目标中的整个 `(hcont : ...)` binder，删除它、只把定理名后加 `_of_stage` 后，再对余下所有字符去空白比较：与本scope唯一fence精确一致。不是只比较前几行；w/hw/真实HasSum1、J、q窗口、真实EY/EX、AE有限stage范围、每活跃点单点正、m／hm／hphase以及整项Summable∧Tendsto结论均保留。没有删除其他前提、改Gaussian参数、换原归一系数或新输入W／gap。

被删除的完整hcont实际要求：对任意全序列d:ℕ→ℝ，若存在同M对全n有界且最终dₙ+nq∈h_Jℤ，则对任意A:Setℝ，只要同一gaussianReal0(toNNReal(T(atomicMeasurew)))对frontier A质量0，实际normalLayerConditionalLaw(atomicMeasurew,q,q/4,dₙ,n).real A趋于该同Gaussian.real A。它是全n滤子极限族，不是只在m上／固定阈值／有界可测A／正目标质量A的较弱替代。U18b必须真实生产这整个族。

原R1第400–429行的实际层相位、曲边恒等式和F_J(d)=exp(−ell*d)g_J(d)，要求沿每个phase→0序列得到(19)：C_n→(h_J/σ_J)Σ_{k∈ℤ}F_J(kh_J)。实际sourceGaussianLayerWeight（J源15–18行）是exp(−ell*d)乘同Gaussian.real{x:−(q/16)d≤x²}，准确保留曲边层权重；Summable结论是真整数序列可和，不能以tsum默认0替代。SampleChangeOfMeasure.lean19–21行实际normalizedTailCoefficient是√(2πn)*exp(n*saddleRate)*同一w的原originalMeasure真iid产品sourceTail质量，不是新定义代理Cn。

因此本声明的直接新增承重是消去J为实现原(19)而保留的解析hcont输入，使真实有限阶段模型的(19)不再依赖这一外加分析假设。来源中的实际层和可和、截断、moving曲边、远切向sign处理已经属于accepted J及其前置；本门不凭scope路线重证它们，也不能把J曾为条件式的事实隐藏为早已无条件完成。

## 3. 同一实际atomicMeasure的概率、有界与非退化门能够从现有输入产生

令μ仅作定义缩写atomicMeasure w，绝不另选概率proxy。实际AtomicMeasure.lean21–22行定义μ=Σ_i ofReal(w_i)·dirac(fixedAtom_i)。39–42行公开atomicMeasure_isProbabilityMeasure(w,hw,hs)直接消费逐项非负和真实HasSumw1，给IsProbabilityMeasure μ；没有要求全w>0、额外积分归一化或手工假定概率。可在证明局部使用该现成实例，然后整个hcont族与U18a都保持这同一个μ。

hb确可从已给hrange逐点得到：对x=stageAtom新增点族 i，若i=inl a，则stageAtom=baseAtom a=fixedAtom(inl a)；若i=inr j，则等于addedAtom j.val=fixedAtom(inr j.val)。FiniteConstraints.lean57–58行stageAtom=Sum.elim baseAtom x，SummableAtoms.lean23–25行AtomicIndex=Fin4⊕ℕ、fixedAtom=Sum.elim baseAtom addedAtom，故这些是真函数身份，不是用概率近似替代。公开fixedAtom_bounds对两个分支都给 |x|≤4+√10；hrange的AE门提升为所需AE hb，包含J0无新增点分支。

还实际核到一个更直接的公开等价充分入口：AtomicMeasure.lean51–55行atomicMeasure_ae_bounds(w)已对该同μ给∀ᵐx,1≤|x|∧|x|≤4+√10，由公开atomicMeasure_ae_range和fixedAtom_bounds证明；取第二分量即可得到同hb，不需读取或调用U17g的private stage helper。无论采用哪条公开路径，不能给新目标增加手工hb，也不需要给无活跃新增点的J0另立假设。

hbase直接从hpos取Sum.inl a，得到∀a:Fin4,0<μ.real{baseAtom a}；stageAtom的定义性等式即完成转换。这里严格性是实际单点质量，不是仅w_a≥0、AE函数非零或无限全w>0。即使其他无限索引权重为0，或J0，四个真实基点仍由hpos(inl a)保证。公开fixedAtom映射实际可区分原子，但本推导不需要擅自加入injectivity或非空J门。

实际RegularCovariance.lean109–130行的公开parabolaCovariance_det_pos(μ,hb,hbase)给0<detΔ，同源157–164行公开normalVariance_pos(μ,hb,hbase)给0<S。两者是对任意真概率μ的一般公开接口，不是仅atomicMeasure版本，不需要另加hsecond／energy／手工rategap。它们内部80–107行先使真实连续平方函数可积，由AE平方为0及正原子推出三基点−1、1、2处二次式为0，排除非零方向；var／cov语义和132–154行积分线性前已先真可积。故此处不能把variance.toReal总化或任意det>0矩阵当作真实协方差。固定μ满足这些实门后，S>0与det>0还先给T=det/S>0，再合法解释Gaussian.toNNReal方差，沿用U18a真实结论。

## 4. 完整hcont族的真实生成与量词不丢失

已接受U18a当前实际公开stage_normalLayerConditionalLaw_real_tendsto（源54–85行）在任意真概率μ下，依次消费J、q、a、hb、真实E[Y]=q、E[X]=a、S>0、det>0、hrange、hpos，然后任意d及全n界／eventual整数相容，再任意A和同Gaussian(frontier A)=0。令a=q/4，传本目标hmeanY/hmeanX及上节真实产生的概率／hb／hS／hD，就逐个给出J所需hcont的完整输出。

具体量词匹配是：先固定w/J/q和真实模型；构造同μ的hb／hbase／hS／hD；再对任意d、hd、hlayer、A、hfrontier，应用同一个U18a公开定理。所得到的函数正是第2节完整被删binder，不含m、m_j或phase极限；所以绝不是对某个指定曲边A或已选phase子列才临时选择一个law／方差。也不需要先假设所求hcont来调用其自身，依赖顺序为公开模型门→U18a→J，无循环。

U18a源真实正常化对象是本来normalLayerConditionalLaw μ q a dₙ n，其全n概率定理保留零原层时dirac0fallback；n0／早期offgrid不会让概率序列失效。U18a已经完整证明同一序列Lévy弱极限和prime Portmanteau的任意frontier-null集合实概率，之后用真Gaussian有限质量的toReal连续性。此处只消费已接受实际public theorem，不复用作者API笔记或旧声明绿灯；没有新MeasurableSet A门，亦不把仅NNRealapply收敛误作.real。

真实hmeanY／hmeanX在同一个μ上；hb和真概率保证相关多项式真可积／L2，因此不是不可积积分默认0而偶然满足均值。d只全n有界，不要求趋常数；eventual格相容未被提升成所有早期n实际可达。所构造的hcont使用同一个目标Gaussian T和统计量(ΣX−nq/4)/√n。它与旧J的q/4中心完全相同，不能误把一般a统计量当tangentDeviation q而不作该实例化。

## 5. 实际消费J后的结论与边界可行性

把上述全族作为J唯一被删参数，连同所有原样w/hw/hs/J/qwindow/均值/stage门/m/hm/hphase传给normalizedTailCoefficient_stage_subsequence_tendsto，直接得到本完整目标的真Summable与同actual normalizedTailCoefficient的Tendsto。J的真实定义和公有TYPE已逐字对照；不需访问其private term_le_shifted_tsum或private count-DCT helper，亦不需要本门新造积分换序或补Gaussian tail假设。旧J证明中的真count可积、两侧Summable和统一几何截断是该accepted public API的实质承重，不能在实现时仅以同名实tsum总化绕过。

J0允许h=dyadicMesh0=1；四基点hbase和全部同μ门仍成立，无新增点或无新增索引可正是合法边界。m只需Tendsto atTop，原type没有StrictMono，本强化不可以擅加；早期m_j=0由既有all-n normalized定义保留，eventual趋∞用于原J证明的正n步骤。phase为固定q/h的真实Int.fract趋0，同law没有按J/n重选q。q窗口与sourceEll固定仍由旧J及其源family提供率/负层支配所需充分门，本门没有扩大到任意q或任意ell。

本轮数学/API阶段独立结论：该唯一强化可由真实公开接口完成，无新增分析假设或目前发现的statement blocker。此为声明可实现性判断，作者尚无本模块源码／proof／Audit，不预报target内核通过。下面才进行两imports的实际public/meta图、源／olean存在性、正式SHA与git/pins的机械绑定。

## 6. 最后独立公开图／缓存存在性／source与pins绑定

数学与完整hcont族匹配核完并持久化后，才独立在指定server从精确两个root imports作source图检查。未读取任何作者candidatecache／scanner／其JSON正文：本轮直接去除嵌套块注释、行注释和字符串，识别普通／public／private／meta import修饰，按实际module头判默认公开边；物理图遍历全部实际import，公开图只沿公开边，均包含public meta边。Shao／Mathlib内部继续递归；Lean／Std／其他外部模块只计独立停止叶，不把外部内部遍历混入Mathlib口径。

实际结果：物理53Shao／2973Mathlib＝3026内部节点，211外部停止叶；公开53Shao／2643Mathlib＝2696内部，加189公开外部停止叶＝2885。两种内部图逐项source及对应既有olean存在性缺0。Physical211不与public189混报；没有用普通import-only图少算meta证明依赖。关键AtomicMeasure／SummableAtoms／FiniteConstraints／RegularCovariance／NormalLayerWeakConvergence／StageLayerSeriesLimit及LevyConvergence／Portmanteau均真实公开可达，所以本拟定两个imports足以消费上述公开模型和分析接口，无需新cache、public wrapper或跨模块privatehelper。

把53个实际project源按canonical `Shao/...lean`路径键→fresh源SHA、排序紧凑JSON重算，SHA256为64b2df2d535f500ead30cf7d5d3bfd8b66016f9fd15c154e2f8254b138a031fb，与冻结scope给定口径一致。没有用作者候选JSON替代实际扫描；所有Mathlib对象仅检查存在，不重复稳定51对象hash或root成功smoke。当前root overlay未作为本工作树额外依赖来源。

本地实际scope与remote scope.md均36行／6141字节／SHA256 dd5a8aa972b0adc3aea0bb089b8e22caf0c1a71cf50f42c4555978d19fe06db8；第1节完整唯一fence确与此scope一致。被独立读到的关键source本地与指定server实际图hash逐项相同：

| 真实公开source | SHA256 |
| --- | --- |
| NormalLayerWeakConvergence.lean（88行／4406B） | 9ffb7595e90afe46ab4e207241b26bbee281e01e1f08d91dafce3aed73bc76d5 |
| StageLayerSeriesLimit.lean（327行／16484B） | 4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d |
| AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| SampleChangeOfMeasure.lean | d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134 |

公开fixedAtom_bounds实际位于SummableAtoms214–234行，对全部AtomicIndex给1≤abs和上界，并由两分支真实atom定义证明；AtomicMeasure_ae_bounds取该定理，所以上节两种hb入口均有实际公开实现。fixedAtom实际已有injective接口；第1节盲译时对重复原子的谨慎保留并非新目标可替换为允许不同任意atom映射，当前最终判断始终绑定上述唯一实际fixedAtom和stageAtom。

fresh git观察：lane仍feat/oq3-normal-layer-weak-convergence，HEAD468fcefcf6205827a9551cba39b4c5afaf959150，status干净；没有新U18b分支。两端StageSourceAsymptotic.lean均不存在，没有本模块source／Audit／probe／成功target可验收。Mathlib HEAD807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4，lake-manifest.json SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e，与接受U18a时同固定版本。

收到root v35行政main推进通知，只作为历史状态记录：冻结scope中v34描述保留，未因此改scope／源／branch、lane merge／rebase／reset或重复任何成功检查。U18a已完整proof接受／PR139不等于U18b已实现或内核检查，本门不预报Kernel／Audit PASS。

本轮只写本新报告与授权remote statement-review.md。远端实际只读进程亲和性独立输出[14,15,16,17]；无Lean／#check／probe／build／rebuild／cachewrite／spawn／commit／pub，无原始完整log下载，不触外部CPU0–9／80GiB任务、全局资源、版本或heartbeat。旧票／源／scope／receipt／shared均未改；没有读取作者implementation／future／actual-diagonal／候选或scanner笔记和JSON正文。

## 7. 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 唯一完整类型相对accepted J确仅消去原完整hcont binder并改名，全部真实模型门和整个Summable∧actualcoefficient极限结论保留。hw+真HasSum1先给同atomicMeasure真概率；公开fixedAtom／stageAtom身份与真实原子界给AE hb；hpos的inl分支给四个实际基点正质量；同μ的一般公开normalVariance_pos和parabolaCovariance_det_pos给S／det正，未新输入手工分析前提。对任意d及其全n界／最终格相容、任意同Gaussian frontier-null A，accepted U18a真实real_tendsto在a=q/4下准确产生原J所需完整hcont族，保留全n fallback和同law／同中心／同variance。再消费原J公开目标即为本完整结论；J0、早期m0、非严格递增m、零权及真Summable／tsum语义无丢失。

声明source／公开图／实际现成对象和pins绑定可用，没有发现数学、量词或静态环境阻塞；此为未实现U18b的独立声明可行性批准，不是实际proof／kernel／Audit验收。实现后仍须完整独立actualTYPE／source／proof和机械门。它拟消除原(19)固定真实阶段模型层和极限的显式hcont缺口，供原26阶段见证与原31固定律生产消费；当前仍未完成最终law diagonal／unbounded remainder、hW／generalKL／literalPhi／原24exactζ或任何根组装，根A/B/C/D全部OPEN，无最优性或新颖性声明。
