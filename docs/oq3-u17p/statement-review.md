# U17p FinitePrefixLaw 独立声明／来源／API审查

STATUS: CORRECT

## 1. 冻结三段Lean完整定义／TYPE独立盲译

本节只读scope63的三个Lean fence，先于scope叙述／R1／实际前置及机械；P尚未实现。既有上下文不视为本声明数学或环境通过。

```lean
def prefixMass (ell : ℝ) (p : Fin 4 → ℝ) (J : ℕ) (u : Fin J → ℝ) : AtomicIndex → ℝ :=
  finiteMass ell p (fun j => if hj : j < J then u ⟨j, hj⟩ else 0) J
```

```lean
theorem finiteMass_eq_prefixMass (ell : ℝ) (p : Fin 4 → ℝ) (J : ℕ)
    (u : Fin J → ℝ) (r : ℕ → ℝ) (hpref : ∀ i : Fin J, r i.val = u i) :
    finiteMass ell p r J = prefixMass ell p J u
```

```lean
theorem exists_source_prefix_radius (p : Fin 4 → ℝ) (q : ℝ)
    (hp : ∀ i, 0 < p i)
    (hc : (constraintMatrix sourceEll) *ᵥ p = constraintTarget q) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ (J : ℕ) (u : Fin J → ℝ),
      (∀ i, 0 < u i) → (∑ i, u i) < eps →
      (∀ i : AtomicIndex, 0 ≤ prefixMass sourceEll p J u i) ∧
      HasSum (prefixMass sourceEll p J u) 1 ∧
      (∫ x : ℝ, normalValue x ∂atomicMeasure (prefixMass sourceEll p J u)) = q ∧
      (∫ x : ℝ, x ∂atomicMeasure (prefixMass sourceEll p J u)) = q / 4 ∧
      (∀ᵐ x ∂atomicMeasure (prefixMass sourceEll p J u),
        x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
          stageAtom (fun j : Fin J => addedAtom j.val) i)) ∧
      (∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure (prefixMass sourceEll p J u)).real
        {stageAtom (fun j : Fin J => addedAtom j.val) i})
```

prefixMass(ell,p,J,u)是AtomicIndex上的真实权重函数：把有限前缀u零延拓为自然数序列（j<J时取u_j，其余0），再取同一个ell/p/J的实际finiteMass。它并非新手工测度或另一个索引类型。

第一目标全称任意ell/p/J/u/r，不要求r非负、可和或q约束；只要整条r在前J个索引与u相同，则两个AtomicIndex→ℝ权重函数完全相等。这要求真实finiteMass连同修正基点仅依赖有限前缀，不能只证新增原子相等或仅AE测度相等。

第二目标固定任意p:Fin4→ℝ与任意实q，在p各项严格正和同一sourceEll矩阵约束M*p=constraintTarget q下，先存在共同实eps>0，再对所有J及所有逐项正有限前缀u，若其有限和<eps，则同一个prefixMass具有逐点非负、真正HasSum1、实际EY=q、EX=q/4、同阶段AE支撑和每个该阶段原子真实正单点质量。eps不能依赖随后J/u；J0包含空前缀且正性条件空称。

没有输入basepositive／概率／可和性／均值／S/D／hcont或矩阵可逆作为额外假设，也没有要求q位于O的特定窗口；若实现需要这些充分门，须由sourceEll固定矩阵、hp/hc和公开半径实际推得。此声明不生产hcont、forallprefix hW、最终diagonal或根闭合，未来消费O仍需其完整hcont与qwindow。

## 2. 来源、真实定义与前缀身份的独立核验

初盲译43行／2933字节，SHA4194a3e9f3627decd3e45895388982c6a4091bd0cb44adedea90513f2cc69016，已先于scope叙述／R1／实际API持久化。当前仅声明门，无P实现／编译／Audit的提前接受。

R1 113–145先给新增点与正质量，再用固定矩阵逆补偿四基点，得到真实finite lawπ_J；486–550要求有限阶段与样本见证先于未来质量选择。本定义将尚未选未来的有限前缀直接变为同一AtomicIndex权重函数，第一目标将它与任何同prefix未来延拓的finiteMass精确识别，因此是先prefix→law→见证→future的实际桥，不是另造手工满足模型门的w。

已读取实际FiniteConstraints／SummableAtoms／FiniteStageMeasure的定义：AtomicIndex=Fin4⊕ℕ；finiteMass=Sum.elim(finiteBase ell p r J)(fun j=>if j<J then rj else0)；finiteBase是compensatedBase ell p (addedAtom|FinJ)(r|FinJ)；compensatedBase=p−M⁻¹*addedMoment，后者是Fin J上的真实有限sum。第一目标因而不需要r可和、非负、q或M可逆：四基点补偿也只读r的前J值，未来无限tail完全不读。

令r0(j)=if hj:j<J then u⟨j,hj⟩ else0。对每个i:Fin J，r0(i.val)=u i（Fin同值proof irrelevance）；hpref给r(i.val)=u i，因此两个受限函数Fin J→ℝ相等。由finiteBase／compensatedBase的真实函数参数相等，所有基点权重相等；对Sum.inr j，若j<J则用hpref⟨j,hj⟩，若j≥J则finiteMass两侧直接为0。funext与Sum两分支即给整个AtomicIndex→ℝ函数相等，不只是added部分或AE measure相等。

这个证明使用公开定义及基础函数外延／Fin.ext／dependent-if简化，不调用其他module private helper（包括任何已有私有prefix congruence）。即使任意ell下矩阵逆采用总化语义，两个相同有限输入仍有同样输出；此纯代数身份不被提升成奇异矩阵的概率构造。

原文新增j从1起，而actual addedAtom k使用h_(k+1)，Fin J包含k=0,...,J−1，正对应源j=1,...,J；J0仅四基点，没有错把j≤J和j<J多取一项。canonical零延拓保留所有未来原子质量0，不把它们当成正质量，也不先选最终r。

## 3. 统一eps在所有J/u外的真实模型生产

### 3.1 真零延拓可和与公开半径

关键公开API实际为FiniteStageMeasure.exists_uniform_finite_radius63–76：任意ell≥0、任意逐点正p，先给eps>0，再对所有非负、Summable且真实tsum<eps的r给所有J／基点finiteBase>0。它要求r非负，不要求整条r严格正；故合法应用于本canonical零延拓。不能误用只接收∀j,rj>0的无限family结论。

取ell=sourceEll，公开sourceEll_pos给ell≥0；hp给p正。由该公开定理先固定eps，它仅依赖ell/p，特别在随后所有J/u之前。之后对任意给定严格正u，r0活跃项u_j>0、其余0，故逐点非负。它在Finset.range J之外严格为0；真实finite-support HasSum API给HasSum r0(∑j∈rangeJ r0j)，Fin有限和／range恒等式把右侧准确识别为∑i:FinJ,u i。因此Summable r0且tsum r0=∑u<eps，不是使用默认tsum0来满足半径门。

公开radius因此给当前J所有four-base的严格正性（实际上给所有stage的基点正性，更强但不必使用）；finiteMass_nonneg再用其非负弱化与r0非负生产完整AtomicIndex逐点非负。没有从外部手工输入basepositive／probability／Summable，亦不需要将eps依赖u/J或已经选择的最终未来r。

### 3.2 真矩阵约束、HasSum1与实际可积均值

公开source_constraintMatrix_nonsingular132–133给固定M(sourceEll).det≠0，由实际显式负det结论而来；当前consumer不调用其内部private source_matrix4。源sourceEll=log(31/30)和非奇异性固定，独立于p/q/J/u。

对同sourceEll/p/r0/J，用公开finiteMass_constraints21–61消费hM和原hc，给每一k:Fin4的真HasSum(weight*constraintFeature_k)=constraintTarget_k。其实际proof先M*M⁻¹有限线性等式，再真实finite-support HasSum、Fin4有限sum与HasSum.sum，不假设无限r的收敛，也不依赖qwindow。取k0，由constraintFeature_0=1、constraintTarget_0=1得到真正HasSum该prefixMass 1；结合非负可消费atomicMeasure_isProbabilityMeasure建立真概率。

公开AtomicMeasure.atomicMeasure_mean96–109从同一全套HasSum约束和权重非负，先用k3−k1除4建立weighted X的真HasSum，再通过atomicMeasure_integral_of_hasSum建立真实Integrable X及EX=q/4。boundaryFeature真实是x²−4x，不能反号。此API不要求预给均值或概率instance，概率随后由HasSum1得到。

公开PositiveRate.atomicMeasure_normalValue31–55也只消费非负和该完整约束；其proof从HasSum0建立实际概率，连续有界原子上先证Integrable Y，从约束先证boundaryFeature和X²真可积，再用Y=X²−2*boundaryFeature积分线性得EY=q。等价代数8EX−EX²=q，整个过程中真可积先于积分线性，不以Bochner不可积总化0充当均值。

因此第二目标不需要qwindow作为前提。若给定p>0与真实hc，矩阵约束已直接控制真实mass／second moment／boundary moment；不把任意q当作独立概率存在性结论。未来消费O仍须从共同source starter家族保留1<q<1.03，P没有生产或修改该窗口。

### 3.3 实际stage AE支撑与每个活跃原子的严格质量

公开atomicMeasure_finiteMass_ae_range90–107对任意ell/p/r/J均成立：四基点Dirac在stage range，j<J的新增Dirac也在，j≥J权重0的分支真实消失。它不需要future r严格正或手工stage支撑输入。将r0代入并展开prefixMass，正好得到冻结AE目标的同stageAtom／Fin4⊕FinJ范围。

严格单点目标不能套用要求整条r>0的finite_original_atom_pos等接口。应直接消费公开atomicMeasure_real_singleton34–37：权重非负时真实real{fixedAtom i}=该权重。该定理先用fixedAtom_injective处理各原子无碰撞，再在有限ofReal上toReal；未将ENNReal top误当有限质量。

对于stage Sum.inl i，其点是fixedAtom(Sum.inl i)，权重为radius给的finiteBase>0；对于Sum.inr j:Fin J，其点是fixedAtom(Sum.inr j.val)，finiteMass中if j.val<J真、r0该项=u j>0。两分支恰给冻结真实单点正质量。j≥J的无限索引并非stage目标，仍为0，不会误称全无限索引正质量或U5a全w>0。

已读公开fixedAtom_injective194–212的实现：baseAtom不同，addedAtom不同且严格介于4与极限基点之间，交叉无碰撞，故上述单点身份确为actual独立原子，不暗加no-duplicate假设。非负权重＋HasSum1还保证真实概率／有限measure门；P的statement不必重复输出probability字段，后续公开API已可直接取得。

### 3.4 J0、量词与实际承重用途

J0时u:Fin0→ℝ，严格正条件为空称、有限和0<eps，r0恒0；addedMoment空sum0、finiteBase=p，所以同一矩阵hc给四基点的真实概率与均值，四点正性由hp保留。没有调用只对J>0成立的finite-prefix bijection、除J或丢失零阶段。

eps固定先于所有J/u，而canonical law完全由当前prefix决定。后续P的输出正好给已接受O所需hw／HasSum／EY／EX／hrange／hpos；O仍另要固定qwindow和该同一prefixMass的完整hcont。第一目标又把未来同prefix的真实finiteMass与当前model精确识别，未来transfer不能偷偷换law。因此这是消除手工模型前提的实际producer，不是无直接消费者的包装。

P不生产hcont或对所有prefix的实际hW，更没有先选最终r来证明当前前缀合法；未来hW与AdaptiveTailBudget／SourceTransferBudgets的“先chooseN再未来r”对接仍OPEN。同一p/q/eps先于未来J/u/n，不在未来重选q或law。

## 4. 实际固定库／公开API门（先于机械）

已经读取公开radius及其底层exists_compensation_radius102–161实现：取m=min p_i>0、A=M⁻¹、S=∑i,k|A_ik|≥0和B=(4+sqrt10)²≥0，eps=m/(1+B*S)>0；以真实有限sum abs估计和∑u<eps确保修正量绝对值<p_i。这里S/B只固定依赖ell，未依赖J/u。FiniteStageMeasure.radius用addedAtom_feature_bound和非负Summable的部分和≤tsum完成共同半径，没有调用私有半径或未来mass构造。

所需标准无限和API在Mathlib/Topology/Algebra/InfiniteSum/Defs294–300，以to_additive生成hasSum_sum_of_ne_finset_zero：function在有限集合外为0才HasSum其有限sum；实现由有限subtype的HasSum和support包含、默认unconditional滤子得到，不是无条件tsum公理。Mathlib/Data/Fintype/BigOperators224–231以to_additive生成Fin.sum_univ_eq_sum_range，经Fin等价range subtype和attach计算；其234–237的Finset.sum_fin_eq_sum_range给有限u与dependent-if零延拓的准确range和。均为真实现成API，未来P不用新cache或Lean探针来猜接口。

Matrix／Topology／BigOperators scoped记法与MeasureTheory／Filter名字空间匹配冻结语法；第一身份可仅用公开defs＋funext／Sum cases／Fin.ext／dependent-if简化，第二身份使用sourceEll_pos与source_constraintMatrix_nonsingular公开theorem。PositiveRate当前import使atomicMeasure_normalValue公开可达，而不是读取某个private积分helper；未调用SourceTransferBudgets proof内的隐藏radius或其他module私有congruence。

## 5. 数学与实际API阶段后，最后环境／源码机械门

第1–4节先持久化105行／12280字节，SHA67244063e73d8c09866b2c93de8eeaeda39087f9fe254a829f702397f5f68263；之后才独立读取scope／git／pins／实际闭包源hash与cache。仅检查现成文件，不Lean／#check／probe／重编。当前没有P source、receipt或Audit，本票不提前验收其实现。

### 5.1 冻结字节与实际工作树

scope63 local sixty-third-unit-scope.md与remote run/u17p-20261021/scope.md实际同5913字节／47行、SHA78df74d7b8040e0eb05966e97f01116a84771e9a5afa7acaf3afd179ff4a6541。三个Lean fence完整DEF body／两个TYPE保留冻结字节；定义和targets不混计。R1真实原件19420字节／575行、SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。

12:19:39 UTC实际server branch feat/oq3-finite-prefix-law，HEAD7f27bc0a58ec3516f7c490e2054b5031ff1c38b7（O／PR131接受后正常发布head），git status干净。local drafts/oq3/FinitePrefixLaw.lean与server worktree同名源均不存在。旧O完整接受报告local／run同22826字节／210行、SHA5e57d920b3e982cf225ac26a5a53c2b11bb1fc84748ce0bed97013e1d47a83d5；没有改／重查其旧成功proof或build。

实际lean-toolchain29字节／1行、leanprover/lean4:v4.36.0-rc1，SHAd581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4；lake-manifest3541字节／117行、SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。Mathlib实际HEAD807d3836b165983210ee2ecf3cd28f239436949c，tracked status干净；没有版本探针、pin或heartbeat更改。

### 5.2 全部7项实际项目前置

local／server各独立读取下列完整7源字节及hash；实际图集合正好这7项，且逐项值均为已接受O的58项前置子集。旧O receipt只在最后机械阶段读其source字典，SHA仍d094a5a3b7af875019e629a639f2f6e1c9b598436784bbddf4cd36617aeef01f；不是作者candidatecache。未以旧receipt取代实际重新计算。

| 相对真实源路径 | 字节／行 | SHA256 |
| --- | --- | --- |
| Shao/OQ3/FiniteConstraints.lean | 9679／241 | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/SourceStarter.lean | 13859／337 | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 10641／237 | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| Shao/OQ3/AtomicMeasure.lean | 6619／139 | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| Shao/OQ3/InverseTilt.lean | 8423／174 | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| Shao/OQ3/FiniteStageMeasure.lean | 9520／191 | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| Shao/OQ3/PositiveRate.lean | 9294／189 | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |

对上述“相对Shao/...lean路径→SHA”map，UTF-8、sort_keys=True、separators=(',',':')的canonical compactSHA4219e7cb2734f96de45a8029c06bc5a7cb443c5db41d75699e6c135821f5115b，准确复现冻结scope63口径；P自身尚不存在，不计入7项。没有模块名键／路径键不明的hash差异。

### 5.3 独立公开图及所有现成source／olean

拟imports恰FiniteStageMeasure、PositiveRate，未额外导入O或私有helper所在module。独立静态lexer剥注释／字符串，识别public／meta组合，按实际new-module／legacy规则重建下表；未读作者candidatecache／扫描器／其JSON正文。外部Lean／Std／其他package只作为停止展开叶，不声称递归遍历内部。

| 图口径，P自身不计 | 物理Shao | 物理Mathlib | public Shao/Mathlib | 外部停止叶 | public合计 | source／olean缺项 |
| --- | --- | --- | --- | --- | --- | --- |
| 普通import／public import | 7 | 2369 | 2331 | 84 | 2415 | 0／0 |
| 含meta import／public meta import | 7 | 2384 | 2346 | 189 | 2535 | 0／0 |

全部实际源／既有olean逐项存在；7Shao集合与完整map相同。第2–4节所用FiniteStageMeasure／PositiveRate／SourceStarter／FiniteConstraints／SummableAtoms／AtomicMeasure公开模块，以及Mathlib.Topology.Algebra.InfiniteSum.Defs、Mathlib.Data.Fintype.BigOperators，均在更小普通公开图可达；meta图亦可达，无缺项／必要import修复。Pconsumer O在本闭包外，仅作未来语义对接，不被误计成第8项依赖。

两个实际固定库主文件SHA：InfiniteSum.Defs为1213ea126c48b375a75023efffdd982a1f837ee2a7bf6cdd6ea4c736365ffd40；Data.Fintype.BigOperators为d0201051dfa54e8b67710ff484c34dc57e75da0e0bced663d798f6df333da638。已读to_additive源证明及完整range转换最后dependent-if分支，未用不存在的手猜API或私有定理。所需概率／实际积分API在对应已接受实际生产源里完整读取，真可积门已在数学节核清。

不需要缺失的Levy／Portmanteau／新KL或其他公共cache；本P无hcont目标，未绕过hcont。所有server项目命令taskset -c 14-17只读，无Lean／#check／probe／重编／cache写／spawn／commit／pub或完整rawlog下载，无ulimit-v／全局资源或外部CPU0–9／80GiB干预。作者prefix-law-next-notes、actual-diagonal、Oimplementation、phase／cusp／future／candidatecache／扫描器与其JSON正文未读；源／旧票／scope／receipt和他人改动未修改。

## 6. 最终声明／来源／API裁决

STATUS: CORRECT

JUSTIFICATION: canonical prefixMass完整body是真实finiteMass在同AtomicIndex上取prefix零延拓；实际finiteBase与所有新增权重仅依赖该prefix，故第一个全称函数身份无需任何可和／正性／逆矩阵假设。第二目标能用公开exists_uniform_finite_radius处理真正非负、有限支持可和的r0，eps先于所有J/u；sourceEll公开非奇异矩阵与原hc给真HasSum约束，实际概率／积分API在真可积后给EY／EX，公开AE和singleton API给同stage真实支持及仅活跃原子的严格正质量。J0、未来零质量和q任意条件式全保留，没有私有API或手工模型假设缺口。全部7实际源、public/meta可达、现成cache和pins一致，无数学／来源／量词／环境必要修复。

原target→拟消除义务→直接consumer：原R1有限律补偿与先prefix后见证的顺序，将由P实际生产每个小正prefix的真实模型门，并用精确prefix身份在未来延拓中保持同一finite law；这正好是已接受O原26见证的实际输入producer。不是预设最终r来给prefix建模，也不是输入一个手工满足门的w。结合未来同prefixMass的真实hcont和固定source starter qwindow，才能进一步生产所有合法prefix的hW，再接预算与单律transfer。

当前CORRECT只是冻结完整DEF／两个TYPE的独立声明／来源／静态API可行性，准许在这两个imports下实施，不是P actual proof／generated／内核／公理门的提前通过。未来实现必须真实构造r0 HasSum和有限sum等式，在正半径下建立basepositive，真调用公开sourceM nonsingular及积分API，分别核活跃singleton，并完整证明第一目标的base与added函数两分支；lead须全文读本final才实施。

仍OPEN：真实hcont／条件Levy与无条件15/19、forallprefix实际hW、最终固定单律diagonal、generalKL／global minimizer、literalPhi、原24 exactζ与全部root A/B/C/D。P不生产共同p/q，未来由固定starter及统一eps与原transfer家族对接；不声称最弱／最优／新颖性或任何根闭合。

本票唯一写新local报告及授权remote副本，初43行独立盲译内容保留（最终仅更新行政STATUS）；冻结scope、旧source／report／receipt／shared／cache均原样。
