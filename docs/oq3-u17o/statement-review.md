# U17o StageSourceWitness 独立声明／来源／API审查

STATUS: CORRECT

## 1. 冻结完整TYPE独立盲译检查点

本节只读取scope62唯一Lean fence，先于本次scope叙述／R1／前置接口／机械检查；尚无O实现，0公开DEF。既有接受前置上下文不等于本目标已验真。

```lean
theorem exists_stage_source_witness
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (hcont : ∀ d : ℕ → ℝ,
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
      (∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
        d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) →
      ∀ A : Set ℝ,
        (ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance (atomicMeasure w)))) (frontier A) = 0 →
        Tendsto (fun n : ℕ =>
          (normalLayerConditionalLaw (atomicMeasure w) q (q / 4) (d n) n).real A)
          atTop (nhds ((ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (transverseVariance (atomicMeasure w)))).real A)))
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      correctedInverseScale sourceEll q (atomicMeasure w) +
        (3 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (16384 * Real.pi) ≤
          normalizedTailCoefficient sourceEll q w n ∧
      (J : ℝ) ≤ Real.sqrt (n : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J)
```

任意固定非负原子权重w，且真实HasSum w 1；任意固定J:ℕ和实数q∈(1,103/100)，假设同一atomicMeasure w的真实EY=q、EX=q/4，AE支撑在实际J阶段四基点与前J新增原子上，且每个该阶段原子真实单点质量严格正。

hcont完整保留为输入：对每一整条实序列d，只要存在全索引实界M且最终d_n+nq落在同一mesh J整数格上，则对每个Gaussian(0,actual transverseVariance)边界为零的集合A，同一actual normalLayerConditionalLaw(mu,q,q/4,d_n,n)的真实实质量趋于该Gaussian的实质量。它是条件概率连续集极限假设，不是本目标结论；没有在此声称Levy或无条件19已证。

对每个额外给定自然数下界N，结论存在自然数n，同时n≥N、n>0；同一w/q/sourceEll的实际normalizedTailCoefficient在该n至少为actual correctedInverseScale加3*h*sqrt(h)/(16384*pi)，且sqrt(n)*h*sqrt(h)至少为J。w／J／q和hcont先固定于N/n，不能为不同n重新选law或q；N可任意大，J包含0。

声明没有输入phase返回子序列、Gaussian整数和可和性或手工正差／S/D门，因此这些若为推导所需，后续必须从真实接受接口消除。需独立核3/16384的严格余量、h/pi/variance正性、时间增长、完整hcont一致性及真实原C_n；不得把它当作完整diagonal、hW或根闭合。

## 2. 真实原义务与实际接受接口的精确匹配

初始完整盲译为44行／3173字节，SHAe817c3d9facadd9da59d8fd047bca7d77792ad9f6aef554784d34293cb5d34a8；先行持久化后才读取scope全文、R1和本节真实前置。O当前仅声明门，尚无实施或内核验收。

R1 486–497明确要求有限律π_J和同q/J固定之后，利用phase任意大返回及(19)/(25)选择n_J，满足C_n≥v_corr⁻¹+(3b/2)h^(3/2)与sqrt(n)h^(3/2)≥J；以后才选未来质量。当前type额外要求超过任意给定自然下界N，是有用且可由固定律子列极限推出的加强。它未声称已构造整个未来质量序列或同一最终律。

已重新读取三个真实接受公开接口，均按同一w／μ=atomicMeasure w／q／J实例化：

- N.exists_stage_phase_return_subsequence只输入J/q，给StrictMono m与actual实fract((m_j:ℝ)*q/h)→0；没有概率／irrational门。真实StrictMono.tendsto_atTop给J所需hm。
- J.normalizedTailCoefficient_stage_subsequence_tendsto的hw／HasSum／qwindow／真实EY和EX／stageAE／stage单点正质量，与本声明全部相同；m／hm／hphase由N提供。其完整hcont binder在本声明保持逐字同式（只删m相关输入，不改hcont任何量词、d整列界、eventual格点相容、Gaussian frontier或actual cond-law）。它结论是真Summable与同一actual系数沿m趋L。
- M.stage_sourceGaussianLayerWeight_lattice_gap对任意真实概率μ而非仅手工矩阵输入；同一stage／q／均值／单点门即给真Summable和L≥correctedInverseScale+ h√h/(4096π)。先由atomicMeasure_isProbabilityMeasure w hw hs建立actual概率instance即可消费它，不需新手工S／D／hR／Summable前提。

M用(k:ℝ)*h而J用h*(k:ℝ)书写相同实际Gaussian层权；逐k乘法交换和tsum_congr给相同L，没有更换law／Gaussian方差或漏掉h/sqrt(S)因子。二者本来各自都给真正Summable，不以实tsum总化0冒充级数收敛。

已读actual normalizedTailCoefficient定义：sqrt(2*pi*n)*exp(n*saddleRate(sourceEll,q,w))*实际原律originalMeasure(sourceEll,w)的n重积sourceTail(q,n)实质量。它不是一条手工序列，也没有额外乘sqrt(S)；J真实极限恰h/sqrt(normalVariance μ)乘同一整数Gaussian层和，与R1(19)425–426一致。

actual correctedInverseScale为(ell*sqrt(normalVariance μ−(32ell/q)*det(parabolaCovariance μ)))⁻¹，sourceEll是真log(31/30)。消费的是已完整接受M/K的真实stage域：M公开proof从stageAE建立X／X²真可积、EX²=q、真实Lp2及VarX=q−q²/16、S/T正、T≤VarX，K将同一实际profile积分识别为corrected值；非把inverse／sqrt总化当作已正。当前O不重复这些证明或另加输入，也不把ell置成1/30。

## 3. 独立数学可行性与准确常数／量词

固定所有给定w/J/q及hcont，设h=dyadicMesh J=((2:ℝ)^J)⁻¹>0，a=h*sqrt(h)>0；J0时h1、a1。真实π>0，令η=a/(16384*pi)>0，Bcorr=correctedInverseScale sourceEll q μ。全部是固定同一阶段实常数，不依赖后续n／子列索引。

M给L≥Bcorr+a/(4096*pi)=Bcorr+4η，目标阈值T=Bcorr+3a/(16384*pi)=Bcorr+3η。因此T<L严格成立，至少留下η>0；无需M不等式本身严格，也不要求Bcorr先为正才可作这个加法比较。b=1/(8192*pi)时M余量正好2b*a，本目标余量正好(3b/2)*a，和原(26)准确一致，未把4与3因子或π归一化混掉。

取N的真实子列m；由其StrictMono给hm:m→∞，用同一hcont消费J，得到C(m_j)→L。因T<L，真实实数序拓扑极限给最终T<C(m_j)，继而最终T≤C(m_j)。不是由“极限≥T”直接推项最终≥T，也没有把limsup／某条换law数组替代固定actual序列。hcont未证明但确为允许的完整输入，不能标记无条件19完成。

对任意给定自然下界N，同时需n≥N、n>0和增长。a>0且J≥0，r=(J:ℝ)/a≥0。实际Archimedean API先选自然数B使r²≤(B:ℝ)。由m→∞，分别最终m_j≥N、m_j≥1、m_j≥B；与上面系数事件取有限交，仍为Nat atTop最终事件。atTop ℕ真正NeBot，Filter.Eventually.exists给某个索引j，取同一个n=m_j，不能用两个不同n各满足一半合取。

此时n≥B给r²≤n，n非负，真实Real.le_sqrt的两个非负门给r≤sqrt(n)；a>0后清除r=J/a的分母，得到J≤sqrt(n)*a=sqrt(n)*h*sqrt(h)。n≥1另给n>0。这个构造不需要预先缓存sqrt→∞的额外定理；只用真实平方根／Archimedean／eventually有限交API。没有除J、q、sourceEll或n；J0、N0不破坏任何步骤。

结论n可依赖整个给定stage数据、hcont和N；type不要求跨所有w的共同样本阈值。整个子列和极限始终固定同一q/J/w，N在n外且可任意大。没有把未来r/J/n下重择q／有限law当成见证；也没有在此宣称对所有合法prefix已经生产hcont或hW。将来接真实prefix家族和选未来mass仍有明确剩余义务。

## 4. 固定库主API的真实类型／实现门（先于机械）

以下实际server源码已只读核，未运行Lean／#check／probe，也没有从作者路线或扫描器取证明。

| 固定库实际文件／行 | 对应真实门 |
| --- | --- |
| Order/Filter/AtTopBot/Tendsto84–85 | StrictMono.tendsto_atTop对ℕ→ℕ由id_le与tendsto_id给真正任意大样本时间 |
| Topology/Order/Basic139–141 | tendsto_order：若a'<L则最终a'<f；证明展开order邻域，无额外可测或可积前提 |
| Topology/Order/OrderClosed227–234 | eventually_gt_nhds／eventually_ge_nhds从严格低于极限的阈值给邻域事件；不可只输入非严格≤ |
| Algebra/Order/Archimedean/Defs67–69 | exists_nat_ge(x:ℝ)给自然B且x≤B，实际由Archimedean.arch构造 |
| Order/Filter/AtTopBot/Defs58–63、Tendsto39–41 | 真eventually_ge_atTop及Tendsto.eventually_ge_atTop，把任意N／1／B的固定自然下界送回同一子列索引滤子 |
| Order/Filter/Basic814–816 | Eventually.exists必须NeBot；Nat atTop有真实NeBot，有限交的最终事件故确有索引，非空滤子假门不可略 |
| Analysis/Real/Sqrt143–149,177–180,239–240,285–288 | sqrt非负、非负输入时sqrt²真还原、le_sqrt需左右真实非负；sqrt正由h>0，J/a≥0且n≥0后才用le_sqrt |
| Analysis/SpecialFunctions/Trigonometric/Basic158–159 | Real.pi_pos由two_le_pi得到；不依赖缺cache的额外π数值Bounds模块 |
| AtomicMeasure39–42 | atomicMeasure_isProbabilityMeasure消费hw和真正HasSum1，不将仅tsum总化1或任意signed weights当概率 |

MeasureTheory／Filter名字空间、Topology／BigOperators scoped记法与真实两个拟imports一致。全部hcont中的Measure、Gaussian、frontier、真实map/cond-law与积分记法来自已接受真实前置；本O不新造定义、instance或替代的conditional law。未来实现须显式建立probability instance、逐式匹配L乘法次序与hcont，不能省略真Summable和strict margin。

## 5. 数学／API阶段持久化后，最后独立环境与机械绑定

第1–4节先持久化为94行／10124字节，SHA932dd739bd4186aa6bc8e216e131880c7631200886fd402951922571eea17f10；随后才读git／pins／源hash并重建实际public/meta图。此时仍无O source／receipt／target或Audit可验收；不把前置N成功算作O成功，不运行Lean／探针。

### 5.1 实际字节、git与scope

11:35:59 UTC只读观察server branch feat/oq3-stage-source-witness，HEAD91b79f92b118abc96b31ffb98c651a905d983d77（已接受N／PR130发布head），git status干净。local drafts/oq3/StageSourceWitness.lean与server worktree Shao/OQ3/StageSourceWitness.lean均不存在。本票只审scope62固定完整type，不实施或编译。N正常发布／分支延续不构成旧源漂移。

| 实际对象，两端独立读取 | 字节／行 | SHA256 |
| --- | --- | --- |
| scope62 local／remote run同 | 5421／46 | 00fd334b7acd0761416aab2e69d380dc1cb0f57869dca3eac3ee05b9959bb4f9 |
| accepted N actual source local／worktree同 | 7782／168 | 0e77e8459f8351213c1842535aedee731f0bbd641414a0192d9fd76d3338511c |
| accepted J actual source local／worktree同 | 16484／327 | 4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d |
| accepted M actual source local／worktree同 | 33728／685 | d211fa4e676fbb76e81ff59008fb654c6b4fdc51c78a1bccd7adf4b1f5b419bd |
| N完整接受终票local／run同，旧字节未改 | 24857／214 | af66b8d356300ed83253533fb51b67d159dc3fea6a51356e5dccb436fbbdeb5d |
| R1真实原件 | 19420／575 | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |

已对O完整hcont binder与实际J公开type逐字比较，完整字符串相同，白空格规范也相同。没有只核短名hcont或删掉d量词、全n界、eventual相容门、frontier零及actual law。第1节完整fence来自冻结scope62，最终保留原字节与量词。

实际lean-toolchain29字节／1行，为leanprover/lean4:v4.36.0-rc1，SHAd581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4。lake-manifest3541字节／117行，SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。Mathlib实际gitHEAD807d3836b165983210ee2ecf3cd28f239436949c。只读pins，不作版本或API探针。

### 5.2 58实际项目前置与两种map键口径

以已接受N的57项源hash map加N自身为冻结对照，再独立逐文件读取worktree全部58 source字节，mismatch0；实际import图的Shao集合也恰为这58项，不只抽查三个直接consumer。旧N receipt仅在机械末阶段读取其已接受source字典，fresh字节SHAb70635642b722833d41dda45eb264ee2ffae4a574acb7bab176465e93c1188a1；没有读取作者candidatecache／扫描器／meta supplement正文。

独立以相同58项真实值转换两种键，并作sort_keys=True、separators=(',',':')的UTF-8 compact JSON哈希：

| 明确键口径 | 真实compact SHA256 |
| --- | --- |
| 模块名，例如Shao.OQ3.StagePhaseReturns | 398c7db25ca11c640e2f69de299f6f3c4e63b145bc476934bfdab14e04be5784 |
| 相对源路径，例如Shao/OQ3/StagePhaseReturns.lean | 421ed32b76248ae644fb5cf8c06210cfaf288f7e11db3dddb09c3da4a4ee49ba |

前者准确复现冻结scope62的398c7db…，后者遵循旧N receipt／本review既有相对路径键口径；旧57项相对路径map仍fresh复现a707cb2a5cd3d5fa94ab8847b548e4838725922efb708a773280cec695edeef7。差别完全来自键字符串，不是source字节／集合漂移、缺前置或未解决的hash异常。scope／旧票均保持原字节；本核验不需要作者扫描器／JSON正文，也不触发Lean或任何cache写。

### 5.3 实际普通／meta图、公开API和现成cache

拟imports精确StagePhaseReturns与StageLayerSeriesLimit。独立静态lexer剥注释／字符串，识别public/meta组合；new-module只沿真实public边构造公开图，legacy按其实际公开导入语义。下表不包含尚不存在的O自身，Lean／Std／其他package只作为停止展开的外部叶，不冒称继续递归它们全部内部依赖。

| 图口径 | 物理Shao | 物理Mathlib | public Shao/Mathlib | 外部停止叶 | public总数 | source／olean缺项 |
| --- | --- | --- | --- | --- | --- | --- |
| 普通import／public import | 58 | 2905 | 2681 | 84 | 2765 | 0／0 |
| 纳入meta import／public meta import | 58 | 2920 | 2696 | 189 | 2885 | 0／0 |

全部58实际项目源和Mathlib依赖源／现成olean逐项存在；Shao集合与上节真实58项map完全一致。M/J/N、AtomicMeasure、SampleChangeOfMeasure、CorrectedScaleContinuity及第4节每个Mathlib主API模块，在更小普通公开图中已经可达；meta图亦全部可达。没有缺public import／scope实例或必要cached API修复，额外15个meta模块均现成。未因计数或键口径变化编译，未改旧scope或引入新依赖。

本次实际读取的主API源SHA256如下，供固定版本核对：

- AtomicMeasure 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39；SampleChangeOfMeasure d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134；CorrectedScaleContinuity b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8。
- AtTopBot.Tendsto 0ec2f390f3a7c9648018b095b58735895d75f7895635ffaedd02baa5e6db5301；Topology.Order.Basic 3602a21a0c9138a3256249ea1cfd2279e6bfd0459272a6f03e0c52d8326aa82f；Topology.Order.OrderClosed 011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e。
- Archimedean.Defs 792d8e81ef492132ffe4cbd31ad9cfa0cf4d2a215b47acb86f1240bba0a6525c；Filter.Basic cdea496b0efbaea8c02084160bad6af60ab6510f3ef5141528f745cafb5dcff2；AtTopBot.Defs ae4f46b0aea83d55ab297b94a127bb09c105bf6319204ef78c9d9c05e38535fe。
- Analysis.Real.Sqrt 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204；Trigonometric.Basic 85fc5b104bd61801d259dda6cf837892c30bc4b44a1b23688398476941770cf7。

scope指定namespace Shao.OQ3，open MeasureTheory Filter，open scoped Topology BigOperators，noncomputable section及双end，与实际前置中的notation／实例环境相容。本声明无新public DEF，没有需另外实现的MeasureSpace／Matrix norm／Gaussian定义或实例选择。无需sqrt导数、π数值Bounds、Levy／Portmanteau或新KL cache；hcont作为显式输入没有被绕过。

所有server项目命令taskset -c 14-17，仅静态只读；未Lean／#check／probe／重编／写cache／spawn／commit／pub／下载完整rawlog。未使用ulimit-v，未改版本／heartbeat／全局资源或CPU0–9外部80GiB任务。作者所有actual-diagonal／phase-return／cusp／implementation／future／candidatecache／扫描器与JSON正文未读。旧已接受源／scope／review／receipt和他人改动全部保留。

## 6. 最终声明／来源／API裁决

STATUS: CORRECT

JUSTIFICATION: 本完整type只保留原stage真实概率／均值／支撑／单点门及实际尚待生产的完整hcont，不另输入phase、Gaussian和Summable或手工S/D/gap。N给同q/J真实严格时间子列，J在同一actual law／hcont下给actual C_n子列极限，M在同一μ与真实stage门下给比目标多η=a/(16384π)>0的充分gap。严格余量确保真实项最终超过目标，m→∞同时满足N／1／平方增长阈值，再在同一eventual索引处取同一个n。全部正分母、平方根非负域、真实可和性和完整hcont匹配都已明确；实际public/meta图、58项字节、现成cache与pins一致，元数据两种键口径已独立复现。没有数学／来源／量词／常数／环境必要修复。

原target→消除义务→直接consumer：本O拟消除R1(26)在固定finite law／q/J后选择任意大真实样本且同时满足实际系数余量与sqrt增长的义务，使用显式而未生产的hcont；直接供后续合法finiteprefix的hW见证、先固定样本后压小未来质量的原transfer／diagonal步骤。相较手工极限／gap参数包装，本type确实通过M/J/N消除这些手工输入，保留的阶段数据是实际有限模型本身；因此原型有直接承重用途。

这仍只是声明／来源／静态API可行性CORRECT，准许按冻结type和两个imports实施，不是O完整proof／内核／公理门的提前接受。未来proof须实际建立atomic概率instance、将M和J的L经乘法交换完整识别，严格比较3/16384与1/4096的余量，合并同一索引的所有eventual事件，并在真实sqrt域上给同一个n的四项合取；lead需全文读取本final后才实施。

明确仍OPEN：实际hcont与无条件15/19、所有合法positivepast的真实hW、prefix与最终单律diagonal、generalKL／global minimizer、literalPhi、原24精确ζ及所有root A/B/C/D。O不生产共同p/q/eps/P；在未来消费时仍须这些参数先于未来r/J/n固定。它不称最弱假设／最优常数／新颖性，也不把本次条件原26见证可行性记成整个根闭合。

本票唯一写入新local报告及授权remote副本，初44行盲译内容保留、仅最终更新行政STATUS；全部冻结scope字节、旧源／旧票／receipt及共享cache未改。
