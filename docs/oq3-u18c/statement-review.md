# U18c SourceFixedLawRemainder 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 1. 唯一完整类型先行盲译

本阶段先仅提取scope67唯一Lean fence；未读取scope说明、作者路线或本轮元数据。零公开定义，唯一无前提存在目标。已有条件式Q/R及U18a/b审查背景不能代替本次无条件强化的可行性证明。

```lean
theorem exists_source_fixed_law_unbounded_scaled_remainder :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
      (∀ i : AtomicIndex, 0 < limitingMass sourceEll p r i) ∧
      (∀ k : Fin 4,
        HasSum (fun i => limitingMass sourceEll p r i * constraintFeature sourceEll (fixedAtom i) k)
          (constraintTarget q k)) ∧
      IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
      (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (∫ x : ℝ, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
      ∀ (K : ℝ) (N : ℕ), ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
        K < Real.sqrt (n : ℝ) *
          (normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r) n -
            correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)))
```

完整量词：无外部假设，存在一个四维实基点质量函数p、一个实q和一个实eps，首先无条件交付每个p_i严格正、1<q<103/100、eps>0以及同一sourceEll的真实矩阵约束 M*p=constraintTarget q。这里hp／q窗口／eps／矩阵约束均为合取承诺，不是某个可由坏参数真空满足的蕴含前件。

在上述p/q/eps固定后，存在单一全序列r:ℕ→ℝ，使全部r_j严格正、真正Summable且实tsum总mass严格小于eps；同一limitingMass sourceEll p r在所有AtomicIndex严格正。对每个Fin4约束坐标k，真实HasSum的是 i↦limitingMass_i*constraintFeature(sourceEll,fixedAtom i,k)，目标和为constraintTarget q k；不是仅tsum等式，也没有误把constraintFeature的实原子参数与坐标位置颠倒。

同一最终r进一步给出原律originalMeasure(sourceEll,limitingMass)的真实概率性质，以及id真Integrable和真实均值0。然后在这个同一p/q/eps/r和原法则已经固定之后，对任意实K和自然数N，存在自然数n，满足n≥N且n>0，并使 K<√n*(actual normalizedTailCoefficient(sourceEll,q,limitingMass,n)−correctedInverseScale(sourceEll,q,atomicMeasure(limitingMass)))。

因此结论是同一实际原法则的带正号缩放余项在任意晚时间仍可任意大；不允许按K/N重选r/q/law，不输入手工hcont／hW／阶段gap或数列极限。K可负、N可0，但交付的n始终正。correctedInverseScale必须最终按同一真实atomicMeasure解释，不能用另一个有限阶段的连续常数代替最终法则；其定义的正域与实际证明门仍待后续核。类型本身没有声称n严格单调、全n发散、绝对值余项或概率Law可随阈值重择。

本阶段仅记录实际冻结目标的量词和原子／概率／HasSum语义；无条件有限见证、共同半径先后次序、对角构造与增长常数是否可实现尚未判断，不能把旧条件式存在定理直接当作本目标的证明。

## 2. 真实来源、完整公开目标与无条件强化边界

首读盲译先行持久化为36行／3465字节／SHA25664f548c19baa202b2aff2e081a691273e4c04ef9917b073a894e12b8572bdb33；此后仅追加。随后读完整38行scope和R1第486–550行真实原文；没有读取任何作者future／actual-diagonal／implementation／candidate笔记或scanner JSON。

R1(26)先为每个固定finite阶段选任意晚n_J，同时要真实finite系数高出连续常数及√n_J*h_J^(3/2)≥J。497–537行明确“先选n_J，后选未来mass”，以(27)实际换测度、(28)/(29)有限产品与tail控制及(30)连续常数误差，把这两项同时转到同一个final law。539–550行才由最终正差与增长得到(31)，排除O(n^(-1/2))。本目标∀K/N给同一个finalr的任意晚正号缩放余项任意大，正是这一逻辑，不是重新选一列法则或只称旧条件式定理可用。

公开类型中p/q/eps的合法性是无条件合取，再∃r，r的正性／真Summable／严格总mass／完整feature HasSum／真实原律概率和可积均值0都在∀K/N外。这里没有Q v1曾出现的合取进入蕴含前件的真空漏洞，也没有错误constraintFeature参数位置。旧R条件声明仍是独立停放版本，本C不是倒改其scope或默认它已无条件成立。

## 3. 公开接口核对：共同半径须在所有未来选择之前固定

实际读FinitePrefixLaw.lean完整两个public类型及prefixMass17–18行定义、SourceTransferBudgets两个完整public类型、AdaptiveTailBudget三个完整public类型、O/M/N的完整public类型与O完整88行实际proof。全部消费接口是生产源公开theorem，下面不调用其他模块private helper。

SourceTransferBudgets.lean64行起的 exists_source_transfer_caps无外部前提，先给p/q/epsT及hp、1<q<103/100、epsT>0、hc=M*p=target q；同一输出还给所有正可和r总mass<epsT时limitingBase与各finiteBase正，以及对任意先给的正eta序列产生cap(J,u,n)。cap对所有合法有限前缀u及所有n先为正，然后对同prefix的全部未来正可和r给两个实际误差<etaJ。cap先于finalr，不含尚未定的future law。

对这个同p/q/hp/hc，再用P公开exists_source_prefix_radius（FinitePrefixLaw55行）得epsP>0。固定eps=min(epsT,epsP)>0，从此先于J/u、W、chooseN及r。任意u>0且Σu<eps也满足两个原半径门；同一公开P提供prefixMass非负、真HasSum1、真实EY=q／EX=q/4、AE实际stage范围、每活跃实际单点正质量。prefixMass只对u作零延拓，并含真实补偿基点，不是仅新增尾权的别名。

这个共同半径必须在构造之前选。不能直接调用Q的公有存在输出拿一个不透明eps，再任意另取P半径而假设所有Σu<eps的前缀均合法；也不能在拿到最终r后缩eps，因为无法保证原r总mass仍小于新eps。同理SourceTransferBudgets第二个便利存在定理隐藏已选eps，本路线只用第一个可见caps接口，并在拥有p/q之后显式取min，然后自行通过公开Adaptive装配。这样无需跨module引用Q、R或P/O的private证明。

## 4. 真正无条件的finite witness可由B/M/N产生

需要在新模块内部拥有一个有限模型见证lemma，其前提就是B的真实模型门并可带任意Nat下界N；不把hcont或系数极限作为输入。可以独立重用O（StageSourceWitness17–85行）实际数学论证，但旧O公有目标仍带hcont，不能直接当无条件producer。该适配只调用B、N、M的现成public接口；这在本声明门是可实现性论证，尚未写Lean实现或预批未来private类型。

固定一个由P提供的w=prefixMass、μ=atomicMeasure w及J/q。先由真实hw／HasSum得到概率；N公开exists_stage_phase_return_subsequence（StagePhaseReturns137行）给任意固定J/q的StrictMono m和实际实fract phase→0，包含J0。StrictMono.tendsto_atTop给m→∞。B完整public normalizedTailCoefficient_stage_subsequence_tendsto_of_stage对同模型／同m给actual coefficient极限L与真整数Summable，不要求hcont。

M公开stage_sourceGaussianLayerWeight_lattice_gap（SourceGaussianLatticeGap550行）在同μ/J/q及其真实均值／stage正原子门下给 I_J+H_J/(4096π)≤L，H_J=h_J√h_J>0。M写k*h_J、B写h_J*k，仅实数乘法交换，不能偷偷改索引或换Gaussian；完整types的tsum项和正常系数其余一致。I_J就是该同μ的correctedInverseScale。M的真实方差／κ／可积／整数可和门均已在该accepted public theorem完成，不在新C新增手工gap假设。

以δw=H_J/(16384π)>0，有 H_J/(4096π)=3H_J/(16384π)+δw，因此 I_J+3H_J/(16384π)<L。B的实际Tendsto给最终系数大于这个阈值，故可选≤形式的finite lower bound。真实N相位返回保证时间任意大；另用exists_nat_gt((J/H_J)^2)和m→∞，同时取m_j≥该Nat阈值、m_j≥N、m_j≥1及上述系数门。Real.le_sqrt_of_sq_le和H_J>0给 J≤√m_j*H_J，得到同一个正n满足所有条件。

这些确切步骤和已接受O50–85行的标准API一致，唯一分析生产点改成实际B而非输入hcont再调用条件J。没有新的缺cache高层API、任意law变换或triangular-array uniform率。全过程q在J／u／phase／n外固定，P的全部前缀均有同一个q，m虽为每个有限模型选用但不重新选q。

## 5. 先真实∀合法prefix见证，再chooseN，最后同一个r

定义W(J,u,n)记录n>0、prefixMass法则的finite系数≥I_J+3H_J/(16384π)，以及J≤√n*H_J。对每个Σu<eps的严格正前缀，P产生完整模型，再由上节真正无条件finite witness产生一个n，所以∀合法prefix的hW在finalr之前已经证明；不是把W当新的外部假设，亦不是为已选r的某些前缀循环论证合法。

固定etaJ=H_J/(32768π)>0，包含J0时h0=1。对transfer epsT输出的cap族，在小半径eps下限制使用：Σu<eps≤epsT使cap(J,u,n)>0，对任意n皆可，不需另猜该n属于某种good event。于是公开AdaptiveTailBudget.exists_witness_first_positive_mass_with_tail_caps（161行）适用于该eps、W、已证明hW和cap，返回先于r的整个total chooseN(J,u)，保证所有合法prefix的W，然后返回唯一正可和r、tsumr<eps和每个真实无限shift-tail(J+k)的严格cap。

非法prefix处chooseN的任意total补值不影响论证；hW/hcap只需在公开定理明确的合法门下。对产出的r，由每项非负与真Summable有Σ_{i<J}r_i≤tsumr<eps，故它所有实际前缀u_J=(r_i)都合法，J0空和也严格<eps。这样再用chooseN在这些prefix的W是非循环的；chooseN函数已在finalr之前存在，不是读到r后为每个J重新选时间。

源caps的同p正性族对tsumr<eps≤epsT适用，给limitingBase各点严格正；加全部r_j>0即得所有AtomicIndex上的limitingMass严格正。公开SummableAtoms107–113行limitingMoment_hasSum，以sourceEll_pos.le、source_constraintMatrix_nonsingular、同hc、r非负和Summable给全部4个真实HasSum(feature sourceEll (fixedAtom i) k)。第0行约束消去乘1给HasSum limitingMass1，而非用实tsum总化。

原律真实概率由公开InverseTilt51行originalMeasure_isProbabilityMeasure取这些非负权重及HasSum1得到；94行originalMeasure_centered以同4行HasSum给id真Integrable和真实均值0。它们在∀K/N之前，对同一个r/originalMeasure成立。对同w的正base、完整moment约束和q窗口，还可消费公开CorrectedScaleContinuity138行source_atomic_corrected_radicand_pos，得S−(32sourceEll/q)det>0；sourceEll>0，因此本correctedInverseScale=(sourceEll*√该真实正radicand)^(-1)有实际正域含义，非靠sqrt／inverse总化碰巧得值。

## 6. 同一最终法则的两项误差与常数逐算

记n_J=chooseN(J,u_J)。P公开finiteMass_eq_prefixMass（34行）在完整前缀等式r_i=u_Ji下给函数身份 finiteMass(sourceEll,p,r,J)=prefixMass(sourceEll,p,J,u_J)，包含真实补偿基点和新增支撑两分支。它不等同于limitingMass：最终无限law的基点补偿仍含未来尾，差异正由transfer控制，不能在这一步误消。

同shift-tail cap／总mass／前缀合法性向公开transfer误差接口分别给：|C∞(n_J)−C_J(n_J)|<etaJ，|I∞−I_J|<etaJ。它们是两个actual normalized系数及actual corrected常数，各law各自的率／normalizer都在既有接口内，不假设finite和limit的rate/Z相同。用第一绝对值的下侧和第二绝对值的上侧，与W的 C_J−I_J≥3H_J/(16384π)=6etaJ，得到

```text
C∞(n_J)−I∞ > 6etaJ−2etaJ = 4etaJ = H_J/(8192π).
```

所以可弱化为所需实际gap≥H_J/(8192π)，同时W给J≤√n_J*H_J。误差预算方向与常数正确；没有只留一个eta、把两个错误同向相消，或把real积分差替代实际originalP概率差。eta在所有u/n/r之前由J给定，严格正cap容许所有countably many约束，与Adaptive的整个future-tail语义吻合。

## 7. 任意K/N的实际同一n与所有边界

由dyadicMesh J=(2^J)^(-1)及2^J≥1，实际0<h_J≤1；故0<√h_J≤1，0<H_J≤1。√n_J≥0，所以J≤√n_J*H_J≤√n_J。两侧非负后平方并用Real.sq_sqrt(n_J≥0)得J²≤n_J；无需假设n_J单调，也不除以J、r_i、K或未知正n。

乘已证明gap时仅需√n_J≥0，便有

```text
√n_J*(C∞(n_J)−I∞) ≥ (√n_J*H_J)/(8192π) ≥ J/(8192π).
```

对任意实K、Nat N，取自然J>max((N:ℝ),K*(8192π))；max≥N≥0保证J≥1。于是N≤J≤J²≤n_J，且W给n_J>0；π>0使J/(8192π)>K。这个同n_J同时任意晚与缩放余项>K。负K／N0仍由同选择覆盖；J0仍参与先前所有caps／prefix族，不在构造中被删，只是最终寻找任意大见证可选择J≥1。

最终r/q/P已在此∀K/N步骤之前固定，后面只评价既有chooseN在既有r前缀上，并选阶段J；不重选law／r。该论证实现R1(31)的正号无界子列意义，不声称全n余项趋∞、n_J单调或uniform triangular-array极限。数学/API阶段独立判断本完整无条件强化可行，没有发现需要新增hcont/hW/gap/limit假设的缺口。下面才核实际四imports联合图、cache存在性与source／版本／git绑定。

## 8. 最后独立四imports联合图／source／缓存与版本绑定

以上数学构造和量词次序明确后，才从实际四个imports做独立公开/meta联合图检查；未读取作者scanner、candidatecache或JSON正文。直接解析实际source，去掉嵌套块注释／行注释／字符串，识别普通／public／private／meta import及module默认可见性；物理图走全部实际边，公开图只走公开边，meta边均计入。Shao／Mathlib内部继续遍历，Lean／Std／其他外部节点只计停止叶，不扫描或假造其内部。

实际联合物理图64Shao／2973Mathlib＝3037内部，211物理外部停止叶；公开图64Shao／2645Mathlib＝2709内部，加189公开外部停止叶＝2898。两图内部逐项source及对应已存在olean无缺。FinitePrefixLaw／StageSourceWitness／SourceTransferBudgets／AdaptiveTailBudget／SourceGaussianLatticeGap／StagePhaseReturns／StageSourceAsymptotic／InverseTilt／SummableAtoms／CorrectedScaleContinuity均真实公开可达。旧SourceCoefficientDiagonal(Q)及SourceRemainderFailure(R)不在此公开联合图中；本可行性构造不需要其opaque存在eps或停放的条件目标。

64个实际project源按canonical相对路径键→fresh源SHA组成排序紧凑map，独立复算SHA256d0bfa7bc611ccb928a773f36cd4de7aa7b62d634147bcbc08721f792670a92b5，与冻结scope口径一致。这里source／olean只读检查不重复root成功smoke或任何旧build，也没有重算稳定51Mathlib对象hash。此前B的53图不能直接覆盖本新联合图，所以只做了本次确有必要的新union核查。

关键实际公开source本地所读副本与remote图逐项hash一致，或在B情形绑定刚接受的同905f源：

| 真实source | SHA256 |
| --- | --- |
| FinitePrefixLaw（108行／4695B） | bf603626347e46c4cc2342d93798cddb81c475eba7c5de3f888ff3e671d6a2d4 |
| StageSourceWitness（88行／4539B） | e757684a3eadbaf84dc0b15e127dac1a8bb7ef24a7f5e562b8a48e4d7ca16ef7 |
| SourceTransferBudgets（215行／11459B） | 59701f99357816ab2703e5c811796f6de9f84e7f0af4208d7225e13b9277e060 |
| AdaptiveTailBudget（192行／8432B） | 86df6ca9eb9aa21b7eff614c9cfdef5be96b4bbd5d192fcb8c5e0ce97c8006bf |
| SourceGaussianLatticeGap（685行／33728B） | d211fa4e676fbb76e81ff59008fb654c6b4fdc51c78a1bccd7adf4b1f5b419bd |
| StagePhaseReturns（168行／7782B） | 0e77e8459f8351213c1842535aedee731f0bbd641414a0192d9fd76d3338511c |
| StageSourceAsymptotic（46行／2139B） | 905f5287250e4ef52cdd0fb7dbcd7823bbd6ceda6ac1de1ee3b82e7959580c8e |
| SummableAtoms | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| InverseTilt | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| CorrectedScaleContinuity | b0391976b809b37b1d0d3cb591c2fc89c9291538e8bc9193db70dd2b1504a2a8 |

scope67两端实际38行／8143字节／SHA25664973e397d95de7b2deb2e42f16a4417ffe2363e53d38d65b11ef19e4cb42031，第1节fence与此冻结版本一致。自己已完整接受B终票仍126行／20069字节／SHA216867808dbf259b8e8b1f2289e8f95add2d1572f7fdf2e8b94025e97749d1c6。图／cache readiness不是C的proof，也不将当时provisional的B状态误记为本次未接受：其source已完成独立终审并以同hash冻结发布。

fresh lane仍feat/oq3-stage-source-asymptotic，HEAD20b5e5103fad7e2180a74fd65c19fab6800abc0f，status干净；尚无新C分支。两端SourceFixedLawRemainder.lean均不存在，没有本模块source／Audit／probe／内核结果可验收。Mathlib HEAD807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4，lake-manifest SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e，与先前接受B的固定版本一致。rootv35 baseline描述是冻结时行政记录，当前stack正确保留B parent，未为吸收rootmain作lane merge/rebase/reset。

本轮所有remote实际只读进程affinity=[14,15,16,17]，无Lean／#check／probe／build／rebuild／cachewrite／spawn／commit／pub／raw完整log下载，不触外部CPU0–9／80GiB、全局资源、pins或heartbeat。只写本新报告及授权run/statement-review.md；未改scope／source／旧review／receipt／shared文件。只读自己允许的正式scope、accepted production source、真实R1和实际固定API，没有读作者未来/implementation/candidate/scanner及其JSON正文。

## 9. 最终独立声明裁决与原义务边界

STATUS: CORRECT

JUSTIFICATION: 该无外部前提的完整目标可由实际现成公开接口构造。先从transfer_caps选择真实p/q/epsT，再同p/q取P半径并固定eps=min，避免Q或便利存在API的不透明eps问题；每个合法prefix由P给真实阶段模型。新模块自有有限见证可把O实际论证中的条件J调用改为已无条件接受B，并用N的真实phase返回和M的1/(4096π)gap给3/(16384π)有限余量与增长；没有手工hcont/hW/gap/limit前提。公开Adaptive先chooseN后r，cap和prefix合法性无循环，最终完整HasSum／真概率／Integrable均值0由同r的公开moment和inverse-tilt API产生。

两项严格eta=H/(32768π)误差从finite6eta留下final4eta=H/(8192π)，对象始终同一最终limitingMass/originalMeasure和corrected常数；finiteMass_eq_prefixMass只识别真实finite截断，未假造与limit基点相等。增长和h≤1给J²≤n_J，不需n_J单调；自然J>max(N,K8192π)给同n任意晚且缩放余项>K。J0／N0／负K／早期0样本、真Summable／严格tail及所有概率／方差正域门均可保留。

本票是冻结scope67的来源／数学／量词／实际API与环境可实现性批准；C尚未写源，未预报任何kernel／Audit PASS。实际实现尤其新增自有private witness和所有生成类型，仍须后续完整独立proof／actualTYPE／机械终审。原(31)的无条件同律结论是本类型拟消除的直接原始义务，当前不计已形式化完成；generalKL／全局扩展Legendre极小性／literalPhi／原24exactζ及其他根组装仍OPEN，A/B/C/D全部OPEN，无最优性或新颖性主张。lead须全文读本完整终票后才实施。
