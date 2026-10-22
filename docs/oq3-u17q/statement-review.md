# U17q v2 SourceCoefficientDiagonal 独立声明／来源／API审查

STATUS: IN_PROGRESS

## 1. v2唯一完整TYPE重新独立盲译检查点

本节仅提取v2冻结Lean fence，先于读取v2 scope说明、R1及本轮接口／机械证据持久化。审查者已有v1独立审查上下文；不把v1修复建议当作v2批准，不隐瞒此上下文。0公开定义，以下完整TYPE不省略任何hcont长续行。

```lean
theorem exists_source_fixed_law_coefficient_diagonal :
  ∃ (p : Fin 4 → ℝ) (q eps : ℝ),
    (∀ i, 0 < p i) ∧ 1 < q ∧ q < 103 / 100 ∧ 0 < eps ∧
    (constraintMatrix sourceEll) *ᵥ p = constraintTarget q ∧
    ∀ (hcont : ∀ (J : ℕ) (u : Fin J → ℝ),
      (∀ i, 0 < u i) → (∑ i, u i) < eps →
      ∀ d : ℕ → ℝ,
        (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
        (∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
          d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) →
        ∀ A : Set ℝ,
          (ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (transverseVariance
              (atomicMeasure (prefixMass sourceEll p J u))))) (frontier A) = 0 →
          Tendsto (fun n : ℕ =>
            (normalLayerConditionalLaw (atomicMeasure (prefixMass sourceEll p J u))
              q (q / 4) (d n) n).real A)
            atTop (nhds ((ProbabilityTheory.gaussianReal 0
              (Real.toNNReal (transverseVariance
                (atomicMeasure (prefixMass sourceEll p J u))))).real A))),
    ∃ chooseN : (J : ℕ) → (Fin J → ℝ) → ℕ,
      (∀ (J : ℕ) (u : Fin J → ℝ),
        (∀ i, 0 < u i) → (∑ i, u i) < eps →
        0 < chooseN J u ∧
        correctedInverseScale sourceEll q (atomicMeasure (prefixMass sourceEll p J u)) +
          (3 * dyadicMesh J * Real.sqrt (dyadicMesh J)) / (16384 * Real.pi) ≤
            normalizedTailCoefficient sourceEll q (prefixMass sourceEll p J u) (chooseN J u) ∧
        (J : ℝ) ≤ Real.sqrt (chooseN J u : ℝ) * dyadicMesh J * Real.sqrt (dyadicMesh J)) ∧
      ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Summable r ∧ (∑' j, r j) < eps ∧
        (∀ i : AtomicIndex, 0 < limitingMass sourceEll p r i) ∧
        (∀ k : Fin 4,
          HasSum (fun i => limitingMass sourceEll p r i * constraintFeature sourceEll (fixedAtom i) k)
            (constraintTarget q k)) ∧
        IsProbabilityMeasure (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
        (Integrable (fun x : ℝ => x) (originalMeasure sourceEll (limitingMass sourceEll p r)) ∧
          (∫ x : ℝ, x ∂originalMeasure sourceEll (limitingMass sourceEll p r)) = 0) ∧
        ∀ J : ℕ,
          0 < chooseN J (fun i : Fin J => r i.val) ∧
          correctedInverseScale sourceEll q (atomicMeasure (limitingMass sourceEll p r)) +
            (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (8192 * Real.pi) ≤
              normalizedTailCoefficient sourceEll q (limitingMass sourceEll p r)
                (chooseN J (fun i : Fin J => r i.val)) ∧
          (J : ℝ) ≤ Real.sqrt (chooseN J (fun i : Fin J => r i.val) : ℝ) *
            dyadicMesh J * Real.sqrt (dyadicMesh J)
```

先无条件存在固定p:Fin4→ℝ、q/eps:ℝ，使p每项严格正、1<q<103/100、eps严格正，且同一个p满足actual矩阵constraintMatrix(sourceEll)乘p等于constraintTarget(q)。这些性质现在是存在量词之后的合取结果；最终合取的右侧是一个以完整hcont为参数的全称命题，不再让hp/hq/heps/hc落入一个总蕴含前件。

hcont对每个J:ℕ和u:FinJ→ℝ，若u所有项严格正且有限和<同一个eps，则对任意d:ℕ→ℝ，凡d整个序列有一个共同实界、且最终d_n+n*q属于同一个mesh(J)整数格，对任意实集合A，只要actual横向方差Gaussian对frontier A质量为0，就有同一actual atomicMeasure(prefixMass sourceEll p J u)的normalLayerConditionalLaw（中心q、q/4，层d_n，样本n）在A上的实质量趋向该Gaussian的实质量。hcont是明确输入，不是本命题生产的结论；不限定A可测，因为类型仅输入frontier零质量，后续须核已有消费者完全匹配。

对于每一个这样的完整hcont，存在一个全定义chooseN:(J:ℕ)→(FinJ→ℝ)→ℕ。在每个合法前缀上，chooseN为正，actual有限律的normalizedTailCoefficient至少等于该有限律的correctedInverseScale加3*h*sqrt(h)/(16384*pi)，且J≤sqrt(chooseN)*h*sqrt(h)。非法前缀上函数仍定义，但不承诺这三个性质。p/q/eps在hcont前，chooseN可依赖hcont，但先于最终r。

随后存在同一条r:ℕ→ℝ，逐项严格正、真正Summable且真实tsum<eps。actual limitingMass在全部AtomicIndex上严格正；对每个k:Fin4，真实函数i↦limitingMass(sourceEll,p,r,i)*constraintFeature(sourceEll,fixedAtom(i),k)具有HasSum到constraintTarget(q,k)。本版取值原子是fixedAtom(i)，坐标是k，不作总化tsum替代。

同一个actual originalMeasure(sourceEll,limitingMass)为概率测度，X真Integrable且积分为0。对于每个J，样本量恰为前面同一chooseN作用于r前J项：它为正；该最终同一law的actual系数至少等于其correctedInverseScale加h*sqrt(h)/(8192*pi)；还满足同一个J增长不等式。q、p、eps和最终r均不得按J/n重新选择；样本虽按前缀选，但不能偷读完整未来r。

类型包括J=0、实q/eps的严格窗口、原子全正和完整真HasSum；尚须独立核真实半径／预算的共同缩小、合法prefix在最终r上的保持、hcont到实际W的全部门、chooseN先于r、同law两项误差和常数、概率／可积零均值，以及实际公开API和环境。当前不宣称hcont／Levy／无条件19／hW／最终diagonal或根闭合。

## 2. 本版本解析与两项修复的独立确认

本票是完整声明／来源／API门，不是未来实现的proof review。第1节原66行、5746字节先行盲译完整保留，SHA256为95b9c232c925b827a5723b8651adb4d145c80acff7e71b580a2721c19b2e216a；其IN_PROGRESS仅表示当时检查点。

已逐字符比较v1/v2完整Lean fence。除两个语义修复外全部类型文本相同：v1的整个family括号及总箭头变为最终合取右侧的显式∀(hcont:完整family) binder（含对应结束逗号），且唯一错误feature项改为constraintFeature sourceEll (fixedAtom i) k。两个余量、增长、HasSum的目标、同一law和所有hcont长续行均未改。v1冻结scope及INCORRECT终票没有被修改。

v2真实逻辑结构是∃p/q/eps, hp∧hq0∧hq1∧heps∧hc∧∀hcont,∃chooseN,...。所以即使未来hcont尚未生产，p正／qwindow／eps正／矩阵约束仍须无条件实际交付；p恒0不能使整条声明真空成立。新的HasSum在i:AtomicIndex处取fixedAtom i:ℝ，再以k:Fin4取真实特征坐标，完整匹配FiniteConstraints.lean35–36、SummableAtoms.lean107–113及InverseTilt.lean94–99。本版没有沿用v1的两项阻塞。

以下给出从当前真实公开API可执行的数学组合核验，不用作者路线或前置成功日志代替论证。

## 3. 固定同一参数与共同小半径，先于hcont和全部未来

实际公开SourceTransferBudgets.lean64–82的exists_source_transfer_caps先存在p/q/epsT，交付hp、1<q<103/100、epsT>0及hc。这些参数在任意eta／cap／r之前，并附带：凡r全正、真Summable、总量<epsT，其limitingBase和全部finiteBase严格正；对任意逐J正误差eta，还给一个在每个合法前缀和每个n均严格正的cap，以及同前缀未来尾<cap时的两项真实误差。

对该同一个p/q及实际hp/hc，消费FinitePrefixLaw.lean55–68公开exists_source_prefix_radius，取得epsP>0；不再调用另一个存在起始参数的定理。固定eps=min(epsT,epsP)>0。所有合法prefix sum<eps自动同时<epsT、<epsP；最终r的总量<eps也同时满足两旧半径。这个共同eps取在hcont、W、chooseN、最终r之前，不能在收到某个u/J或未来r后重选。

这里不能直接把exists_source_mass_with_witness_and_transfer的某个固定epsT当成已自动小于后来得到的epsP，也不能读取该定理proof内部私有半径。本组合使用公开的第一条caps接口，再用公开AdaptiveTailBudget见证优先接口于缩小后的eps；因此缩小半径不丢任何输出，没有隐藏radius前提或重选p/q。

令h_J=dyadicMesh J=((2:ℝ)^J)⁻¹，a_J=h_J*sqrt(h_J)，b=1/(8192*pi)，eta_J=b*a_J/4。由2^J>0、取逆正、Real.sqrt_pos和pi>0，h_J、a_J、b、eta_J对全部J严格正。J=0时h_0=1，不是0。FiniteConstraints的dyadicMesh_pos是private，不能跨模块消费；这里由公开定义及普通pow_pos／inv_pos重新证明这一简单正性即可，不需要该私有引理。

由同一caps接口，在上述正eta下先取得cap(J,u,n)。它依赖固定参数／有限前缀／给定n，不依赖最终r；其尾控制是实际∑'j,r(J+j)，与有限支持j<J的第一个未来索引J一致。

## 4. P加完整hcont真实生产全部合法前缀的W

定义W(J,u,n)为v2 chooseN子句中的三个实质结论的合取：n>0、actual有限系数至少corrected scale加(3*b/2)*a_J，以及J≤sqrt(n)*a_J。该W是一个全定义的命题函数；无需假定它在非法前缀上可满足。

给任意合法J/u。P的公开radius接口输出w=prefixMass sourceEll p J u逐项非负、真实HasSum w 1、EY=q、EX=q/4、真实stage有限AE支持及全部活跃Fin4⊕FinJ原子正单点质量。这些不是全无限AtomicIndex处处正：未来零延拓权重本来为0。P的完整定义是finiteMass对u的零延拓；其已接受证明先建立真正有限支持HasSum再用公开矩积分API，非利用总化tsum或不可积积分默认0。

P接口给出的hw/HasSum由AtomicMeasure.lean39–42实际产生atomicMeasure w的概率实例。其实际矩积分基础还分别是AtomicMeasure.lean96–109的真Integrable id及EY对应PositiveRate.lean31–41的真Integrable normalValue，不把单独的积分值等式当作可积替代。O也由同一个hw/HasSum建立实际概率并消费相同EY/EX／stage支持／正单点门。

把v2完整hcont作用于同一个J/u及其合法证明，得到的函数恰是StageSourceWitness.lean26–36的hcont参数：同一atomicMeasure w、同一q和q/4、同一全部有界d、同一eventual整数格条件、任意A及actual transverseVariance Gaussian的frontier零质量门；没有缩成相位0或只对一条d/A的收敛。

于是公开exists_stage_source_witness（StageSourceWitness.lean17–42），取其任意大门N=0，即给某个n的完整W。它已在accepted O中通过实际phase子序列、J系数极限和M的充分gap生产见证；本次不再次假设W、不输入手工Gaussian gap，也不把hcont宣称已生产。由此获得∀合法J/u,∃n,W(J,u,n)，这是本Q在显式hcont条件下真正可生产的forall-prefix hW。

J=0时u:Fin0→ℝ为空，逐项正是空全称，sum=0<eps；P保留四个补偿基点概率与正单点门，O含J0且仍给n>0。没有给空前缀额外nonempty假设。n无需单调；目标只要求每个前缀的见证／增长，O的结论足够且未偷偷加强为strictmono。

## 5. 先chooseN，后同一条全正真可和r

公开AdaptiveTailBudget.lean161–174的exists_witness_first_positive_mass_with_tail_caps精确接受eps>0、上述全定义W、全合法prefix的hW、cap及在合法prefix且W时cap>0。其最后一门由SourceTransferBudgets给的更强“合法prefix上对所有n cap>0”直接获得；sum<eps≤epsT把合法性传过去，未循环使用最终r或尚未证明的hW。

该API先存在完整chooseN并在每个合法prefix上给W(J,u,chooseN J u)，再存在r，输出∀j,r_j>0、Summable r、真实tsum r<eps以及每一个完整无限shift-tail小于cap(J,r前缀,chooseN(J,r前缀))。不是只约束下一个原子，也不以总化tsum的默认0代替可和。其实际161–189行已读取：chooseN对合法prefix以Classical.choose选hW，非法前缀定义0，然后把cap∘chooseN送入公开adaptive tail构造。私有state／递归均由既有公开定理封装，不需要Q跨模块访问。

因此选样本函数时可读取完整有限u与hcont，但还没有最终r。最终r是根据已定函数的所有预算构造，不能反过来先有最终r再偷选依赖其完整未来的样本。p/q/eps保持同一个，全部J共用一条r。

对该r的每个实际前缀u_J(i)=r(i.val)，严格正直接由r正给出；真Summable及非负使有限和≤tsum r<eps。这里用实际SourceTransferBudgets.lean206–209已用的Fin.sum_univ_eq_sum_range及Summable.sum_le_tsum，确保hn和hcap都在真正合法前缀上应用。并非从前缀预算事后假设合法性。

## 6. 完整prefix身份与两项误差的准确同law余量

公开FinitePrefixLaw.lean34–53的finiteMass_eq_prefixMass，对任意ell/p/J/u/r只需∀i:FinJ,r(i.val)=u(i)，便给完整函数等式finiteMass ell p r J=prefixMass ell p J u。其真实证明分别处理finiteBase的有限矩补偿和新增分支的if(j<J)，所以包括四个补偿基点，不只是后面的新增原子。对最终r的u_J该前缀等式是逐点rfl；无需全r严格正或Summable来证明该身份本身。

同一个r因tsum<eps≤epsT且已有真Summable／全正，可在caps的herror上使用。输入上述前缀身份、完整shift-tail cap及同一个n=chooseN(J,u_J)，得到实际：

```text
|C_limit(n) - C_finite(n)| < eta_J,
|R_limit - R_finite| < eta_J.
```

其中C是声明中的normalizedTailCoefficient，R是同声明的correctedInverseScale；finite一侧通过公开完整权重等式准确换成prefixMass。两个C各为其自己的actual原律、normalizer和rate对应的系数，绝不假定有限律与极限律的I/Z相等，也不把atomic tilted law与original law偷换。caps输出已是这两个真实表达式，不需新增TV/RN或积分交换主张。

W给C_finite(n)≥R_finite+(3b/2)*a_J。两绝对值严格误差各为eta_J=b*a_J/4，因此

```text
C_limit(n) > C_finite(n) - eta_J
           ≥ R_finite + (3b/2)*a_J - eta_J
           > R_limit + (3b/2)*a_J - 2*eta_J
           = R_limit + b*a_J.
```

故目标的非严格下界成立，且还有严格余量；1/(8192*pi)与3/(16384*pi)换算准确，没有把两次误差只扣一次或丢掉sqrt(h)。增长及n>0直接来自同一个W，未重选一个n分别满足系数和增长。上述只用有限实数绝对值及线性运算，无额外换序／极限／Fubini门。

## 7. 最终原子全正、真实HasSum和同一original law

由caps的hfamily，以同一个r的全正／Summable／总量<epsT取得limitingBase每项严格正。limitingMass实际是Sum.elim limitingBase r，故所有AtomicIndex上的质量严格正：基点由hfamily、后续点由r正；不是仅从p>0忽略补偿而断言limitingMass>0。

由sourceEll_pos.le、公开source_constraintMatrix_nonsingular、同一个hc、r非负及Summable r，公开SummableAtoms.lean107–113的limitingMoment_hasSum给每个k完整真HasSum，单项正是v2的limitingMass...i * constraintFeature sourceEll (fixedAtom i) k。该实际证明先建立addedFeature真Summable，再把Fin4有限HasSum与ℕ无限HasSum合并；Q无须也不得退化为无可和门的tsum恒等式。

取k=0，公开constraintFeature／constraintTarget定义化简得到HasSum(limitingMass)1。InverseTilt.lean51–55的originalMeasure_isProbabilityMeasure在实际非负权重和该HasSum下给原律真概率，其证明先有inverseExp真Integrable，不把非可积tilt=0分支当概率。InverseTilt.lean94–99的originalMeasure_centered消费同一完整四矩HasSum，给X真Integrable和积分为0；未仅写总化积分等于0。该original law、误差中的limitingMass、最终系数中的limitingMass均由同一p/q/r确定。

## 8. 来源对应、公开可消费性与剩余边界

已重新逐行读取真实R1第486–550行。第486–497行先固定有限阶段、选样本／增长后才选未来质量；第501–507行将真实normalized coefficient与同一各自原律对应；第521–526行要求两项(b/4)*h^(3/2)误差；第531–537行要求所有未来尾预算兼容并保持无限全正／总mass小；第539–548行传到同一最终固定律。本版组合逐项对应这些来源，而非一个手工W输入的包装。

直接消费链：公开caps固定参数及预算半径 → P在共同小半径生产每个真实prefix模型 → 完整hcont与O生产所有合法prefixW → 公开Adaptive先chooseN后r → 完整prefix身份及两项误差传到同一固定law → 真实全矩／原律概率／可积中心。没有消费外部模块的private prefix_sequence_hasSum、prefixZero、内部finite-prefix helper或私有dyadicMesh_pos；所需简单h_J正性由公开定义重证。普通概率／积分主API是既有接受的实际接口，无缺失Levy cache的新依赖。

本门批准的是这条带显式完整hcont的声明及其可用公开API／数学可实现性，不是尚不存在的Q实现或内核证明。未声称实际hcont已生产，也未把条件性的forall-prefix见证升级为无条件hW、完整19／最终diagonal或任意根闭合；literalPhi、原24exactζ、一般KL／global minimizer等仍OPEN。hcont若未来由U18a生产必须属于完全相同的实际prefixMass家族，不能换一个p/q/eps或参考law。

## 9. 最后的新鲜机械／环境绑定

数学与全部量词／实际API核验后，才重新只读核对两端scope、关键生产源、meta-aware图、pins及git。未读取作者candidatecache／scanner或其JSON正文。

v2 scope两端均66行、8114字节，SHA256 20081afcebdf022810d74841657c5633b523712db40803660bd776069c3eed8a；本票第1节完整fence与其逐字符相同。v1 scope仍64行、7228字节，SHA256 ad76ec9efa3ce968e2128b0bce2092f8a4c4321150bf4fddb4b053d90ae77b61；v1最终report仍182行、16803字节，SHA256 69c06dfbb370d0480cd0906331785fe428f3473f06c69e773f5feaa337e21139，两端历史证据均未改。R1真实只读原件575行、19420字节，SHA256 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。

本轮实际读取的十份关键local生产源均逐项与指定server worktree新鲜SHA匹配：

| 实际生产源 | SHA256 |
| --- | --- |
| FinitePrefixLaw.lean | bf603626347e46c4cc2342d93798cddb81c475eba7c5de3f888ff3e671d6a2d4 |
| StageSourceWitness.lean | e757684a3eadbaf84dc0b15e127dac1a8bb7ef24a7f5e562b8a48e4d7ca16ef7 |
| SourceTransferBudgets.lean | 59701f99357816ab2703e5c811796f6de9f84e7f0af4208d7225e13b9277e060 |
| AdaptiveTailBudget.lean | 86df6ca9eb9aa21b7eff614c9cfdef5be96b4bbd5d192fcb8c5e0ce97c8006bf |
| FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |

独立图扫描从精确三个拟imports出发，去除源码注释／字符串后解析普通、public与public meta import。在Shao／Mathlib中递归，对Lean／Std等外部停止叶不声称展开。含meta物理闭包为62 Shao／2920 Mathlib；公开可达为62+2638=2700内部节点加189外部叶=2889。普通不含meta物理闭包为62／2905；普通公开为62+2623=2685内部节点加84外部叶=2769。四个口径内部源码与olean存在性均缺0；物理图外部叶分别210／103，不混为公开图计数。

实际62个Shao源用canonical相对路径Shao/...lean作键、源SHA作值，排序紧凑map的SHA256仍为e3723003af9ea2bb0be7f06f3216ef1246268a6995e784346e35b0b1e7fb8303。新鲜结果与此前已核冻结图一致；公开API在现有imports下可达，未新增模块或下载缓存。仅确认olean存在，不冒称新Q已elaborate或编译。

实际工作树/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3仍为feat/oq3-finite-prefix-law，HEAD c6a4768260f55cc6d7c648015516e0a730035706，status --short为空，符合本版明确的“声明批准后才建Q分支”。Mathlib实际HEAD 807d3836b165983210ee2ecf3cd28f239436949c；lean-toolchain为leanprover/lean4:v4.36.0-rc1，29字节／1行／SHA256 d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4；lake-manifest.json 3541字节／117行／SHA256 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e。

两端SourceCoefficientDiagonal.lean均不存在；run内Q的source／Audit.lean／Audit.log／receipt.json也均不存在。没有Q构建／类型输出／公理审计可读或宣称PASS，本票只是v2声明门。报告完成后只上传statement-review-v2.md并核双端字节／行数／SHA。

全程只写本新报告及授权remote副本；所有server项目操作taskset -c 14-17只读，没有Lean／#check／API probe／重编／cachewrite／commit／pub／spawn／完整rawlog下载，不触外部CPU0–9／80GiB或全局资源，不改pins／heartbeat，不用ulimit-v。所有作者implementation／actual-diagonal／prefix-law-next／phase／cusp／future／candidatecache／scanner及其JSON正文均未读取。

## 10. 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: v2确实无条件交付固定hp/qwindow/eps/hc，完整hcont留为最后合取的显式输入，真实HasSum按fixedAtom i取值。用同一公开caps参数、P公开prefix半径的共同min，可在所有未来前固定合法模型范围；P加同一完整hcont及O公开见证生产全合法prefix的W；公开Adaptive接口在缩小半径下先选完整chooseN，再生产同一条全正真Summable r和每个真实shift-tail cap。完整prefix权重等式含四基点，真实两项各(b/4)*h*sqrt(h)误差从(3b/2)有限余量留下至少b最终余量；真四矩HasSum再给同一original law概率、X真可积零均值。J0／非法prefix不承诺／全部最终prefix合法等边界均匹配实际API，无需任何跨模块private接口或缺失缓存。

本结论仅批准冻结scope64-v2（SHA20081afc...3eed8a）的完整声明／来源／数学可实现性及当前公开环境；未来实现仍需按actual TYPE盲译、完整proof／所有private/generated、实际TYPE与机械最后的独立审查。v1的INCORRECT历史保留；本门没有实现／编译Q，也未消除真实hcont、无条件19／hW／最终diagonal、generalKL／literalPhi／原24exactζ或根A/B/C/D。
