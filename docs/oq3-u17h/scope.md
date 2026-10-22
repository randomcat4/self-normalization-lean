# OQ3-U17h：实际相位全部正负层的真实加权积分分解

冻结v1，DECLARATION_REVIEW_QUEUED_AFTER_U17G_COMPLETE_FINAL_IF_LEVY_CACHE_MISSING；未批准/未实施。拟 Shao/OQ3/StageLayerDecomposition.lean；imports Shao.OQ3.NegativeLayerGeometricTail、Mathlib.Algebra.Order.Floor.Ring、Mathlib.Algebra.Order.Archimedean.Real.Basic、Mathlib.MeasureTheory.Integral.Bochner.Set；namespace Shao.OQ3/open MeasureTheory Filter/open scoped BigOperators/noncomputable section。一完整公开DEF、一个完整公开目标。前序G完整终票lead全文读后才派本声明门；root固定Levy/Portmanteau就绪时更优先U18a，不以缺cache停工。批准前不写本源/Leanprobe，无新cache/公共源/pins/旧source编辑。

原始目标→R1(19),400–429实际全部格层加权和；source current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662。剩余关键义务→U16b/F的相位序列尾界尚未证明等于原sourceTail加权积分，且双侧零层不能重复。本模块消除→真正product-AE网格相容/精确实际phase/正负层disjoint覆盖及真实可积后层积分countable分解；直接消费者→将有限层条件Gaussian极限和U16b/F共同尾接成原19。未完成→conditionalLevy/固定层moving阈值/sign尾/真正dominated-series limit19/cuspEM/rotation/hW/generalKL/所有根，仍OPEN。

```lean
def sourcePositiveNormalLayerTerm (mu : Measure ℝ) (q ell h theta : ℝ)
    (n k : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp (-ell * (h * ((k : ℝ) + 1 - theta))) *
    (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = h * ((k : ℝ) + 1 - theta) ∧
        z ∈ sourceTail q n}

theorem stage_source_layer_decomposition (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :
    ∀ n : ℕ,
      let theta : ℝ := Int.fract ((n : ℝ) * q / dyadicMesh J)
      Summable (fun k : ℕ =>
        sourcePositiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      Summable (fun k : ℕ =>
        negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      Real.sqrt (n : ℝ) *
          (∫ z : Shao.Path n in sourceTail q n, Real.exp (-ell * normalDeviation q z)
            ∂Measure.pi (fun _ : Fin n => mu)) =
        (∑' k : ℕ, sourcePositiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) +
          ∑' k : ℕ, negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k
```

独立审查先完整DEF体和完整TYPE盲译并持久化，再本路线/来源/actual原库语义，机械最后。q/ell任意实，mu真概率及AE真实stage足够；无需均值/正原子/q>0/ell>=0以证明这个精确支持分解。不能因为结论更一般而把任意measure的real总化质量当概率；本TYPE真概率使所有产品有限。n=0也允许且不得除n/sqrt n；只除h=dyadicMesh J，所有J包括0真h>0。

phase是实际theta=Int.fract(Nq/h)，0<=theta<1；FloorRing ℝ真实实例在已静态读且现成cache的Algebra.Order.Archimedean.Real.Basic:37，Int.fract定义Defs:264为x-floor x；Ring:311 floor_add_fract、438 fract_nonneg、445 fract_lt_one可用。不得误用不存在的Data.Real.Archimedean路径或只凭generic FloorRing漏实实例。

真实stageAtom_normalValue_lattice给每坐标Y属于hℤ，经产品AE逐坐标/有限整数和得到同nu-AE存在整数m使M=h*(m-theta)。这个AE格点事实必须实际证明，不从源报告赋格或把AE当所有path。m由样本整数和减floor(Nq/h)得到，h非零后真实分母消去；n0有限空和照常。

正方向层Pk={M=h*(k+1-theta) ANDsourceTail}，非正方向Nk={M=−h*(k+theta) ANDsourceTail}。0<=theta<1/h>0保证Pk的法向值严格正、Nk非正，同方向index不同给值不同、两方向disjoint。整数m=0及负整数归Nk，正整数归Pk，可用Int.ofNat0/Int.ofNat(succ k)/Int.negSucc k构造精确Nat索引，避免toNat符号/零层错误。theta0时仅N0是真零层，P0从+h开始；不要两边同时算零。现有U16b positiveNormalLayerTerm的内部已是k+1−theta，其参数就是同theta，不把1−theta再传进去；新DEF保留真实sourceTail交事件，不能用U16b只有{M=d}的raw质量代替精确项。

whole weight对同nu必须先真Integrable。可由真实stage Y>=−9（公开fixedAtom_normalValue_lower）和对任意x的Y<=16（normalValue=16−(x−4)^2）得AE |Y|<=16，产品有限和给|M|<=(16+|q|)*N。任意ell的−ell*M<=|ell|*|M|，故exp weight由实际有限常数exp(|ell|*(16+|q|)*N)真AE支配；M/exp连续提供AEStronglyMeasurable，nu真概率有限后用Integrable.of_bound。不能对ell任意时只用ell>=0的单侧weight界；也可用真实有界连续有限产品helper，但必须核API全部门。再常数乘sqrtN得scaled integrand真可积，含n0无需正除。

全部Pk/Nk各可测（连续M等值交sourceTail_measurable），每方向countable pairwise disjoint、两union真正disjoint。AE网格覆盖使sourceTail与两union AE相同，而非点态相同。setIntegral_congr_set只在真实AE set equality下用；setIntegral_union的可测/Disjoint/各restrict真可积全部先建；每方向hasSum_integral_iUnion或integral_iUnion的真IntegrableOn全union门来自whole scaled integrand，不遗漏。每层用setIntegral_congr_fun真实M=d常数和真finite probability setIntegral_const得到exact正DEF/负F DEF。hasSum_integral_iUnion同时给原正/负actual sequences真Summable，后tsum identity，不能用不可和tsum默认0；这一固定n可和本身不代替U16b/F对n共同tail。

实际Bochner.Set:320–325 hasSum_integral_iUnion在Countable索引、层measurable/Pairwise Disjoint和全union真IntegrableOn下给真实HasSum；327–330 integral_iUnion是其真tsum等式；85–87 setIntegral_union要求两restrict可积与真disjoint/可测。现成cache均已读：Floor.Ring、Archimedean.Real.Basic、Bochner.Set为true。最后声明门仍须核完整实际Shao/Mathlib public import闭包和pins，不改cache/重做旧成功proof。

原固定p/q/eps/P先于未来r/J/n选择，本精确identity不许按J/n重选q/ell；均值/协方差gap的原source消费由G独立承担，此处不重做或隐藏。真实正actual项<=U16b raw positive项可由真概率finite的measureReal_mono及非负权重得，在后续19组合时实际证明，不能误称精确等式。当前不是有限层limit或全部19，不因多一个相位接口称root闭合。

新作者target/Audit仅指定server严格-DautoImplicit=false、CPU14–17/native-M8192-j4/lane1heavy；禁止ulimit-v/改心跳语义/干预外部CPU0–9/80GiB任务。唯一reviewer只读noLean/probe/rebuild/spawn/cachewrite/raw完整log下载，传递仅propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。所有根A/B/C/D OPEN，beta<2/5仅充分修复，无最弱/最优/新颖性主张。
