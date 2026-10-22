# OQ3-U17k：实际源有限阶段Gaussian层密度与连续常数

冻结v1，DECLARATION_REVIEW_REQUESTED_AFTER_U17J_ENTIRE_FINAL_READ；未批准/未实施。拟Shao/OQ3/SourceGaussianBoundaryProfile.lean；imports Shao.OQ3.StageLayerSeriesLimit、Shao.OQ3.GaussianBoundaryConstant；namespace Shao.OQ3/open MeasureTheory Filter/open scoped Topology BigOperators/noncomputable section。0公开DEF、1完整公开目标（实际profile等价/Integrable/原20常数同一合取目标，不拆包装节点）。J完整338行CORRECT proof终票lead已全文读后才冻结本scope；08:06UTC U18a两root及原51项仍缺。整份独立声明终票全文读前不写本源/Lean probe。

原始来源current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，411–443及原20。原始目标→实际有限阶段F_J的Gaussian层概率和原20连续常数。剩余关键义务→J实际概率型Gaussian层权重未正式接到已有标准密度profile和源连续积分；一般连续常数API的S/D/hR不能偷当原模型手工输入。本模块消除→actual Gaussian map/标准密度身份、实际profile真可积、源stage实际均值/支持/正性推出全部参数门后的原20 corrected inverse scale。直接消费者→原25格和减连续积分的正间隙及原19常数比较。未完成→hcont真实生产者U18a/无条件15与19、字面Phi/CDF改写、cuspEM/rotation/hW/generalKL/所有根。

```lean
theorem stage_sourceGaussianLayerWeight_profile_and_integral
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    (∀ d : ℝ, sourceGaussianLayerWeight mu q sourceEll d =
      gaussianBoundaryProfile sourceEll (boundaryKappa q mu) d) ∧
    Integrable (sourceGaussianLayerWeight mu q sourceEll) ∧
      (1 / Real.sqrt (normalVariance mu)) *
        (∫ d : ℝ, sourceGaussianLayerWeight mu q sourceEll d) =
          correctedInverseScale sourceEll q mu
```

独立审查先实际唯一完整TYPE盲译并持久化，再scope/R1、全部实际主API/公开可达、最后依赖/pins/cache；没有公开DEF。作者candidate/future/implementation笔记不可读。μ/J/q/sourceEll在未来n/k/子列外固定，所有真实均值/AE stage/单点正性保留；不额外把S/D/T/hR当原模型新假设。p/q/eps/P先于r/J/n；beta<2/5只为充分修复，无最优/最弱/新颖性主张。

第一分支要证明同一actual Gaussian事件与gaussianBoundaryWeight的标准密度积分身份，不仅同名定义替换。实际gaussianReal_map_const_mul取sqrt(T)，先T>0/sq_sqrt/Real.coe_toNNReal取得真实NNReal方差一致；map_apply须有统计量及实际平方闭事件可测。q/T/kappa真正性后拉回平方事件，保全d<0/0/>0与严格/非严格边界，不非法开负平方根。标准Gaussian的integral_indicator/真有限概率及integral_gaussianReal_eq_integral_smul(v!=0)转真实标准密度，indicator可测再重排成已有profile。

源参数先stageAE→hb、hpos inl→真实正基点，调用一般μ S/D/T正性；不得仅atomic-only专用式。实际X/X² Integrable和MemLp2先于真实EX²=q及VarX=q−q²/16。transverseVariance_le_variance_id与q>1得q/(32T)>1/30>sourceEll，所有分母先正；T=D/S及q/S正给hR=S−(32ell/q)D>0。boundaryKappa正和真实平方公式给2ell<kappa²，再gaussianBoundaryProfile_integrable/gaussianBoundary_constant_eq_corrected，按第一分支真实函数等价传可积/积分。不能以总化integral/log/sqrt/toNNReal替代这些门。

初始实际API索引：Gaussian.Real273 integral_gaussianReal_eq_integral_smul需要v!=0、327 gaussianReal_map_const_mul精确方差mk(c²)*v、Map.map_apply需可测；GaussianBoundaryConstant20–28实际profile/kappa定义、52–58标准density-tail piecewise、200–209真Integrable与真实连续积分、233–247 kappa平方及corrected常数。G/StageSourceNegativeTail35–92是原stage实际参数已证producer的前置参考，内部private不能越权调用；本新证明须消费公开API或独立重证所需源参数。

07:54:45UTC双imports真实词法剥注释/字符串闭包54Shao/2905Mathlib源和现成olean全齐，metadata source-gaussian-profile-candidate-cache.json。J327line源4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d已获338line完整CORRECT终审。正式声明门仍独立核真实全闭包/API公开图/pins/hash；不下载cache/不编依赖/不更换pins/rebase/共享源复制。Root唯一cachewriter和integrationowner。

所有作者Lean仅指定server CPU14–17/native-M8192-j4/strict-DautoImplicit=false/lane1heavy；禁止ulimit-v/心跳或语义弱化/干预外部CPU0–9的10核80GiB任务。reviewer只读，noLean/#check/probe/rebuild/cachewrite/raw全日志复制/spawn/commit/source或旧票编辑。传递公理仅propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。此scope静态冻结不计已接受目标；所有root A/B/C/D OPEN。
