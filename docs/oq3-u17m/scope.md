# OQ3-U17m：原25实际有限阶段Gaussian格和的统一正间隙

冻结v1，DECLARATION_REVIEW_REQUESTED_AFTER_U17L_ENTIRE_FINAL_READ；未批准/未实施。拟Shao/OQ3/SourceGaussianLatticeGap.lean；imports Shao.OQ3.GaussianBoundaryLaplaceMixture、Mathlib.Analysis.Calculus.Deriv.MeanValue、Mathlib.MeasureTheory.Integral.Prod、Mathlib.MeasureTheory.Integral.DominatedConvergence、Mathlib.Topology.Algebra.InfiniteSum.NatInt；namespace Shao.OQ3/open MeasureTheory Filter/open scoped Topology BigOperators Interval/noncomputable section。0公开DEF/1完整公开合取target（真整数Summable与实际正差不拆包装节点）。L完整397行CORRECT proof终票lead已全文读后正常发布PR128/headf879f4d2c7b768b938b32f08826963254fabc9d1才冻结本scope。09:38:18UTC freshU18a两root及原51项仍缺；root唯一cachewriter。整份独立声明终票全文读前不写本源/Lean probe。

原始来源current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，411–443及448–481、486–494。原始目标→原25同一实际有限阶段Gaussian格和相对原20连续corrected常数的统一正h^(3/2)间隙。剩余承重义务→L真positive混合身份尚未给真实可和/混合求和积分交换/连续积分交换/零层一次/端点抵消/统一正余量；一般矩阵或手工参数的格差包装不能代替实际stage结论。本模块消除→原stage同μ真实均值、支持、singleton正性生产S/D/T/ell-gap及方差上界后，给真正整数Summable及显式普适正差。直接consumer→原26的实际phase回返与对角n_J选择（仍须U18a真实hcont→无条件19）。未完成→原24精确ζ渐近/余项、hcont/无条件15/19、phase回返/diagonal实际nJ、Phi字面CDF、hW/generalKL及全部根。

```lean
theorem stage_sourceGaussianLayerWeight_lattice_gap
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight mu q sourceEll
      ((k : ℝ) * dyadicMesh J)) ∧
    correctedInverseScale sourceEll q mu +
      (dyadicMesh J * Real.sqrt (dyadicMesh J)) / (4096 * Real.pi) ≤
      (dyadicMesh J / Real.sqrt (normalVariance mu)) *
        ∑' k : ℤ, sourceGaussianLayerWeight mu q sourceEll
          ((k : ℝ) * dyadicMesh J)
```

独立门先只读实际唯一完整TYPE盲译并持久化，再scope/R1/数学与实际主API/公开可达，最后56项目/2905库闭包/pins/cache/hash。作者所有implementation/candidate/future/cusp笔记禁止读。无新公开DEF。输入μ是真概率而不要求atomicMeasure表示；J0保留；q区间、EY=q、EX=q/4、真实stageAE、所有真实singleton正性逐项保留。不添加手工S/D/T/κ/a/gap/Summable/hcont、uniform compactfamily或原EM/ζ假设。μ/J/q均同一组，实际sum和corrected常数不得换law。

这是一条直接证明原25的充分下界路线，公开结论写h*sqrt h/(4096π)，h=dyadicMesh J>0时等于h^(3/2)/(4096π)，可供原25取b=1/(8192π)>0、J0=0；这些选择只有本目标完整通过后才可计完成。比原25更强的全J版本不声称原24精确ζ或最优常数。p/q/eps/P先于r/J/n的原家族选择顺序保留；本∀μ/J/q接口本身不新选q或以n依赖参数代替固定q。β<2/5仍仅充分修复，无最优/最弱/新颖性主张。

必要分析门：实际g在正半轴=1，负半轴由L真实positive混合；乘exp(ell*x)后率s(t)=a(1+t²)−ell，a=κ²/2，必须先由实际stage门推出a>1/30>sourceEll>0才可作正率几何和/半轴积分。真正正负两列Summable及全整数Summable先于tsum重排，零只计一次。混合下的积分与格和交换必须先∀k真Integrable及积分范数和真Summable，或等价真实prod Integrable/Tonelli有限门；连续负半轴也须section真可积和真实norm积分可积后才Fubini。不能用总化实积分/tsum默认值抵消端点。

梯形指数余量R_s(h)=h/(exp(sh)−1)+h/2−1/s需要在s,h>0后证明0≤R≤h/2，sh≥4时R≥h/4。正k≥0部分与负k≥1部分的h/2项必须在真可积/真可和门后精确抵消；积分权2/(π(1+t²))的真实半轴质量1也须消费实际Cauchy积分。φ(t)=(t−2)exp(t)+t+2的真实微分/单调性可服务R非负，不能把该不等式当新增假设。统一正余量与具体4096π常数需独立核算，非借原24的未证EM。

源参数门：stageAE给真实hb；四基点正质量给一般μ S/D/T>0；X/X²真Integrable和MemLp2先于EX²=q、VarX=q−q²/16，再T≤VarX推出a>1/30。stage实际|Y|≤16在真实MemLp2/variance公式/积分上界后给S≤256、0<sqrtS≤16，不以总化variance代替二阶门。h=2^(-J)的正性/≤1必须真实证明，不能调用别模块private helper。

初始实际API：K公开stage_sourceGaussianLayerWeight_profile_and_integral给同μ真实函数身份/Integrable/原20常数；L公开gaussianBoundaryWeight_neg_laplace_mixture给所有κ>0/x≥0真实核Integrable与准确混合。Deriv.MeanValue437–440 monotone_of_hasDerivAt_nonneg；DominatedConvergence112–115 integral_tsum_of_summable_integral_norm消费各项真Integrable和积分norm真Summable；Prod230–242 integrable_prod_iff/prime先真meas/section/normintegral，再integral_integral_swap；ImproperIntegrals77–80/102–107 正确负rate的真exp可积/积分；Bochner.Set733–736 setIntegral_mono_set的真Integrable/非负/集合门；NatInt真实Summable/tsum reindex。每个都要读固定实际类型/实现/公开图，不凭文件名或物理cache猜可用。

常数核查可仅使用cached Trigonometric.Basic的Real.two_le_pi与sqrt(a)>1/6（a>1/30>1/36）。Mathlib.Analysis.Real.Pi.Bounds缺olean，当前imports不含它且无需π<4/π>3；不得lane补缓存。09:32:44UTC候选imports词法剥嵌套注释/字符串闭包56Shao/2905Mathlib源和现成olean全齐（当时L仍provisional，冻结前其397行终票已读接受），metadata source-gaussian-lattice-gap-candidate-cache.json；正式独立门须重新核，不能依作者candidate metadata。L源fd470e5ffcea5299222a570389ae9603beb1e78b34c065d637e26e08c76dd421，proof914e0bd66627f9812ab97a611ca0bdd0a37d030e4d4d1b9981c2e0be98986eee。共享cache/integration仅root。

作者全部Lean只指定server CPU14–17/native-M8192-j4/strict-DautoImplicit=false/lane1heavy。禁止ulimit-v、心跳或语义弱化、外部CPU0–9的10核80GiB任务干预。reviewer仅新票及授权远端副本写权、只读源/API，无Lean/#check/probe/rebuild/cachewrite/raw全日志复制/spawn/commit/source/旧票编辑。全传递公理仅propext/Classical.choice/Quot.sound，禁止sorry/admit/newaxiom/unsafe/native_decide/implemented_by。所有root A/B/C/D OPEN；此scope尚未批准/实施/计接受。
