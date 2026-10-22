# OQ3-U17l：实际Gaussian负曲边概率的正Laplace混合身份

冻结v1，DECLARATION_REVIEW_REQUESTED_AFTER_U17K_ENTIRE_FINAL_READ；未批准/未实施。拟Shao/OQ3/GaussianBoundaryLaplaceMixture.lean；imports Shao.OQ3.SourceGaussianBoundaryProfile、Mathlib.Analysis.Calculus.ParametricIntegral、Mathlib.Analysis.Calculus.MeanValue、Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus；namespace Shao.OQ3/open MeasureTheory Filter/open scoped Topology Interval/noncomputable section。0公开DEF、1完整公开合取target（真实IntegrableOn和实际Gaussian密度曲边身份不拆包装节点）。K完整312行CORRECT proof终票lead已全文读后才冻结；08:47:59UTC U18a两root及原51项仍缺，root唯一cachewriter。整份独立声明终票全文读前不写本源/Lean probe。

原始来源current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，411–421、448–481。原始目标→原25实际负半轴Gaussian曲边的格点正间隙。剩余关键义务→已有actual Gaussian概率/密度profile尚无真实正指数混合表示，不能据总化积分身份直接交换格和与积分或宣称凸梯形正差。本模块消除→所有κ>0、x≥0的实际gaussianBoundaryWeight κ (−x)与无参数正Cauchy密度加指数核之间的准确积分身份，包含x0、并先给真正IntegrableOn。直接消费者→原25格和减连续积分的统一h*sqrt(h)正下界；K已将原actual sourceGaussianLayerWeight接至该真实密度profile。未完成→原24精确ζ系数渐近/原25uniform下界本身、hcont真实生产者U18a、无条件15/19、字面Φ/CDF、rotation/hW/generalKL/所有根。

```lean
theorem gaussianBoundaryWeight_neg_laplace_mixture
    (kappa x : ℝ) (hk : 0 < kappa) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ =>
      Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2))
      (Set.Ioi 0) ∧
    gaussianBoundaryWeight kappa (-x) = (2 / Real.pi) *
      (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-((kappa ^ 2 / 2) * (1 + t ^ 2)) * x) / (1 + t ^ 2))
```

独立审查必须先仅actual唯一完整TYPE盲译并持久化，再scope/R1与primary来源、实际主API/公开可达、最后依赖/pins/cache。没有公开DEF。作者implementation/candidate/future笔记不可读。kappa/x是任意真实正参数及非负位移；x0不能删除，右端Integrator是默认真实Lebesgue的Ioi0 restriction，不是输入μ或人为概率实例。分母1+t²全实严格正，κ²/2真实正；不得对缺失可积的实总化积分默认值推等式。

数学primary核对为NIST DLMF7.7.1 https://dlmf.nist.gov/7.7.E1 的正实轴恒等式（取z=κsqrt(x/2)），此处不导入erfc或新增公理；形式证明必须从已接受gaussianBoundaryWeight真实标准密度定义及实际Gaussian/积分微分API自行完成。DLMF不是本项目已形式化定理，不宣称该经典公式新颖。

真积分门：对x≥0实际核非负且≤(1+t²)^−1，后者已有真Integrable；真实x0质量来自半线反正切积分与标准Gaussian全质量，不靠toReal无限消失。若采用积分号下微分，必须先有实际核真可积、导数measurable、参数邻域在积分变量外统一的可积主控及真实HasDerivAt；不得交换无主控导数。Gaussian负曲边的尾积分/端点/平方根正域须逐门保全，x0须单独或由真实连续极限处理，不能假设0处可微。若用Fubini/Tonelli则先证明相应非负／真可积门再转real。本target不假设混合身份、原EM/ζ、hcont/Summable或额外小κ条件。

初始实际API索引：GaussianBoundaryConstant20–25真实weight/profile、52–58真实piecewise Gaussian尾；ImproperIntegrals274–289 inv_one_add_sq真可积与Ioi反正切积分；GaussianIntegral115–117 Gaussian真可积、289–299真实halfGaussian积分；ParametricIntegral284–302真实dominated derivative API；IntervalIntegral.Basic1172–1180尾积分相减的真Integrable门；FundThmCalculus931–939 continuous primitive；MeanValue767–771开放连通集deriv0常值。正式独立门须核其实际类型/实现与公开图，不能凭文件名猜API。

08:46:53UTC真实词法剥嵌套注释/行注释/字符串闭包55Shao/2905Mathlib，全部源/现成olean齐，metadata gaussian-laplace-mixture-candidate-cache.json（侦察时K仍provisional，但冻结前其完整终票已读）。未运行Lean/probe/下载cache/编依赖/改pins，共享cache及integration归root。K冻结source22df4806e0179c5dc1ea70f759895bdd6a8610ae1f212c3e16b38d0bf6282515，proof d5d40a8e834c5bd70f0abf73a7536e7e235e1e1c5a0586d2dd7ed4e31da64880。

p/q/eps/P先于r/J/n；beta<2/5只是充分修复，无最优/最弱/根闭主张。全部作者Lean仅指定server CPU14–17/native-M8192-j4/strict-DautoImplicit=false/lane1heavy；禁ulimit-v/心跳或语义弱化/干预外部CPU0–9的10核80GiB任务。reviewer只读noLean/#check/probe/rebuild/cachewrite/raw全日志复制/spawn/commit/source或旧票编辑。传递公理仅propext/Classical.choice/Quot.sound，禁sorry/admit/newaxiom/unsafe/native_decide/implemented_by。所有root A/B/C/D OPEN。
