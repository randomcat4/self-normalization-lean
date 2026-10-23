# U22b 冻结：开放真实积分域上的全部加权矩Fréchet导数

2026-10-23，FROZEN_BEFORE_IMPLEMENTATION。U22a新source165行ea105db471a073ac5eca67b4f94ff986766fd3fe3685790fb4859497da49289a已首次完整server和首次全4owner公理门PASS，fresh完整proof审查运行；它是本单元明确的待独立接受直接依赖，不误标已合主干。当前单元先冻结精确声明，允许作者准备后继实现；不改U22a源/TYPE/既有成功证据。租约1只用于实际独立完整proof审查，不添行政模型上下文；相关依赖可合为一个实质milestone再PR。

原目标：R2 report.md38–60、83–92与root-contract第2/4节的任意真实倾斜law下实际均值/Hessian桥。U22a只给真实矩与所有方向累积量，不能据此宣布Fréchet微分。本单元生产完整参数空间R²上的真Fréchet导数，随后k=0/1/2和真实log/商求导可供actual gradient/Hessian与均值逆消费者；本单元本身不关闭这些消费者或原B。

拟模块Shao.OQ3.OpenDomainWeightedMoments；namespace Shao.OQ3，open MeasureTheory，open scoped Topology NNReal ENNReal，noncomputable section。0公开DEF，1公开THM；无额外caller可积支配函数/导数或bounded假设。

```lean
import Shao.OQ3.QuadraticTiltCumulants
import Mathlib.Analysis.Calculus.ParametricIntegral
```

```lean
theorem open_domain_weighted_moment_hasFDerivAt
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (k : ℕ) (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let I : ℕ → (ℝ × ℝ) → ℝ := fun n p =>
      ∫ x : ℝ, x ^ n * Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
    let pr0 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
    let pr1 : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
    Integrable (fun x : ℝ => x ^ k * Real.exp (theta.1 * x + theta.2 * x ^ 2)) mu ∧
      HasFDerivAt (I k) ((I (k + 1) theta) • pr0 + (I (k + 2) theta) • pr1) theta
```

精确范围：mu任意实概率，theta属于真实二维指数积分域内部，k任意自然数（含0）。I为字面真实带指数加权积分，不把不可积时默认0当目标。导数是整个R×R参数空间的HasFDerivAt，斜率两项实际积分及两个公开连续线性投影完全固定；不是只给方向导数或形式矩恒等式。没有中心化、非退化、bounded、WC、实际导数等式或支配函数作为caller输入。

必要真实支配须由原前提生产：开放性选择thetaPlus=(theta1,theta2+delta)仍在内部，delta>0，epsilon=delta/4。对|t1-theta1|<epsilon、|t2-theta2|<epsilon，以2|x|≤1+x²得到exp(t·W)≤exp(epsilon/2) exp(thetaPlus·W)。参数导数的算子范数由这同一指数乘[‖pr0‖|x|^(k+1)+‖pr1‖|x|^(k+2)]控制。thetaPlus上的真实tilt全阶矩和integrable_tilted_iff给该支配函数真Integrable。然后才可消费hasFDerivAt_integral_of_dominated_of_fderiv_le；不能借“所有方向导数存在”跳过此门，也不能调用别模块private helper。

执行约束：保持原精确TYPE，完整失败留server，首成功不重复，复用同版库和必要现成对象；所有Lean仅CPU14–17/native8192MiB/j4/autoImplicit=false/单heavy。root独占shared/cache/pins/imports/integration，现有read-only accepted-source-view只为Lean包根的实际执行需要复用，不复制或写缓存。最终新鲜完整语义/证明审查和全部actual owner/private/generated公理白名单门必需。原B及full Hessian/meaninverse、Edgeworth/胞/Laplace/远概率、原D仍不由本单元自动闭合；PR173/C由root裁决，不作新颖性或最优性声明。
