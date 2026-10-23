# U22a 冻结：开放真实积分域上的二次倾斜矩与方向累积量

2026-10-23，FROZEN_BEFORE_IMPLEMENTATION。math-theorem与当前精简规则；作者和最终完整语义/证明审查分离，最终审查用fresh gpt-6.1-sol/xhigh。PR173由root验收，本单元独立继承正式v43 accepted d80ba2a19fca34aa6e5dd765d6091900fe0c09c4，不依赖未整合173，不重复既有合格门。无新行政模型上下文或专属执行控制包装。

来源：只读R2 report.md38–60、83–92与root-contract第2/4节。原B要求在K有限的开邻域上把真实倾斜均值/协方差绑定实际log-partition导数，不能假设目标等式、用不可积积分默认0或用特定源律接口冒充任意mu。这里先交付精确承重子依赖：任意真实mu、任意真实积分域内theta的指数积分比与可积等价；theta在该域内部时，生产真实倾斜概率/矩及全部方向一、二阶累积量。方向导数不是完整Fréchet Hessian，后者与局部均值逆、原B分析链保持OPEN。

拟模块Shao.OQ3.QuadraticTiltCumulants，namespace Shao.OQ3，open MeasureTheory，open scoped Matrix Topology NNReal ENNReal，noncomputable section。0公开DEF，2公开THM。精确imports和完整TYPE：

```lean
import Shao.Probability.BivariateLegendre
import Shao.OQ3.RegularCovariance
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Measure.Tilted
```

```lean
theorem quadratic_tilt_mgf_identity
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta d : ℝ × ℝ)
    (htheta : theta ∈ Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
    let Z : (ℝ × ℝ) → ℝ := fun p =>
      ∫ x : ℝ, Real.exp (p.1 * x + p.2 * x ^ 2) ∂mu
    IsProbabilityMeasure nu ∧ 0 < Z theta ∧
      ∀ t : ℝ,
        (Integrable (fun x => Real.exp (t * F x)) nu ↔
          (theta.1 + t * d.1, theta.2 + t * d.2) ∈
            Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2))) ∧
        ProbabilityTheory.mgf F nu t = Z (theta.1 + t * d.1, theta.2 + t * d.2) / Z theta

theorem open_domain_quadratic_tilt_directional_cumulants
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (theta : ℝ × ℝ)
    (htheta : theta ∈ interior
      (Shao.Probability.bivariateMGFDomain mu (fun x : ℝ => (x, x ^ 2)))) :
    let nu : Measure ℝ := mu.tilted (fun x => theta.1 * x + theta.2 * x ^ 2)
    let means : Fin 2 → ℝ := ![∫ x : ℝ, x ∂nu, ∫ x : ℝ, x ^ 2 ∂nu]
    let D : Matrix (Fin 2) (Fin 2) ℝ := parabolaCovariance nu
    IsProbabilityMeasure nu ∧
      MemLp (fun x : ℝ => x) 2 nu ∧ MemLp (fun x : ℝ => x ^ 2) 2 nu ∧
      ∀ d : ℝ × ℝ,
        let F : ℝ → ℝ := fun x => d.1 * x + d.2 * x ^ 2
        let f : ℝ → ℝ := fun t => Real.log
          (∫ x : ℝ, Real.exp
            ((theta.1 + t * d.1) * x + (theta.2 + t * d.2) * x ^ 2) ∂mu)
        0 ∈ interior (ProbabilityTheory.integrableExpSet F nu) ∧ MemLp F 2 nu ∧
          (∀ k : ℕ, Integrable (fun x => (F x) ^ k) nu) ∧
          HasDerivAt f (d.1 * means 0 + d.2 * means 1) 0 ∧
          HasDerivAt (deriv f)
            (d.1 ^ 2 * D 0 0 + 2 * d.1 * d.2 * D 0 1 + d.2 ^ 2 * D 1 1) 0
```

量词与真实性：mu任意实概率，无有界/原子/中心化/正定/WC假设。第一目标只要求theta真实指数可积，比例恒等式对全部t成立，并显式交付可积等价，不能把域外总化恒等式当导数。第二目标只要求theta在实际二维指数积分域内部；全部方向d（含0）保留，矩阶k含0。nu、means、D、F、f均为字面真实对象；nu不是自由概率，D不是caller矩阵，一二阶导数/矩存在性不是输入。全部结论仅在内部点及其合法参数线邻域使用；不要求原mu本身具有未倾斜高阶矩。

必要实际API已定向读：Tilted.lean126–136、230–249、293–309提供真倾斜概率、指数积分比、真实integrable_tilted_iff；MGFAnalytic.lean43–64、171–242提供内部积分域下真mgf/cgf导数及二阶矩公式；IntegrableExpMul中内部域给矩/MemLp。相应MGFAnalytic/IntegrableExpMul现成olean已一次确认存在，不重建缓存。开放域经连续参数线给0的真实一维邻域，随后log比恒等式只在该邻域转为常数加真实cgf。完整Fréchet可微性不得仅由所有方向导数推出。

执行：先冻结本完整TYPE再实现；复用已有目标Lean/actual-owner审计方式，全部仅serverCPU14–17/native8192MiB/j4/autoImplicit=false/单heavy；首成功证据按源hash复用，完整失败保留，不重复v43/pins/smoke/cache扫描。只在own新branch/source内写，不改共享定义/imports/cache。最终完整源码、所有actual owner/private/generated TYPE、传递公理及来源映射须fresh独立审查；标准三公理白名单，无sorry/admit/newaxiom/unsafe/native_decide。当前不关闭B/C/D，不作最优性或新颖性声明。
