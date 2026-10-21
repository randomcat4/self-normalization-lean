# OQ3-U12d v2：有界相位三阶余项与真实中心联合幂极限

冻结候选v2，PROPOSED；尚无实现，独立声明门通过前不得实施。拟文件 `Shao/OQ3/NormalTangentPowerLimit.lean`，导入 `Shao.OQ3.NormalTangentMoments`、`Shao.OQ3.FiniteFarArc`、`Mathlib.Analysis.SpecialFunctions.Complex.LogBounds`；namespace Shao.OQ3，open MeasureTheory Filter，open scoped Matrix，noncomputable section。

v1只是从未冻结/审查/实施的候选，原文件twenty-sixth-unit-scope.md保留。v2改用已有缓存中的Complex.exp_bound和通用指数幂极限，直接证明有界实际投影的三阶余项，因而无需缺失CLT/Taylor缓存，也不需要方差归一化、hQ>0或正定协方差。变化在本候选中明确列出，不据此更改任何已冻结单元的前提。原root缓存请求可供后继工作使用，不再是本候选的实施依赖。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，309–345，特别339–343。只证明实际联合中心特征函数在sqrt(n)尺度的点态n次幂极限，不包含极限积分交换、Fourier反演、条件Lévy或混合LLT。

## 候选完整类型

```lean
theorem centeredNormalTangentCharacteristic_cubic_remainder (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ u : ℝ, |u| ≤ delta →
      ‖centeredNormalTangentCharacteristic mu q a (u * v) (u * s) -
        (1 - ((normalTangentQuadratic mu v s * u ^ 2 / 2 : ℝ) : ℂ))‖ ≤
          C * |u| ^ 3

theorem centeredNormalTangentCharacteristic_power_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    Tendsto (fun n : ℕ =>
      (centeredNormalTangentCharacteristic mu q a
        ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n)
      atTop (nhds (Complex.exp ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ)))

theorem finite_atomic_normal_tangent_power_tendsto (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ) (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j)
    (v s : ℝ) :
    Tendsto (fun n : ℕ =>
      (centeredNormalTangentCharacteristic (atomicMeasure (finiteMass ell p r J))
        q (q / 4) ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n)
      atTop (nhds (Complex.exp
        ((-normalTangentQuadratic (atomicMeasure (finiteMass ell p r J)) v s / 2 : ℝ) : ℂ)))
```

零定义、三个公开目标。首目标在固定同一mu/q/a/v/s后选C/delta，随后对该整个u窗口统一。真实连续有界投影Z=v(Y−q)+s(X−a)在同一mu下真MemLp2，EZ=0、EZ²=actual Q；由实际AE上界取得M>0使|Z|≤M。选delta≤1/(M+1)，保证|u|≤delta时AE有‖i uZ‖≤1。Complex.exp_bound在n=3给真正点态三阶余项界；三个有限多项式项、指数及余项先真可积，再合法积分，使用概率质量1与两个真实矩给本结论。C可依赖固定方向，但不能依赖随后u；零方向/Q=0仍合法，不以除零归一化处理。

第二目标取u_n=1/sqrt(n)。n最终≥1，sqrt正及平方=n都须明确提供。三阶余项在乘n后由C/sqrt(n)控制并趋0，因此真实特征函数满足1−Q/(2n)+o(1/n)。固定库Complex.tendsto_pow_exp_of_isLittleO_sub_add_div给所列n次幂极限；n=0按库总化逆与零次幂处理，不在非法除法中使用。此点态极限不要求Q严格正，也不要求方向非零；退化的Q=0给极限1。没有把各n不同的mu或中心代进来。

第三目标从U12c取得同一finiteMass真实概率与EX=q/4、EY=q，以及真实AE支撑。全部v/s在这个同一有限倾斜律下实例化第二目标；J0与非负零质量允许，任意r只用有限前缀而不要求Summable。正定协方差将在中心Gaussian可积/LLT阶段另外消费，不能反过来暗加为本点态幂极限的必要前提。

外部库归属与环境：固定mathlib807d3836的Analysis/Complex/Exponential.lean377处Complex.exp_bound（需‖z‖≤1、n>0）与Analysis/SpecialFunctions/Complex/LogBounds.lean371–382处Complex.tendsto_pow_exp_of_isLittleO_sub_add_div（需实际little-o）均为现有结果，本项目只在实际源律上完成输入证明。LogBounds.olean已只读确认存在；其实际导入和前置须由独立声明审查再核。未改缓存、pins或共享定义。U12e完整证明票之后再串行审查本候选；声明批准前不实施。所有根A/B/C/D仍OPEN。
