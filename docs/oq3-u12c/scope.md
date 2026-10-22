# OQ3-U12c：中心联合投影的真实二阶矩与有限阶段实例

冻结候选v1，PROPOSED；尚无实现。拟文件 `Shao/OQ3/NormalTangentMoments.lean`，导入 `Shao.OQ3.NormalTangentGaussian`，namespace Shao.OQ3，open MeasureTheory，open scoped Matrix，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，309–345，特别335–343。为后继特征函数二阶展开绑定真实中心投影、可积性和二阶矩；最后一个目标在同一实际有限atomicMeasure上消除均值输入。当前不使用缺失CLT/Taylor缓存，不声称特征函数幂极限。

## 冻结定义与目标

```lean
def centeredNormalProjection (q a v s x : ℝ) : ℝ :=
  v * (normalValue x - q) + s * (x - a)

theorem centeredNormalProjection_memLp_two (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a v s : ℝ) :
    MemLp (centeredNormalProjection q a v s) 2 mu

theorem centeredNormalProjection_integral_zero (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    (∫ x : ℝ, centeredNormalProjection q a v s x ∂mu) = 0

theorem centeredNormalProjection_second_moment (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (v s : ℝ) :
    (∫ x : ℝ, (centeredNormalProjection q a v s x) ^ 2 ∂mu) =
      normalTangentQuadratic mu v s

theorem finite_atomic_normal_tangent_moments (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ) (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j) :
    IsProbabilityMeasure (atomicMeasure (finiteMass ell p r J)) ∧
      (∫ x : ℝ, x ∂atomicMeasure (finiteMass ell p r J)) = q / 4 ∧
      (∫ x : ℝ, normalValue x ∂atomicMeasure (finiteMass ell p r J)) = q ∧
      ∀ v s : ℝ,
        MemLp (centeredNormalProjection q (q / 4) v s) 2
          (atomicMeasure (finiteMass ell p r J)) ∧
        (∫ x : ℝ, centeredNormalProjection q (q / 4) v s x
          ∂atomicMeasure (finiteMass ell p r J)) = 0 ∧
        (∫ x : ℝ, (centeredNormalProjection q (q / 4) v s x) ^ 2
          ∂atomicMeasure (finiteMass ell p r J)) =
            normalTangentQuadratic (atomicMeasure (finiteMass ell p r J)) v s
```

一公开定义、四公开目标。所有随机变量积分/可积性都在显式同一mu或同一实际finiteMass原子律下，q/a只在中间两目标通过真实均值等式使用。首目标对任意中心q/a成立，因为有界支撑使投影多项式的平方真实可积；可用真实平方可积等价MemLp2，不能以总化二阶矩数值替代。

第二目标先证明Y与id真正可积，再合法移出线性组合/常数并使用实际均值。第三目标先建立(Y-q)²、(X-a)²和(Y-q)(X-a)真实可积，再展开平方并逐项积分。Var(Y)=integral(Y-q)²、Cov(Y,X)=integral(Y-q)(X-a)、Var(X)=integral(X-a)²须在真实概率/可测及均值条件下绑定，结果是U12b actual normalTangentQuadratic，不是另造形式二次型。

最后目标实际使用同一ell/q/p/r/J的有限四约束与非负质量，不调用采用另一组p/q的存在性族。有限质量权重真正HasSum1给真实概率；约束E(X²)=q和E(X²−4X)=0给E X=q/4，真实Y=8X−X²给E Y=q。所有v/s然后共用这一个实际有限律与这两个中心，真MemLp2/均值零/二阶矩接口实例化。hp/hr仅需非负，不要求无关全无限严格正或Summable r；finiteMass零延拓本来有有限支撑。若参数q与真实非负四约束不相容，前提本身无模型，而非对任意q给概率存在性。

本单元提供后继一维线性投影的实际中心与二阶矩输入。没有把这些矩结论当作Taylor余项、n次幂极限、Gaussian积分极限交换、Fourier反演、完整LLT、实际hW或根闭合。U12b须先完成独立完整审查，本候选再串行独立声明/source审查；批准前不实现。根A/B/C/D保持OPEN。
