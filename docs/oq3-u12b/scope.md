# OQ3-U12b：真实法向/切向协方差与中心高斯积分

冻结候选v1，PROPOSED；尚无实现。拟文件 `Shao/OQ3/NormalTangentGaussian.lean`，导入 `Shao.OQ3.RegularCovariance`、`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`、`Mathlib.MeasureTheory.Measure.Lebesgue.Integral`。namespace Shao.OQ3，open MeasureTheory，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，238–258、309–345，特别341–343的联合协方差二次型与法向Gaussian积分。此单元把实际Cov(Y,X)与已有Delta=Cov(X,X²)绑定，证明实际二次型完成平方、正性与完整法向高斯积分；尚不证明特征函数Taylor幂极限或Fourier反演。

## 冻结定义与目标

```lean
def normalTangentQuadratic (mu : Measure ℝ) (v s : ℝ) : ℝ :=
  normalVariance mu * v ^ 2 +
    2 * ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu * v * s +
    ProbabilityTheory.variance (fun x : ℝ => x) mu * s ^ 2

theorem covariance_normal_id (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) :
    ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu =
      8 * parabolaCovariance mu 0 0 - parabolaCovariance mu 0 1

theorem normal_tangent_covariance_det (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) :
    normalVariance mu * ProbabilityTheory.variance (fun x : ℝ => x) mu -
      (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu) ^ 2 =
        (parabolaCovariance mu).det

theorem normalTangentQuadratic_complete_square (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hS : 0 < normalVariance mu) (v s : ℝ) :
    normalTangentQuadratic mu v s =
      normalVariance mu *
          (v + (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu /
            normalVariance mu) * s) ^ 2 +
        transverseVariance mu * s ^ 2

theorem normalTangentQuadratic_pos (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) (v s : ℝ) (hne : v ≠ 0 ∨ s ≠ 0) :
    0 < normalTangentQuadratic mu v s

theorem normalTangentGaussian_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (hS : 0 < normalVariance mu) (s : ℝ) :
    Integrable (fun v : ℝ => Real.exp (-(normalTangentQuadratic mu v s) / 2))

theorem integral_normalTangentGaussian (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (hS : 0 < normalVariance mu) (s : ℝ) :
    (∫ v : ℝ, Real.exp (-(normalTangentQuadratic mu v s) / 2)) =
      Real.sqrt (2 * Real.pi / normalVariance mu) *
        Real.exp (-(transverseVariance mu * s ^ 2) / 2)
```

一公开定义、六公开目标。默认v积分/Integrable均为同一实际实Lebesgue测度，显式导入Lebesgue.Integral；随机变量矩和协方差均在传入真实概率mu下。hb为实际源原子族已有的固定有界支撑门，足以证明id与id²真正MemLp2、全部协方差的实际可积门，不把总化variance/covariance当成无需矩条件的形式符号。

Y=normalValue=8X−X²。由真实Cov线性、对称及Cov(X,X)=VarX得C=Cov(Y,X)=8A−B，其中A=Delta00、B=Delta01；U7已审S=VarY=64A−16B+E，E=Delta11。因此S*A−C²=A*E−B²=detDelta。该变换的行列式绝对值1，没有误插8²因子，也没有将X方差当成Y方差。先证明真正MemLp2再消费covariance_fun_sub_left等线性接口。

完成平方只在S>0下作除法：Q(v,s)=S(v+(C/S)s)²+(D/S)s²，transverseVariance为实际D/S。若D>0且(v,s)不同时为0，则Q严格正；该正性前提单独保留，没有把所有Measure无条件视为正定。U7实际源族可提供S/D严格正。

最后两个目标只需S>0而不需要额外D>0：固定s时，exp(−Q/2)=exp(−(D/S)s²/2)乘系数S/2>0的平移Gaussian。实Lebesgue平移不变性保持真实Integrable及积分；先独立证明真正Integrable，再用完整Gaussian积分与正S的根号等式给sqrt(2pi/S)*exp(−tau²s²/2)。固定s的有限正指数因子无论tau²如何总是有限，不需要静默增添D>0；源物理解释由实际正定律供给。

此结果对应混合LLT证明中形式Gaussian积分的真实协方差/条件方差常数；没有证明实际特征函数在n缩放后的幂极限、积分极限交换、Fourier反演、Lévy收敛或源(15)/(19)。不选择不同p/q/r，根A/B/C/D仍OPEN。先独立声明/source审查，批准前不实现；不调用缺失CLT缓存，不写共享cache或新公理。
