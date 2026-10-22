# OQ3-U10a：真实高斯曲边界积分与修正常数

冻结候选v1，PROPOSED；尚无实现。拟文件 `Shao/OQ3/GaussianBoundaryConstant.lean`，导入 `Shao.OQ3.CorrectedScaleContinuity`、`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`、`Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`、`Mathlib.MeasureTheory.Integral.Prod`。namespace Shao.OQ3，open MeasureTheory，noncomputable section。

来源：R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，411–444，特别(20)。目标是把实际标准高斯两尾构成的完整连续边界积分算出，并接到现有实际协方差定义的 correctedInverseScale。不是有限阶段LLT、全层极限或尖点Euler–Maclaurin。

## 冻结定义与目标

```lean
def gaussianBoundaryWeight (kappa d : ℝ) : ℝ :=
  ∫ z : ℝ in {z : ℝ | -((z / kappa) ^ 2) ≤ d},
    Real.exp (-(z ^ 2) / 2) / Real.sqrt (2 * Real.pi)

def gaussianBoundaryProfile (ell kappa d : ℝ) : ℝ :=
  Real.exp (-ell * d) * gaussianBoundaryWeight kappa d

def boundaryKappa (q : ℝ) (mu : Measure ℝ) : ℝ :=
  Real.sqrt q / (4 * Real.sqrt (transverseVariance mu))

theorem gaussianBoundaryWeight_eq_piecewise (kappa : ℝ) (hk : 0 < kappa) (d : ℝ) :
    gaussianBoundaryWeight kappa d =
      if 0 ≤ d then 1 else
        (2 / Real.sqrt (2 * Real.pi)) *
          ∫ z : ℝ in Set.Ioi (kappa * Real.sqrt (-d)), Real.exp (-(z ^ 2) / 2)

theorem gaussianBoundaryProfile_integrable (ell kappa : ℝ)
    (hell : 0 < ell) (hk : 0 < kappa) (hgap : 2 * ell < kappa ^ 2) :
    Integrable (gaussianBoundaryProfile ell kappa)

theorem integral_gaussianBoundaryProfile (ell kappa : ℝ)
    (hell : 0 < ell) (hk : 0 < kappa) (hgap : 2 * ell < kappa ^ 2) :
    (∫ d : ℝ, gaussianBoundaryProfile ell kappa d) =
      kappa / (ell * Real.sqrt (kappa ^ 2 - 2 * ell))

theorem boundaryKappa_sq (q : ℝ) (mu : Measure ℝ) (hq : 0 < q)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det) :
    boundaryKappa q mu ^ 2 = q * normalVariance mu / (16 * (parabolaCovariance mu).det)

theorem gaussianBoundary_constant_eq_corrected (ell q : ℝ) (mu : Measure ℝ)
    (hell : 0 < ell) (hq : 0 < q) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det)
    (hR : 0 < normalVariance mu - (32 * ell / q) * (parabolaCovariance mu).det) :
    (1 / Real.sqrt (normalVariance mu)) *
        (∫ d : ℝ, gaussianBoundaryProfile ell (boundaryKappa q mu) d) =
      correctedInverseScale ell q mu
```

三公开定义、五公开目标。积分均为Lebesgue上的真实Bochner积分；Integrable是独立公开结论，不能利用不可积函数的总化积分0伪造等式。标准高斯密度是 exp(-z²/2)/sqrt(2pi)，正分母和整体积分1必须证明。Weight定义采用对二次边界的高斯积分；首目标必须真证明它恰为源文的1/两侧高斯尾分段函数，不能只把源g重新命名。

计划路线：对固定z，边界条件等价于 d≥-(z/kappa)²；真实∫_{该半线}exp(-ell*d)dd=exp(ell*(z/kappa)²)/ell，ell>0保证可积。把它乘以高斯密度后，z方向成为严格正系数 b=1/2-ell/kappa² 的Gaussian。先用参数可测性、每个切片的真实Integrable以及该Gaussian控制证明二维核可积，再作Fubini换序，不能先使用未经证明可积的Bochner交换。

首目标d≥0时边界集合是全集，规范化Gaussian积分给1；d<0时集合为两个外侧半线，端点零测，偶性给二倍右尾。这一目标包括d=0，kappa>0，不把kappa=0作为物理定义域。

最后两个目标使用现有 normalVariance、transverseVariance=(det实际parabolaCovariance)/normalVariance、correctedInverseScale 的原定义。真实S>0、D>0和q>0使kappa正且平方为q*S/(16D)；真实R=S-32ellD/q>0推出kappa²>2ell，所有平方根/逆分母均在严格正域。正根和域条件必须消费，不能只平方后忽略符号。U7及U11d已审源原子律可提供上述前提，本单元不另选p/q/r、不把所有Measure无条件视为概率。

服务器现有固定版本的GaussianIntegral、ImproperIntegrals及Integral.Prod缓存可导入。仅API探针确认实际Gaussian积分/可积性、指数半线积分与integrable_prod_iff及Fubini签名；尚无本单元实现/编译/完整独立票。必须先独立声明与来源审查，未通过前不实现。无新公理、无近似积分/数值积分代替解析证明、无LLT/尖点常数差/实际hW或根闭合主张。根A/B/C/D保持OPEN。
