# OQ3-U13a：实际单格点坐标的有限样本Fourier反演恒等式

冻结v2，DECLARATION_REVIEW_PENDING；尚无实现，提交独立声明门。拟文件 `Shao/OQ3/NormalLayerFourier.lean`，导入 `Shao.OQ3.SampleBoundary`、`Shao.OQ3.FiniteFarArc`、`Mathlib.Analysis.SpecialFunctions.Integrals.Basic`、`Mathlib.MeasureTheory.Integral.Pi`；namespace Shao.OQ3，open MeasureTheory，open scoped BigOperators Matrix，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，309–345，尤其333–343的只对Y作格点反演。当前仅证明真正有限样本的精确反演与同一有限律实例，不证明极限、基本区间积分的中心/远弧组合或条件Lévy。

v2仅显式追加已有缓存的proof-only Integral.Pi导入；它公开转导Integral.Prod，提供有限产品积分分解及Fubini。两定义体、五完整类型、默认测度与假设完全不变。旧v1冻结scope原样保留；批准前不实施。

## 冻结定义与完整类型

```lean
def normalLayerIntegrand (q a d s : ℝ) (n : ℕ) (z : Shao.Path n) : ℂ :=
  ({w : Shao.Path n | normalDeviation q w = d}).indicator
    (fun w : Shao.Path n => Complex.exp
      (((s * ((∑ i, w i) - (n : ℝ) * a) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * Complex.I)) z

def normalLayerCharacteristic (mu : Measure ℝ) (q a d s : ℝ) (n : ℕ) : ℂ :=
  ∫ z : Shao.Path n, normalLayerIntegrand q a d s n z
    ∂Measure.pi (fun _ : Fin n => mu)

theorem normal_lattice_character_orthogonality (h : ℝ) (hh : 0 < h) (k : ℤ) :
    ((h / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ in Set.Icc (-Real.pi / h) (Real.pi / h),
        Complex.exp (((t * (h * (k : ℝ)) : ℝ) : ℂ) * Complex.I)
          ∂(volume : Measure ℝ)) = if k = 0 then 1 else 0

theorem iid_centeredNormalTangentCharacteristic_power (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (q a t s : ℝ) (n : ℕ) :
    (∫ z : Shao.Path n, Complex.exp
      (((t * normalDeviation q z + s * ((∑ i, z i) - (n : ℝ) * a) : ℝ) : ℂ) * Complex.I)
        ∂Measure.pi (fun _ : Fin n => mu)) =
      centeredNormalTangentCharacteristic mu q a t s ^ n

theorem normalLayerIntegrand_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a d s : ℝ) (n : ℕ) :
    Integrable (normalLayerIntegrand q a d s n) (Measure.pi (fun _ : Fin n => mu))

theorem normal_layer_Fourier_identity (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a h d s : ℝ) (hh : 0 < h)
    (hgrid : ∀ᵐ x ∂mu, ∃ k : ℤ, normalValue x = h * (k : ℝ))
    (n : ℕ) (hlayer : ∃ k : ℤ, d + (n : ℝ) * q = h * (k : ℝ)) :
    normalLayerCharacteristic mu q a d s n =
      ((h / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / h) (Real.pi / h),
          Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
            centeredNormalTangentCharacteristic mu q a t
              ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n ∂(volume : Measure ℝ))

theorem finite_atomic_normal_layer_Fourier_identity (ell q : ℝ) (p : Fin 4 → ℝ)
    (r : ℕ → ℝ) (J : ℕ) (hM : (constraintMatrix ell).det ≠ 0)
    (hc : (constraintMatrix ell) *ᵥ p = constraintTarget q)
    (hp : ∀ i, 0 ≤ finiteBase ell p r J i) (hr : ∀ j, 0 ≤ r j)
    (d s : ℝ) (n : ℕ)
    (hlayer : ∃ k : ℤ, d + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) :
    normalLayerCharacteristic (atomicMeasure (finiteMass ell p r J)) q (q / 4) d s n =
      ((dyadicMesh J / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ in Set.Icc (-Real.pi / dyadicMesh J) (Real.pi / dyadicMesh J),
          Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) *
            centeredNormalTangentCharacteristic (atomicMeasure (finiteMass ell p r J))
              q (q / 4) t ((Real.sqrt (n : ℝ))⁻¹ * s) ^ n ∂(volume : Measure ℝ))
```

两公开定义、五公开目标。normalLayerCharacteristic是未归一化的真实层特征积分，s=0时是该层实际概率（嵌入复数），不是条件概率律的特征函数；不以层概率为分母。所有外层Fourier积分显式volume，样本积分使用真实有限产品mu^Fin n。general q/a只是代数中心；精确反演不需要它们等于均值，也不需要协方差正性、随机支撑有界或最大格距。格点门是明确的零offset normalValue∈hℤ，所列有限源确实满足该门；没有把一般带offset格距擅自改为零offset。

首目标先区分k0，使用真实区间体积2pi/h和正h归一化。k非0时，连续指数在紧区间真可积，可转换到有向区间积分，实际复指数原函数积分式及端点exp(i pi k)=exp(−i pi k)给0。该端点恒等式需真正整数k，不能对任意实频率声称正交；h>0与pi>0保证端点顺序和所需非零分母。

第二目标将真实样本中心相位展开为各坐标中心相位之和，再用复exp(sum)=prod及真正有限产品积分分解；相位/乘积范数1、有限产品概率给真实可积先于分解。n0的空和/空积与零次幂都为正确值1。第三目标通过真实可测层事件与范数1指数在实际产品概率下给真可积，不能从总化积分定义猜测层积分存在。

第四目标从单坐标hgrid通过真实有限产品AE坐标与有限求和得到实际normalDeviation(q,z)−d∈hℤ，明确使用hlayer的d+nq格点相容门。在这个AE事件上，首目标就是层indicator。乘上真实切向相位、先证明在限制Lebesgue区间×产品样本概率下的联合Integrable，再合法Fubini；第二目标将内层样本积分变成同一actual characteristic的n次幂。复相位的负号、外部h/(2pi)和tangent频率s/sqrt(n)需逐一精确保留。

第五目标从同一finiteMass的真实有限四约束/非负质量取得概率，actual atomicMeasure_finiteMass_ae_range与stageAtom_normalValue_lattice给零offset格点门，h=dyadicMesh J>0；实例化第四目标，始终同一ell/q/p/r/J及q/q4中心。所有r只进入有限前缀，无需Summable；J0/零质量允许。hlayer是显式格点相容条件，比实际可达更宽但反演仍有效；n0时若d非0但相容，正交给0，d0给1。sqrt0逆与切向相位按库总化合法，不进行非法消分母。

拟环境所用现有固定API：Integrals.Basic242的intervalIntegral.integral_exp_mul_complex需要复系数非零，Complex.exp_eq_exp_iff_exists_int提供整数周期；有限产品积分分解、Products/Prod Fubini、actual probability product实例均须独立核前提与缓存。SampleBoundary已导入Common FiniteIID/FinitePath，公共文件只读。本冻结单元在U12f完整最终票已由lead全文读取后独立声明审查，批准前不实施。根A/B/C/D仍OPEN；没有Fourier积分渐近、条件归一化/Lévy、混合LLT、层支配、实际hW或根闭合主张。
