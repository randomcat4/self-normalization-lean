# OQ3-U12f：带有界层位移的截断中心Fourier积分极限

冻结候选v1，PROPOSED；尚无实现，独立声明门通过前不得实施。拟文件 `Shao/OQ3/CentralFourierIntegral.lean`，导入 `Shao.OQ3.NormalTangentPowerLimit`、`Shao.OQ3.NormalTangentDomination`、`Mathlib.MeasureTheory.Integral.DominatedConvergence`；namespace Shao.OQ3，open MeasureTheory Filter，noncomputable section。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，309–345，特别335–343。目标把真实点态幂极限、增长窗口共同Gaussian支配及U12b真实Gaussian全积分连接，包含有界法向层位移d_n的Fourier相位。当前不做格点Fourier反演、格点归一化或条件Lévy，不能记作混合LLT已闭合。

## 候选定义与完整目标

```lean
def centralFourierIntegrand (mu : Measure ℝ) (q a delta s : ℝ)
    (d : ℕ → ℝ) (n : ℕ) (v : ℝ) : ℂ :=
  (Set.Icc (-delta * Real.sqrt (n : ℝ)) (delta * Real.sqrt (n : ℝ))).indicator
    (fun w : ℝ =>
      Complex.exp (((-(w * d n / Real.sqrt (n : ℝ)) : ℝ) : ℂ) * Complex.I) *
        (centeredNormalTangentCharacteristic mu q a
          ((Real.sqrt (n : ℝ))⁻¹ * w) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n) v

theorem centralFourierIntegrand_integrable (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (q a delta s : ℝ) (d : ℕ → ℝ) (n : ℕ) :
    Integrable (centralFourierIntegrand mu q a delta s d n) (volume : Measure ℝ)

theorem centralFourierIntegrand_tendsto (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (delta : ℝ) (hdelta : 0 < delta)
    (s : ℝ) (d : ℕ → ℝ) (hd : ∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) (v : ℝ) :
    Tendsto (fun n : ℕ => centralFourierIntegrand mu q a delta s d n v)
      atTop (nhds (Complex.exp ((-normalTangentQuadratic mu v s / 2 : ℝ) : ℂ)))

theorem exists_centralFourierIntegral_tendsto (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : ℝ) (d : ℕ → ℝ),
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
        Tendsto (fun n : ℕ =>
          ∫ v : ℝ, centralFourierIntegrand mu q a delta s d n v ∂(volume : Measure ℝ))
          atTop (nhds (((Real.sqrt (2 * Real.pi / normalVariance mu) *
            Real.exp (-(transverseVariance mu * s ^ 2) / 2)) : ℝ) : ℂ))
```

一公开定义、三公开目标。定义是真实mu的中心特征函数幂乘实际层位移相位，再作增长实区间的零延拓；所有外层积分显式为同一标准实Lebesgue测度，随机积分始终在mu下。n=0时逆sqrt按库总化，相位及零次幂合法定义，窗口为单点、零延拓函数Lebesgue积分为0；不得在此初项消去sqrt。

首目标不需要delta正性或随机有界支撑：固定n的相位和characteristic连续，复范数≤1；窗口可测、紧且有限体积，故零延拓真Integrable。负delta给空窗口（n>0），也正确。第二目标只需delta>0及真正有界d序列；固定v最终进入窗口，d_n/sqrt(n)→0由真实界和sqrt趋∞得到，不要求d_n本身收敛。相位趋1，再乘U12d的同一mu点态幂极限。此阶段不需要S/D正性，退化方向也允许。

第三目标在全部s/d之前从U12e选共同delta/c。对每个固定s，eventual阈值在全部v之外；增长窗口中，模长1的真实位移相位不改变U12e的exp(−c v²)界，窗口外函数为0。因此有真正全实v的eventual AE共同可积支配；每项真可测/可积由首目标给，点态极限由第二目标给，再用固定库filter版支配收敛交换极限与真实Lebesgue积分。最终极限复指数是实Gaussian的嵌入，须明确实到复积分转换，再用U12b的actual S与transverseVariance真实全积分给所列常数。不能在这一过程将actual Q替换为任意形式矩阵。

hd使用全序列统一实界；实际O(1)层序列可通过有限初项补界满足该条件，但本单元不把未形式化的这一转换作为隐含假设。没有要求d_n格点可达：这里仅分析中心Fourier积分，格点可达性与反演恒等式属后续门。delta先于s/d，M和每个s的eventual阈值可在其后；delta不可逐s或逐d重选。

环境：Mathlib.MeasureTheory.Integral.DominatedConvergence已有olean。固定源SHA256 `56394aacfe591230d26a1d93641f2a1d3e3a3eae4fcfe772775533a1da295833`，68–77的filter版实际需要eventual AEStronglyMeasurable、eventual AE共同bound、真实Integrable bound及AE点态Tendsto；使用该版本才能处理U12e只在最终n成立的统一界，不能全n冒用。U12d完整独立票先完成，本候选再独立声明审查，批准前不实施。根A/B/C/D全部OPEN。
