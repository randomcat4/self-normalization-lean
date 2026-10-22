# OQ3-U12e：实际中心弧的共同Gaussian支配

冻结候选v1，PROPOSED；尚无实现，独立声明门通过前不得实施。拟文件 `Shao/OQ3/NormalTangentDomination.lean`，导入 `Shao.OQ3.NormalTangentMoments`、`Shao.OQ3.FiniteFarArc`、`Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds`；namespace Shao.OQ3，open MeasureTheory Filter，noncomputable section。本候选不依赖U12d或缺失CLT/Taylor缓存。

来源R1 report.md SHA256 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`，309–345，特别中心弧Gaussian积分及远弧衰减之间的支配门。只证明真实中心弧模长及平方根尺度幂的可积Gaussian上界，尚不做极限积分交换或Fourier反演。

## 候选完整类型

```lean
theorem exists_normalTangentQuadratic_coercive (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det) :
    ∃ c : ℝ, 0 < c ∧ ∀ t s : ℝ,
      c * (t ^ 2 + s ^ 2) ≤ normalTangentQuadratic mu t s

theorem exists_centeredNormalTangentCharacteristic_gaussian_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ t s : ℝ,
      |t| ≤ delta → |s| ≤ delta →
        ‖centeredNormalTangentCharacteristic mu q a t s‖ ≤
          Real.exp (-c * (t ^ 2 + s ^ 2))

theorem exists_centeredNormalTangentCharacteristic_scaled_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) (hS : 0 < normalVariance mu)
    (hD : 0 < (parabolaCovariance mu).det) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∀ s : ℝ,
      ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
        |v| ≤ delta * Real.sqrt (n : ℝ) →
          ‖(centeredNormalTangentCharacteristic mu q a
            ((Real.sqrt (n : ℝ))⁻¹ * v) ((Real.sqrt (n : ℝ))⁻¹ * s)) ^ n‖ ≤
            Real.exp (-c * v ^ 2)
```

零公开定义、三公开目标。actual Q由同一mu的真实协方差确定，绝不把形式正定矩阵代替它。第一目标可用U12b完成平方，记S=VarY>0、T=D/S>0、k=Cov(Y,X)/S，取c=min(S/2,T/(2k²+1))。真实恒等式与 t²+s²≤2(t+ks)²+(2k²+1)s²给共同正下界，不需要未经证明的矩阵谱结论或方向依赖常数。

第二目标路线为真正二样本积分：令Z=t(Y-q)+s(X-a)，实际mu.prod mu下证明 ‖E exp(iZ)‖²=E cos(Z(X)-Z(X'))。须先建立exp/cos及中心矩对应函数真实可积，再合法Fubini/移出实部与乘积。U12c给同一Z均值0及二阶矩actual Q，因而 E(Z-Z')²=2Q。实际有界X/Y和固定q/a给共同delta>0，使全部|t|,|s|≤delta下的二样本相位差AE绝对值≤pi。固定库Real.cos_le_one_sub_mul_cos_sq提供 cos u≤1−2u²/pi²；因此 ‖phi‖²≤1−4Q/pi²≤exp(−4Q/pi²)，再取非负平方根并用第一目标得到共同c>0。任何乘积AE支撑、中心化或可积门都必须真实给出，不能由总化积分数值推断。

第三目标的delta/c先于切向频率s选取。每个固定s只允许充分大n阈值依赖s；阈值还强制n≥1，以便合法使用sqrt n>0及(sqrt n)²=n。对所有|v|≤delta sqrt n共用同一Gaussian上界exp(−c v²)；不得把v也固定后选阈值来弱化此统一门。该上界在全实v上真正可积，后继交换极限时还需显式证明截断/积分条件，当前结论未把这一后续工作记完成。

环境：Trigonometric.Bounds的固定olean已只读确认存在，源码139–147的cos二次上界可用；只使用已编译U12c及既有U12a/U12b导入链。U12c完整独立审查后，本候选须独立声明审查通过才实施。根A/B/C/D仍OPEN；没有有限样本层反演、格点归一化常数、条件Lévy、混合LLT、实际hW或根闭合主张。
