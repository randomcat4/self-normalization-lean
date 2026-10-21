# OQ3-U15b：真实产品测度与两样本余弦积分的平方下界传递

冻结v1，DECLARATION_REVIEW_QUEUED，尚无批准/实现。拟Shao/OQ3/ProductMeasureDomination.lean，imports Shao.OQ3.TiltedMeasureDomination、Mathlib.MeasureTheory.Measure.Prod、Mathlib.MeasureTheory.Integral.Bochner.Basic及同一已缓存六tactic分模块。namespace Shao.OQ3、open MeasureTheory、noncomputable section。所有root ABCD OPEN。

来源R2 report.md SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55，343–373，特别(20)经(21)到(22)的真实两样本非负积分传递。本单元直接证明真实产品measure和实际1−cos核的m²因子，及U15a真实有界二次tilt的同一exp(−4B)实例化；没有复制缺失root公共特征恒等式，不声称已关闭WC/标准化或rootC。

```lean
theorem prod_measure_domination (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0)
    (hdom : (m : ℝ≥0∞) • mu ≤ nu) :
    (m : ℝ≥0∞) ^ 2 • mu.prod mu ≤ nu.prod nu

theorem cosine_pair_integral_domination (mu nu : Measure ℝ)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (m : ℝ≥0)
    (hdom : (m : ℝ≥0∞) • mu ≤ nu) (u v : ℝ) :
    (m : ℝ) ^ 2 *
      (∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂mu.prod mu) ≤
      ∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (u + v * (z.1 + z.2))) ∂nu.prod nu

theorem quadratic_tilted_cosine_pair_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ)
    (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L) (s t : ℝ) :
    Real.exp (-4 * (L * (M + M ^ 2))) *
      (∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
        ∂(mu.tilted (fun x => u0 * x + v0 * x ^ 2)).prod
          (mu.tilted (fun x => u0 * x + v0 * x ^ 2))) ≤
      ∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
        ∂(mu.tilted (fun x => u * x + v * x ^ 2)).prod
          (mu.tilted (fun x => u * x + v * x ^ 2))
```

0公开定义、3完整目标。m取NNReal而非任意ENNReal，故标量有限，保留m=0；概率实例保留真实product有限/SFinite。第二真实cosine核连续，0≤1−cos≤2，两实际product概率下真Integrable，必须先证再用integral_mono_measure；不能把总化积分当有限积分。第三共同M/L在全部tilt参数及频率前确定，系数不依赖任一参数，M0/L0仍合法。tilt两概率必须先由U15a实际quadratic exp Integrable与isProbabilityMeasure_tilted得到，不能从tilted名字假定。

证明路线：对hdom两次使用实际Measure.prod_mono，将(m•mu).prod(m•mu)改写为m²•mu.prodmu；actual prod_smul_left在Prod.lean877–881，prod_smul_right在WithDensity.lean753–758，SFinite门由真实概率/有限NNReal标量。第二先在nu.prodnu下证真非负与Integrable，integral_mono_measure(prod_dom)比较真实积分，再integral_smul_measure及ENNReal.toReal_pow/coercion得到(m:real)²，不接触top.toReal。m0只给0≤实际非负积分，完全合法；无正标量非法消去。

第三取m=NNReal.mk(exp(−2B),exp_nonneg)，B=L(M+M²)，由U15a actual measure domination改写为hdom，先实例化两个真实tilt概率，再用第二。指数平方(exp(−2B))²=exp(−4B)须由实际exp加法或exp_nat_mul证明；不凭近似或混淆m与m²。

root v30的quadraticChar_gap_identity能在整合后识别两个真实cosine积分为1−|quadraticChar|²；当前旧stack缺该公共源，作者不复制/修改/rebase。本单元不依赖它，也不把其旧证明计新目标。后续特征缺口/除2 WC常数、紧参数盒宽选择/标准化仍未关闭。原始根C只有全部source输入与目标组合后才可能关闭。

实际WithDensity/Prod/Bochner.Basic/Tilted与六tactic缓存已只读核；U15a是唯一项目依赖（105行冻结源5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b），当前仅作者门，完整review经lead全文读取后才让唯一reviewer审本scope，批准前不实现。标准充分机制，无最优常数/新颖性主张。
