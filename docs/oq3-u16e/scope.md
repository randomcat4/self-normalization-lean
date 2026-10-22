# OQ3-U16e：真实协方差试验倾斜代价的三次下界与负层权重余量

冻结v1，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟Shao/OQ3/NormalTrialCost.lean。imports Shao.OQ3.CenteredLogMGF、Shao.OQ3.LocalRateMargin；namespace Shao.OQ3、open MeasureTheory、noncomputable section。两个公开定义、两个公开目标。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，350–383：真实中心K_c、优化倾斜、实际协方差逆型代价与曲边负层余量。本单元采用显式线性试验参数，直接生产真实logMGF试验代价的下界；这是标准充分替代路线，不定义或宣称已经构造实际Legendre上确界、逆函数/Hessian或source(16)概率估计。

```lean
def normalTrialTilt (mu : Measure ℝ) (y z : ℝ) : ℝ × ℝ :=
  let S := normalVariance mu
  let T := transverseVariance mu
  let b := ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / S
  (y / S - b * ((z - b * y) / T), (z - b * y) / T)

def normalTrialCost (mu : Measure ℝ) (q a y z : ℝ) : ℝ :=
  (normalTrialTilt mu y z).1 * y + (normalTrialTilt mu y z).2 * z -
    centeredNormalLogMGF mu q a (normalTrialTilt mu y z).1 (normalTrialTilt mu y z).2

theorem exists_normalTrialCost_cubic_lower (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det) :
    ∃ D radius : ℝ, 0 < D ∧ 0 < radius ∧ ∀ y z : ℝ, |y| + |z| ≤ radius →
      Integrable (fun x : ℝ => Real.exp (centeredNormalProjection q a
        (normalTrialTilt mu y z).1 (normalTrialTilt mu y z).2 x)) mu ∧
        0 < (∫ x : ℝ, Real.exp (centeredNormalProjection q a
          (normalTrialTilt mu y z).1 (normalTrialTilt mu y z).2 x) ∂mu) ∧
        gaussianRateProfile (normalVariance mu) (transverseVariance mu)
          (ProbabilityTheory.covariance normalValue (fun x : ℝ => x) mu / normalVariance mu)
          y z - D * (|y| + |z|) ^ 3 ≤ normalTrialCost mu q a y z

theorem exists_normalTrialCost_weight_margin (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a ell : ℝ)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = a)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu)) :
    ∃ delta gamma c : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ k r : ℝ, 0 ≤ k →
        k / (n : ℝ) ≤ delta → |r| / (n : ℝ) ≤ delta →
          (n : ℝ) * q * k / 16 ≤ r ^ 2 →
            gamma * k + c * r ^ 2 / (n : ℝ) ≤
              (n : ℝ) * normalTrialCost mu q a (-k / (n : ℝ)) (r / (n : ℝ)) - ell * k
```

完整定义在任意mu上按实除法/log/积分总化；定理的真实mu概率、hb、真实两中心与S>0和det>0不可省略。T的actual定义是parabolaCovariance.det/normalVariance，hS/hD给真正T>0；b是同一个mu的真实Cov(Y,X)/S，有任意符号，不是自由数值或source固定数值。normalTrialCost是具体线性参数计算得到的实际logMGF试验代价，不是名为率就自动满足Fenchel/Legendre性质。第一目标明确给试验指数真Integrable和严格正normalizer，排除log/积分总化。

实际normalTangentQuadratic_complete_square在hb/hS门下给Q(v,s)=S(v+b*s)^2+T*s²，T和b精确如定义。取w=z−by，s*=w/T，v*=y/S−b*s*，有v*+b*s*=y/S。合法S/T非零代数给

`v*y+s*z−Q(v,s)/2 = y²/(2S)+(z−by)²/(2T)`。

这是实际协方差二次型的试验对偶恒等式，不能仅把泛型U16c的自由S/T/b换名就声称实际绑定。所有除法在hS/hT之后清分母，不除b或y/z。

共同参数控制可选

`L=1/S+(|b|+1)^2/T+1>0`。

对任意y/z，由三角不等式、正分母和|b|非负，|s*|≤((|b|+1)/T)(|y|+|z|)，再|v*|≤|y|/S+|b||s*|，所以|v*|+|s*|≤L(|y|+|z|)。这一L固定在所有y/z之前，允许b0和零目标。它是真全局线性试验映射界，不依赖每点选择参数球。

U16d已冻结真中心logMGF上界，作者已空build02及完整公理检查通过，正在完整独立审查，尚未接受发布；必须待lead全文读完最终票后才派本声明门。若最终接受，在同一mu/hb/hq/ha下取得统一C>0和delta>0，再取radius=min1(delta/L)>0和D=C*L³>0。所有目标l1≤radius的试验参数均落同一delta球，先消费真exp可积和Z>0，再消费真实logMGF≤Q/2+C*(|v*|+|s*|)³。三次误差由正C和共同L界控制，结合上式真对偶恒等式给第一目标。D/radius在全部y/z之前。

第二目标将第一目标的第三分量作为hI，取I=normalTrialCost mu q a（显式真实函数），调用已完整审查的U16c exists_cubic_rate_weight_margin，S/T/b取本实际mu同一值，T>0由真实hS/hD得到。q>0、ell≥0、实际hgap、正D/radius及两个真实均值门均显式保留；delta/gamma/c在全部n/k/signed r之前，k任意非负实、r可负，ell0、k/r0和n1均有效。第一目标不要求q>0，第二目标需要q>0以合法消费曲边门，不能偷换这两个范围。

这条显式试验路线给实际函数的局部三次下界，修复U16c仅generic I输入的空缺；但它没有证明normalTrialCost等于实际Legendre变换，也未声明任意上确界或Fenchel性质。下一步若用于真实单侧尾倾斜，须单独证明s*在正/负尾的正确符号、实际iid倾斜换测度、相同最大span与紧倾斜族统一C/sqrt n；不能从试验代价下界直接标(16)/(17)概率完成。它不证明global正尾唯一性/远区gap、完整19/LLT/hW/WC/KL或根完成。

直接依赖均为本lane已冻结或待完整最终审查后才准用的模块，不需新Mathlib缓存、root公共源码、修改imports/pins/cache或rebase。作者在本声明批准前不实施或Leanprobe；唯一reviewer先盲译两个完整定义体及两个完整类型并持久化，再source/实际库/数学门。根ABCD全部OPEN，无最弱/最优/新颖性主张。
