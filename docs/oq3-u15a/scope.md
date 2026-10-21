# OQ3-U15a：有界势差的真实倾斜测度统一下界

冻结v1，DECLARATION_REVIEW_QUEUED；尚无独立声明批准、尚无实现。拟Shao/OQ3/TiltedMeasureDomination.lean，imports Mathlib.MeasureTheory.Measure.Tilted、Mathlib.Analysis.SpecialFunctions.Exp 和cached proof-only FieldSimp/Ring/Positivity/Linarith/FunProp/NormNum。namespace Shao.OQ3、open MeasureTheory、noncomputable section。无Shao项目依赖，不复制或修改root公共模块。

来源R2 report.md SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55，343–373，特别有界X/固定参数邻域给(20)的真实正密度下界。本单元以实际测度domination形式提供足供后继两样本缺口的标准下界，先真正证明tilt可积性。不声称已经证明(21)/(22)或根C，根ABCD全部OPEN。

```lean
theorem quadratic_exp_integrable_of_ae_abs_le (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u v : ℝ) :
    Integrable (fun x : ℝ => Real.exp (u * x + v * x ^ 2)) mu

theorem tilted_measure_domination_of_abs_sub_le (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (f g : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : Integrable (fun x => Real.exp (f x)) mu)
    (hg : Integrable (fun x => Real.exp (g x)) mu)
    (hfg : ∀ᵐ x ∂mu, |g x - f x| ≤ B) :
    ENNReal.ofReal (Real.exp (-2 * B)) • mu.tilted f ≤ mu.tilted g

theorem quadratic_tilted_measure_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (u0 v0 u v : ℝ)
    (hu : |u - u0| ≤ L) (hv : |v - v0| ≤ L) :
    ENNReal.ofReal (Real.exp (-2 * (L * (M + M ^ 2)))) •
      mu.tilted (fun x => u0 * x + v0 * x ^ 2) ≤
        mu.tilted (fun x => u * x + v * x ^ 2)
```

零公开定义、三完整公开目标。mu始终真实概率，M/L/B非负且固定；共同系数exp(−2L(M+M²))严格正，独立于所有u0/v0/u/v。后者只通过同一盒宽L约束，M和L在参数前确定。没有“每参数取自己的常数”替代统一结论。最后仅支撑AE有界，不要求离散/有限支撑；M=0/L=0仍必须合法覆盖。一般f/g不额外假定连续或全局有界，真实exp Integrable足够。

证明路线：首目标|x|≤M时x²≤M²且u*x+v*x²≤|u|M+|v|M²，故真实exp函数由常数exp(|u|M+|v|M²)界定；连续性给AEMeasurable/Integrable.of_bound，概率给finite measure。不得凭tilted之名先声称概率（库非可积tilted=0）。

第二目标Zf=integral expf>0、Zg>0必须先由真实hf/hg和mu概率得到。在同一mu-AE上f−B≤g≤f+B，expg介于exp(−B)expf与exp(B)expf，积分给Zg≤exp(B)Zf。于是exp(−2B)expf/Zf≤expg/Zg；每次乘除均用Zf/Zg/exp严格正。实际mu.tilted是withDensity(ofReal(expf/Zf))，Measure.withDensity_mono和finite ENNReal.ofReal scalar的withDensity_smul'传递真实测度下界，不先假定未经证明的RN下界。ofReal(exp...)有限，不能误把top.toReal=0当普通标量。

第三目标同一hb上精确势差为(u−u0)x+(v−v0)x²，绝对值≤L|x|+Lx²≤L(M+M²)；M/L非负门、abs x²=x²和x²≤M²均显式。先消费首目标给两真实tilt可积，再消费第二目标；对应tilt为真概率可由actual isProbabilityMeasure_tilted得到，但不增加公共目标数量。

实际已只读核查Tilted.lean42–43真实定义；tilted_of_not_integrable46–48为零测度；isProbabilityMeasure_tilted126–135需真实exp Integrable；WithDensity.lean102–107 withDensity_mono需AE比较、137–142 withDensity_smul'需标量≠top。相关Tilted/WithDensity/Exp及六tactic olean存在，无新Mathlib cache需求。没有把实际RN或measure比较替换为错误总化积分恒等式。

root v30公共LowFrequencyDamping的quadraticChar_gap_identity及QuadraticCharacteristic.norm_quadraticChar_le_one在本地curated已有，但旧OQ3堆叠工作树实际缺这两个公共源码/olean；已inbox请求root整合接通，作者不复制/修改/rebase。本单元不依赖它们。后续m²缺口、WC系数、紧参数集转统一盒宽、协方差标准化、无界版假设等仍待后继门，不能据这三目标计根C完成。

U14b完整最终proof报告经lead全文读完后，唯一reviewer再对本scope三完整声明盲译/source/API门；批准前不实施。无最优常数、最弱修复或新颖性主张。
