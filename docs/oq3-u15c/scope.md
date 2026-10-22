# OQ3-U15c：紧参数集产出同一正测度/两样本积分下界

冻结v1，DECLARATION_REVIEW_QUEUED，尚无批准/实现。拟Shao/OQ3/CompactTiltDomination.lean；imports Shao.OQ3.ProductMeasureDomination、cached Mathlib.Analysis.Normed.Group.Bounded及同一六tactic分模块。namespace Shao.OQ3、open MeasureTheory、open scoped ENNReal NNReal、noncomputable section。两个公开目标、零公开定义。

来源R2 report.md SHA572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55，343–369，尤其“紧参数集上m>0与theta无关”。U15a/b中盒宽L是输入，本单元从真实紧K选出共同L，再产出同一个正实m，供所有theta与全部频率使用。根ABCD全部OPEN，无最优或新颖性主张。

```lean
theorem exists_compact_parameter_box (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ K, |p.1 - u0| ≤ L ∧ |p.2 - v0| ≤ L

theorem exists_compact_quadratic_tilted_domination (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂mu, |x| ≤ M) (K : Set (ℝ × ℝ)) (hK : IsCompact K) (u0 v0 : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ K,
      (ENNReal.ofReal m • mu.tilted (fun x => u0 * x + v0 * x ^ 2) ≤
        mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)) ∧
      ∀ s t : ℝ, m ^ 2 *
        (∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
          ∂(mu.tilted (fun x => u0 * x + v0 * x ^ 2)).prod
            (mu.tilted (fun x => u0 * x + v0 * x ^ 2))) ≤
        ∫ z : ℝ × ℝ, 1 - Real.cos ((z.1 - z.2) * (s + t * (z.1 + z.2)))
          ∂(mu.tilted (fun x => p.1 * x + p.2 * x ^ 2)).prod
            (mu.tilted (fun x => p.1 * x + p.2 * x ^ 2))
```

K允许空，u0/v0不必属于K；当K非空时共同正m仍可依赖整个固定K和固定基准，但绝不依赖后面的p,s,t。M≥0允许M0；K允许退化点集。所有tilt是实际库定义，不是新概率替身；真实概率性/积分可积性必须通过已审U15a/b的真实门，不能靠totalized积分。

路线：对连续实函数F(p)=|p.1−u0|+|p.2−v0|，actual IsCompact.exists_bound_of_continuousOn给真实C且normF≤C；令L=max C 0。L≥0，两个绝对值均≤其和≤normF≤C≤L，适用空K（不需要假定C≥0）。该接口是Analysis.Normed.Group.Bounded.lean91–95由@[to_additive IsCompact.exists_bound_of_continuousOn]生成的真实标准定理，olean已只读存在，不猜其nonempty门。

第二令B=L(M+M²)，m=exp(−2B)>0，在全部p/s/t之前固定。对同一hbox给hu/hv，U15a给真实ofReal(m)测度下界，U15b给同一exp(−4B)余弦核积分下界；必须用exp加法/幂恒等式精确证明m²=exp(−4B)。这样是同一m的测度与平方积分比较，不是分别选两个不相关常数。M0/L0时m1，K空后续门vacuous，但选出的m仍真严格正。

项目依赖闭包为ProductMeasureDomination（冻结源81行9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f）和其U15a前置5445a68...。当前U15b仅作者门/完整review运行；其最终完整报告经lead全文读完后，唯一reviewer再审本scope，批准前不实现。无新Mathlib cache需求，不复制旧stack缺失的root char源码，不rebase。

本目标仍未把cosine积分识别为实际特征函数模平方差，不关闭WC/除二常数/标准化、不扩成无界X、不证明KL或Levy/LLT/hW。root v30公共identity需root整合接通后再做实际consumer。源ROOT_C只有原输入与目标全部闭合才可能关闭；此处仅紧参数共同常数producer。
