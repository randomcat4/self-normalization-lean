# OQ3-U16d：真实中心二元对数矩母函数的统一三次上界

冻结v1，DECLARATION_REVIEW_QUEUED，尚未批准或实现。拟Shao/OQ3/CenteredLogMGF.lean。imports Shao.OQ3.NormalTangentMoments、Mathlib.Analysis.Complex.Exponential、Mathlib.Analysis.SpecialFunctions.Log.Basic；namespace Shao.OQ3，open MeasureTheory，noncomputable section。一个公开定义、一个公开目标。

来源 current/oq3/proofs/r1/report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，350–371：真实K_c(v,s)=log E_mu exp(v(Y-q)+s(X-a))，实际协方差二次部分和局部三次余项。本单元生产真实K_c的统一参数球三次上界；不能把固定方向特征函数余项或单位模积分替代成真实正指数矩母函数。

```lean
def centeredNormalLogMGF (mu : Measure ℝ) (q a v s : ℝ) : ℝ :=
  Real.log (∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu)

theorem exists_centeredNormalLogMGF_cubic_upper (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10) (q a : ℝ)
    (hq : (∫ x : ℝ, normalValue x ∂mu) = q)
    (ha : (∫ x : ℝ, x ∂mu) = a) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ v s : ℝ, |v| + |s| ≤ delta →
      Integrable (fun x : ℝ => Real.exp (centeredNormalProjection q a v s x)) mu ∧
        0 < (∫ x : ℝ, Real.exp (centeredNormalProjection q a v s x) ∂mu) ∧
        centeredNormalLogMGF mu q a v s ≤
          normalTangentQuadratic mu v s / 2 + C * (|v| + |s|) ^ 3
```

定义完整体是实际实指数的真实Bochner积分取实log。该全函数在任意measure/参数上按Lean总化；定理必须显式产出真实Integrable和严格正normalizer才解释log，不能用log0或不积分时的积分0伪证。mu是真概率；hb是真AE有界支撑，不要求原子性、非退化或实际协方差正定。q和a只以真实两积分等式绑定，任意符号；不擅加source q>0/ell条件。C和delta严格正并先于全部v/s，整个闭l1参数球共用，含v=s=0及边界。

centeredNormalProjection的真实定义为v*(normalValue x-q)+s*(x-a)，normalValue=8x-x²。normalTangentQuadratic为实际中心协方差二次型，由已完整审查NormalTangentMoments在这两中心门下给真积分0和真二阶矩恒等式。本单元不能把矩阵系数当作未绑定自由S/T/b；不要求它正定，也不推断实际Legendre逆Hessian。

数学路线：在共同紧支撑区间上，用两个连续函数normalValue-q及x-a的有限上界，选择一个K>0（可取两个绝对界的max加1），在同一AE支撑上有这两个绝对值均≤K。因此对所有v/s，|f(v,s,x)|≤K*(|v|+|s|)。固定delta=1/K>0后，球内真|f|≤1，C=K³>0。所有AE界和见证在参数量词顺序中保持统一，不能从旧U12d固定方向C/delta推出整个球统一。

真实exp(f)由连续函数在hb紧区间上的有界性真Integrable（现有integrable_continuous_of_fixed_bounds可直接用于任意固定v/s）；或以exp1真有界Integrable。两种路线均不能使用phase的模恒1。integral_exp_pos必须在真Integrable后消费，mu概率给非零measure。

固定mathlib已实际只读核对：Analysis/Complex/Exponential.lean 517–521有Real.exp_bound，直接对实f和n3使用，得到|exp f-(1+f+f²/2)|≤(2/9)|f|³≤|f|³。无需绕Complex实部。由此逐点exp f≤1+f+f²/2+|f|³。再以|f|³≤K³*(|v|+|s|)³为统一常数误差。在积分比较前真证明多项式和exp的可积性；中心0/实际二阶矩恒等式给Z≤1+normalTangentQuadratic/2+C*l1³。Z>0之后消费Real.log_le_sub_one_of_pos，得到目标。不得把泛函名字、Big-O或Real积分总化替代这些步骤。

只读核对缓存：Mathlib.Analysis.Complex.Exponential源码SHA35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146；Mathlib.Analysis.SpecialFunctions.Log.Basic源码SHA0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97，两olean真实存在。integral_exp_pos实际在MeasureTheory/Integral/Bochner/Basic 792–798，输入真exp可积。无需新cache或root公共源码，所有Lean检查只在指定服务器。

本单元不生产实际Legendre变换或其三次minorant、不证明Fenchel试验参数恒等式、紧倾斜族统一C/sqrt n、Chernoff(16)/(17)、远区gap、完整层和(19)、LLT/hW或根完成。下一步可选真实线性试验参数结合此上界，建立直接Chernoff试验代价；若使用I，必须真正绑定其对所有试验参数的Fenchel下界，不能用实sSup对无界集合总化0。U16c仍只消费generic I下界。

当前U16c完整独立审查运行；lead全文读完其最终票后才派本单元声明门。唯一reviewer必须先盲译完整定义体和完整目标签名并持久化，再source/实际API/数学门；批准前不实现。无最弱、最优或新颖性主张，根ABCD全部OPEN。
