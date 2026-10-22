# OQ3-U14a：源全局最小性所需的纯二元熵下界

冻结v1，DECLARATION_REVIEW_QUEUED；尚无独立声明批准、尚无实现。拟Shao/OQ3/BinaryEntropyBounds.lean；导入Mathlib.Analysis.SpecialFunctions.Log.NegMulLog、Mathlib.Analysis.Calculus.Deriv.MeanValue和已有cached proof-only Mathlib.Tactic.FieldSimp、Ring、Positivity、Linarith、FunProp、NormNum；namespace Shao.OQ3，noncomputable section。Tactic总入口olean不存在，明确只用这些已缓存分模块，不请求作者写cache。

来源R1 report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，161–259，尤其(10)–(13)的二元熵控制。本单元给标准纯实数工具，使用略弱但足够供后续全局率间隙的下界；不声称新颖、最强或已完成全局最小性。它不依赖缺失的Levy/KL DataProcessing缓存，也不从条件LLT推出全局最小性。

```lean
def entropyRemainder (x : ℝ) : ℝ := x * Real.log x - x + 1

def binaryRelativeEntropy (p z : ℝ) : ℝ :=
  p * Real.log (p / z) + (1 - p) * Real.log ((1 - p) / (1 - z))

theorem entropyRemainder_quadratic_of_le_one (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (x - 1) ^ 2 / 2 ≤ entropyRemainder x

theorem entropyRemainder_quadratic_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    (x - 1) ^ 2 / (2 * x) ≤ entropyRemainder x

theorem entropyRemainder_nonneg (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ entropyRemainder x

theorem binaryRelativeEntropy_refined_lower (p z : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    (p - z) ^ 2 / (2 * max p z) ≤ binaryRelativeEntropy p z
```

两个公开定义体、四个完整公开目标。实log在0处虽总化，但xlogx项的连续延拓正是0；第一个目标必须覆盖x0，不能在0套log导数。二元定义在p0/p1、z内点时与真实有限Bernoulli相对熵一致，零项按0log0=0处理；并未对p/z负值或z0/z1声称KL解释。

可行证明路线：对0≤x≤1，g(x)=entropyRemainder(x)−(x−1)²/2连续于闭[0,1]，内部导数为logx−(x−1)≤0，g(1)=0，由闭区间反单调得g(x)≥0。Real.continuous_mul_log提供x0处真正连续性，HasDerivAt_mul_log只在内部x≠0消费。对x≥1，g(x)=entropyRemainder(x)−(x−1)²/(2x)，连续于[1,∞)，导数为logx−1/2+1/(2x²)；Real.one_sub_inv_le_log_of_pos给logx≥1−1/x，因此该导数≥(x−1)²/(2x²)≥0，g(1)=0。可以改写有理项后求导，但每一次消x都必须有x≥1带来的严格正性。

第三目标按x≤1或x≥1消费前两真实二次下界和平方/正分母非负，不需额外log端点假设。第四目标先在z>0、1−z>0下建立精确恒等式

`d(p,z)=z*entropyRemainder(p/z)+(1−z)*entropyRemainder((1−p)/(1−z))`。

两个ratio均非负，第二项由第三目标非负；若p≤z，第一项用ratio≤1的下界化为(p−z)²/(2z)且max=z；若p≥z，则p>0、ratio≥1，第一项用另一二次下界化为(p−z)²/(2p)且max=p。p0只走前支、p1第二ratio0由真实连续扩展处理；没有非法约掉可能为0的p。max p z>0由z>0保证。不能只对内部p∈(0,1)证明后漏掉两个端点。

固定缓存/API已只读初核：NegMulLog.olean、Deriv.MeanValue.olean及六tactic模块存在；Real.continuous_mul_log45–51、Real.hasDerivAt_mul_log71–74、Real.log_le_sub_one_of_pos307–310、Real.one_sub_inv_le_log_of_pos312–313。真正单调性API是Analysis/Calculus/Deriv/MeanValue.lean412–416、481–485的monotoneOn_of_deriv_nonneg/antitoneOn_of_deriv_nonpos，需Convex域、域上ContinuousOn、interior域上DifferentiableOn和真实导数符号。不能误用另一Analysis/Calculus/MeanValue文件来猜签名。

本冻结单元待U13c完整最终报告由lead全文读取后，再由唯一reviewer独立声明/source门；批准前不实施。后续仍须实际Bernoulli kernel合法性、数据处理、likelihood/KL差恒等式、数值率间隙与唯一性/尾内点降熵，均不由此四目标自动关闭。根A/B/C/D全部OPEN；不增加任何β范围/最弱修复/新颖性主张。
