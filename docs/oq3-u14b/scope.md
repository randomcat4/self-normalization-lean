# OQ3-U14b：源三段二元熵的充分统一率间隙

冻结v1，DECLARATION_REVIEW_QUEUED；尚无独立声明批准、尚无实现。拟Shao/OQ3/SourceBinaryEntropyGap.lean，imports Shao.OQ3.BinaryEntropyBounds 与 cached Mathlib.Analysis.Complex.Exponential，proof-only沿用缓存FieldSimp/Ring/Positivity/Linarith/FunProp/NormNum，不使用缺失ExponentialBounds总数值模块，不写共享cache。namespace Shao.OQ3、noncomputable section。

来源R1 report.md SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，161–237，尤其(11)–(13)与ell*q<103/3000<0.035。U14a供标准纯实工具，本单元证明略弱但严格充分的统一7/200下界；不是源更强常数/最优常数/新颖性，也不改变根定理假设。所有根ABCD OPEN。

```lean
theorem binaryRelativeEntropy_ge_first_term (p z : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    p * Real.log (p / z) - p + z ≤ binaryRelativeEntropy p z

theorem binaryRelativeEntropy_gt_two_mul (p z : ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1)
    (hlog : 3 < Real.log (p / z)) :
    2 * p < binaryRelativeEntropy p z

theorem binaryRelativeEntropy_source_gap (q H R : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hH0 : 50 < H) (hH1 : H < 51) (hR0 : 0 < R) (hR1 : R ≠ 1)
    (hp0 : 0 ≤ (q * R ^ 2 - 1) / H) (hp1 : (q * R ^ 2 - 1) / H ≤ 1) :
    (7 / 200) * (R - 1) ^ 2 <
      binaryRelativeEntropy ((q * R ^ 2 - 1) / H) ((q - 1) / H)
```

零公开定义、三个完整公开目标；p/z只在z>0且p≥0时解释，首目标包含p0/p1，第二严格p>0。最后显式保留实际概率可行性hp0/hp1，z=(q−1)/H由50<H、1<q<1.03自动属(0,1)，R≠1让(R−1)²严格正。没有从总化实div/log推出不合法概率域。

证明路线只供可行性而非批准：第一目标由补项u=(1−p)/(1−z)≥0及(1−z)*entropyRemainder(u)≥0直接展开，约掉的仅正1−z，不约p或1−p、不套log_div。第二目标由p>0、log(p/z)>3与z>0使首目标左侧>2p。

末目标分R<1、1<R≤3/2和R≥3/2。小区间由U14a refined lower与max=z和精确p−z=q(R−1)(R+1)/H，把下界写成(R−1)²乘q²(R+1)²/[2H(q−1)]；R>0及q>1给分子>1，2H(q−1)<2*51*(3/100)，足得系数>7/200。此仅较弱充分界，无需额外R>0.98或源(11)更强1/(1−z)。

中区间max=p，正qR²−1/H可合法作分母；系数为q²(R+1)²/[2H(qR²−1)]。以q²>1、H<51、q<103/100控制分母，足证(R+1)²>(7/100)*51*((103/100)*R²−1)。这是紧区间上的显式二次多项式正性，可由(R−1)*(3/2−R)≥0及1≤R≤3/2给代数证书（或再分区间），不需源的有理函数求导；真实符号与严格裕度必须逐一保留。

大区间qR²−1>5/4、0<q−1<3/100，故p/z=(qR²−1)/(q−1)>125/3>27。cached Analysis.Complex.Exponential 的Real.abs_exp_sub_one_sub_id_le取x1给exp1≤3，Real.exp_nat_mul给exp3≤27；Real.lt_log_iff_exp_lt在p/z>0后才推出log(p/z)>3。第二目标遂给d>2p；再由q>1、H<51、R>1给2p>2(R²−1)/51>(7/200)*(R−1)²，最后严格平方使用R≠1。无需导入缺失的数值ExponentialBounds或声称43常数最优。

纯实数三个结论不证明实际随机Bernoulli核合法性、实际KL的数据处理、likelihood/KL差恒等式、R=1的KL零等价、尾内点混合降熵或唯一全局最小性。下一实际KL门尚缺缓存，已inbox请求root，作者不cache get。U14a完整最终proof报告被lead全文读取后，唯一reviewer再执行本单元声明盲译/source/API门；批准前不实现。
