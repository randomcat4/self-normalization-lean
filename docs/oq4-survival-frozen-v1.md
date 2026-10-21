# OQ4 实际有限最大值Laplace与条件一侧S冻结 v1

原文 current/oq4/b01/proof01.md §2 SP、§3 S1–S3后的概率提取。该单元衔接LaplaceTail和LaplaceGenerating，必须使用公共Path/prefixSum/maxWithZero/closedUpper及真实有限产品Π_j，不另造抽象最大值law或条件化产品。

ν为任意ℝ Borel概率测度；H_j(a)=Shao.maxWithZero a，T_j(a)=Shao.prefixSum a j。对L>0定义

a_L(j)=∫exp(−H_j/L)dΠ_j，b_L(k)=∫exp(−max(T_k,0)/L)dΠ_k，A_L(k)=finiteSumLaplacePayment ν L k。

冻结目标：

1. 对全部自然j/k包括0，三个被积函数真实可测且可积；0≤a_L(j)≤1，0≤b_L(k)≤1，a_L(0)=1，A_L(k)=1−b_L(k)。不要求ν任何矩，不用不可积积分默认0。
2. 证明Antitone(a_L)，使用真实不同维Π的前缀投影或独立拼接及其测度保持性，完整保留H中的0时刻。不能假设生存后增量独立，不能仅把非增性作为输入。
3. 对0<s<1，证明∑s^j a_L(j)、∑s^(k+1)b_L(k+1)/(k+1)及对应A级数真正可和。明确的唯一SP输入是源原始形式，对全部L>0和0<s<1给出
   ∑'j,s^j a_L(j)=exp(∑'k,s^(k+1)b_L(k+1)/(k+1))。
   必须由此及真实log级数推出LaplaceGenerating使用的等价(1−s)^(-1)exp(−W)，不能直接把等价式或所需S结论再作为假设。
4. C_BE≥0、β≥1，明确对每个自然k≥1及每个实x给实际普通和CDF误差
   |Π_k.real{a | T_k(a)/sqrt(k)≤x}−standardNormalCDF x|≤C_BE β/sqrt(k)。
   在同一明确SP输入下，对每个d≥0、自然m≥1、L=d+β，真正实例化LaplaceTail及LaplaceGenerating，证明
   a_L(m)≤sqrt(2) exp(5+3C_BE)(d+β)/sqrt(m)。
5. 证明实际闭事件概率支付Π_m.real(closedUpper d)≤exp(d/L)a_L(m)，再得
   Π_m.real(closedUpper d)≤sqrt(2) exp(6+3C_BE)(d+β)/sqrt(m)。
   保留全部原子、d=0、m=1、全零路径。闭事件必须确与H_m≤d一致，不能换成严格上界或无原子版本；Markov支付两侧真实可积。此处只证ν的上侧，−ν的上侧及最终双侧S接口可后续独立实例化。

拟Shao/OQ4/FiniteSurvivalLaplace.lean。β在此是明确CDF误差参数≥1，所有矩/中心/方差条件由未来BE供给者负责；本模块不声称这些条件自动推出BE。SP本身仍是明确外部输入，不加新公理。所有无条件BE/SP/S/AC/O0、B1、长时间K/Kv和完整OQ4根仍OPEN。不得额外假设可和性、a非增性、所需一侧生存界或改写公共定义。
