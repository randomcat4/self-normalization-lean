# 真实有限最大值 Laplace 与条件一侧界：匿名完整推导

设ν是实直线任意Borel概率测度，Π_j为Fin j上真实有限产品，T_j为公共prefixSum，H_j为公共maxWithZero（包含零时刻）。L>0时定义a_L(j)=∫exp(-H_j/L)dΠ_j、b_L(k)=∫exp(-max(T_k,0)/L)dΠ_k，A_L(k)为已审finiteSumLaplacePayment。

1. H_j与T_j均为公共连续统计量。H_j≥0且max(T_k,0)≥0，因此两指数被积函数连续、取值[0,1]，在真实概率Π下可积。A的被积函数也实际可积。空路径所有前缀为0，故H_0=0、a_L(0)=1；相同理由b_L(0)=1。逐点1-exp(-max(T_k,0)/L)与端点指数互补，真可积积分的线性给A_L(k)=1-b_L(k)，包含k=0。所有界均保留原子和无界支持。

2. 对长n+1路径取真实前n坐标投影p_n到Path n。真实Π_{n+1}的坐标原本独立且各边缘为ν；固定注入i↦i.castSucc所取的前n坐标仍原本独立，故p_n推送Π_{n+1}精确为Π_n。这是未条件化产品的测度保持，不是在生存事件上主张独立。对每个k≤n，公共有限和定义给T_k(p_n a)=T_k(a)。故H_n(p_n a)≤H_{n+1}(a)，零时刻也包含在内。于是exp(-H_{n+1}/L)≤exp(-H_n∘p_n/L)。对两侧真实可积函数积分并使用推送积分公式，得a_L(n+1)≤a_L(n)，继而Antitone(a_L)。

3. 因a_L,b_L,A_L都在[0,1]，三个生成级数分别受真实可和的几何级数支配，真正Summable。令B(s)=Σ_{k≥1}s^k b_L(k)/k、W(s)=Σ_{k≥1}s^k A_L(k)/k。由A=1-b、真实对数级数Σs^k/k=-log(1-s)及可和级数的线性，得B=-log(1-s)-W。仅把原始SP恒等式G(s)=exp(B(s))作为明确输入，推出
G=(1-s)⁻¹exp(-W)，因为1-s>0。这不是额外假设等价式。

4. 保留β≥1、C_BE≥0以及对每个自然k≥1和实x的实际Π_k下标准化普通和CDF误差输入。固定d≥0，取L=d+β≥1。已审LaplaceTail把每个k的该输入转换为A_L(k)≥1/2-(1+C_BE)L/√k，完整保留β≤L；A真实界在所有k均成立。令C=1+C_BE，将上述A、实际a、已证明Antitone和第3步从原始SP导出的精确恒等式代入已编译LaplaceGenerating，得每个m≥1
 a_L(m)≤√2 exp(2+3(1+C_BE))L/√m
 =√2 exp(5+3C_BE)(d+β)/√m。
不从矩条件推断CDF误差，也不证明SP。

5. 公共闭事件closedUpper d与H_m≤d在所有m/d下精确等价。该事件由H的可测性可测，包括全部边界原子与零路径。逐点有
1_{closedUpper d}≤exp(d/L)exp(-H_m/L)：事件内由H_m≤d得右侧≥1，事件外右侧非负。indicator及右侧都在概率Π_m下真实可积，故真实积分给Π_m.real(closedUpper d)≤exp(d/L)a_L(m)。因d≥0、β≥1，d/L≤1，再乘第4步系数界，得到
Π_m.real(closedUpper d)≤√2 exp(6+3C_BE)(d+β)/√m。
这里d=0、m=1及全零路径无须例外处理；从未将闭事件换成严格事件或去掉原子。

范围：仅为ν上侧，在明确全k/x的CDF误差与原始全L/s的SP输入下的条件结论。未证明BE、SP、无条件一侧S、反号law的上侧、最终双侧S/AC/O0、B1、K/Kv或OQ4。所有完整根OPEN。本文为匿名数学推导，不是独立审查票。
