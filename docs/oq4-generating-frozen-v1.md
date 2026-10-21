# OQ4 S2–S3 与生成函数系数提取冻结 v1

原文 current/oq4/b01/proof01.md §3 S2–S3。该模块只关闭确定性解析链：S1序列下界与明确Spitzer型生成函数恒等式推出Laplace系数的平方根衰减；不证明Spitzer恒等式、BE或实际随机游走law。

令实数L≥1、C≥0，A:ℕ→ℝ满足对每个自然k≥1，0≤A k≤1且A k≥1/2−C L/sqrt(k)。定义对0<s<1的真实和式

W(s)=∑' n:ℕ, s^(n+1) A(n+1)/(n+1)。

冻结目标：

1. 对每个0<s<1证明上述级数真正Summable（必要绝对收敛也须证明），不借tsum默认0；证明S2的明确安全常数界
   W(s)≥−(1/2)log(1−s)−log L−(1+3C)。
   J=ceil(L²)可仅作证明工具，不是额外输入。任何调和和、幂尾和及log幂级数所需可和性都须由钉死mathlib定理或本地证明真实建立。允许更强的中间常数，不更改本界。
2. 任意a:ℕ→ℝ，0≤a j≤1，且Antitone a。对0<s<1，G(s)=∑' j:ℕ, s^j a j也须证明真正Summable。若对每个0<s<1明确给出精确生成函数恒等式
   G(s)=(1−s)^(-1) exp(−W(s))，
   则证明S3的明确界
   G(s)≤exp(1+3C) L/sqrt(1−s)。
3. 同一完整前提下，对每个自然m≥1，证明
   a m≤sqrt(2) exp(2+3C) L/sqrt(m)。
   可取s=exp(−1/m)，必须证明0<s<1、1−s≥1/(2m)以及真实G中有限前缀的下界；m=1、C=0、L=1合法，不丢a0项、不对0除法。

后续实际law模块才把A_k=E[1−exp(−T_k^+/L)]、a_j=E[exp(−H_j/L)]实例化，并证明a的非增性和概率Markov支付；本模块不将这些法则、SP或S作为已证。若C=1+C_BE，再乘Markov支付e后的安全生存常数是sqrt(2) exp(6+3C_BE)，这里只记录下一实例化的代数目标，不提前宣称实际S闭合。

拟Shao/OQ4/LaplaceGenerating.lean。所有无条件BE/SP/S/AC/O0、B1、长时间K/Kv与完整OQ4根仍OPEN。不更改任何既审源/公共定义。
