# OQ4 真实核上的条件有限 D8 吸收冻结 v1

源 current/oq4/b01/proof01.md §8 D2–D8。把已证真实核D0–D4、实际自由系数块幂控制及既有非循环DelayedRecurrence组合起来；不是把有限标量递推的变量重新命名后宣称概率输入已证。

ν为ℝ概率测度，id/y²/|y|³真实可积，均值0、二阶矩1，β≤M、M≥0。h≥1且π(1+M)≤h，m=⌊h²⌋₊，N自然数且m≤N。沿用实际principalCosine、principalRate、kernelCosine/killedMass及其归一化量，起点|z|≤h。令R=exp(π²)，A,B,E≥0。

明确块前提（对每个|w|≤h）：

- U_m |r|(w)≤E/h³，其中r是实际主余弦残差。
- G_m(w)≤A φ(w)+B/h。

不把这两条说成已由O0/R3/R4证明。另设有限小系数条件

(A R)(E R/h³)N+B R/h≤1/2。

令H=2(1+A R)R。冻结结论：

1. 对每个自然k≤N，0≤Ghat_k(z)≤H。
2. 对每个m≤k≤N，|Fhat_k(z)−Fhat_m(z)|≤(E R/h³)(k−m)H。

证明必须实际从核身份/正性和块前提导出满足DelayedRecurrence签名的两条标量递推；用系数上界放大D3时显式使用Fhat/Ghat非负。初段k≤2m及Fhat_m≤R必须由真实核质量和已证逆幂控制给出，不作为循环前提。m≥1须从h≥1和自然floor推出，N=m及零A/B/E均保留。所有归一化的ρ>0来自完整矩/阈值前提，不称ρ为杀死特征值。

该单元关闭条件性、显式有限常数的真实核D8桥。没有证明块前提、B1的Fhat_m→1、实际O0/R3/R4、iid生存所需其他概率估计、终端Brownian块、4/π、K/Kv或OQ4。拟Shao/OQ4/KernelAbsorption.lean，不改共同定义或既审源。
