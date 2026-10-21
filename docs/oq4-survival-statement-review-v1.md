# 实际有限最大值 Laplace v1 声明语义与常数核查

STATUS: CORRECT
STATUS_SCOPE: FROZEN_STATEMENT_SEMANTICS_AND_CONSTANTS_ONLY
ROOT_STATUS: OPEN
LEAN_STATUS: NOT_RUN

仅读 frozen-finite-survival-laplace-v1.md 与数学源 b01/proof01.md §2 原始 SP、§3 末端概率提取，并采用先前获准读取的公共 Path/prefixSum/maxWithZero/closedUpper 定义语义。未读作者代码、证明或审查票，未实施或运行 Lean，未修改冻结、数学源、Git 或公共文件。

## 实际有限产品与零时刻

Π_j 是 ν 的真实有限 iid 产品，H_j 使用公共 maxWithZero，明确包含零前缀，不是仅对正时间求最大值。对 j=0，空产品概率 law 与 H_0=0 一致，故 a_L(0)=1 正确。

L>0 下，H_j≥0 与正部 T_k≥0 使三个测试均可测、有界且真实可积，不要求 ν 的矩。0≤a_L,b_L≤1 以及 A_L=1−b_L 的积分恒等式正确；A 的 [0,1] 范围亦由此保留。k=0 没有被 BE 的正时间条件错误排除出这些定义。

## Antitone 必须由实际 law 供应

冻结要求证明不同维 Π 下 a_L 的非增性，而不是把它列为输入。真实前缀投影或未条件化独立拼接可以合法比较 H_j 与 H_m；包含零时刻的公共最大值适用于 j=0 和全部前缀。

当前没有假设生存后增量独立，也没有用抽象最大值 law 替换公共路径函数。这一部分量词和目标忠实对应源 H_j≤H_m 的实际概率使用。

## 原始 SP 与等价生成式

唯一显示 SP 输入恰为源原式：左侧从 j=0 开始，右侧正时间项以 k+1 重索引，正部 Laplace 系数 b_L 与参数 θ=1/L 相符。没有引入零分母，也没有漏掉 a_0 项。

a、b、A 的真实级数可和性列为待证结论；它们的 [0,1] 界足以供应所需几何支配。A=1−b 与真实 log 幂级数必须用于导出
(1−s)^{-1}exp(−W)；
冻结没有把这个等价式或目标 S 重新当作独立假设。所有实 log/逆数的定义域由 0<s<1、L>0 保证。

## CDF 参数与实际实例化

CDF 条件对全部自然 k≥1、全部实 x 作用于真实 Π_k 的标准化和，使用同一个实际 standardNormalCDF。k≥1 保证 √k>0。β 在本模块是明确的统一 CDF 误差参数≥1，并未假称它自动就是第三矩或自动推出 BE。

d≥0、L=d+β 使 L≥1、1≤β≤L，完整满足 LaplaceTail 与 LaplaceGenerating 的参数要求。LaplaceTail 给出的 C=1+C_BE 非负，代入生成模块的系数 √2 exp(2+3C)，准确得到
\[
a_L(m)\le\sqrt2\,e^{5+3C_{\rm BE}}(d+\beta)/\sqrt m.
\]
没有遗漏一个指数单位或额外因子。

## 闭事件支付与生存常数

公共 closedUpper d 与 H_m≤d 的逐点等价是正确目标，包含零前缀、闭等号、原子和全零路径。Markov 支付必须在这一个真实事件上进行，冻结没有改成严格事件。

精确概率支付为
Π_m.real(closedUpper d)≤exp(d/L)a_L(m)。
因为 d≥0、β≥1、L=d+β，exp(d/L)≤e 是有效安全放大。因此最终常数 √2 exp(6+3C_BE) 正确。

d=0 时闭事件及 exp(0) 的精确支付保留；m=1 仍在全部正分母范围内。两侧真实可积性明确要求，未使用不可积积分默认零。

## 单侧及认证边界

该接口只给 ν 的上侧。−ν 的相应 CDF/SP 输入、反射 law 及双侧 S 接合留待后续；本票没有借此宣称下侧自动已证。

源中心、单位方差和有限第三矩等条件仍由未来 BE 供给者用来实际证明 CDF 前提；原始 SP 本身也仍是显式外部输入。本模块若完成，只关闭从这两个实际输入到上侧生存界的 law 实例化，不证明无条件 BE/SP/S。

未发现声明语义或常数缺口，可以进入实现及后续独立形式审查。本票不认证任何实现、B1、长时间 K/Kv 或完整 OQ4；全部完整根保持 OPEN。

## 版本锁

- 冻结声明：C:/game/shao lean/drafts/oq4/frozen-finite-survival-laplace-v1.md
- SHA256：988DB8DE1F059C3CC49DACDD72346A1459B7E40773EF96F4C19370221634EC76
- 数学源：C:/game/shao/current/oq4/b01/proof01.md
- SHA256：7C51246EB02A0D694A366CE3AB5A3A9CCA03723160C1291BCE29DD817F68BC38
