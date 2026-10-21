# 条件有限核吸收 v1 冻结声明语义盲审

STATUS: CORRECT
STATUS_SCOPE: FROZEN_STATEMENT_SEMANTICS_AND_CONSTANTS_ONLY
ROOT_STATUS: OPEN
LEAN_STATUS: NOT_RUN

本轮只读 frozen-kernel-absorption-v1.md，并以此前获准读取的数学源 b01/proof01.md §8 D2–D8，以及 frozen-finite-v1.md、frozen-kernel-recurrence-v1.md、frozen-cosine-powers-v1.md 的声明作对照。未读任何作者证明、实现或审查票，未修改冻结或他人文件，未实施或运行 Lean。

## 三个归一化系数

R=exp(π²) 是已冻结自由系数幂界的统一安全常数。当前 ν 的概率/矩条件、共同 β≤M、阈值 h≥1 且 π(1+M)≤h，完整保留了取得 ρ>0 及相关逆幂界的条件。

对应 DelayedRecurrence 的参数如下：

| 标量递推参数 | 当前冻结供应值 |
|---|---|
| 延迟块系数 | A R |
| 一步增量系数 | E R/h³ |
| 余项系数 | B R/h |
| 初段与初值上界 | R |

块残差输入 E/h³ 的精确归一化因子为 ρ^{−(m+1)}，故采用 ER/h³ 正确。块生存输入的两个系数分别乘 ρ^{−m}，故采用 AR 与 BR/h 正确。m≥1、0<ρ≤1 及已冻结逆幂界足以覆盖该 m 次幂；没有漏掉残差系数的一步幂次。

把精确系数放大为上述安全系数时，必须使用 Fhat、Ghat 非负，冻结第 21 行已明确要求。这一非负性只在源起点 |z|≤h 下使用，未把区间外可能为负的余弦值当作正值。

## 小系数与输出常数

DelayedRecurrence 的小系数条件 A_FD D_FD N+B_FD≤1/2，按上表正是
\[
(AR)(ER/h^3)N+BR/h\le1/2.
\]
乘法中的自然数 N 按实数嵌入解释。A、B、E 的位置与 R 的两个乘积因子均正确。

初始常数取 R 后，该有限引理给出的安全上界为
H=2(1+AR)R，
与冻结第 16 行一致。因此 Ghat≤H 和
|Fhat_k−Fhat_m|≤(ER/h³)(k−m)H
的系数匹配既有冻结签名。H 显式依赖 A；本声明没有把任意 A 藏进一个仅依赖 M 的常数。

## 初段必须来自实际核

k≤2m 的 Ghat 上界由真实核行质量≤1及自由系数的 ρ^{−2m}≤R 取得。Fhat_m≤R 同样由源域内 0≤φ≤1、真实核正性/质量和相应逆幂界取得。冻结把这些列为需要实际导出的事实，没有将所求长期 Ghat 上界作为前提，因而未循环。

当前只需有界初值 Fhat_m≤R，不要求或供应 B1 的 Fhat_m→1。把有限振荡界升级为源 D8 中趋近一的结论，仍需后续 B1 及尺度极限。

## 自然数与零参数边界

h≥1 保证 h²≥1 和 m=⌊h²⌋₊≥1，符合 DelayedRecurrence 的正块长要求；m≤N 已显式列出。所有增量与延迟指标都在既有递推的合法自然数范围内，k−m 的使用仅在 m≤k 时发生。

N=m 时振荡区间只含初值点，结论有一致的零差分解释。A、B、E 可为零，正性与小系数条件仍按原式处理，不应新增严格正参数。没有要求 Ghat 单调或预先存在其统一上界。

## 条件性与源作用域

两条块估计对全部 |w|≤h 明确作为前提：U_m|r|≤E/h³ 和 G_m≤Aφ+B/h。它们对应源 R3/R4 的输入位置，当前模块不证明 O0 或这两条估计。

本声明准确供应真实核上的条件有限 D8 代数桥；没有将有限标量变量换名后声称概率输入已证。未证明 B1、实际 iid 路径生存的其他估计、布朗终端块、4/π、长时间 K/Kv 或 OQ4。

未发现声明语义或常数缺口，可以进入实现及后续独立形式审查。本票不认证任何实现完成状态；根保持 OPEN。

## 版本锁

- 冻结声明：C:/game/shao lean/drafts/oq4/frozen-kernel-absorption-v1.md
- SHA256：5DDB3C77AC61F416FFE6D3569F76B20FB7FB05468E97E7E4EBBF742D9D36C767
- 数学源：C:/game/shao/current/oq4/b01/proof01.md
- SHA256：7C51246EB02A0D694A366CE3AB5A3A9CCA03723160C1291BCE29DD817F68BC38
