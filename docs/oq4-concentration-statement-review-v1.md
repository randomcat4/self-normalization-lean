# BE 到闭区间集中 v1 声明语义与常数核查

STATUS: CORRECT
STATUS_SCOPE: FROZEN_STATEMENT_SEMANTICS_AND_CONSTANTS_ONLY
ROOT_STATUS: OPEN
LEAN_STATUS: NOT_RUN

仅读 frozen-interval-concentration-v1.md 与指定数学源 b01/proof01.md §2 BE、§3 AC 及 β≥1 的使用位置。未读 OQ4 作者证明、实现或审查票，未修改冻结或他人文件，未实施或运行 Lean。本票不认证外部 Berry–Esseen 定理或任何实现。

## 闭区间与原子

第一项的对象、量词与误差形式正确：μ 是概率测度，L、ε 非负，G 在全实轴满足实际 L-Lipschitz 条件，CDF 近似对所有实 x 成立。该条件给出的闭 Icc 质量上界是
L(b−a)+2ε，而非删去左端原子的 CDF 差。

a=b 的零长度情形必须仍有 2ε 的原子误差；冻结已明确保留。Lipschitz 比较函数连续，允许在左端使用 CDF 单侧极限，没有要求 μ 无原子或有密度。a≤b 与各常数的非负条件完整。

## 实际标准高斯实例

第二项指定实际 Mathlib 标准高斯概率 measure gaussianReal 0 1，并指定 Φ 为该 measure 的 cdf；没有仅留下一个抽象比较函数的未实例化 Lipschitz 前提。

标准高斯密度的全局上界一是有效的宽松常数，因此实际 Φ 的全实轴 1-Lipschitz 目标正确。cdf 与 γ.real(Iic x) 的一致性在此实际概率 measure 上也是正确的目标。最终实现必须确实证明这一实例及其 CDF 识别，不能仅交付第一项抽象引理后宣称已具备标准高斯比较。本票不审查该实现。

## β≥1 的矩条件

第三项只用概率 measure、二阶积分为一及二阶/第三绝对矩可积，足以得到 β≥1，无需均值零。

冻结允许的逐点式 3u²≤2u³+1 在 u≥0 全局有效；取 u=|y| 与所列可积性相容，数值系数准确。这个矩事实是独立于 BE 的无条件局部结论，不需第四矩、对称性、密度或无原子假设。

## 从真实标准化 BE 前提到 AC

t≥1 保证实数嵌入 t 为正、√t>0，标准化和 law 与区间缩放均合法；t=0 没有混入默认除零情形。prefixSum 的可测映射和真实有限乘积 law 构造是明确义务。

原单位闭区间在正标准化后长度为 1/√t。应用实际 Φ 的 1-Lipschitz 界与两端 CDF 误差，所得系数是
1/√t+2C_BE β/√t。
第三项 β≥1 正确把它支付为
(1+2C_BE)β/√t。
故 Cq=1+2C_BE 是有效明确常数，没有遗漏闭左端的第二个误差，也不需要额外两倍高斯密度因子。

CDF 误差前提对每个实 x 都直接使用真实 Π_t 下的标准化和概率；有限样本原子、零路径和任意区间平移均保留。没有使用生存条件后的独立性。

## 源作用域与认证边界

源 BE 的完整适用条件仍是 iid、中心、单位方差、有限第三绝对矩。第四项的局部逻辑只要求显示的实际 CDF 误差，因而允许满足该前提的更广 ν；冻结已正确标为条件性推广，不能借此省去源 BE 的条件或声称 BE 已证。

第一至第四项若全部实现，可关闭 β≥1、实际高斯比较以及条件 BE→闭 AC 的接口。它们不证明外部 BE，也不证明无条件 AC、SP/S、O0、R3/R4、B1/Brownian 输入、K/Kv 或根 OQ4。

未发现声明语义或常数缺口，可以进入实现与后续独立形式审查；根保持 OPEN。

## 版本锁

- 冻结声明：C:/game/shao lean/drafts/oq4/frozen-interval-concentration-v1.md
- SHA256：EF262E8E8FF61FA0CD2966E6A56C0D73182E54237437A3854AF87BA15878CF85
- 数学源：C:/game/shao/current/oq4/b01/proof01.md
- SHA256：7C51246EB02A0D694A366CE3AB5A3A9CCA03723160C1291BCE29DD817F68BC38
