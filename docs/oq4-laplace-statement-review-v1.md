# 正部 Laplace 尾接口 v1 声明语义与常数核查

STATUS: CORRECT
STATUS_SCOPE: FROZEN_STATEMENT_SEMANTICS_AND_CONSTANTS_ONLY
ROOT_STATUS: OPEN
LEAN_STATUS: NOT_RUN

仅读 frozen-laplace-tail-v1.md 与数学源 b01/proof01.md §3 S1，并采用此前获准读取的 IntervalConcentration 冻结签名及必要公共定义语义。未读实现、作者证明、独立证明票或审稿票，未修改冻结、数学源、Git 或公共文件，未实施或运行 Lean。

## 正部、严格尾事件与可积性

L>0 保证 1−exp(−max(x,0)/L) 是全局介于零和一的可测实函数。因此对任意概率 law μ 的真实可积性与 0≤A_L≤1 是正确目标；不需要 μ 的任何矩。

尾积分中使用 μ.real(Ioi u)，即严格事件 x>u，与 CDF 的 x≤u 恰为补事件。冻结没有用 x≥u 直接替换严格尾，也没有删除 μ 的原子。零点原子的正部贡献为零；正点原子按严格尾公式保留。

右侧在正半轴相对 Lebesgue 积分。端点 u=0 的纳入与否不改变该 Lebesgue 积分，当前 (0,∞) 表述与源 S1 一致。指数核非负且在正半轴的质量为一，尾概率至多一，故右侧真实可积的要求正确且不需要尾部矩。实际实现须证明所有可测性、尾积分恒等式和可积性，不能使用不可积积分默认零。

## 实际高斯半质量与标准化

第二项指定实际 γ=gaussianReal 0 1、Φ=cdf γ。标准高斯在零点无原子且关于零对称，所列 Φ(0)=1/2 与 γ.real(Ioi 0)=1/2 均为正确实际实例目标；不是对任意比较分布假定半质量。

第三项继续使用同一个实际 Φ，以及此前 IntervalConcentration 所指定的全实轴 1-Lipschitz 性。CDF 前提采用 y/√q≤x，q≥1 使标准化分母真实为正。取 x=u/√q 时对应的正是 μ 的未标准化闭 CDF 点 u，未遗漏一个 √q 因子。

## 下界常数 1+C_BE

实际高斯半质量与 1-Lipschitz 性给出的严格尾比较具有线性损失 u/√q；BE 型 CDF 损失为 C_BE β/√q。以归一化指数核积分后，线性损失支付为 L/√q，CDF 损失保留 C_BE β/√q。

由冻结的 β≤L，安全合并常数确为 (1+C_BE)L/√q。因此
A_L≥1/2−(1+C_BE)L/√q
正确，不缺少额外的二。这里使用的是单个 CDF 点的严格尾补集，不是闭区间的两个 CDF 端点误差。

1≤β≤L 与源 L=d+β、d≥0、β≥1 的选择一致。下界在小 q 时可为负，冻结正确保留独立的 A_L≥0，并没有因此要求 q 足够大、收紧 L 或强行声称正的 S1 下界。

## 真实有限和 law 与源范围

第四项使用 μ=(prefixSum · q)_*Π_q，要求由真实可测有限和映射构造概率 law。A_L 的实际积分随后对应源 T_q 正部的期望；测试本身有界，故无需额外矩来执行这次推送。

产品 CDF 输入、q≥1、C_BE≥0 与 1≤β≤L 均保留。这里的 Π_q 是未条件化 iid 乘积 law，不使用生存条件后的独立性；ν 可以有原子、零路径、不对称或无界支持。

局部结论允许比源更广的满足显示 CDF 前提的 law。源的 BE 定理本身仍需要 iid、中心、单位方差及有限第三绝对矩；当前模块不能以这个条件式冒称已证明 BE、SP 或完整一侧 S。β 作为源实际第三绝对矩、L=d+β 的正式实例化仍由源上下文供应。

未发现声明语义或安全常数缺口，可以进入实现与后续独立形式审查。本票不认证 BE/SP、S2/S3、无条件 S/AC/O0/R3/R4、B1、长时间 K/Kv、E1–E6 或完整 OQ4；全部完整根保持 OPEN。

## 版本锁

- 冻结声明：C:/game/shao lean/drafts/oq4/frozen-laplace-tail-v1.md
- SHA256：871F99A3C95FC3ACA755FC507A278C63E2FA1C896F53689ADD04D8B808C320A1
- 数学源：C:/game/shao/current/oq4/b01/proof01.md
- SHA256：7C51246EB02A0D694A366CE3AB5A3A9CCA03723160C1291BCE29DD817F68BC38
