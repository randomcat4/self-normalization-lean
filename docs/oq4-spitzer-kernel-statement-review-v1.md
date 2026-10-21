# BE 与原始 SP 到实际有限核吸收 v1 声明语义核查

STATUS: CORRECT
STATUS_SCOPE: FROZEN_STATEMENT_SEMANTICS_AND_CONSTANTS_ONLY
ROOT_STATUS: OPEN
LEAN_STATUS: NOT_RUN

本轮只读 frozen-spitzer-kernel-bounds-v1.md，并对照此前完整读取的数学源 b01/proof01.md §3/5/6/8 与获准读取的既冻 ReflectedSurvival、FiniteSurvivalLaplace、KilledBlockBounds 接口声明。未读作者 reflected 实现、证明或审查票；未联网、操作服务或运行 Lean；未修改冻结、数学源、Git、公共文件或缓存。

## 实际 β 与唯一外部输入

β 明确定义为实际 ν 下的 ∫|y|³，而不是新增自由数值替身。ν 的概率条件、id/y²/|y|³ 的真实可积性、均值零、二阶矩一、M≥0、β≤M 与 C_BE≥0 均完整保留。

实际二阶/三阶矩足以供应 β≥1；无需把它重复列为新的独立假设。CDF 输入只对 ν 给出，量化全部自然 t≥1 和全部实 x，使用真实有限乘积普通和与正的 √t 标准化。

ν 与 ν⁻ 各自的原始 SP 都明确保留为输入，量化全部 L>0、0<s<1。ν⁻ 的 BE 应由实际高斯反射与严格 CDF 极限导出；没有另加反射 BE、S/AC、非增性、可和性、生存后独立性或目标吸收界。

## 现有谓词及 S/AC 常数

按本任务给定的现有最终签名，真实参数顺序为
iidIntervalConcentration ν β C_q、
iidOneSidedSurvival ν β C_S。
新冻结第 15 行使用该顺序，β 与常数没有互换；目标明确供应现有谓词，不新造抽象概率接口。本票不检查作者实现中的实际调用。

由已冻有限 law/反射链得到的
C_q=1+2C_BE，
C_S=√2 exp(6+3C_BE)
均正确、非负，只依赖 C_BE。只有外部 BE 另给固定通用数值常数时，它们才是通用数值常数，当前没有漏掉该依赖。

## 真实 R3/R4 供应与常数

h≥3、m=⌊h²⌋ 下，实际半块 S/AC 输入给出
C_layer=12 C_q C_S M(1+M)，
与既冻 BoundaryOccupation 的全部层形式一致。实际 κ 的子概率质量与闭域 AE 支持应由核幂接口供应，不是额外测度假设。

解析平均残差在共同 β≤M 下准确由
E=π³M/48+2πC_layer(1+2M)
支付，因此真实 U_m|r_h|(z)≤E/h³ 的常数有效。R4 的 A=2C_S、B=2C_S M 亦准确给出
G_m(z)≤2C_S principalCosine(h,z)+(2C_S M)/h。

这些块界列为内部导出的结论，不是再次索要的 R3/R4 输入。实际 r_h、核作用、质量和余弦测试及其可测/可积性均被保留；没有换成纯标量序列或实际谱特征值假设。

块界的常数依赖为 M、C_BE（C_q、C_S 已明确定义），没有遗漏 C_q C_S。原子、端点和无界跳跃均被原闭事件接口保留，不需第四矩、密度或非格点前提。

## 有限 D8 的归一化与边界

第三项在块界之外增加 π(1+M)≤h、N≥m 以及显示 smallness。h≥3 已供应 h≥1 和 m≥1；完整矩/阈值条件供应真实自由系数 ρ>0 及统一逆幂界 R=exp(π²)。

以 A=2C_S、B=2C_S M 代入既冻 KernelAbsorption，归一化系数分别为
(2C_S)R、ER/h³、(2C_S M)R/h。
因此
((2C_S)R)(ER/h³)N+(2C_S M)R/h≤1/2
以及 H=2(1+(2C_S)R)R 均正确。

输出质量界含 k=0；余弦振荡只在 m≤k≤N 使用自然差 k−m 后转实数。k=m、N=m、闭域端点都保留，没有非法负索引或时零杀死，也没有假设归一化初值已经等于一。

这是依靠已内部供应块界的有限条件 D8，不是 B1 或长时间收敛。没有新增 B1、实际 O0/R3/R4、终端布朗块或吸收结论作为输入。

## 结论与认证范围

未发现声明语义或常数缺口，可以进入实现与后续独立形式审查。本票仅确认从显示 BE、两份原始 SP 和完整矩/高度/时间/smallness 条件到实际有限核界的接合目标。

本模块不证明外部 BE/SP、Brownian B1、长时间极限、4/π、K/Kv、E1–E6 或完整 OQ4；全部完整根保持 OPEN。最终仍需实际编译、最终签名匹配与传递公理审计。

## 版本锁

- 冻结声明：C:/game/shao lean/drafts/oq4/frozen-spitzer-kernel-bounds-v1.md
- SHA256：D93F79AFC43C6463E3DC2B954F27E92E6E5585FEF0505FE4C205E7BA86223CCD
- 数学源：C:/game/shao/current/oq4/b01/proof01.md
- SHA256：7C51246EB02A0D694A366CE3AB5A3A9CCA03723160C1291BCE29DD817F68BC38
