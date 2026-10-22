# OQ4 实际能量归一化因子 log 误差 N2 冻结 v1

STATUS: FROZEN_PENDING_STATEMENT_REVIEW
ROOT_STATUS: OPEN

源为 shao@35d4580b61e22e7145f47730045a09874ef93259 的 oq4/energy01.md §E1 式(2) 的 log Z 条、共同矩类说明及 log 二阶余项支付。源 SHA256 2e0387f0a35ca677853e45fff271cc2fb0e87db9ee9c6b2f00d3bcf56b51d9e6。拟新 Shao/OQ4/EnergyLogNormalizer.lean；只依赖冻结的实际 N0 和已审矩引理，不依赖 N1 倾斜 law。不改任何旧源/公共定义。

## 对象、前提与常数

ν 为 ℝ 上 Borel 概率测度，x²、|x|³ 真正 ν 可积，∫x²dν=1；β是实际∫|x|³dν。T≥0、M≥0、β≤M、s∈ℝ、|s|≤T。沿用 N0 的真实 Z=energyNormalizer ν h s 和 C_Z(T)=1/8+T/2+exp(4T)T²。

显式定义共同高度阈值与误差常数（建议名 energyLogThreshold、energyLogErrorConstant）：

H(M,T)=2*(1+M+T+C_Z(T)*M)，
C_log(T)=C_Z(T)+4*T²+4*C_Z(T)²。

对全部上述 ν,M,T，全部 h≥H(M,T)，全部 |s|≤T 给下列有限结论。C_log 预先只是 T 的函数，H只是 M,T 的函数；不得隐藏 ν、β、h 或 s 依赖。id可积/原中心条件不需要；β≥1从实际矩内供，不是新增假设。原 ν 无四阶/指数矩、密度、对称、有界支撑或非格点要求。

## 冻结目标

1. 该显式高度内部供应 h≥2、β≤M≤h，以及真实 Z 靠近一：|Z−1|≤1/2，从而 1/2≤Z≤3/2，特别 Z>0。实际调用 N0 的可积性/一次展开，不把所需 Z 误差或正性列为新输入，也不能依赖 total log 的零/负值约定。
2. 证明实际归一化因子的有限 log 误差
   |Real.log (energyNormalizer ν h s)−s/h²|≤C_log(T)*β/h³。
   必须覆盖正、负 s 及 log 余项的两种符号；T=0、s=0 保留。s=0 时真实 Z 为闭截断质量，一般不等于一，不可假设其 log 为零。
3. 保持精确常数。可使用内部纯实 lemma |log(1+v)−v|≤2v²（|v|≤1/2），但它不能代替最终实际 Z theorem。平方余项支付的系数四必须保留，β²/h⁶由共同高度及 β≤M≤h≤h³支付，h⁻⁴由内部 β≥1 支付。不得改成依赖 M 的误差系数仍记为 T-only。

M<1 的矩类可能为空；无需另加 M≥1 或 M>0。对固定原 law 可取 M=β恢复源“固定β充分大h”。本版不要求最优阈值或最优常数，不扩展到无共同矩界的行类。

## 边界与排除范围

沿用 N0 的闭截断及严格补集，保留零点/±2h原子和无界原 ν。N2只认证有限 log 误差，不构造或认证 N1 law/矩，不证明 E2 精确再中心化、E3 路径密度、E4 能量集中、B1、BE/SP、K/Kv、随机分母或任何完整根。

作者不得改前提或常数，先匿名数学证明再实施；当前仅声明预备，先完成 N1 源冻结，未另分配新作者。所有 Lean 仅server，作者唯一发射新目标olean；独立source无-o/全部新声明/全OQ4共存、父module-owner和传递公理审计。禁止sorry/admit/new axiom/unsafe/native_decide，只用标准三公理。
