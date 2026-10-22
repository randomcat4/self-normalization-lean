# EnergyLinearTiltVarianceWindow v1 独立最终形式审查

STATUS: CORRECT
SCOPE: FULLY_CHECKED — 共同有限参数方差窗口第四叶
E2_STATUS: OPEN
ROOT_STATUS: OPEN

审查对象是本机 `drafts/oq4/energy-linear-variance-window/EnergyLinearTiltVarianceWindow.lean` 与指定服务器 `Shao/OQ4/EnergyLinearTiltVarianceWindow.lean`，二者最终 SHA256 均为 `a0059db361b524332d85c73eb13577b67de5df1fe4d7f41c3cd2aba9072e5c73`，12062 字节、204 行。服务器检查时分支 `feat/oq4-linear-comparisons`，HEAD `ae4b9c3865e33e231252693e23ff0338ead29b16`。未发现数学或形式关键缺口。

## 冻结边界与独立性

冻结声明 SHA256 `2129a2141ff4c38a3af2874143bba06cb94975affb7baf81237ac9809db23d7d`；匿名证明 SHA256 `1571edff7df1dbaecb12720b4081d21013c8869340ef643faae84331ea63832c`；先前独立数学票 `energy-linear-variance-window-math-review-v1.md` 的 SHA256 `5fcf6406bf78f6bae8055322d514a798b6391b5be91720693e7b5f5475e98fbc`。三者复核均未改变。数学票保持原件，本票补充实际最终源、完整实际签名、独立编译、全部新增常量及共存证据。没有读取作者收据、总结、账本或译者票；没有改动实现、证明、冻结声明、公共源、Git 或缓存，也没有生成任何目标 olean。

## 实际接口与证明核查

1. **同一明确常数与共同量词，源第11–36、64–71行。** 四个透明定义精确给出 A=P(T)M、B=exp(2)K(A+6)、C=A+5exp(2)K，以及 Hvar=energyLogThreshold(M,T)+8(1+A+B+C+K)。实际签名先量化 M,T,K，再对任意满足共同高度的 h 及窗口内 s,t 给结论；没有将 K 依赖消去。实际输入只有实数非负参数、ν 的概率性、原平方/绝对三次矩可积、单位二阶、原均值零、实际 β≤M，以及两个闭参数窗口。没有额外 M≥1、ν 有界支持/指数矩/第四矩/对称或 θ/方差前提。

2. **高度、分母与指数支付，源第23–60行。** 先用已认证 P(T)≥1 证明 A,B,C≥0，再由原 H0≥2 与 Hvar 的非负附加项推出 h≥H0、h≥2、8A,8B,8C,8K≤h。fraction_bounds 仅除以正 h 与 h²，以 X≥0、8X≤h 推出 X/h≤1/8、X/h²≤1/8≤1/2；未除以可能为零的 A,B,C,K。指数定理内部将窗口与 8K≤h 合并为 4h|t|≤1/2，故 D²=exp(4h|t|)≤exp(2)。所有这些都是已证明结论，没有作为新的分布假设。

3. **实际 E1 初始支付与真可积性，源第74–107行。** 调用同一 ν,h,s 的实际 energyE1_common_bounds，其结论内部供应 μ=energyTiltedLaw 的概率性和 id/平方/绝对三次矩真可积。Pβ≤PM=A 与正分母给 |q−1|≤A/h、|m0|≤A/h²、r≤A。再由 8A≤h 得 q≤2、|m0|≤1。u1≤1+q≤3 使用实际可积的 |x| 与 1+x² 作 integral_mono，并使用真实概率质量计算常数积分；没有用不可积积分默认零值。原 id 可积性由已认证 E1 依赖内部供应，不是遗漏的隐藏输入。

4. **两个归一化数值与保留原均值项，源第110–166行。** 实际比较第三叶用于同一 μ 和 μ_t。q,u1,r 的非负性与前一项给 r+qu1≤A+6、q+|m0|u1≤5；与 D²|t|≤exp(2)K/h² 合并，得到 |q_t−q|≤B/h² 及 |m_t−m0|≤5exp(2)K/h²。三角不等式保留初始误差，精确得到 |q_t−1|≤A/h+B/h² 和 |m_t|≤C/h²。两项 1/8 支付给前一总误差≤1/4；C 的支付给后一项≤1/2。没有误把新均值设为零，也没有少掉 A/h²。

5. **同一真实中心平方与真实导数，源第169–200行。** actual firstlaw moments 返回 μ_t 下 id、平方的真可积性，并将 energyLinearMean=A1/L 与实际均值积分识别。导数叶返回同一 μ_t 下中心平方真可积及真实积分身份；第184行用实际二阶矩等式将 A2/L 改写成 q_t。因此 v_t 的实际对象是 ∫(x−m_t)² dμ_t，身份为 q_t−m_t²。内部 |q_t−1|≤1/4 与 |m_t|≤1/2 给 m_t²≤1/4，从而 1/2≤v_t≤2。最终 HasDerivAt 由已认证 energyLinearMean_hasDerivAt_centeredSquare 实际调用，导数值恰是同一积分，不是形式微分或额外可微性输入。

6. **闭端点与零参数。** 实际所有窗口均为 ≤，保留 h=Hvar、|s|=T、|t|=K/h²。K=0 时只迫使 t=0，B=0 仍合法；T=0 时保留 s=0；M<1 的可能空分布域没有被新增 M≥1 缩窄。所有测度为真实 Borel 概率；只调用倾斜法则下既有 a.e. 支持接口，不把该支持扩为原 ν 的全局支持。没有密度或排除原子的条件。q_t 作为原点二阶处理，方差是明确减去新均值平方后的真实中心积分。

## 独立服务器证据

检查日期 UTC `2026-10-21T18:34:37.784920+00:00`。通过项目激活脚本后进入指定服务器工作树；所有 Lean 调用均使用 `taskset -c 0-3 lake env lean`，逐个进程运行。本次没有 `-o`，没有重编旧目标，也没有写共享缓存。

- 最终源无输出文件目标检查：退出0，日志0字节，零警告/零错误。
- 将最终完整源接上审计附录后执行 `lean --stdin`：退出0，零警告/零错误。附录打印4个定义及全部7个显式定理、关键真实依赖签名，并遍历整个环境的 `getModuleIdxFor? declName = none`，对每个新增常量记录完整实际类型及 collectAxioms；没有 namespace、root 或名称过滤。
- 实际动态结果为15个新增常量，独立核对是4个定义、7个定理和4个生成项。每项传递公理都只在 `{propext, Classical.choice, Quot.sound}` 白名单内。
- 全部既有30模块加本模块共31个 `Shao.OQ4` 模块，在同一输入中真实 import 后检查高度、初始矩、窗口矩和最终定理，退出0，零警告/零错误。主窗口定理的传递公理也直接打印为标准三项。该共存检查没有以单独目标成功替代共同环境成功。
- 31份 OQ4 源与递归枚举的全部32份 `Shao/Basic`、`Shao/Probability` Lean 源，检查前后63项 SHA256 清单完全一致；31份 OQ4 逐项另与独立冻结源清单一致。ClosedSurvival、FinitePath、FiniteIID、MeasurablePath 四个共同路径依赖也与先前固定 SHA 一致。本机最终源与服务器源 SHA 相同。
- 本机及服务器最终源禁用项扫描均通过：没有 sorry、admit、axiom、新公理占位、unsafe、native_decide 或 sorryAx。完整 proof 也已逐段阅读，未将结论反塞为假设。

实际新增常量（统一前缀 `Shao.OQ4.`，完整环境枚举结果）：

- 定义：energyLinearVarianceA、energyLinearVarianceB、energyLinearVarianceC、energyLinearVarianceThreshold。
- 定理：energyLinearVariance_constants_nonneg、energyLinearVariance_height_bounds、energyLinearVariance_fraction_bounds、energyLinearVariance_exponential_bound、energyLinearVariance_initial_bounds、energyLinearVariance_moment_bounds、energyLinearVariance_window。
- 生成项：energyLinearVarianceC._proof_1、energyLinearVarianceB._proof_1、energyLinearVarianceB._proof_2、energyLinearVarianceThreshold._proof_1。这四项实际只依赖 propext；其余十一项传递公理均为标准三项。审计未预设生成项必须位于这些名称下。

原始日志仅保留服务器目录 `repro_outputs/oq4-energy-linear-variance-window/independent-review-v1/`：

| 文件 | 字节 | SHA256 |
| --- | ---: | --- |
| target.log | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| source-allnew-audit.log | 130212 | d1ea5e8120bed47855e8e2956bb84f8260aac0bd3aa12f153339699f24cf8022 |
| coexist-31.log | 4403 | e26d677b88e139cb78edc932dafe36ed419a675d85ebc5b3290b3b9ce441f722 |
| hashes-before.txt | 6344 | 49a88e382a70c4271513a68233d3aa7f5dcd8f16276bef8e3288d9d06233590e |
| hashes-after.txt | 6344 | 49a88e382a70c4271513a68233d3aa7f5dcd8f16276bef8e3288d9d06233590e |

本次仅认证明确固定 M,T,K 后的有限真实方差窗口及其导数值接口；没有选择 K(M,T)，没有证明端点异号、θ 存在/唯一、选 θ 的中心化或 h^-4 对数界。完整 E2/E3/E4/K/Kv、随机分母及 OQ4 根全部 OPEN。所有本审查服务器调用均已结束，无本审查遗留的 live Lean 进程。
