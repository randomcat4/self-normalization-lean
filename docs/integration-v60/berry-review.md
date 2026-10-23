# BerryEsseen 独立完整审查

STATUS: **CORRECT**

审查者：`/root/common_berry_full_review`，全新独立审查上下文，`gpt-6.1-sol / xhigh`；不是生产作者。审查采用 math-theorem，服从当前 streamlined acceptance；未启用 math-ultra。结论仅适用于以下精确源版本及其五个公开头，不认证生存概率、Lindley 结果或任何原始根组闭合。

## 精确对象与证据绑定

| 对象 | SHA256 / 标识 |
| --- | --- |
| `Shao/Probability/BerryEsseen.lean`，1950 行、92682 字节 | `8bf02df1210d69a2934746987d0022a85166d17c9850fa4fd27656eb88bb2af9` |
| 原成功 `BerryEsseen.olean` | `d67df1b97eddcde16ee7d9fedc6e6e7e4af11e22e04732a69dbd0b5883b76b57` |
| 仅该源的提交 | `ba7ef8674924248e6eb6fb78d8c59aaf848a6627` |
| 提交父版本 | `2044113b88476b1d3b3c47f3da8b5388b15b6c9a` |
| 八头冻结文件（本次只取前五头与唯一定义） | `674a688c637cc88eb5d3e1f5c43486725e8f1f64510a248ca9742b423a8db2fa` |
| 完整 actual types / 唯一 value 导出 | `01287fa1419ff72d337e27d786e74e79cc1d86458a74af14ac325d87f5003244` |
| 原生全 owned 公理表 | `4d0a0675617535831e11e85473908b8533c3619c211b45df65f73fb578ac2bb3` |
| 原生 actual types / value 打印日志 | `07b3879faee51f50864599601c971ef5ccb0c7a5cb81f302b0cd9fb4b876b057` |
| 服务器 evidence-summary 原文件 | `e92373bdedde26341e8a8e3b21d7f2378d708ed100e69268ecbd29bb77bf2b90` |
| 本地 berry-first-five-evidence 摘要文件 | `34b47e474accaa97965d60a33e4d55aa7b7102bdb7339b6f738f2dc8ee4e17d0` |

服务器原件目录为 `/root/rivermind-data/shao-lean-20261021/artifacts/common-survival-cdf/step-043`。本地摘要与服务器摘要的序列化不同，不将二者文件哈希混同；所列 source/object/log/audit/type 文件摘要逐项一致。只读复核确认：归档源、提交内源、当前作者工作树源及本地待审源同哈希；当前安装的模块对象也与原成功对象同哈希。原 Lean 与原 owned audit 的直接退出码均为 0，不以外层显示命令的退出码代替它们。

Lean 固定为 `leanprover/lean4:v4.36.0-rc1`，Mathlib 为 `807d3836b165983210ee2ecf3cd28f239436949c`。原成功命令为服务器 `lake env lean -M8192 -j4 -DautoImplicit=false -o <step-043/BerryEsseen.olean> Shao/Probability/BerryEsseen.lean`，以既定 `root-heavy.lock` 和 CPU10–13 串行执行。本审查复用此精确成功源与全 owned 审计，不重编、不重跑审计、不执行本地 Lean。

## 阅读与覆盖

完整逐段阅读了本地固定源 1–1950 行，包括所有 53 个显式 theorem 的完整证明、唯一定义、import 和选项。下表分段无遗漏覆盖整个文件；末尾空行及 namespace 关闭同样已读。

| 源码行 | 完整审查内容 |
| --- | --- |
| 1–29 | imports、autoImplicit、名字空间、唯一 literal definition |
| 30–95 | 相位可积、特征函数一阶差、Fourier 商的非负性、局部有界及可积性 |
| 96–185 | 闭阶跃函数、精确区间截面、乘积可积与 CDF 差的 L1 性 |
| 186–313 | 阶跃 Fourier 公式、Fubini 条件及两实际 CDF 的变换 |
| 314–441 | sinc 四次方主控、可积性、尾部及绝对一阶矩 |
| 442–553 | box 卷积、相位区间积分、三角函数与 Fourier 变换 |
| 554–645 | 四 box 卷积连续性、带宽、三角平方积分及零点值 |
| 646–764 | 反演及 2π 换元、sinc 核归一化、矩和自然频率带宽 |
| 765–812 | 实际 withDensity 平滑概率律及其全部性质（也覆盖未被主链调用的辅助结果） |
| 813–939 | 正尺度变换、缩放核、Fourier 模界及带外消失 |
| 940–1070 | CDF 差 Fourier 范数、连续卷积反演及平滑 CDF 误差 |
| 1071–1212 | 双侧逐点去平滑、积分、上确界吸收和尾概率 |
| 1213–1317 | 公开原子闭 CDF smoothing 结论 |
| 1318–1471 | 三阶矩到 MemLp、β≥1、三阶导数、复值 Taylor 及频带界 |
| 1472–1605 | 实际有限乘积特征函数、幂差及公开归一化 CF 界 |
| 1606–1754 | Gaussian 主控积分、实际和的一阶矩及公开 unit-variance CDF 界 |
| 1755–1826 | 实际中心化/标准化推前概率律的完整矩支付 |
| 1827–1887 | 实际坐标推前、有限乘积映射及 centered CDF |
| 1888–1950 | raw-sum 事件、带符号平移、绝对漂移误差及文件关闭 |

还完整核对了原实际 owned 环境中的 **119/119 个完整类型**和 **1/1 个 literal definition value**。计数来自原生 module owner 表与源声明映射：118 theorem = 53 显式源 theorem（5 public + 48 private）+ 65 generated theorem；另有唯一 definition `cdfFourierError`。并非仅按 public 前缀抽查。

实际打印设置为 `pp.all=true`、`pp.maxSteps=10000000`、`pp.deepTerms=true`、`pp.proofs=true`。119 个类型的字面省略符 `⋯` 数为 0；每个原类型 SHA256 和 value SHA256 重新计算一致。为避免反复读相同的显式实例投影，阅读时将重复的平衡子表达式无损提取为 92 个完全展开的字典项，再完整读全部 119 个剩余类型及 value。所有字典项（包括实例、宇宙参数与量词）均完整读过；逆展开逐类型与仅规范化空白的原文本相等，没有删去参数、假设、结论或隐式内容。原完整类型仍保留在既有导出文件，紧凑覆盖表保存逐声明名字、原始类型哈希、generated 归属和源位置。

服务器只读复核还从原 `owned-audit.stdout` 重新提取所有类型和值的哈希，与导出逐项相等；119 个名字集合与 `env.getModuleIdxFor?` 选择得到的原生 owned 表相等且唯一，owner 全为 `Shao.Probability.BerryEsseen`。因此私有、自动生成及定义的归属均已覆盖。

唯一定义 actual value 的 SHA256 为 `2eb5e3b3c3b23097e4c7f2215c772daa86358f9d00a3368bb657464306a6407e`，其完整值就是冻结的 `fun mu nu t => ‖charFun mu t - charFun nu t‖ / |t|`。没有新 private definition、选择型 Berry–Esseen 常数或结果型数据封装。

## 原文到五个公开陈述

独立阅读了固定原文 `C:/game/shao/current/c12/supplement.tex` 1073–1106 行，源哈希 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。1075–1081 行是任意正方差 iid 和的经典 centered Berry–Esseen 陈述，闭事件为 `≤`，尺度为真实标准差和中心绝对三阶矩；原文归属 Petrov。后续 Spitzer 和 survival 只用于识别本次边界，不作本模块证明输入。

候选、source contract 和 proof route 的精确哈希分别为 `2113b671d2c8cf1ecf306c031972bbefc40cff91f819c249171e99b1a83c3769`、`3dc281f7b05477a9e32665059b09e5018755de8c83ffdb23f86cbb0ed0e621dd`、`9dbdb16e0d82eedd7654260dd187d0436a14e258457bfaf51b7818d6ba60b400`。五个源头与冻结头移除空白后逐字符完全相等；实际 elaborated 类型也分别完整读过。

1. `cdf_error_le_fourier_smoothing` 对两实际概率律、各自有限一阶矩及仅比较律的 Lipschitz 闭 CDF 给出结论。首项确实是 Fourier 商在闭有限频段上的可积性；次项是任意实数 x 的实际闭 CDF 差。没有对第一律加密度、无原子、连续或对称条件。
2. `iid_unitVariance_charFun_error` 作用于真正的 `Measure.pi (fun _ : Fin k => nu)` 经 `prefixSum / sqrt k` 推前所得律。前提只有概率、有限绝对三阶矩、真实零均值、真实单位二阶矩、k≥1 和明确频带。独立性、乘积 CF、Taylor 或 Gaussian 比较均由证明支付。
3. `iid_unitVariance_berryEsseen` 给出每个 k≥1、每个 x 的实际闭事件概率，比较对象是既有的实际标准 Gaussian CDF，右端是字面 `1024 * β / sqrt k`。没有 hCDF、CLT 速率或同等强度结论作为输入。
4. `iid_centered_berryEsseen` 使用实际均值 `mu=∫z`、实际 `variance id nu` 与 `m3c=∫|z-mu|³`；事件为 `(S_k-k*mu)/(sqrt V*sqrt k)≤x`。有限 raw 三阶矩支付所需有限矩，V>0 支付正标准差。没有假定一般律中心化或单位方差。
5. `iid_uncentered_berryEsseen` 的事件确实是 raw 和 `S_k/(sqrt V*sqrt k)≤x`；右端保留 `|mu|*sqrt k/sqrt V`。没有把随 k 增长的漂移误差藏进统一 centered 常数。

`Path k` 的实际值是 `Fin k → ℝ`，`prefixSum a k` 的过滤条件在长度为 k 时包含全部坐标。完整实际 product law、measurable pushforward 和闭事件对应关系都在证明中出现，而非仅名称相似。k=0 没有被不合法标准化；k=1、t=0、正负 t、任意 CDF x 均在证明覆盖内。V=0 由冻结前提排除，未借 totalized 除法伪造正性。

## 完整证明的承重点检查

**一阶矩与闭原子。** 96–313 行将每个 CDF 与零点质量的阶跃 CDF 比较，截面准确等于带符号的半开区间 indicator，绝对积分为 |z|。从真实一阶可积性得到乘积可积、Fubini 和 `F_mu-F_nu∈L1`；对非零 t，直接区间积分给出 `-(φ_mu-φ_nu)/(it)`。起点/终点的闭原子没有被假设为零。30–95 行另证 Fourier 商近零有界及有限频段可积；t=0 的定义值 0 只处理该点，不代替近零论证。

**核的归一化与尺度。** 442–764 行从实际 box 函数 b=1[-1,1] 推导 g=b⋆b=(2-|x|)+、p=g⋆g、p(0)=16/3、Fourier p=16 sinc(2πt)^4。对可积且连续的 p 使用真正 Fourier 反演，得到自然频率公式 p(x)=(8/π)∫exp(iux)sinc(u)^4 du，因此 q=3/(2π)sinc⁴ 的变换为 (3/16)p，积分等于 1，|t|>4 时为 0。这里 p 未归一化，与路线中的 p4=p/16 一致。sinc⁴ 及 |u|sinc⁴ 的可积性先独立证明；绝对一阶矩≤3/π≤1。无假定平滑分布或借未证积分归一化。

**平滑 Fourier 反演。** 813–1069 行对 c>0 定义 K(y)=c⁻¹q(c⁻¹y)，支付积分 1、非负、连续、有界及矩≤c。取 c=4/T 后自然频率带宽为 T。`be_convolution_inverse_bound` 的 L1、连续性、有界性和 Fourier 主控条件都被实际支付，给出 H⋆K 的逐点界。自然特征函数频率 t=-2πxi 及换元 Jacobian 1/(2π) 均显式保留；频率零点只在体积测度下作合法 ae 排除。得到真实平滑 CDF 差≤I/(2π)。

**去平滑。** 1071–1316 行只对第一 CDF 使用单调性；比较 CDF 使用已给的 Lipschitz 性。坏尾部的损失为 2D，其中 D 是实际 `sSup range |F-G|≤1`。h=16/T、E|W|≤4/T 给两侧尾概率各≤1/4。积分后 D≤A+L(h+c)+D/2，从而每点≤2A+2L(h+c)。不要求上确界达到、不要求原子消失；40L/T≤64L/T 和 I/(2π)≤I 给冻结公开常数。

**定量 CF。** 有限三阶矩给 MemLp3；真实单位二阶矩给 β≥1。使用复值函数适用的范数 Taylor 余项定理与三阶导数范数≤β，实际代码得到较宽的 β|u|³/2。频带 β|u|≤1/2 于是给 |φ(u)|≤exp(-u²/4) 及单步误差≤(5/8)β|u|³。它与候选路线的较锐 /6、衰减 /3 不同，但没有改冻结假设或头；实际较宽估计已完整足够。真实有限 product CF 等于 φ(t/√k)^k；幂差归纳给 kR^(k-1)d。以 u=t/√k、k u²=t² 及 (5/8)≤exp(-u²/8) 支付目标 exp(-t²/8) 衰减，统一含 k=1。没有把定性 little-o 或 CLT 当定量结果。

**实际 CDF 与 1024。** 1645–1753 行从真实坐标可积性、finite sum 和 measurable map 支付和律的一阶矩；Gaussian 一阶矩、特征函数及 1-Lipschitz CDF 来自实际 Gaussian 接口。通过方差为 4 的 Gaussian 二阶矩计算得到 ∫t²exp(-t²/8)=4√(8π)≤32，且有独立 integrability 结论。T=√k/(2β)>0，频段商积分≤32β/√k，尾项=128β/√k，故总界≤192β/√k≤1024β/√k。相应 actual map 的闭集合质量准确改写为冻结事件；没有未经支付的积分或概率律。

**一般均值/方差与漂移。** 1755–1886 行构造 Z(z)=(z-mu)/sqrt V 及 zeta=nu.map Z，逐项证明概率性、三阶可积、均值零、二阶矩一和第三矩 m3c/(sqrt V)^3。`Measure.pi_map_pi` 将真实逐坐标映射推到 product zeta；点态 prefix 恒等式和 closed set map_apply 给实际 centered 事件。1888–1948 行以 d=mu√k/sqrt V 把 centered≤x-d 精确变为 raw≤x，再以 Gaussian Lipschitz 界补上 |d|。d 的符号未丢失，正标准差和正 √k 均由明确正性支付。

## 已接受依赖与传递公理

复用已接受 v59 的 qualified baseline：receipt SHA256 `30f1cbf1885bfbd141c23a68844696af992cb4b31eb21afc93b6d912da425ccc`；其原 baseline source/object map SHA256 `08aa6be91b171600308a3dee99dc096e9c67e0acf6c230e11b8638e90b5ebae8`。服务器只读比对以下三个真实消费的项目依赖，其源码与 .olean 均逐项等于已接受 map：

| 依赖 | 源 SHA256 | 对象 SHA256 |
| --- | --- | --- |
| Shao.Basic.FinitePath | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` | `14238ea05500cb0e3d6b105253aaeca80c5744612687a1054906de7dd64f2572` |
| Shao.Probability.MeasurablePath | `827dc47b74dae67101a4d874f412e4cb55bafe1e67b9ba767c6896c0b7e58b41` | `8f8cae0273f3b20cf08377c049b4c93e87396a05609c76a4885ab5b2df620de8` |
| Shao.OQ4.IntervalConcentration | `491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875` | `28b1b4463996ab9fb521de2847bff6928e3f98633d47460b1b27dfa6976d3c31` |

独立阅读了实际 Path/prefixSum 值、measurable_prefixSum 接口，以及 standardNormalCDF 的值、actual Gaussian real-Iic 等式和完整 Lipschitz 头及其交互。针对真正承重的 Mathlib 调用，服务器定向读取完整接口：特征函数定义/缩放/乘积/共轭，contDiff 和 iteratedDeriv，Taylor 系数与范数余项，Fourier 正逆变换及卷积、连续卷积，Lebesgue 正尺度积分换元、map integrability、map integral、finite pi_map_pi/eval，以及 Gaussian CF、均值、方差和密度积分。检查其假设在本源调用点得到满足。未复读旧依赖完整证明、未遍历旧传递 DAG、未重新审计已接受旧单元。

原 all-owned gate 以环境的 module owner 选择全部常量，对每个常量运行传递 `Lean.collectAxioms`，并拒绝白名单外项。本次复核原生表的 119 个唯一 owner、kind、类型覆盖与每行公理集合：119/119 合法；其中仅 propext 48 项、propext+Quot.sound 4 项、三项白名单齐备 67 项。并集恰为 `{propext, Classical.choice, Quot.sound}`。原 gate 拒绝除 cdfFourierError 外的任何 defnInfo，并实际只有一个 definition。源码 forbidden token 扫描为零：无 sorry、admit、axiom、unsafe 或 native_decide。数学假设未改动。

## 结论边界与交接

这五头是实际有限 iid CDF 义务的完整生产证明，允许作为已有 conditional CDF 消费者的实际输入。结果是经典 Berry–Esseen/Fourier smoothing 的形式化，不作数学新颖性或常数最优性主张。

本次没有审查或认证 freeze 后三头、FiniteSurvival、SourceLindleySurvival、原始删除/截断生存概率、加权平方和、完整 C1/C2 或 OQ3/OQ4/OQ56 根组；这些范围仍 OPEN。没有把本次 CDF milestone 写成 survival 闭合。旧依赖的合格 review、kernel/AX 证据按上述精确绑定复用；未声称本上下文重读了它们的全部旧证明，也未声称重跑过成功 Lean。

交付：本报告、`coordination/common-berry-full-review.json` 与逐 actual-type 覆盖表 `coordination/common-berry-full-review-types.json`。本审查者从未改生产源、假设、对象、缓存、原始日志或共享 registry。审查完成，专属审查报告写权在最终校验后释放；普通 agent turn 随回报终止，无持久运行或新调度。
