# EnergyLinearTiltCentering v1 独立最终形式审查

STATUS: CORRECT
SCOPE: FULLY_CHECKED — 同一实际线性族的共同中心参数存在第五叶
E2_STATUS: OPEN
ROOT_STATUS: OPEN

本机 `drafts/oq4/energy-linear-centering/EnergyLinearTiltCentering.lean` 与服务器 `Shao/OQ4/EnergyLinearTiltCentering.lean` 的实际最终 SHA256 均为 `82f48c2123d499eed5a7ac8974ff7d51d18e09987539f8323dece141e08bbe16`，7357 字节、127 行。检查时分支 `feat/oq4-centering-and-path`，HEAD `1695839731c586cbeb34f157f9aec2246ec00c7a`。最终实际签名和实现完整覆盖冻结接口，未发现数学或形式关键缺口。

## 冻结输入与范围

冻结声明 SHA256 `ab00e1b2348ea71a82e4cac65f157df25598e0d21c9c942eeba8065937486e1c`；匿名证明 SHA256 `05899c370b22a54c329908fb748f2ab3059b156e6716a049ae0b34b37b13c559`；独立数学票 `energy-linear-centering-math-review-v1.md` SHA256 `59b30b205092c058227237e032d081f42e7436c29fb9b811c359ea090c8f54d1`。三者在最终审查后逐项复核均未改变，原数学票保持冻结。本票新增最终实现、实际签名、独立服务器编译、公理和共存证据，不覆盖或替代原数学票。

未读取作者收据、总结、账本、检查点或译者票；未改动证明、冻结、源、共同文件、Git 或缓存。作者仍是唯一目标 olean 发射者，本审查没有 emit 或重编旧目标。以下行号针对上述127行最终源。

## 完整接口与非循环证明核查

1. **共同常数与全部量词，第11–39行。** 两个透明定义恰为 K(M,T)=1+4A(M,T)、Hcenter(M,T)=Hvar(M,T,K(M,T))，没有换阈值或让 K 依赖 ν,h,s。实际定理输入只有 ν 的概率性、M,T≥0、h≥Hcenter、|s|≤T、原平方与绝对三次矩真可积、单位二阶、原均值零及实际 β≤M。没有新端点、可微性、连续性、方差、θ、已中心化 μ 或其他概率结论作为假设。参数先固定 M,T 后对所有 admissible ν,h,s 成立；没有暗增 M≥1、原有界支持、指数/第四矩、对称或密度条件。

2. **K、h、a 的正性，第17–29行。** P(T)≥1 供应 P≥0，结合 M≥0 得 A≥0、K>0；原窗口高度定理在这个固定 K 下给 h≥energyLogThreshold(M,T)、h≥2。由此 h²>0 且 a=K/h²>0，正性都在内部返回。源未除以 A、M、T 或初始均值，没有因零参数缩窄冻结域。

3. **真实初始均值，第42–49行。** 分开调用 firstlaw 的实际 t=0 身份与窗口初始 E1 支付，返回 m(0)=∫x dμ 及 |∫x dμ|≤A/h²。原 ν 均值零只用于既有 E1 支付；代码没有把 μ 当成原本均值零的测度。原 id 可积及 μ 下的真实一阶可积由已认证矩/law 接口内部供应，不是额外隐藏假设。

4. **MVT 的实际 API 与全部区间点，第52–69行。** m 的真实全实连续性由 energyLinear_family_continuous 供给，当前 h≥2 满足其 h≥1 输入。对任意 x<y、−a≤x、y≤a，局部 hw 逐个取 u∈Ioo x y，经两端约束推出 |u|≤a，再调用同一 ν,M,T,K,h,s 的真实 energyLinearVariance_window。局部 v(u) 定义恰为同一 μ_u 下 ∫(z−m(u))² dμ_u；hw 返回 v(u)≥1/2 与 HasDerivAt m v(u) u，非任意数值导数。

   服务器直接检查的实际 `exists_hasDerivAt_eq_slope` 要求 x<y、ContinuousOn m (Icc x y)、以及每个 Ioo 点的 HasDerivAt；返回 c∈Ioo x y 与 v(c)=(m(y)−m(x))/(y−x)。源第65–66行完整供应这些前提，再以 y−x>0 合法清分母并使用同一 hw c hc 的下界，得到 (y−x)/2≤m(y)−m(x)。没有遗漏端点连续性、开区间可微性或中间点窗口成员证明，也未在窗口外使用方差下界。

5. **严格端点，第72–95行。** a>0 允许分别在 [0,a] 与 [−a,0] 调用增长定理，左右朝向均正确。代码将真实初始均值身份改写回 m(0)，并使用绝对值的双侧界。第87–93行内部证明正余量 a/2−A/h²=(1/2+A)/h²>0，正1来自固定 K=1+4A。然后线性组合推出 m(−a)<0<m(a)，不是仅弱异号，也没有另添非退化假设。

6. **IVT 与同一 θ，第98–107行。** 连续函数仍为实际 energyLinearMean ν h s；a>0 内部给 −a≤a。实际 `intermediate_value_Icc` 接口为 Icc(f(−a),f(a)) 包含于同一 f 对 Icc(−a,a) 的像；代码用已证明端点严格符号的弱化构造0的值区间成员，再从像中抽出同一实 θ。Icc 成员经 abs_le 精确转为 |θ|≤K/h²，并保留同一 m(θ)=0。没有假设 θ 存在，没有换函数，也没有引入选择函数或唯一性结论。

7. **实际中心法则和真积分，第110–123行。** 同一个存在定理返回的 θ 原样用于 energyLinearTiltLaw ν h s θ。h≥2 供 h≥1；既有 firstlaw 返回真实概率性、该法则下 a.e. 闭支持 |x|≤2h，以及 id/平方/绝对三次矩真可积。最后用同一 moments 定理的真实均值身份 ∫x dμ_θ=m(θ) 再接 m(θ)=0，故积分零不是不可积默认值。μ_θ 为同一 energyTiltedLaw 的实际 exp(θx)/L(θ) 密度法则；正归一化及测度对象由既有 firstlaw 供应，没有另造均值零法则。a.e. 支持不被扩成原 ν 全局支持。

8. **边界及承诺范围。** h=Hcenter、|s|=T 使用弱输入；M<1 的可能空矩类保留，不加 M≥1；T=0、s=0、θ=0 和任意原子均保留。A=0 时 K=1 且端点余量仍正；本叶 K 始终正，不需要 K=0 分支。所有 MVT 点在同一闭窗口，IVT 返回闭范围。没有排除0或截断闭端点原子。实际结论没有 θ 唯一、可测/连续选择、全实严格单调、选 θ 的 h^-4 logL 或最终二三阶矩估计。

## 独立服务器检查与公理

检查完成 UTC `2026-10-21T18:48:32.323724+00:00`。经指定激活脚本后进入指定服务器工作树；全部 Lean 使用 `taskset -c 0-3 lake env lean`，三个调用按顺序逐进程执行，不带 `-o`，不重编旧目标，不写共享缓存。

- 最终源独立目标检查退出0，日志为空，零警告/零错误。
- 完整最终源加审计附录经 `lean --stdin` 检查退出0，零警告/零错误。打印2定义、7个显式定理、MVT/IVT 与必要实际依赖签名，并遍历整个环境所有 `getModuleIdxFor? declName = none`，记录完整实际类型和 collectAxioms；不使用 namespace、root 或声明名称筛选。
- 实际动态枚举10个新增常量：2定义、7定理、1生成项。每项传递公理都在 `{propext, Classical.choice, Quot.sound}` 白名单内。此数来自实际环境遍历，不依赖作者报数。
- 固定既有31个模块加本模块共32个 `Shao.OQ4` 模块真实 import 于同一输入，随后检查实际初始均值、增长、端点、存在和法则定理及 MVT/IVT，退出0，零警告/零错误。主法则定理直接打印的传递公理也为标准三项。
- 32份 OQ4 与递归枚举的全部32份 `Shao/Basic`、`Shao/Probability` Lean 源，检查前后64项 SHA256 完全一致。全部旧31份 OQ4 和32份共同源另逐项匹配本审查者前一窗口叶的独立冻结清单；本机与远端新源 SHA 一致。
- 本机及远端最终源禁用项扫描均通过，未发现 sorry、admit、axiom、新公理占位、unsafe、native_decide 或 sorryAx。实际 proof 已逐段核对其语义及参数，未以编译成功代替自然数学核查。

新增常量完整列表，统一前缀 `Shao.OQ4.`：

- 定义：energyLinearCenteringK、energyLinearCenteringThreshold。
- 定理：energyLinearCentering_K_pos、energyLinearCentering_height_bounds、energyLinearCentering_initial_mean、energyLinearCentering_interval_growth、energyLinearCentering_endpoints、energyLinearCentering_exists、energyLinearCentering_law。
- 生成项：energyLinearCenteringK._proof_1，实际只依赖 propext；其余九项传递公理均为标准三项。遍历规则覆盖任何可能生成在导入名称下的 helper，并未预设只有此生成名称。

原始完整日志只在服务器 `repro_outputs/oq4-energy-linear-centering/independent-review-v1/`：

| 文件 | 字节 | SHA256 |
| --- | ---: | --- |
| target.log | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| source-allnew-audit.log | 116375 | f3f0009db61f56dda8a24ef95619391a1af0c48fca6a907f59328cf71c40ef2c |
| coexist-32.log | 4456 | 97dbbce9a73f058c3fcbfbacd3a00be11167cd3ecf5e8616ee580aa98cd5267b |
| hashes-before.txt | 6450 | 223411cf16f5b64924cbf658b12d8c2363926550b0de2ed2930ae0de9f3f2b73 |
| hashes-after.txt | 6450 | 223411cf16f5b64924cbf658b12d8c2363926550b0de2ed2930ae0de9f3f2b73 |

本票仅认证上述有限中心参数存在及同一实际中心法则接口。所选 θ 的 log 支付、完整 E2/E3/E4/K/Kv、随机分母及 OQ4 根全部 OPEN。本审查所有服务器调用均已结束，无本审查遗留 live Lean 检查。
