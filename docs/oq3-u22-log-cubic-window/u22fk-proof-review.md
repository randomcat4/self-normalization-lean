# FK248 独立最终数学审查

STATUS: CORRECT

JUSTIFICATION: 完整最终源码证明了逐字冻结的通用加权振荡积分支配命题。显式核函数逐点模长为一；非负连续权重与连续误差给出实际复值被积函数的连续性，其模长恰为已知可积的加权绝对误差。于是得到该复值函数真正的限制测度可积性，再由积分范数不等式得到对所有频率同一右端的界。全部最终声明、两处声明内 let、唯一实际 TYPE 和全部证明均已完整审查；保存的首次原生编译与同一首次对象的全实际所有者递归公理审计精确绑定这些字节。未发现数学缺口或额外前提。此裁决仅认证 FK248，不认证实际模型装配、傅里叶反演或原 OQ3 根命题。

审查者为全新独立非作者上下文 `/root/oq3_fk248_final_review`，指定模型 `gpt-6.1-sol`、推理强度 `xhigh`。作者为父实例 `/root`。本轮使用 math-theorem 的独立验缝流程和 chinese-output-style，未使用 math-ultra。唯一写入为本报告；没有修改源、冻结、类型、依赖、收据、协调或共享文件，也没有派生子实例、连接服务器、运行 Lean/公理检查、上传、Git/API 发布或向其他聊天发送消息。

## 精确字节与完整读取覆盖

下表 FK248 文件均位于 `C:/game/shao lean/drafts/oq3/`，全部完整读取。摘要、字节数与 LF 数在本轮直接从本地保存字节计算。

| 文件 | SHA256 | 字节 / LF |
|---|---|---|
| u22fk-frozen-declaration.lean.txt | `430d27f065c5008e9e04767c45adf2f4c26516478cc0a8190347ba50ea244352` | 684 / 13 |
| u22fk-source.lean | `2e51edd82d8da7151cf9fcd8ea0381c7065c48886cd300498a1f226346bc8796` | 1995 / 48 |
| u22fk-actual-types.txt | `dd8717250f76de598e7bd1c48cdd7f6da88b873d082edefa2572870c104827f4` | 744 / 12 |
| two-hundred-forty-eighth-unit-scope.md | `3c47ef91def8e885c7adcd26f74f8ca98e1c7016dbcdc45e3a0f5aac42333e8e` | 1959 / 31 |
| u22fk-bearing-dependency-binding.json | `6695e6e4767067cc31060f954fab750365f1e24857577549385fea06ff8cc034` | 2063 / 38 |
| u22fk-receipt.json | `75c0e3ed482a17cdf3a4043883d6c232aab0db0dc8e6bd312bc5380b980d6cfc` | 5480 / 186 |
| u22fk-audit-record.json | `ba28ca627e6efcdf8328bedf09e97fb04032410f6b7840d8cdec9f202bb1c473` | 3029 / 103 |
| u22fk-build-history.json | `1e7ca87e1378d1a6d7fa4103169ac1cc3c5cb824c453cdd8e81313474ea9e5dc` | 2267 / 83 |
| u22fk-Audit.lean | `2fd4b3acc96a8fdad3e75cdc9178dffacda3ec40aea89aa3b1d2934f7a36d002` | 2014 / 47 |
| u22fk-server-dependency-binding.json | `7932f8ee26e535baca46680195f2551f9c136f59bdfd2206e70afdb041b437b8` | 671 / 13 |
| u22fk-own-firstO-view-binding.json | `e0bc1e0ba581b972b176690ce9060939ac831bb2143779f0dd5cd89e6bd06a16` | 571 / 10 |

冻结、最终源和完整实际类型均无 BOM、无 CR，分别恰有 13、48、12 个 LF。源文件不存在 `sorry`、`admit`、新增 `axiom`、`unsafe` 或 `native_decide`。`noncomputable section` 没有绕过内核检查。

另完整读取原始 `C:/game/shao/current/oq3/proofs/r2/report.md` 的 139–156、220–235、493–523 行，完整读取 `proofs/r2/repair01.md` 全 226 LF 和 `C:/game/shao/current/oq3/verdict.md` 全 58 LF。verdict 实际位于 OQ3 目录根部，未将不存在的 `proofs/r2/verdict.md` 当作已读文件。三份原始文件的 SHA256 依次为 `572e74aa9c12e2771f5543a5709a2807666eeea0a4076e7a3263e5c7bcf87f55`、`9d2e554838aa15b645aaf74a42468d423fed606aa91c1181d0dddf4e87c57cfd`、`fd0a5732845aa96ab1725e6d1e52676502092e49d2c00225ce1fde26ac06f3b5`，与分派绑定完全一致。原始来源只读。

本轮亦读取适用技能及其提示词库、公开工作流、Lean 核验协议，并核对当前 AGENTS 的 OQ3 明确恢复条款、SERVER 的钉死版本及 TEAM 的实际所有权审计输出边界。`library/lean-toolchain` 为 `leanprover/lean4:v4.36.0-rc1`；SERVER 记录 mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。本轮不探测或使用本地 Lean；机械通过状态来自下述已有精确服务器收据，没有重放检查。

## 冻结声明、实际类型与全部量词

直接提取最终源第 8 行开始、证明分隔符 ` := by` 之前的完整声明，并补回声明末 LF，与 13 LF 冻结文件逐字比较，结果为完全相等。不是只比较定理名或目标摘要。最终源第 8–20 行覆盖唯一公开定理 `Shao.OQ3.pair_weighted_oscillatory_error_integral_bound`。

声明逐项为：任意 `e : (ℝ × ℝ) → ℂ`；显式 `he : Continuous e`；任意 `s : Set (ℝ × ℝ)`；任意自然数 `k`；以及同一集合上同一函数 `sqrt(z.1^2+z.2^2)^k * ‖e z‖` 的 `IntegrableOn`。两个 let 依次为实权重 `weight z = sqrt(z.1^2+z.2^2)^k` 和复核 `kernel x z = exp(-I * ↑(x.1*z.1+x.2*z.2))`。结论对每个实二维 `x` 同时断言实际复值函数 `kernel x z * ↑(weight z) * e z` 可积及其积分范数不超过同一加权绝对误差积分。

完整 12 LF 实际类型恰有一个 `DECL/TYPE`，`KIND theorem`，没有 `VALUE`。其中 `Continuous e →` 是源中证明参数 `he` 的打印形式；两个 `have weight := ...; have kernel := ...;` 是源中两个 let 的打印形式，没有额外假设。所有积分和 `IntegrableOn` 显式展开为 `MeasureTheory.volume`；定义域确为 `ℝ × ℝ`，不是实一维、有限网格或概率空间。实到复的嵌入、负号、乘法顺序、两个坐标的内积、自然幂及 `∀ x` 均与冻结一致。没有隐含的集合可测性、有限体积、频率界、额外误差率或新增随机模型假设。

## 全部证明的逐段数学核验

1. 第 21 行 `intro weight kernel x` 引入的是已固定定义的两处 let 和任意频率，不是在两处 let 上新增自由选择。以下论证始终使用冻结给出的同一权重和同一核。

2. 第 22–25 行：坐标投影、平方与加法、非负平方根以及自然次幂均连续，故 `weight` 连续；`Real.sqrt` 总是非负，自然次幂保持非负，故逐点 `0 ≤ weight z`。这里没有对 `z`、`k`、`s` 增加限制，也不需要在原点可微。

3. 第 26–28 行：固定任意实二维 `x` 后，`x.1*z.1+x.2*z.2` 为实值连续函数，实到复嵌入、乘以 `-I` 和复指数保持连续。令该实数为 `t`，则 `Re(-I*↑t)=0`，所以 `‖exp(-I*↑t)‖ = exp(Re(-I*↑t)) = exp(0) = 1`。`Complex.norm_exp` 与 `Complex.mul_re` 的简化正是此恒等式；不是以未证的核有界性代替真正模长一。

4. 第 29–32 行：复数范数乘法性给出 `‖kernel*↑weight*e‖ = ‖kernel‖*‖↑weight‖*‖e‖`。实到复嵌入保持范数，实范数为绝对值，再用权重非负将 `|weight|` 化为 `weight`。故严格得到逐点等式 `‖kernel x z * ↑(weight z) * e z‖ = weight z * ‖e z‖`。等式对所有 `z` 成立，没有忽略零点或仅在集合内部成立的缺口。

5. 第 33–35 行：同一 `kernel x`、实权重的复嵌入及 `he` 的连续性，经两次复乘法给出实际复值被积函数连续。复数为可分完备赋范空间，连续函数具有所需强可测性，因此对当前限制测度得到几乎处处强可测性。这里证明的是将要积分的真实函数，不是仅证明一个实值包络连续。

6. 第 36–39 行：将 `hInt` 看作关于 `volume.restrict s` 的实值可积性。`Integrable.mono'` 所需条件是目标复值函数几乎处处强可测，以及其范数几乎处处不超过该可积实函数。前者来自上一段，后者由第 4 段逐点等式取 `.le`，再用 `Filter.Eventually.of_forall` 得到。由此独立得到实际复值函数的 `IntegrableOn`；没有把“积分在不可积时按零定义”的约定当作可积性证明，也没有把待证可积性作为输入。

7. 第 40–45 行：先把真正可积性 `hi` 放入合取结论，再对同一 `volume.restrict s` 使用 Bochner 积分范数不等式 `‖∫ f‖ ≤ ∫ ‖f‖`。最后以第 4 段逐点等式作几乎处处积分同余，将右端精确替换为 `∫ weight z * ‖e z‖`。支配函数由 `hInt` 可积，其实值积分有限且非负。整个证明没有交换极限、导数或积分，没有归一化系数丢失，也没有使用傅里叶反演定理。

## 边界、集合及统一性攻击

任意集合 `s` 的结论正确：`IntegrableOn` 和集合积分使用限制测度，限制测度对任意集合有定义。本证明只用关于这一测度的可测性、支配可积性、积分范数不等式及积分同余，没有调用需要 `MeasurableSet s` 的示性函数或限制测度取值公式。因此不需要把可测性补进冻结前提，也不声称 `s` 本身必为可测集合。

空集时两边积分为零且可积性成立；零测集合也没有例外。无界域及无限体积域允许出现，但仍必须满足已写的 `hInt`；连续性本身不会被误用为无界域可积性。`k=0` 时权重恒为一，包括原点按自然幂约定的 `0^0=1`；`k>0` 时原点权重为零，均无奇点。`x=(0,0)` 时核恒为一，退化为普通加权积分三角不等式；任意大频率仍有同一模长一恒等式，无额外频率阈值。`e=0` 亦给出零等式。逐点论证覆盖每一个 `x`，右端与 `x` 无关，故具有声明所说的统一性；没有额外宣称关于 `x` 的导数、全频率可积性或联合可积性。

## 已资格化依赖的精确复用

唯一编译导入为 `Shao.OQ3.ComplexGaussianWeightedLocalIntegral`（FB239）。我完整读取它的公共源码声明（`u22fb-source.lean` 第 1–31 行）及全部 21 LF `u22fb-actual-types.txt`，并完整读取 `u22fb-qualification.json`。FB 的旧完整证明及旧审查不重新审理：本轮核对旧审查文件摘要和已资格化记录，提取旧 receipt 的资格字段，不声称再次完整读取该旧报告或全部旧 receipt。FK 的实际证明没有引用 FB 定理 `complex_gaussian_damped_local_weighted_integral_bound`，只使用该已编译模块所带入的 mathlib 连续性、复指数、范数和 Bochner 积分接口。不存在把 FB 的高斯包络假设偷偷当作 FK 前提的情况。

FB 精确复用绑定为：源码 `dde1d75d0f69740c12e208af3cd47ac289cfe44909eccc1a1c56e6624b915dd4`（3892 B / 84 LF）；实际类型 `153e94a51ac637d1f4682e95bccf36c369c6ddd1b6b1b76c49bb88ed4d8ebd46`（1230 B / 21 LF）；资格记录 `41e368bfe12ccc6e13187ace8fb2884741d4310849385d5c2e1cd2b203c8d958`；已完整独立审查报告 `5bc4f3b72016590c833ac9517fb9a42190bd0975e613930b0c703732fadfeefc`（128 LF，父已完整读）；receipt `c55e11399c1129e0a7f85816024723c2f626e13038c1a14c56bf6e029be51d92`；首次成功原对象 `996c6fdeb24bd466f53e5cb0b025742d4005c5e72226366de72886be6c560613`（203264 B）。其一条 TYPE、零 VALUE、三处 let 与已资格化范围被保留；旧 CY 的历史对象归档局限没有被本报告扩大为更强的历史证据。

FK 的服务器依赖绑定于 `2026-10-27T18:53:56.068915+00:00` 记录新模块/对象尚不存在、己方实际 heavy 为空、锁空闲，并把唯一依赖的源码和上述已资格化首次对象绑定到已接受对象视图。它记录 `oldProofReplay=false`、`sharedCacheMutation=false`。FK 的 own-firstO 视图绑定只新增本模块原对象链接 1 条，旧条目变更 0、共享缓存写入 0、二进制复制 0。以上为已保存服务器观察，本人没有连接服务器重新观察或散列原对象。

FI246 不是 FK 的编译导入，也不是此证明调用的数学定理。我完整读取 `u22fi-qualification.json`（SHA256 `1ce857ba2cafeb5a8a2a501f699b85e0fdeaa10843f9fd9c6301de9381612a8c`），精确复用其中父已完整读过的 151 LF 独立报告资格；没有重审已接受 FI 全证明。该记录绑定 FI 源 `b2c8a569775bcb27ced07d4aa0272053d40e44f4d65cd10d720df09edf1c09a4`、报告 `bd2e53247870f87ef6424f9edc4955c834f9234b7df5a986d7ef2e5d64ea017b`、receipt `6bff49d8429051568103980d49fe518406110785fe8076550a90887f837b5f0a` 和首次对象 `cc7d825b6659f3bdc8af5bdf59fde0f2bb37bb212ad256382a1c46eb7f942c62`。其已资格化范围包含实际规范模型在原 `n^3 log(n)` 窗口的加权绝对误差真正可积性与误差连续性；FK 的后续实际消费者仍须明确代入同一误差、同一窗口及其证据。

## 首次对象、全实际所有权及递归公理证据

`u22fk-build-history.json` 恰有 native001：最终源摘要 `2e51...8796`，1995 B / 48 LF，自然 RC0，4.707207400351763 秒，完成于 `2026-10-27T18:54:09.739273+00:00`。日志绑定为 SHA256 `fe9a6b741bba0630c9977614157f0259907b0b7ebce576a9400b542ee4518626`、133 B；分派的执行事实记载无 warning。本轮没有另读服务器原生日志，退出码、耗时和日志摘要来自保存收据。没有先前失败、第二次成功或旧成功重跑。

同一首次原对象 SHA256 为 `5de2badad586e9c72065aa7a5ce1a588f1043d57027f1073315638837d06f712`、87760 B。own-firstO 记录将该对象链接到实际审计读取的 accepted-source-view；receipt/audit-record 以相同源、对象及实际类型摘要记录全实际所有者审计 RC0，5.628180706873536 秒，时间 `2026-10-27T18:54:19.006298+00:00`。审计日志为 `6aa50e1e5ea6b14c391d293c871494e825352ace120935ba0f3a9b0a8d89415d`、996 B。审计自身源码摘要与上表一致，不是用新对象替代首次成功对象。

完整 47 LF Audit 导入最终模块和 Lean，先检查冻结目标存在且为 theorem，再遍历 `env.constants.toList`，用 `env.getModuleIdxFor?` 和真实 `env.header.moduleNames` 选择实际模块所有者；不以命名空间前缀或手选公开名过滤常量。对每一实际所有者拒绝新 axiom，运行递归 `Lean.collectAxioms` 并拒绝标准白名单之外的公理，输出完整 TYPE；若为 `.defnInfo` 则输出完整 VALUE。最后检查所有者集合非空、冻结目标计数为一，并输出实际总数。因此私有/生成名如果存在也在所有权枚举范围内。

实际结果为 all_owned=1、all_theorems=1、public_theorems=1、non_theorem_values=0，唯一名字正是完整审查的公开定理；不是将预期公开数冒充实际所有者数。两个 let 是定理类型内部定义，没有未读顶层定义或需要另读的 VALUE。实际 TYPE 和递归公理并集均为且仅为 `propext`、`Classical.choice`、`Quot.sound`。源级完整证明审查与这些精确原对象的机器证据互补，未用打印巨型定理证明项代替源码审查。

收据保留 CPU36–39/44–47、`-M8192 -j4`、ROOT_OQ56_OQ3_40 及缓存感知内存准入观察；内嵌内存助手的历史 `phase` 标签仍为 ROOT_OQ56_OQ4_39，不把它解读为资源授权变更。源版本、对象、类型、冻结与审计之间没有矛盾。本轮没有新机器执行，亦不声称自己复测了实时资源或线程状态。

## 原始来源忠实性与明确未闭合范围

原 report 139–156 行把截断半径固定为 `n^3 log(n)`，分小频、紧中频、弱 Cramér 远频，并给出最弱远弧指数 `n^(1-(5/2)beta)/(log n)^beta`；末尾范围审计保留严格 `beta<2/5`，不含等号端点。完整 repair 明确 `0<beta<2/5` 和 Song 的 uniform-in-law Theorem 2.1、`s=8` 归属，修补小格振荡与精确边界 Laplace 常数 `v_corr`，并单列远区局部化条件。完整 verdict 保留真正联合非格点仍不足的已接受反例，只把正面命题视作一种充分修复，未声称最弱边界或历史首次。

FK 是无额外概率内容的通用分析引理；`e` 连续和加权绝对误差可积性是其已冻结的输入接口，供 FI246 已证实际误差消费。它没有把这两个通用输入当作原 OQ3 新增前提，也没有证明任何实际误差自动满足接口。FK 本身不含 `n`、`beta`、law/IID、累积量或 `Pn`，因此不能凭此 helper 单独宣称完成原 `n^3 log(n)` 模型装配；下一 FL 的实际代入尚须独立实现和核验。

原 report 220–235 行出现的 Hermite 修正密度及其积分识别，不由此范数不等式建立。真正密度、全 `ℝ²` 特征函数积分、反演/Hermite 对应、平滑/去平滑、外部概率论输入、B–D 与原根均保持 OPEN。p54/v_corr 修补、Song 一致律归属、严格指数范围与已接受反例均未被改动。此正确的积分支配是辅助步骤，不是傅里叶反演证明，也不具有独立新颖性或原根闭合的主张。

## 使用量与权限释放

实际模型/强度按本次分派为 `gpt-6.1-sol` / `xhigh`，fresh 独立审查。运行时 token 遥测未向本上下文提供：input_tokens=null，cached_input_tokens=null，output_tokens=null，reasoning_subset_tokens=null；null 表示不可用，不是零。不推算购买额度或订阅百分比精确分摊。

运行状态：`COMPLETED_STOPPED`。本报告的唯一写入/审查权限已释放；writer=0，children=0，Lean/AX/heavy=0，inflight=0，pending=0，uncertain=0。无后台继续执行。本独立最终审查已完成，等待父实例 ENTIRE 全读后自行决定资格化。
