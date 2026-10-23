# Actual D / uE 全实线二次分部积分与统一包络：完整独立终审

STATUS: CORRECT

审查者 `/root/common_low_whole_review`，实际模型 gpt-6.1-sol / xhigh，fresh 独立验证上下文；未参与声明或证明编写。使用 math-theorem，未使用 math-ultra、未创建下属。本轮只写本报告与配套 JSON；没有修改 Lean、执行 Lean 或重新收集公理。

冻结对象为 `Shao.Probability.SourceOddEvenWholeLineIBP`，提交 `a0f8ba9118e91f701b39db3b4e0abcddabb31992`（parent `4162f0318ddb5468367853b8a545484b71968f43`）的 583 行、31207 字节源码。SHA256 `51d8c67a85a4dac4d3b0db133ca8902da7a25ce13c868c65ef258ec987baf796`；对象 SHA256 `01f8df4d5fe563e6c4265f33b172655db220b91bacebe097f4ad5afe30bebdab`。本地、服务器现存源码、冻结 Git blob 三方哈希一致；只验收此精确版本。

## 冻结及原始语义

独立提取全部三个公开完整声明，与两个 active root freeze 的候选逐字比较，仅空白归一后全部相同：

- `quadraticFullNoise_odd_wholeLine_twiceIBP`。
- `quadraticFullNoise_even_wholeLine_twiceIBP`。
- `quadraticFullNoise_odd_even_derivative_envelope`。

两项旧公开声明还与封存的 v04-before-envelope 文件作原始字节比较，完全相同。`whole-line-original-public-header-hashes.json` 的散列口径包含 `:= by`，按同一口径得到原值 `9d621d14d98cedf080e6c1e8794b24d30b69c6a98dac46be6899c99749003b85`、`412860fec95c126ced2c3c7d5a93f96299b49f68772cd6ab3854b1dd29b952c8`。9436fc4d 开头的 fixed-v moment proposal 在实施前已被替代，不是本次 active contract。

完整读取 active 候选和合同，散列分别为 `05529e5474b849116d4d4d05dcc7dcaeb4c738c9352f238e3c6030d63d7a6c11`、`123e403ce3f7a3e307e9cf1a83721b3331e587c8257ddf44da783176ee619929`、统一包络补充 `834ef0694192f0b3975d015a6c8a62ad910effdcedb405f1209e4be54571887e`。

原始 read-only `main.tex` LF651–735（SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`）及 `supplement.tex` LF2350–2367、2560–2587（本批完整阅读范围包含 LF2325–2410、2560–2587、3400–3510；SHA256 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`）明确给出真实 D、E、Ξ=K(u,v)^8K(−u,v)^8ρhat(γu) 及全实线负逆平方 IBP 身份。实际 ScalarNoise 是既验收的固定紧支撑光滑密度，保留原文 rapid-decay 机制。

公开输入仍为同一真实概率律 ν、真实三矩可积、真实 variance(id)>0、h>0 及原 increment 的 a.e. 支撑界。无均值零、对称、γ≤2h、自由 regularity/decay/Fourier-L1 或 IBP 前提。所有 m∈ℕ（含0）与 v∈ℝ 保留；实 a 两个符号均覆盖，仅要求 a≠0。积分测度是整个实线的 Lebesgue volume，复数值 Bochner 积分；所有导数均为标准实参数 deriv 的真一阶/嵌套二阶导数。

包络量词是固定 ν/h/m 后先存在一个 B(u)，随后才 ∀u v；不是逐个 v 选择 B。B 非负并对每个自然 k 给出真正 `Integrable (|u|^k*B u)`。六个范数对象是实际 D、D'、D''、W=uE、W'、W''。

## 完整证明审查

| 全部手写声明/源码行 | 独立核对 |
|---|---|
| boundedC2（定义）13–16 | 对 f(v,u) 明确全局可微及 deriv 可微，并在全部 v/u 之前存在统一非负常数，约束0/1/2阶真实范数。它是内部包，不是公开所求结论的输入。 |
| boundedC2_const 18–22；add 24–40 | 真导数的全局身份先建立，再求二阶；常量 norm 和 A+B 同时控制所有 v。 |
| boundedC2_mul 42–84 | 正确二阶四项，交叉项两次出现；4AB 同时支付零/一/二阶。 |
| boundedC2_const_mul 86–87；pow 89–93；reflect 95–110 | 任意复数常乘、所有自然幂（0 用常量1）、实反射的一阶负号及二阶正号全部正确；uniform-v 性保持。 |
| characteristicMoment（定义）112–115；norm 117–120；hasDerivAt 122–132 | 实 X/Y 的相位模为1；j次 moment 因子为 (iX)^j，求导准确成为 j+1；不需要 Y 的矩。 |
| characteristicIntegral_hasDerivAt 134–152 | 对 j 与 j+1 真实 |X| 矩作 dominated differentiation，导数主控与 u/v 无关；有真实可测性与使用点 integrability，未假定可交换导数。 |
| characteristic_boundedC2 154–189 | 概率支付0矩；真实 |X|、X²支付一/二导数。常数 1+∫|X|+∫X² 在全部 v/u 前选择，所有 v 仅留在模1相位内。 |
| densitySchwartz（定义）191–193 | 真实 sourceScalarDensity 复值化后的 compact support 与 ContDiff∞，不是换成任意 Schwartz 函数。 |
| scalarChar_fourier 195–209 | withDensity 转为真实密度积分；Mathlib Fourier 的 −2π 相位在 −t/(2π) 处等于 +tr。密度非负支付 toReal_ofReal。 |
| scaledScalar_schwartz 211–222 | γ≠0 给 c=−γ/(2π)≠0 的真实连续线性等价，Fourier Schwartz 按此等价复合，逐点精确等于 sourceScalarChar(γu)。 |
| schwartz_product_data 224–255 | p 的真实 boundedC2 与实际 Schwartz 因子乘积；F'=p's+ps'，F''=p''s+2p's'+ps''。各项由实导数的可测性、uniform bound 和 Schwartz L1 支付。 |
| schwartz_product_envelope 257–319 | 真正构造 B=C(norm(s)+2norm(s1)+norm(s2))；SchwartzMap.derivCLM 是标准 deriv。每个 k 的三个多项式加权 norm-L1 逐项相加，真实支付 B 的所有矩；同一个 B 对所有 v/u。 |
| bounded_sin_mul 321–324；bounded_cos_mul 326–329 | sin/cos 绝对值≤1，真实 bounded multiplier L1。 |
| wholeLine_twiceIBP 331–373 | 先精确给 sin(au) 导数 a cos、cos 导数 −a sin；两次 Mathlib 全线 IBP 的三项 L1（uv'、u'v、uv）全部实际支付。最终 ∫sin F''=−a²∫sin F，所以 ∫sin F=−(a²)⁻¹∫sin F''。 |
| third_moment_pos 375–391 | 零非负真实三矩蕴含 id=0 a.e.，方差零矛盾；由此 γ=m3/V>0，未另加 γ 界。 |
| quadraticChar_boundedC2 393–404 | 真实 ν 的 a.e. 有界支撑支付 |a|/a² 可积；调用刚证明的真实 characteristic 积分。 |
| chord_boundedC2 406–415 | 真实 quadraticChordLaw 的概率、第一坐标绝对一矩与二矩由既验收 chord data/moments 支付；不用任意自由 K。 |
| signed_prefix_boundedC2 417–434 | 真实 φ(u,v)^m、φ(−u,v)^m，任意 σ，half-sum，实际两个8次 chord 因子逐项组装。所有 m/v 保持。 |
| odd public 436–471 | 真实 γ>0 支付实际 scalar Schwartz；σ=−1 前缀乘 s 逐点严格等于 D，再导出 D/D'/D'' L1 和 IBP；无 D-decay 假定。 |
| envelope public 473–540 | sU=u*s 由 temperate-growth ofReal 乘法保为 Schwartz。分别给实际 D 与 W 构造 Bo、Be，最终 B=Bo+Be 同时支付六范数和所有自然矩。B 在 v/u 之前选择。 |
| even public 542–581 | σ=+1 的真实前缀乘实际 u*s 精确等于 uE；不是把乘 u 的导数漏掉。三项 L1、真导数和同一负逆平方 IBP 完整支付。 |

已核对固定 Mathlib API：`IntegralEqImproper.lean:1369` 的 `integral_mul_deriv_eq_deriv_mul_of_integrable` 正是全实线 identity，三项 integrability 足以消除端点，实际应用以全局 HasDerivAt 支付其 tsupport 条件。两次都未用有限区间恒等式冒充 whole-line。另核对 Schwartz derivCLM、smulLeftCLM_apply_apply 和非零连续线性等价复合的真实接口；后者保留快速衰减，不能用零缩放。

m=0 不被排除：odd 前缀为0，even 前缀仍为实际 chord 乘积，W=uΞ，由实际 u*s Schwartz 机制支付。v 任意实数，所有 raw/chord 一二阶 bound 与 v 独立；不存在偷用低频、cone、γ≤2h、m≥6 或源归一化条件。

## 实际所属声明、公理与精确执行证据

完整源码1–583、全部45 ACTUAL_TYPE、全部3 DEFINITION_VALUE 均已完整阅读。包括21 private 手写引理、3 public 定理、18 generated 定理和3 private 定义；42项 theorem、0项 public definition。三个定义的实际值分别是 boundedC2 的显式量词包、真实 (iX)^j 相位、真实 density 的 toSchwartzMap。

18个生成项全覆盖：boundedC2_const._simp_1_1 为通用 norm 非负命题；densitySchwartz._proof_1/2 为真实复值密度 compact support/ContDiff∞；characteristicMoment.eq_1 为全部 Ω/μ/X/Y/v/j/u/ω 参数保留的实际定义方程。scalarChar_fourier._simp_1_1–7 和 wholeLine_twiceIBP._simp_1_1–7 各自依次为通用2/3/4非零、非零乘积、非零自然幂、非零整数幂、cast(n)+1非零的命题化简；各通用类型/类假定完整阅读，没有将其误当新的 source 假设。

全部类型/值日志为229918字节，SHA256 `5de32d36af6981118e70109faf103de6db1ec9f04563383febcc16afa93e2218`。重复标准实例/投影树以351个唯一别名作无损压缩，反向逐字符复原成功；所有数学类型、量词、测度与假设完整保留。45个导出名字与 audit JSON 精确相等，3个 value 名字正好等于其全部 definition；无省略号。

已完整阅读既有 `WholeLineIBPOwnedAudit.lean`（SHA256 `dd3e0951fbe8878acaafa1a620a1c899460218ecd6bb7a5f10815419ce38db8b`）和实际导出脚本（SHA256 `0e1a20395e36f7aa572d41a7d5f7ed4a41be27a4fadf57777c81b643bc23b23a`）。前者按 `getModuleIdxFor?` 精确 owner 遍历全部 private/generated/public，并对每项 `Lean.collectAxioms` 传递审计。audit JSON SHA256 `7fb5078b9f6ca85a28d5e77698887ef6dcab6ce5609a6621305d994d59cbf07e`、audit log SHA256 `6ae631bf363455d88e5c14f02260fd7e794c48c06084eae6492a0e304051c007`；kind/AX逐行与JSON匹配。所有45项仅白名单 propext、Classical.choice、Quot.sound。禁止构造零匹配，源 UTF8/LF、零CR。

复用作者原成功服务器检查：作者 receipt SHA256 `0f47eaf2fbe61ef49879ddb878135cb5a22ed1a770155ed705fc6a70cb6aaf09`。07和08/object日志均 SHA256 `e9b746e98480e7319e3328fda5e21c0c418b772d11f71b03513436d012e32700`；它们有旧 mathlib warning 和 `ring` 非终结提示，无 error。原执行 exit 补充 SHA256 `7207d72cdf7820196dc109323eccec1be7a2a1bc1f79472b8071b526259c7a1e` 本地/服务器相同：07原session13456/chunk991dff exit0；08/object、owned audit、actual export 原session50886/chunk2e6c62 exit0，原shell对每步非0立即退出。该补充追溯原执行，旧源码/对象/receipt/log 未改，未重跑。

实际读取项目 toolchain 为 `leanprover/lean4:v4.36.0-rc1`，mathlib Git HEAD `807d3836b165983210ee2ecf3cd28f239436949c`。原门使用 CPU10–13、root-heavy.lock、-M8192/-j4/-DautoImplicit=false。本审查不把只读哈希命令记为 Lean 验证。

旧依赖不重审证明：SourceFutureNoiseOddEven 的既有完整独审 CORRECT，source7de2d26d/objectf4d6d31b 与本 worktree 一致；ScalarNoise/Chord/FullNoise 的实际消费接口及完整源/对象绑定已核。此前七个冻结 source 全哈希逐项仍相同。原 root 安装的 SourceKernelAmplitudeFamily 未作为此模块数学增量或本审查接受对象。

本次接受实际全实线二次 IBP（D、uE）与同一 uniform-v 六导数多项式L1包络。未声称 marked pair/triple L1、joint measurability/Fubini、amplitude substitution、地域积分、概率贡献、去平滑或 C1/C2 根完成。后续消费者必须真实支付这些项。无实质缺口、无必要代码修复、无新颖性声明。两项分配终审均完成，普通审查执行已结束，无 Lean/写入在途。
