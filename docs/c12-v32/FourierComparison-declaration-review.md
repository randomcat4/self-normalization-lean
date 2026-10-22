# FourierComparison / QuadraticChordNoise 独立声明审查

结论：**CORRECT（仅声明阶段）**。冻结提案中的四个定义、四个公开定理忠实表达原文的真实三角弦构造、精确特征积分与锥内比较；未发现需要修改前提或结论的关键缺口。本票不是实现或 Lean 认证。

## 冻结对象与职责

- 审查对象：`drafts/c12/FourierComparison-next-scope.md`。
- 精确 SHA256：`912c3e001bcea85a64332c9efaf530ef55f3ddc0bf055841a762468a65a5ab44`。
- 拟实现：`Shao/Probability/QuadraticChordNoise.lean`，namespace `Shao.Probability`，四定义、四公开定理，`autoImplicit false`。
- 审查者未编写候选数学源码，未修改提案或既有库，未运行 Lean、目标检查、缓存探测或远程计算；只拥有本审查文件。
- 原文固定字节：main.tex `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`；supplement.tex `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`。

已核原文 main.tex 610–625、650–721 与 supplement.tex 1988–2042、3325–3357、3420–3467，并核对现有 QuadraticCharacteristic、LowFrequencyDamping、Power、OddPower 和已接受 SourceTruncationBridge 的相关接口。这里认证原文已明写的技术依赖，不作新颖性声明。

## 原文到四定义的对应

固定同一真实条件增量 law ν，记 `V = variance id ν`，`D = a − a'`，`θ = u + v(a + a')`。ν 不随频率更换，均值允许非零。

三角 law 是 Lebesgue measure 上的真实密度 `(1 − |t|) 1{|t| ≤ 1}`。偏置 pair 从同一 `ν.prod ν` 以真实非负密度 `D²/(2V)` 构造；其中分母是实际方差，不能换成 raw second moment。Chord law 是偏置 pair 与独立三角变量 T 的真实产品经 `(T D, T(a² − a'²))` 的推前。两个坐标共用 T 和 pair，故保留原文所需依赖；本票没有假定这两个坐标独立。

`quadraticChordChar` 是该真实 law 下的复相位积分，正号与现有 `quadraticChar` 一致，没有自由特征函数、自由乘子或所需 Fourier 差界作为输入。所有定义在 Lean 中虽为 total，概率解释只在明确的 `V > 0` 条件下认证。

## 四个声明的数学核验

**1. `quadraticTriangle_probability_char`：正确。** 密度非负可测，质量为 `2 ∫₀¹ (1 − t) dt = 1`。偶性使正弦积分为零；余弦积分在非零频率给 `2(1 − cos t)/t²`，频率零的真实积分为 1。闭区间端点处密度为零，没有质量歧义。结果允许非零频率处为零，未假设正特征函数。

**2. `quadraticChord_law_data`：正确。** 已接受 `quadratic_pair_square_moment` 对概率 ν 及 h3 给出真实 `Integrable D² (ν.prod ν)` 和 `∫ D² = 2V`，无需均值零。配合 hV，偏置密度总质量恰为 1。三角 law、产品及可测多项式 map 因而给实际概率 chord law。

原 law 的 AE 支撑先进入真实产品，再经绝对连续的 withDensity 和 map 传递。由 `|T| ≤ 1`、`|a|, |a'| ≤ h`，得到 `|Z| ≤ 2h`；又 `Y = Z(a + a')`，故 `|Y| ≤ 2h |Z|`。这是真实 AE 陈述，无需把 ν 的 AE 条件升级为逐点条件。所有实 u、v 的复相位模长为 1，真实概率 law 即支付其 Bochner 可积性；不需额外高阶矩。h3、hV、支撑与 h 均属于同一 ν。

**3. `quadraticChordChar_exact`：正确。** 在偏置 pair 上先对独立 T 积分，三角特征函数的输入恰为 `Dθ`。若 θ、D 均非零，则

`D²/(2V) · 2(1 − cos(Dθ))/(Dθ)² = (1 − cos(Dθ))/(V θ²)`。

θ 非零而 D 为零时，真实三角特征函数取零频率值 1，但偏置权重为零，两边仍为零；不能在这一集合非法消去 D。θ 为零时，三角特征函数同样为 1，真实贡献为 `D²/(2V)`，所以冻结 Q 的 `D²/2` 分支是必要且精确的连续延拓。特别在 u = v = 0 时，`∫ D² = 2V` 给 `K(0,0) = 1`；若零分支误写为 0 将立即错误。

对全部 pair，`0 ≤ Q ≤ D²/2`：非零 θ 分支由 `0 ≤ 1 − cos r ≤ r²/2`，零分支为等号。Q 为可测分段函数，pair-square 的真实可积性支付 Q 可积性；这里不需要有界支撑或第四矩。精确积分公式使 K 虚部为零且实部非负；同一支配积分还给 `K.re ≤ 1`。因此声明中的实区间界是被证明的结论，没有隐藏在输入里。

公开声明编码了 quotient 的正确连续零值，没有另外声明 Q 或 K 的全局连续性定理；实施和后续使用应保持这一精确范围。

**4. `quadraticChordChar_cone_gap`：正确。** 在真实产品的满测集上，`|a + a'| ≤ 2h`。闭锥条件 `|v| ≤ |u|/(4h)` 与 h > 0 给

`|u|/2 ≤ |θ| ≤ 3|u|/2`。

u ≠ 0 因而保护 θ ≠ 0、u² > 0；hV 保护 V 分母。平方再取倒数给

`4/(9u²) ≤ 1/θ² ≤ 4/u²`。

乘非负分子 `1 − cos(Dθ)`，积分并除正 V，随后使用同一 ν、u、v 的已接受 `quadraticChar_gap_identity`，恰得到冻结式的 4/9 和 4。没有额外 2 因子：偏置的 2V 已与三角特征式中的 2 相消。v 的锥边界取等号仍有效。未除以 characteristic gap 或 quadraticChar，因此 gap = 0 和 quadraticChar = 0 都保留。

## 量词与边界攻击

- **非中心、原子与零差值：** ν 为 {0,1} 上公平 law 时均值 1/2、V = 1/4；它直接满足所列矩条件。这验证不能偷加中心化、对称、无原子或密度假设。对角 D = 0 允许有正原 law 产品质量，已经在精确式中独立处理。
- **θ 的零集可有正质量：** 同一 {0,1} law 取 u = 1、v = −1，弦上 Y = Z，真实 φ 与 K 均为 1。Q 的连续分支给出正确值；此点不满足 h = 1 的锥条件。若删除锥，上界将错误地要求 1 ≤ 0。
- **单弦不具有单独 u 偶性：** 对该非中心两点 law，`K(u,v)` 等于三角特征函数在 u + v 的值，故 `K(−u,u) = 1` 而一般 `K(u,u) ≠ 1`。原文完整 Ξ 的 u 偶性来自两组反向 family，不能移植到当前 K。
- **共振与零 gap：** 对 {−a,a} 公平 law、a > 0、v = 0、u = π/a，有 `|φ| = 1`、K = 0，且满足锥条件；比较两端均为零。这不是遗漏的严格正 gap 条件。
- **退化方差和 cutoff：** Dirac law 的 V = 0 被 hV 明确排除；不把 total 除法的 0/0 行为认证成概率偏置。h > 0 明确保护锥分母，h = 0 的支撑本来也与正方差不相容。三角频率 t = 0、D = 0、θ = 0、u = v = 0 和闭支撑端点均有正确约定；仅锥比较排除 u = 0。

SourceTruncationBridge 对真实 `ρ = cond ν₀ {|z| ≤ ε/(1+x)}` 在其完整原有来源条件下支付这里的概率、h3、支撑、正 cutoff 与正方差。当前泛化 law 接口没有删去那些来源条件，也没有声称任意未截断 ν₀ 自动满足它们。

## 范围与后续接受门

本票允许 root 冻结当前精确提案后安排实施；没有声明修改建议或数学关键缺口。具体 Mathlib 积分接口可用性和实际编译尚未检查，不能预先标记 `LEAN_FULLY_CHECKED`。

实现后必须重新绑定精确数学源码 SHA、实际 server 目标与对象检查、全部 module-owned 声明（包括 private/generated/跨 namespace）的传递公理白名单、实际依赖与版本锁、禁用项扫描，以及新的独立完整 proof 和 source-to-statement 审查。四个定义及四个公开定理的 elaborated 类型必须与本冻结集合对应；不能以实现便利改变假设。根导入、manifest、完整集成门与 merge 仍由 root 负责。

本单元仅关闭真实单弦 law、三角特征积分、精确 K 与锥内 gap 比较。两组各八份的完整 Ξ、独立标量平滑噪声、u 偶性、完整支撑/矩预算、K/Ξ 导数、谱隙优化、高频衰减、Fourier 反演与各频区积分均仍待后续工作；本票不把 OddPower 与本 K 自动拼成完整 Fourier 比较，不改变 C1/C2 或其它根目标的 OPEN 状态。
