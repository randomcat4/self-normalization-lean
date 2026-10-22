# Rademacher 有限 S1：独立匿名数学审查 v1

STATUS: CORRECT
EVIDENCE: MATH_ONLY
SCOPE: frozen-rademacher-finite-s1-v1.md 的 C1–C5
FORMAL_CHECK: NOT_PERFORMED_IN_THIS_REVIEW
SPECTRUM_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN

JUSTIFICATION: 在本任务准许引用的固定上游数学引理接口下，匿名证明完整推出冻结的 C1–C5。全指标起点值、奇数指标双射、cot 有限和、真实乘积路径概率桥及独立低阈值分支均匹配冻结对象与全部量词；未发现关键数学缺口。此结论仅为数学审查通过，不是本叶或 AllModes 的 Lean 认证。

## 1. 阅读边界、独立性与版本

本审查在全新验证上下文中进行。只审阅指定冻结命题、一份匿名证明、指定原始来源、三个固定上游数学接口，以及必要的已认证公开签名和透明定义。没有修订命题或匿名证明，没有实施 Lean，没有有限实例枚举，没有外部检索，也没有把他人的审查判断作为正确性证据。

已先完整读取工作区 `AGENTS.md`、`SERVER.md`、`coordination/TEAM.md`；使用 `C:/Users/UIO/.agents/skills/math-theorem/SKILL.md`，并完整读取其 `references/prompt-library.md`、`references/openai-workflow.md`、`references/lean-verification.md`。本任务明确限定 MATH_ONLY，故不运行 Lean；全部 shell 调用的 workdir 均为 `C:/game/shao lean`，未运行本机 Lean 或重计算。

以下七份固定输入的 SHA256 与长度均已实际核对，并在报告落盘前再次核对一致。相对路径均以 `C:/game/shao lean/` 为根。

| 固定输入 | bytes | SHA256 |
|---|---:|---|
| `drafts/oq4/frozen-rademacher-finite-s1-v1.md` | 10956 | `e2e9240f739e737c83195f177dcd54707c023151cf3e4faf7f1d862e87b585fe` |
| `drafts/oq4/rademacher-finite-s1/proof.md` | 15767 | `5145ecabae8fd09c46bddf35ceda431c27633f40e29221e1ef3e7c25aad2d401` |
| `C:/game/shao/current/oq4/c01/spectrum01.md` | 4306 | `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b` |
| `drafts/oq4/frozen-rademacher-iteration-v1.md` | 5464 | `15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80` |
| `drafts/oq4/frozen-rademacher-finite-basis-v1.md` | 9862 | `4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f` |
| `drafts/oq4/frozen-rademacher-all-modes-v1.md` | 6845 | `dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10` |
| `drafts/oq4/rademacher-cosine/declarations.md` | 39048 | `e9ec045fccfd4ed68f5b6515f1b28310ab90bf71609cb7bba87a0c1b4d7f850c` |

原来源的版本锁为任务指定的 commit `35d4580b61e22e7145f47730045a09874ef93259`；本审查核对的是提供的来源文件内容哈希，未执行 Git 操作。来源全文为 119 行；仅其第 11–34 行用于本次数学范围核对，后续 S2–S5 不在裁决范围。

对 `rademacher-cosine/declarations.md`，实际展示和解析的行段为 148–179、213–280、334–453、518–598：包括 angle 的定义等式、halfENNReal 的定义等式、integer_closed_iff、killedKernel_row、law 的定义等式和 law_isProbabilityMeasure。334–367 的主余弦积分公开签名随指定段一并可见，但不用于替代全部模态。该文件中出现的 generated helper 仅展示完整类型，没有读取其证明体。

必要的只读 library 访问仅向验证上下文展示以下声明的完整签名、透明定义和 ambient variable/namespace 行。提取 theorem 签名时按括号深度寻找顶层 `:=`，没有把 `(n := n)` 等具名参数误当作证明体起点，也没有展示或使用旧 theorem 证明体。

| 只读文件 | bytes | SHA256 | 实际使用的内容 |
|---|---:|---|---|
| `library/Shao/OQ4/KilledKernel.lean` | 5403 | `f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f` | killedKernel 透明定义；killedKernel_apply 签名 |
| `library/Shao/OQ4/KilledIteration.lean` | 9162 | `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5` | killedIterKernel/action/mass 透明定义；zero、integrable、measurable、mass_eq_real、bound、action_zero、action_one、semigroup 签名 |
| `library/Shao/OQ4/KilledPathLaw.lean` | 13356 | `1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f` | shiftedClosedSurvival 透明定义；mass_eq_path_probability、shiftedClosedSurvival_eq_closedStrip、mass_eq_closedStrip_probability 签名 |
| `library/Shao/Basic/FinitePath.lean` | 10146 | `898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb` | Path、prefixSum 透明定义 |
| `library/Shao/Basic/ClosedSurvival.lean` | 6754 | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` | closedStrip 透明定义 |

为尝试读取必要透明定义而定向打开 `library/Shao/OQ4/RademacherCosine.lean` 时，该路径不存在，未返回文件内容；随后只使用上述已锁定 declarations 文件中的精确公开等式和签名。

未读取任何 intake、candidate、来源语义审查、其他数学审查、上游匿名证明、作者过程文件或新 Lean 实施；没有修改 frozen/proof/实施/canonical/Git/cache。没有意外向验证上下文展示旧 theorem 证明体。本报告是唯一写入的文件。

## 2. 依赖解释与真实对象核对

匿名证明第 11–128 行固定的对象与冻结命题一致：law 是内部概率实例支持的真实二点测度；`Path n = Fin n → ℝ`；prefixSum 是对 `i.val < k` 的有限和；closedStrip 对全部 `k ≤ n` 要求弱闭生存。对非负 h，额外的 k=0 条件由 S_0=0 自动满足，故与来源的 1≤k≤n 弱事件相同。n=0 由真实空路径集合处理，没有借用未定义的空集最大值。

已核对的 killedKernel_apply 是平移 law 后限制到 `Set.Icc (-h) h` 的真实测度；没有条件归一化。killedIterKernel 的透明定义为该核的自然数幂，killedAction 为其真实实值积分，killedMass 为对常数一的 action；零步核为起点 Dirac。匿名证明没有用一个新矩阵或新递推替代这些对象。

固定数学引理的引用点准确：

- FiniteBasis B2 对任意 `F : ℤ → ℝ` 及合法整数 r 给出范数 H 对应的显式重建；匿名证明只在第 350–360 行用 F=1、r=0 独立核对零步总和。
- AllModes D2 对相同 m、h、r、n 给出 `killedMass = ∑ q_j μ_j^n v_j(r)`，含全部 J_m、零谱、负谱以及 n=0；匿名证明第 303–307 行合法取 r=0。
- Iteration 的固定接口保持与上述相同整数网格和真实核；本证明没有另加网格保持假设，也没有重证或读取其匿名证明。

这些是本次获准引用的精确上游数学引理，不是本叶新增的自由输入或新公理。任务派发说明 Iteration 与 FiniteBasis 已完整形式认证；本审查不重做其认证。AllModes 仍在实施，不能把它写成已经形式认证。引用其固定数学接口足以进行当前模块式数学审查，但不能据此给本叶颁发 Lean 认证。

## 3. C1：全部零起点值

PASS。匿名证明第 132–191 行先对任意自然 j 使用 H>0 消去分母，得到

`v_j(0) = sin((jπ/(2H))H) = sin(jπ/2)`。

这一步没有先假设 j 为奇数。然后对自然 u 的加法公式归纳给出 `sin(uπ)=0`、`cos(uπ)=(-1)^u`。代入偶数 j=2u 得零；代入奇数 j=2ℓ+1 得 `sin(ℓπ+π/2)=(-1)^ℓ`。指数均为自然数，符号和相位与冻结值相同。

## 4. C3：完整指标分割、逆映射与端点

PASS。匿名证明第 142–165 行的自然数除法分割覆盖全部 `J_m={1,…,2m+1}`。

- 偶数 j=2u 满足 1≤u≤m；反向每个这样的 u 都落在 J_m。
- 奇数 j=2ℓ+1 满足 0≤ℓ≤m，即 ℓ∈range(m+1)；反向也成立。
- 两部分不交且穷尽；各映射的单射性由整数乘法消去直接得到。
- 在奇数部分，j≥1，故自然数 j−1 没有截断问题；j−1=2ℓ，因此自然数逆函数 `(j−1)/2` 确实返回 ℓ。
- ℓ=0、m 分别对应 j=1、2m+1=2H_N−1。偶数补集为 2,…,2m。奇数共 m+1 项、偶数共 m 项，总计 2m+1 项，没有丢末模态或纳入吸收端点。

这些结论足以重编号 D2 的同一个有限和，没有扩张到完整逐原子核谱。

## 5. C2：有限正弦和、非零分母与范数

PASS。匿名证明第 195–293 行对任意合法奇数 j=2ℓ+1 置 `θ=jπ/(2H)`、`t=θ/2=jπ/(4H)`。由于 1≤j≤2H_N−1 且 H>0，严格有 `0<t<π/2`，所以 sin t>0；cot 使用的全部角度均已覆盖，除以 `2 sin t` 合法。

状态变换 `k=s+H_Z` 把 `s=-m,…,m` 双射到 `k=1,…,N`，其中 N=2m+1，逆变换为 s=k−H_Z。实数转换后 s+H=k，故求和确为 `∑_{k=1}^N sin(kθ)`；两端实际状态映到 1、N，没有把 ±H_Z 放进状态集。

一般三角恒等式

`2 sin(θ/2) sin(kθ) = cos((k−1/2)θ) − cos((k+1/2)θ)`

逐项求和后，准确留下 `cos t − cos((N+1/2)θ)`。又 `N=2H−1`、`2Hθ=jπ`，故末项角为 jπ−t。j 为奇数给出 cos(jπ)=−1、sin(jπ)=0，故末项为 −cos t。于是有限和满足 `2 sin t · sum = 2 cos t`，得到 `sum=cot t`，而不是其负值或两倍。

最后仅按原 q_j 定义乘以 1/H。所用范数为 H，不是状态数 2m+1；无概率归一化混入。上述推导对全部合法 m、ℓ 成立，不依赖有限数值检验。

## 6. C4：真实路径概率的完整 S1

PASS。匿名证明第 297–344 行保留 `m≥1`、`m≤h<m+1`、全部自然 n。它们推出 h≥0，且整数 0∈I_m，恰好满足 AllModes D2 与真实概率桥各自的全部条件。

在 D2 中取 r=0 后，全部偶数被加项因实际 v_j(0)=0 而为零，对 n=0 同样成立。奇数部分按 C3 的双射重编号，再代入 C1 和 C2，并提出共同因子 1/H，得到冻结 C4 的同一显示式。没有把 signed μ_j^n 改成 |μ_j|^n，没有只保留主模态，也没有用渐近或概率上下界替代等式。

已认证公开桥的完整签名是：对概率 law、任意自然 n 及满足 0≤h 的实数 h，

`killedMass ν h n 0 = (Measure.pi (fun _ : Fin n => ν)).real (Shao.closedStrip h)`。

匿名证明第 331–340 行正确在已推出 h≥0 后使用此桥；law 及概率实例与上游相同。因此最后对象确为真实乘积路径测度对 closedStrip 的实值概率，不是把“概率”重新定义为矩阵总质量。集合概率和核积分在本稿中没有被逐样本恒等式替代。

## 7. 零步、零谱与负谱

PASS。匿名证明第 346–370 行显式检查了以下退化项。

1. 对每个实 μ，自然数幂 μ^0=1，含 0^0=1；C4 推导从未要求 n>0。以 B2 取 F=1、r=0 得 `1=∑ q_j v_j(0)`，相同偶数消去与奇数重编号即给 S1 在 n=0 的右侧为 1。真实零步 Dirac 也给左侧质量和路径概率为 1。
2. j=H_N=m+1 的角为 π/2，μ=0。若 m=2d，该指标为奇数 j=2d+1，落在 ℓ=d，cot 角为 π/4，零步贡献为 `(-1)^d/H`；稿件保留了该项，只有 n≥1 才以 0^n=0 消失。若 m 为奇数，该指标为偶数，消去原因是 v_j(0)=0，不是“零谱永不贡献”。
3. 合法 j>H_N 满足 π/2<θ_j<π，确有 μ_j<0。全部奇数负模态保留，尤其 j=2m+1、ℓ=m；偶数负模态仅按 C1 消去。没有额外时间奇偶、正谱、非零谱或无周期假设。

## 8. C5：独立低阈值及真实半群方向

PASS。匿名证明第 374–442 行另取全部 `0≤h<1`，没有把 C4 或完整谱基推广到 m=0。

已逐字核对 killedKernel_row 的公开类型：参数为任意 `m : Nat`、满足 m≤h<m+1 的 h、任意整数 r；没有 1≤m 或 r∈I_m 的额外前提。两项分别按整数条件 `|r+1|≤m`、`|r−1|≤m` 保留 halfENNReal 倍 Dirac，否则为零。因此取 m=0、r=0 时，两个条件都因 1>0 而失败，得到真实测度 `K_h(0)=0`，包括 h=0。

零步由真实 Dirac 得 `M_{h,0}(0)=1`。任意正自然 n 写作 1+k，令 g=T_{h,k}1。常数一可测且由 1 有界；killedAction_measurable 和 killedAction_bound 的完整签名确实给 g 可测且在所有实起点上 |g|≤1，无需额外网格或正生存条件。

实际 killedAction_semigroup 签名的方向为

`T_{h,a+b} f(z) = T_{h,a}(T_{h,b} f)(z)`，

条件仅为 f 可测有界及内部 law 概率实例。稿件合法取 a=1、b=k、f=1，于是

`M_{h,1+k}(0) = T_{h,1}g(0) = ∫ g dK_h(0) = 0`。

这里一次幂等于原核由真实 `killedIterKernel = K_h^n` 的透明定义及 K_h^1=K_h 得到。外层 T_1 先从真实零起点走一步，内层 T_k 作用剩余步，恰为所需方向；并未误用“所有其他起点的行也为零”。最后 0≤h 满足相同 closedStrip 概率桥，故全部 n 的 if 分支成立。

## 9. 阈值全覆盖与弱端点

PASS。匿名证明第 446–465 行对 h≥0 分成 h<1 和 h≥1。后者取非负实数的自然数 floor m，得到 m≤h<m+1；若 m=0 则 h<1 矛盾，故 m≥1，确能调用 C4。整数 h=k≥1 时选 m=k，没有换成 ceil(h)。

integer_closed_iff 的公开签名与稿件使用相同：对任意整数 s，在 m≤h<m+1 下，实数 |s|≤h 当且仅当整数 |s|≤m。因此 h=m 的 ±m 弱端点保留，±(m+1) 被排除；真实边界行向外的一半质量丢失，向内保留的一半不重新归一化。C4 与 C5 合起来覆盖全部 h≥0、全部自然 n；不需要生存质量非零，也没有在任何地方以它作分母。

## 10. 最终裁决与未关闭范围

C1、C2、C3、C4、C5 均为 PASS；在准许的固定上游数学引理接口范围内，无需作者修订或增补数学前提，未发现关键数学缺口。匿名证明与本次冻结 v1 对应，没有将完整有限谱公式弱化为主余弦、raw mass sum、有限实例或长期近似。

本报告的 `CORRECT` 严格限定为 `MATH_ONLY`。它不宣称本叶已经 PROVED/LEAN_FULLY_CHECKED，不代替后续来源到 Lean 陈述忠实性审查、真实上游导入接口一致性检查、实际 Lean 执行、传递公理与完整 canonical 审计，也不授权写入或发射 canonical 产物。尤其 AllModes 的形式认证仍需关闭；本报告没有把“固定数学接口”写成“已认证 Lean 定理”。

本叶之外的 S2 正负配对与统一余项、S3 布朗基准、S4 实阈值格点位移渐近、S5 临界子列、strict 事件及其端点分类、其他实起点 coset、逐原子或任意测试函数完整核谱、sharp01 和一般 OQ4 均不由本次审查关闭。Spectrum/OQ4 根继续 OPEN。
