# 第269单元独立源码与证明审阅

STATUS: CORRECT

JUSTIFICATION: 对精确冻结的局部命题，已完整审阅新64行源码、其中15行声明与38行证明。先由原乘积测度下的 L² 假设及包络平方可积性建立两侧可积，再平方原几乎处处包络、比较积分、分解同一乘积测度上的乘积矩，最后对非负预算取平方根。未发现关键数学缺口、额外假设或目标循环前提。

这是 SOURCE／PROOF 阶段裁决。`machineChecked = false`、`qualified = false`；本审稿人未运行 Lean、工具链探测、服务器检查或公理审计。实际类型、全部所属声明及传递公理证据仍须由负责人后续提供并另行激活本独立最终审稿人。此报告不代表共同窗口、原概率尾界、完整 OQ56 或根目标已经完成。

## 独立性和精确版本

独立审稿角色为 `/root/oq56_unit269_review`，唯一写入范围为 `drafts/oq56/unit269/source-review-01`。作者角色已在其唯一 `LASTFINALWRITE.json` 释放作者、写入、执行、发布及子上下文权限；本审稿人未写作者源码、冻结声明、库或共享协调文件，未修订命题或证明，也未委派工作。

激活文件为 `source-review-ACTIVATION.json`，4348字节，SHA256 `df6d6b3c662a7dd9b822ab57e398037903a8d8d411b1c3dd01281c1254913355`。其14项输入逐一核对实际字节数与 SHA256，全部匹配。作者清单的5项载荷及最终释放记录的3项交叉绑定亦匹配。初始实际阅读确认见同目录 `READ_ACK.json`。

本裁决绑定源码 `author-01/OriginalEnvelopeRhoBound.lean`：2735字节、64个 LF、SHA256 `5fc29e9c832de61f4cb1d7e85a54b0499fe4cf263ae1190922f4196474840fc8`。绑定证明 `PROOF.txt`：1794字节、38个 LF、SHA256 `113b55f719ad99bef2cef92d1f28fd1e638342f98314f787529f11e5609baeba`。冻结 HEAD 为708字节、15个 LF、SHA256 `e6b29476dcf4dbe33d50bfd3b15c28fcee9b95555b8c9da63966836fb0587e4e`。

独立字节比较确认：源码严格等于 `PREAMBLE + HEAD + PROOF + CLOSING`。源码1–9行对应前言9行，10–24行对应冻结 HEAD 1–15行，25–62行对应证明1–38行，63–64行对应结尾2行。相同字节只计一次语义审阅，覆盖没有空洞。源码仅有冻结的一个公开定理，无新增辅助声明；禁止项静态扫描为空。这一静态结果不替代实际所属常量清单或传递公理审计。

## 陈述与原接口对应

冻结命题在任意 `Ω : Type u` 及原 `MeasurableSpace Ω` 上，取原概率测度 μ、实核 r、实包络 w、同一实预算 M。完整前提是：原 `μ.prod μ` 上的 `MemLp (Function.uncurry r) 2`；`w ≥ 0` 几乎处处；`w²` 对 μ 可积；`M ≥ 0`；`∫w² ≤ M`；原乘积测度下 `|r(o,y)| ≤ w(o)w(y)` 几乎处处。结论将 `v` 定义为原乘积测度下的真实 `∫r²`，将 `rho` 定义为 `Real.sqrt v`，并按冻结顺序给出 `0 ≤ v ∧ v ≤ M² ∧ 0 ≤ rho ∧ rho ≤ M`。

已完整读取第268单元冻结 HEAD。其原 `g(o)=∫h(o,y)dμ(y)`、`r(o,y)=h(o,y)-g(o)-g(y)`、`v=∫r²d(μ.prod μ)`、`rho=sqrt v` 在 HEAD 21–25行；同一 w、`hW/hSq/hSqBound/hEnv` 在26–33行，预算为外层已固定的 `Menv ≥ 0`。因此本辅助定理的实参映射为：同一 Ω、同一原可测空间、同一 μ、该原 r、同一 w、`M := Menv`。显式 `@Measure.prod Ω Ω mΩ mΩ μ μ` 与此处 `μ.prod μ` 只在类型类参数写法上不同，测度和可测空间完全相同。

已读旧 `ActualQuadraticTiltMoments.lean` 的完整公开合同186–279行和所需上下文。该合同在原 μ 下定义同一 g/r/v，并在236行给出原 r 对原 `μ.prod μ` 的 L² 性；`Function.uncurry r` 与 `fun o => r o.1 o.2` 定义相同。此旧合同的哈希为 `f4772e78008aad28d89f99a6c52e63ba15329fab40c1b66fb41dc2ed3b249d10`，23460字节。本次只复用其既有合同，未重新认证旧证明；新源码本身只导入该模块，并未调用其带倾斜矩结论来假定新目标。旧合同中另有倾斜测度 ρ 及其矩 A/B/D，均未被混同为本次原 v。

本单元所需 `hr2` 是可积性输入，并非 `v ≤ M²` 或 `rho ≤ M`；`hSqBound` 是原先保留的包络二阶矩预算，不是新残差矩预算。定理没有加入 `hGeometry`、目标尾界、共同窗口或欲证结论作为前提。后续消费者仍须在其实际上下文提供并实例化 hr2；本报告没有声称第268单元消费者已经修改或共同窗口已闭合。

## 完整数学核验

令 `q(o)=w(o)²`、`I=∫q dμ`。冻结的 hSq 使 q 可积，I 是有限实数。q 处处非负，所以 `I ≥ 0`；hSqBound 给出 `I ≤ M`。

源码27–29行先以 `MemLp.integrable_sq` 从 hr2 得到 `(o,y)↦r(o,y)²` 对原 `μ.prod μ` 可积。`Function.uncurry` 的展开只改变写法。30–32行由两份 hSq 与 `Integrable.mul_prod` 得到 `q(o)q(y)` 对同一乘积测度可积。两项均在50行使用积分单调性之前建立，因此没有借用不可积 Bochner 积分的默认零值来证明上界。

33–38行只在 hEnv 的原乘积测度满测集上推理。设该点为 (o,y)，则 `0 ≤ |r(o,y)| ≤ w(o)w(y)`；非负数幂的单调性给出 `|r(o,y)|² ≤ (w(o)w(y))²`，再用 `|r|²=r²` 及 `(ab)²=a²b²` 得到 `r(o,y)² ≤ q(o)q(y)`。右侧底数的非负性已由上述夹逼蕴含，不需要额外搬运单边 hW 的满测集，也没有把几乎处处结论提升为处处结论。冻结的 hW 保留但未使用；它对这个局部不等式是冗余条件，不是遗漏的证明义务。

39–44行分别对处处非负的 r² 与 w² 使用积分非负性。45–57行用已经建立的两侧可积性与几乎处处比较得到

`v ≤ ∫q(o)q(y)d(μ.prod μ) = (∫q dμ)(∫q dμ) = I² ≤ M²`。

中间等式来自同一 μ 与同一 μ 的乘积积分公式；这里不是对任意相关二元分布作错误的独立性分解。μ 为概率测度，提供所需有限性及 σ 有限性，ℝ 提供该公式的标量、完备与范数结构。虽然保存的 Mathlib `integral_prod_mul` 以全定义 Bochner 积分写成无显式可积前提的公式，本使用点已另证 q 和 q⊗q 可积，故有通常有限矩/Fubini 意义。最后一步以 `0 ≤ I` 与 `I ≤ M` 对非负数平方，方向正确。

58–62行保持原 `rho=sqrt v`。`Real.sqrt_nonneg` 给出 rho 非负；`Real.sqrt_le_sqrt` 从 `v ≤ M²` 得到 `sqrt v ≤ sqrt(M²)`；原 hM 使 `sqrt(M²)=M`，不把 `|M|` 偷换为 M。四个合取结论均已建立。v 非负也已单独给出，未依赖平方根对负数的默认约定。

## 被调用合同及条件

下列完整承重签名及其命名空间、类型与测度上下文已从本地保存的固定版本接口读出；没有访问服务器或网络。固定项目版本为 `leanprover/lean4:v4.36.0-rc1`，Mathlib 为 `807d3836b165983210ee2ecf3cd28f239436949c`。这里只是读取版本文本，未探测或运行工具链。

| 调用 | 已读合同与本次条件 |
| --- | --- |
| `MeasureTheory.MemLp.integrable_sq` | `{α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ} (h : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ`。已读固定提交保存片段 `L2Space.lean` 28–43行，包含完整上下文；本次 α 为 Ω×Ω，测度为 μ.prod μ。 |
| `MeasureTheory.Integrable.mul_prod` | `{L : Type*} [NormedRing L] {f : α → L} {g : β → L} (hf : Integrable f μ) (hg : Integrable g ν) : Integrable (fun z : α×β => f z.1*g z.2) (μ.prod ν)`。已读 Prod 48–60、278–305行，定理显式省略无关的 SFinite ν 条件；本次 L=ℝ，两份输入均为 hSq。 |
| `MeasureTheory.integral_nonneg` | 对实值情形，`(hf : 0 ≤ f) : 0 ≤ ∫x, f x ∂μ`。已读 Bochner Basic 141–154、179–185、616–673行及相关有序结构上下文；两被积函数均为实平方。 |
| `MeasureTheory.integral_mono_ae` | `(hf : Integrable f μ) (hg : Integrable g μ) (h : f ≤ᵐ[μ] g) : ∫f ≤ ∫g`。本次明确传入 hrSq、hProductSq、hSquareEnvelope，三者同一原乘积测度。 |
| `MeasureTheory.integral_prod_mul` | `{L : Type*} [RCLike L] (f : α→L) (g : β→L) : ∫z, f z.1*g z.2 ∂μ.prod ν = (∫x,f x∂μ)*(∫y,g y∂ν)`。已读 Prod 332–350、438–448、509–541行，并确认外层 SFinite μ/ν 上下文；原概率测度满足。 |
| `pow_le_pow_left₀` | 在实数满足的有序带零幺半群及乘法单调结构上，`(ha : 0 ≤ a) (hab : a ≤ b) : ∀n, a^n ≤ b^n`。已读代数 Basic 403–407、512–518行及上下文。两次分别取 a=|r|、a=I，n=2。 |
| `Real.sqrt_nonneg` | `(x : ℝ) : 0 ≤ Real.sqrt x`；已读 Real 命名空间与143–145行。 |
| `Real.sqrt_le_sqrt` | `{x y : ℝ} (h : x ≤ y) : sqrt x ≤ sqrt y`；已读208–210行及实数变量上下文。 |
| `Real.sqrt_sq` | `{x : ℝ} (h : 0 ≤ x) : sqrt (x^2)=x`；已读180行及上下文，本次输入为 hM。 |

`sq_abs`、`mul_pow`、`pow_two`、`abs_nonneg`、`sq_nonneg` 仅实现上文逐式核对的实数绝对值/平方恒等式与非负性；`filter_upwards`、`simpa only`、`dsimp only`、`refine` 只组织这些已说明的数学步骤，不藏有额外假设。源码没有调用新的未证辅助引理。实际导入闭包、参数推断和精确 TYPE 接受仍属于后续服务器机械阶段，本 SOURCE 阶段不伪造该结果。

Prod 与 Bochner Basic 的实际本地字节/哈希已分别匹配保存的 `verified-source-files.json`：32338字节/`8ccfbcad5fffde3f8d0dfa3167b80dacfb524bc10790f1744b8b8a9b3f4c3a05`，72547字节/`66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670`。L2 完整签名保存片段明确绑定同一 Mathlib 提交及原文件 `c5737e32b9b1e2a6a0d04b411244ed90d0fcf25aab0449b51865d39182eb4593`。补充接口文件本身的本地哈希列于覆盖清单，未把它们当作当前服务器运行证据。

## 边界、量词和对抗核查

- M=0：`0 ≤ I ≤ 0`、`0 ≤ v ≤ 0²`，因此 I=v=rho=0；证明没有除以 M、I、v 或 rho，没有严格正性遗漏。
- 等号：`I=M`、`v=M²`、`rho=M` 均可取等，所有比较都是弱不等式。任意概率空间上的常值 `w=c≥0`、`r=c²`、`M=c²` 达到等号，也核对了预算的幂次。
- r=0、w=0、M较大或较小的非负值均沿同一推导。未要求 r 的点态可测版本；hr2 含所需几乎处处强可测性，hSq 含 q 的所需可测与可积条件。w 本身不另需点态可测。
- Ω 仅有原可测空间；无标准 Borel、可数生成、有限支持、可分、非原子或拓扑空间假设。概率测度本身是冻结输入，未构造新测度或完成化/编码新的 Ω。
- 所有零测集在原 μ 或原 μ.prod μ 上使用；没有错误地从单边几乎处处断言逐点乘积结论，也没有对对角线另加质量假设。
- 定理对任意满足前提的 r 成立，故不必为该局部界增加对称性、规范性、均值为零等条件。应用于原残差时仍使用同一残差，而不是把泛化的 r 误称为已经完成原核模型。
- 未把有限样本、数值检验或某个特殊分布代替一般证明；本轮未运行此类计算。没有假设目标界，也没有把另一方差、新预算或倾斜二阶矩放入原 v 的位置。

## 覆盖、保留范围和阶段结束

新源码1–64行全部覆盖；其中声明10–24行、证明25–62行完整覆盖。冻结 HEAD 及证明文件与相应源码范围相同的字节不重复计审；精确映射见 `SOURCE-COVERAGE.json`。14项激活输入及作者清单/释放的交叉绑定全部通过；SOURCE 阶段结束前再次核对原输入未变。

本单元是包络二阶矩到原残差平方根尺度的局部辅助定理。共同相对窗口/吸收、实际 p54 条件模型与均值/方差/分布、外部 hSZ/hSZC 存在性、DC、完整 OQ56 和根目标均保持 OPEN；本轮未开展新颖性裁决，也不把这一初等积分辅助界包装为独立新研究成果。

SOURCE 阶段完整通过且无修订要求。后续待负责人绑定同一源码的服务器目标成功、同一首个原始对象、完整实际 TYPE/必要 VALUE 与全部所属声明的递归 AX 证据；再由本角色按新的机器阶段激活核对，当前 `qualified` 仍为 false。公理白名单为 `propext`、`Classical.choice`、`Quot.sound`，本轮没有声称实际传递闭包已经符合白名单。

请求模型/努力为 gpt-6.1-sol/xhigh；本工具环境未暴露实际 model/backend/effort，亦未暴露 input/cachedInput/output/reasoningSubset，分别记录 null，不把请求值或估算量当成观察结果。

本角色阶段结束时 proofWriter/heavy/inflight/uncertain/pendingExternal/children 均为0，仅声明本审稿角色的本地六零，不代表观察了其他线或服务器。保留同一独立最终审稿人身份，普通最终答复结束本回合；没有活跃等待、轮询、睡眠或自动延续，机器阶段须另有明确激活。
