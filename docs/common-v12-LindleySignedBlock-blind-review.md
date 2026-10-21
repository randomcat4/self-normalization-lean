# LindleySignedBlock 最终独立源码语义与证明审查

STATUS: CORRECT（源码数学审查）

本裁决覆盖冻结实现的全部定义、公开声明、十四个私有 helper 及证明论证，范围是源文的历史事件带权有限 signed-block 支付。未发现数学声明改变、源语义偏离或证明缺口。未运行本机或服务器 Lean，未重跑目标编译或公理审计；作者服务器回执仅作为另行执行记录，不作为本报告的数学依据。仅新增本报告，未修改实现、scope、归档、旧依赖或他人文件。

## 冻结绑定与 scope 比对

- 实现：C:/game/shao lean/drafts/c12/LindleySignedBlock.lean，428 行。
  SHA256：a9f959580b66cc8de684ebe93be0bce360db44e30f5a7ea93b4e85bc9730dd15。
- 原声明提案：LindleyFourier-next-scope.md。
  冻结原始 SHA256：99f2a8c006c56569cbc34514786c9f7ac972d8892cf5171a826f4b8b5a44773e。
- 当前含状态更新及 implementation receipt 的 scope：
  C:/game/shao lean/drafts/c12/LindleyFourier-next-scope.md。
  本轮实际 SHA256：73b86a7475d461d230bc8ec27d2ab8d761d928044cc31b1188165eb5751702a8。
- 已接受有限未来核依赖：C:/game/shao lean/drafts/c12/LindleyTelescoping.lean。
  本轮复核 SHA256：518b7029d435ddd3b32a414f8893d6c49e26910cff18117d8da0cc6eb67bc93c。
- 原 main.tex SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- 原 supplement.tex SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

版本记录另作精确说明：协调者提供的归档路径 C:/game/shao lean/runs/programme-20261021/proofs/LindleyFourier-next-scope.md 在本轮读取时同样为 73b86a…，与当前 draft 逐字 diff 无差异，不能将该归档声称为 99f2a8c… 原字节。为独立核实数学正文未变，审查者只在内存中将当前 scope 还原为本线程初次实际读取的原 Status 段、两条原 ledger 状态和原 minimum-next-action，并移除后来附加的 implementation receipt；所得 UTF-8/LF 内容 SHA256 精确复现 99f2a8c006c56569cbc34514786c9f7ac972d8892cf5171a826f4b8b5a44773e。没有写回任何文件。因此数学正文、代码签名和原来源锚点保全，整文件差异确为上述状态/回执变化；报告没有以新 scope 摘要冒充原冻结提案。

复用先前独立声明盲译及来源审查 LindleySignedBlock-statement-review.md，并逐项核对本轮实际实现。公开内容保持为 1 定义、4 定理；新增的 @[instance_reducible] 是 measurable-space 类值定义的归约属性，没有新数学前提、事件重定义或 sigma 完备化。源码只导入已接受 LindleyTelescoping，未通过不稳定 _private 名称调用其 helper。

## 实际全部公开声明与量词

记 a(ω)=(X₀(ω),…,Xₙ₋₁(ω))，W₀=0、Wᵣ₊₁=max(0,Wᵣ+Xᵣ)，Qᵣ=∑ⱼ<ᵣXⱼ²，Qₙ=同一条路径的 energy。fℓ 是既有 ν 的真实 ℓ 维乘积未来核。零基 r 的实际缺陷为
\[
 \Delta_r=f_{n-r-1}(0,Q_{r+1})
        -f_{n-r-1}(-\max(-(W_r+X_r),0),Q_{r+1}).
\]
它不是任意 bounded correction，且两个分支都使用实际 Qᵣ₊₁。

1. **lindleyHistory（19–23 行）。** 任意 n、任意类型 Ω、任意 X:Fin n→Ω→ℝ、任意 k≤n；定义为实际原始前 k 个坐标路径 pₖ 的 Borel comap。定义本身不假设 Ω 的环境可测结构或 X 可测。
2. **lindleyHistory_eq_iSup（25–33 行）。** 相同任意参数下，history 等于所有 j:Fin k 对应原坐标 Xⱼ 的 Borel comap 的上确界。没有遗漏部分坐标，没有柱事件限制；k=0 为 ⊥。k=n 是全部有限样本生成的 σ-代数，不声称等于环境 σ-代数。

以下三条的共同真实量词为：任意 n∈ℕ、任意带可测结构的 Ω、概率 μ:Measure Ω 与 ν:Measure ℝ、每个 Xᵢ 可测、iIndepFun X μ、每个 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib；任意 k≤n、任意 E∈lindleyHistory X k hk；任意可测 ψ:ℝ²→ℝ 且处处 0≤ψ≤1。没有中心化、矩、正方差、正能量、μE>0、条件独立或目标望远镜作为前提。

3. **iid_lindley_future_step_on_history（196–211 行）。** 对任意 i:Fin n、r=i.val 且 k≤r，
   \[
   \int_E f_{n-r-1}(W_r+X_r,Q_{r+1})\,d\mu
   =\int_E f_{n-r}(W_r,Q_r)\,d\mu.
   \]
   当前原编号为 r+1，故事件确在该步之前可测。左侧第一坐标尚未反射，第二坐标已含 Xᵣ²；全程使用原 μ 的 set integral 和原 ν 的未来核。
4. **iid_lindley_signedBlock_identity（308–323 行）。**
   \[
   \int_E\sum_{r=0}^{n-1}1_{\{k\le r\}}\Delta_r\,d\mu
   =\int_E\{\psi(W_n,Q_n)-f_{n-k}(W_k,Q_k)\}\,d\mu.
   \]
   mask 恰选 r=k,…,n−1，即源一基 k+1,…,n。结论是期望恒等式，不是两内部随机变量逐点相等。
5. **iid_lindley_signedBlock_bound（398–408 行）。**
   \[
   \left|\int_E\sum_{r=k}^{n-1}\Delta_r\,d\mu\right|
   \le(\mu E).{\rm toReal}.
   \]
   绝对值保留在整个带符号块积分之外。概率 μ 保证右端有限且是实际事件概率，未出现 n−k 损失。

## 全部基础 helper 的证明审查

- **35–44 行：路径前缀与真实递归状态可测。** prefixPath 逐坐标取值可测；Wₖ 使用已接受的点态 “反转原前缀的 maxWithZero” 表示，配合真实前缀和固定反转映射得到可测性。这里没有把终时 Wₙ 与原顺序 max 的分布等式误当逐点等式。
- **46–61 行：有限测度下真可积性。** 实值可测 [0,1] 函数由可积常数 1 支配；kernel 合成项使用已接受的一般 kernel 可测性和真实 [0,1] 界。ρ 可以是有限限制测度，不要求其为概率；ν 的未来核仍是真概率。
- **63–81 行：真实 Qᵣ₊₁=Qᵣ+aᵣ²。** 把严格前缀 filter 扩为插入当前 i，验证 i 不在旧 filter 后求和。边界 i=0 和 i=n−1 均正确。
- **83–113 行：前缀依赖和插入坐标不变性。** state_prefix_congr 先证明实际 prefixPath 相等，再使用既有点态状态公式；squares_prefix_congr 只在 j.val<k 的真正 filter 上替换坐标。state_insertNth、squares_insertNth 在 j<i 的每一项使用 insertNth_apply_below，因此更改当前 i 值不影响 Wᵢ、Qᵢ。
- **115–124 行：整个历史前缀在当前坐标插入下不变。** 由 j<k≤i.val 得 j<i，逐坐标证明 prefixPath(insertNth i z b,k)=prefixPath(insertNth i 0 b,k)。使用的正是冻结条件 k≤i.val，未把它换成含当前坐标的 k=i.val+1。
- **126–142 行：真实乘积坐标拆分。** measurePreserving_piFinSuccAbove 的逆对应 insertNth，从 ν×νⁿ 到 νⁿ⁺¹；hp.measurable 给合成可测。换元后，在 141–142 行 integral_prod_symm 之前明确用 [0,1] 界证明乘积被积函数可积。外层是其他坐标 b，内层是当前 z；不是假设一个无关独立副本。
- **144–175 行：有限尾段 cancellation。** 首先通过两种有限总和公式证明一般相邻差和。尾段令 Gⱼ=f_{max(k,j)}：j<k 时相邻值都为 fₖ，j≥k 时恢复原相邻差；Gₙ=fₙ、G₀=fₖ。索引 max(k,j)≤n 由 hk 和 j≤n 推出，没有越界扩展。k=n、n=0 均在相同证明中成立。
- **185–192 行：真实 iid 路径积分转移。** 从已有完整 samplePath IdentDistrib 合成可测 F，再用 integral_eq 转到 νⁿ。F 的额外可积性不是此同律等式的前提；本次使用的 LW/RW 已另证 [0,1] 界和可测性，后续 Fubini 使用真可积性。

以上十四个私有 helper 均按实际声明和证明阅读，没有引入新的概率独立、半群、加权等式或有待证明目标作为假设。

## 核心证明一：每个历史事件的真实带权单步

**212–222 行**直接将 hE 按 comap 定义展开为存在 Borel B⊆Path k，使 E=pₖ⁻¹(B) 精确相等。rcases 的 rfl 代入的是全事件等式，不是仅 a.e. 的表示。n=0 的分支用不存在的 i:Fin 0 排除。其余分支定义完整路径事件 P={a:prefixPath a k∈B}；hP 证明其路径可测性，hEamb 通过 hX 证明 E 的原环境可测性。这覆盖所声明 history 中所有事件，没有缩小到矩形柱集，也没有添加环境可测前提或 σ-代数完备化。

**223–252 行**定义真实 L、R，并分别证明可测和 [0,1] 界，再形成 LW=P.indicator L、RW=P.indicator R。指标不属于 E 时值为零，属于时等于 L/R，故两带权函数同样是可测 [0,1] 值函数。

**253–258 行**先由 hEamb 合法把原 set integral 改为真实指标积分，再用 iid_integral_path 转移到 νⁿ，随后才使用真实 product coordinate split。没有将无权 iid_lindley_future_step 在 μ.restrict E 下调用，也没有声称受历史条件限制后的所有原坐标仍有原 iid 律。

**261–280 行**固定其他坐标 b，内层真实 L 积分用 Qᵢ₊₁=Qᵢ+z² 和 Wᵢ/Qᵢ 插入不变性化为
\[
 \int f_{n-i-1}(W_i(b)+z,Q_i(b)+z^2)\,d\nu(z).
\]
hlen 由 i<n 给出 n−i=(n−i−1)+1；已接受真实 kernel semigroup 将其识别为 fₙ₋ᵢ(Wᵢ(b),Qᵢ(b))。R 内层确为常数，以 ν 概率质量一积分。这一步没有把 Qᵢ₊₁ 错误冻结为 Qᵢ。

**281–304 行**另证 hPconst：由于 k≤i.val，P 的整个前缀不随 z 变化。随后按固定 b 的 P 成员性分支：在 P 中两指标函数分别恢复 L/R，并使用 hcore；不在 P 中两边全部为零。原历史权重被真实保留，而不是在未经证明时从无权等式上乘一个随机变量。该段精确完成了声明审查时要求的新证明义务。

## 核心证明二：只在积分内有限望远镜

**324–327 行**定义 Tⱼ=∫E fₙ₋ⱼ(Wⱼ,Qⱼ)，其值是标量期望，而不是任意路径wise 替代。所有时间索引均在 Fin(n+1)。

**331–344 行**分别在有限 μ.restrict E 下构造反射后当前项 hcurr 与反射前项 hpre 的真可积性。此处使用限制测度仅作积分和可积性运算；没有给它概率实例或调用其下 iid。

**345–361 行**调用刚证明的带历史单步，将 Tᵢ 的积分替换为反射前积分；在 hcurr/hpre 已成立后于 353 行使用 integral_sub。随后点态使用真实 lindleyState_succ 和纯量 reflection_defect，得到
\[
 T_{i+1}-T_i=\int_E\Delta_i\,d\mu.
\]
反射缺陷的两个分支始终保留同一个实际 Qᵢ₊₁。这是合法的积分内等式，未错误断言 Fᵢ₊₁−Fᵢ=Δᵢ 点态成立。

**362–378 行**用真实 f₀=ψ 和 Qₙ=energy 得到终点 Tₙ；既有 integrable_lindley_test_and_delta 给每项 Δ 的原 μ 可积性，再限制到 E，建立每个 mask 被积函数 hmasked；终点 hterminal、起点 hstart 也各自可积。

**379–394 行**只有在上述 hmasked 后才调用 integral_finsetSum，随后逐项替换为 T 的真实差，使用 sum_fin_tail_sub 得 Tₙ−Tₖ；最终 hterminal/hstart 保障 integral_sub，把结果写回端点差的 set integral。没有逐项绝对值、无限和或不合法积分交换。

## 核心证明三：常数一乘真实事件概率

**409–424 行**首先重写为刚证明的端点差恒等式。对每个 ω，终端 ψ 与起始 future kernel 均在 [0,1]；415–421 行分别用这两个真实界得到差的绝对值至多一。422–424 行对有限 μE 使用实际 norm_setIntegral_le_of_norm_le_const_ae，将 C=1 的结果化为 (μE).toReal。

没有使用 ∑|Δᵢ|，没有 n−k 因子，也没有除 μE 或任何正质量条件。该常数一与源文相同。所需 Mathlib comap、有限乘积拆分、set-integral norm API 的真实类型已经在此前独立声明/依赖审查中通过指定服务器源码读取确认；本轮未为已核对接口无谓重跑 Lean。

## 零边界、来源忠实度和范围限制

- **n=k=0：** hE 仍是空前缀的 trivial history；weighted step 无 i:Fin 0；sum_fin_tail_sub 和 f₀=ψ 给两端为零，支付为 0≤μE。μ、ν 的概率前提仍明确存在，未从空 hLaw 推出 ν 概率。
- **k=n：** mask 选不到任何 i<n，块为空；起点等于终端 f₀(Wₙ,Qₙ)，故差逐点为零。weighted-step 的 k≤i.val 分支不可能出现。
- **k=0：** history=⊥，只允许 trivial-history 事件；E=Ω 分支与已接受无权有限 Duhamel 相容。未把任意未来事件当作 time-zero history。
- **μE=0、零能量、退化或非中心增量律：** 没有除零、能量分母、矩或正方差步骤，全部合法。若代入源严格 CDF 测试，它仍是 1_{q>0, |w|<t√q}，原开边界和零能量约定不变；该模块没有重新定义 CDF 或最大值的 law。
- **任意原始概率 Ω：** hX 将前缀 comap 嵌入环境可测结构；没有要求 history 等于整个环境，也没有新任意 filtration 或独立历史假设。

实现使用 main.tex:552–590 的同一真实递推、Q、future kernel 和 Δ。对 supplement.tex:824–830 的所有原 history 事件、k≤n 和 [0,1] 测试，308–424 行给出目标带符号块支付；其中间恒等式正是 3052–3068 行的有限望远镜，常数一对应 3069–3073。847–858 的 low-clock 应用仍需另有该事件的实际概率估计。

**最终裁决：CORRECT。** 冻结实现完整保全原声明并实现该有限 signed-block 源引理，未发现 critical gap。源码未见 sorry/admit/new axiom/unsafe/native_decide，亦未借用其他模块 _private 名称。本报告是独立源码数学审查，不把作者回执的目标 exit 0 和 24 声明白名单审计变成本轮自行执行的内核认证。

该结果只支付实际 μ(E)。clock 概率界、实际平滑噪声构造、Fourier/characteristic-function 比较、导数估计、严格 CDF 平滑误差及完整 C1/C2 均未由此闭合，且没有作为该证明的循环前提。
