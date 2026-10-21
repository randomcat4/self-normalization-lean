# GaussianTail 最终独立源码语义与证明审查

STATUS: CORRECT（源码数学审查）

本裁决覆盖冻结实现的两个定义、七个公开定理、十个私有 theorem 和全部 309 行证明。先逐项核对本审查者此前独立盲译的冻结签名，再阅读全部证明及必要的真实 Mathlib API 源码。未发现声明变化、源语义偏离或数学证明缺口。

未运行本机或服务器 Lean，未重复目标编译、全量验证或传递公理审计。作者所述目标无诊断、29 声明标准公理审计和禁项检查属于另行服务器证据，不作为本报告的数学依据，也不表述为本轮自行执行的内核认证。只新增本报告，没有修改实现、scope、旧依赖、缓存或他人文件。

## 冻结材料及签名一致性

- 实现：C:/game/shao lean/drafts/c12/GaussianTail.lean，309 行。
  SHA256：f166fab0061199e25d0391bbde5c977905e368513a6e0e18b492877c65160922。
- 原冻结 scope：C:/game/shao lean/drafts/c12/GaussianTail-next-scope.md。
  SHA256：26a01989f5b8169ac37f44f543b3f0312a7e668bd26562e221f64d5c60a6dbef。
- 作者另行执行回执：C:/game/shao lean/drafts/c12/GaussianTail-review-receipt.md。
  SHA256：bdd78cb2ff5ae5faa1ea9e1427e4fc51379634a96720394620eb39a73ea72f95。
- 先前独立声明审查：C:/game/shao lean/drafts/c12/GaussianTail-statement-review.md。
- main.tex SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- supplement.tex SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

前三个文件哈希本轮实际复核。两定义的 body 与原提案一致，七个完整公开签名与 scope 除空白外逐字相等。没有换 Gaussian 参数、改严格尾定义、增删非负阈值条件、改常数、增加 Mills 或 Gaussian 误差假设。先前已独立核对的 Gaussian normalization、无原子、CDF 和半线 FTC 公共接口复用；本轮只补读实际新使用的无序半线差、endpoint FTC 和 MVT 接口。

## 实际定义及全部公开量词

令 γ=ProbabilityTheory.gaussianReal 0 1，其中 0 是实均值、1 是 NNReal 方差。

1. **standardNormalDensity（14–15 行）。** 所有实 x，φ(x)=gaussianPDFReal 0 1 x，即实际 φ(x)=(√(2π))⁻¹ exp(−x²/2)。
2. **standardNormalTail（17–18 行）。** 所有实 x，Ψ(x)=(γ(Ioi x)).toReal。定义是实际概率 law 的严格尾，不是代理 CDF 或预设解析函数。
3. **standardNormalTail_representation（43–49 行）。** 对所有实 x，Ψ 同时等于弱尾 γ(Ici x) 的实值、1−实际 Mathlib cdf γ x，以及真实 Lebesgue volume 下的 ∫Ioi x φ。
4. **standardNormalTail_basic（91–95 行）。** 无参数合取：Ψ 在全实数上 Antitone；Ψ(0)=1/2；每个有限实 x 都有 0<Ψ(x)<1；每个实 x 都有 Ψ(−x)=1−Ψ(x)。没有在负阈值采用路径误差的零延拓。
5. **standardNormal_derivatives（108–110 行）。** 对所有实 x，HasDerivAt φ (−xφ(x)) x，且 HasDerivAt Ψ (−φ(x)) x。没有由调用者额外提供连续性或积分假设。
6. **standardNormal_mills_bounds（147–151 行）。** 对实 x≥0，
   \[
   \phi(x)/(1+x)\le\Psi(x)\le(4/3)\phi(x)/(1+x),\qquad
   \phi(x)/\Psi(x)\le1+x.
   \]
   包括 x=0，不声称在负线性分母或 x=−1 极点适用。
7. **standardNormalTail_ratio_bound（225–228 行）。** 任意非负实 x,y，无顺序条件，
   \[
   \Psi(y)\le(4/3)\frac{1+x}{1+y}e^{(x^2-y^2)/2}\Psi(x).
   \]
8. **standardNormalTail_local_comparison（242–246 行）。** 任意 x,t≥0，若 |t−x|≤1/(1+x)，则 e⁻²Ψ(x)≤Ψ(t)≤e²Ψ(x)。允许端点为零，不声称覆盖负 t。
9. **standardNormalTail_deletion_comparison（284–287 行）。** 任意 j∈ℕ、x≥0，若 (j:ℝ)≤x²/2，则
   \[
   \Psi(\sqrt{x^2-j})\le3e^{j/2}\Psi(x).
   \]
   不需要样本长度、j<n、非空路径、正方差、原始矩或 BE。j 是明确 Nat cast，没有自然减法陷阱；x=0、j=0 与条件取等都允许。

## 真实 Gaussian 和全实表示、正性、导数

**20–41 行**前五个私有事实直接从实际 Gaussian 库得到 density 正性和真实全局 L1，化简出标准方差一的显式公式，再用真实 exp/平方 chain rule 得 φ′=−xφ。由每个实点的 HasDerivAt 推全局连续，未假设所需 density 导数。

**50–61 行**明确用 variance one≠0 安装 γ 的 NullSingletonClass，再以 Ioi_ae_eq_Ici 得严格/弱尾桥。CDF 使用实际 cdf_eq_real 和 Iic x 的有限实概率补集公式；最后以 gaussianReal_apply_eq_integral 及非负 density 积分，才消去 ENNReal.ofReal 的 toReal。γ 的概率质量有限，所以没有将 ∞.toReal=0 混入补集或单调性运算。

**63–70 行**以实际 density representation、真 IntegrableOn 和 setIntegral_pos_iff_support_of_nonneg_ae 证明每个有限 x 的严格尾正性。φ 处处正，所以 support=univ，实半线的 Lebesgue 质量非零；该论证适用于负 x，且不因半线体积无限而丢掉 L1 条件。

**72–89 行**实际 gaussianReal_map_neg 经可测 neg 的 map_apply 将 Ioi(−x) 对应为 Iio x，再对 Ici x 取补集，最后通过前述无原子桥把弱尾识别为 Ψ(x)。所以 Ψ(−x)=1−Ψ(x)，没有把原子情况下的 Iio/Iic 差异无条件忽略。

**91–106 行**Antitone 从真实尾集合包含得到，toReal_mono 明确使用 Gaussian 质量不为 top；反射在零点给精确半值；正尾 Ψ(−x)>0 配合反射给 Ψ(x)<1。所有结论对全实阈值成立。

**112–125 行**不是只对 x≥0 拼 density derivative。证明先用实际全局 L1 得
\[
 \Psi(t)=\Psi(0)-\int_0^t\phi(a)\,da
\]
对任意实 t 成立，再对有向 interval integral 应用 endpoint FTC。因此负 t 的积分方向和 t=0 的端点都正确。调用时提供了 density 的 interval integrability、局部强可测和 endpoint continuity。

本轮指定服务器只读核验：

- IntervalIntegral/Basic.lean:1176–1181 的 integral_Ioi_sub_Ioi' 要求两个半线的真 IntegrableOn，**没有 a≤b 前提**；反向端点通过 integral_symm 处理。实现 117–120 行使用的正是这个带 prime 的版本。
- IntervalIntegral/FundThmCalculus.lean:725–728 的 integral_hasDerivAt_right 对任意实 a,b，以真 interval integrability、StronglyMeasurableAtFilter 和 ContinuousAt f b 给 d/du ∫a..u f=f(b)。实现全部满足，不需要 b>0。

因此公开 tail derivative 是实际严格尾函数的全实导数，而非只定义一个 −φ 值或仅证明右导数。

## Mills：真实 L1、导数和无限远零极限先于 FTC

**127–135 行**由 t²→+∞、−t²/2→−∞ 和真实 exp 在 −∞ 处趋零，证明 φ(t)→0。该极限独立于 Mills，不用循环假设。

**137–145 行**对 t≥0，分母 (1+t)² 严格正。由 (t−1)²≥0 及 t≥0 得实际权重
\[
 A(t)=\frac{t^2+t+1}{(1+t)^2}
\]
满足 3/4≤A(t)≤1。两个方向正确，上界所需域没有跨过 t=−1。

**152–168 行**对固定 x≥0，定义 F=φ/(1+t)、g=φA。对实际 Ioi x，t≥0，故 0≤g≤φ。证明同时建立 g 的 a.e. 强可测性并以真 density L1 支配，得到 IntegrableOn g (Ioi x)。有界权重不是被默认当成 L1；它明确乘上已知 L1 density。

**169–179 行**在所有 t∈Ici x，证明 1+t≠0，再由真实 quotient derivative 计算 F′(t)=−g(t)，包括有限端点 x=0。**180–185 行**在最终 t≥0 时以 0≤F(t)≤φ(t) squeeze 得实际 F→0；没有只引用“存在某极限”或未经证明写零边界。

**186–190 行**在上述导数、g 的真实 L1 和零极限齐全后，才调用已独立核验的 integral_Ioi_of_hasDerivAt_of_tendsto'，使用 hgi.neg 作为导函数 −g 的可积性。库结论是 ∫F′=0−F(x)，提出 integral_neg 后得到
\[
 \int_x^\infty g=F(x).
\]
符号正确，也没有把未可积导函数的 Bochner 默认积分当作 improper FTC。

**191–203 行**分别用两边的真实 IntegrableOn 比较 ∫g≤∫φ 和 ∫(3φ/4)≤∫g，再用真实 tail representation，得到 F≤Ψ、(3/4)Ψ≤F。**204–211 行**将后一式合法化为 Ψ≤(4/3)F，常数倒数正确；最后利用 Ψ(x)>0 和 1+x>0，从 F≤Ψ 移项得到 φ/Ψ≤1+x。没有除以 x 或零尾，也没有假设 hazard。

这条链实际实现了 source Mills 所需固定正 c,C，不是把“Gaussian integral 已知”当作所求 Mills 的替代物。x=0 与任意大非负 x 都在同一证明范围。

## 通用尾比、局部双边 e²、删除阈值

**213–223 行**真实 density formula 给所有实 x,y 的精确 identity
\[
 \phi(y)=e^{(x^2-y^2)/2}\phi(x).
\]
**229–240 行**只在非负 x,y 使用各自适用的 Mills：上界在 y，下界在 x。所有 exp、4/3、1+x、1+y 以及 tails 的符号正确，乘不等式的方向未反转。无 x≤y 或 y≤x 输入，故通用 ratio 的无序范围确实被证明；指数为负时也保持相同 identity。

**247–259 行**定义 δ=|t−x|，从邻域条件推出 δ(1+x)≤1、0≤δ≤1；由全实正尾得到真实 log Ψ 的 HasDerivAt，norm 等于 φ/Ψ。**260–267 行**在实际凸区间 [0,x+δ] 上使用 MVT：两个端点 x,t 都在其中，所有 s≥0，hazard≤1+s≤1+x+δ。这没有在负 s 使用非负域 Mills，也没有要求一个端点严格大于零。

服务器只读 MeanValue.lean:728–734 确认该 API 的输入是区间内真实 DifferentiableAt 和 deriv norm bound，结论方向为 ‖f(y)−f(x)‖≤C‖y−x‖；实现的 x,t 顺序及全局 log derivative 符合。**268–282 行**进而给
\[
 |\log\Psi(t)-\log\Psi(x)|
 \le(1+x+\delta)\delta
 \le1+\delta^2\le2,
\]
再以 exp 单调性和 Ψ>0 得双边 e²。退化区间 x=t=0 同样合法，不在零值上取 log。

**288–295 行**令 y=√(x²−j)。由 hj 和实平方非负证明 radicand≥0，故 y≥0、y²=x²−j；在 x≥0 下得 y≥x/2，所以 (1+x)/(1+y)≤2。指数精确识别为 (x²−y²)/2=(j:ℝ)/2，没有将平方根换成错误符号分支。

**296–307 行**对 x,y 使用真实 ratio bound，乘数 exp(j/2)Ψ(x) 非负，先得系数 (4/3)·2=8/3，再放松为三。未引用保留样本的 Gaussian 尾概率假设。x=0 时 Nat cast 非负和 hj 强制 j=0；证明不需除 x 或 y，因此无需另添正阈值前提。j=0 时 y=x，hj 等号也允许。该纯数值结论没有自然 subtraction、空样本或方差归一化假设。

## 来源边界及最终裁决

main.tex:169–171 的 Ψ=1−Φ 与本实现真实 CDF 桥一致，且 Brownian 绝对最大值尾 H 始终是另一对象。supplement.tex:1027–1029 的 Mills 域 z≥0、205–211 的删除阈值及 1369–1377 的层比均由当前实际 normal-tail 接口提供对应 deterministic input。main:457–465 的正相邻阈值、807–814 的 hazard 及 e⁴ 比较由当前较强 hazard 和 e² 覆盖；预算 factor eight 与样本误差界不是本模块的结论。

Gaussian strict/weak equality仅由 γ 的无原子性得到，不能拿去修改原样本的 weak crossing、strict survival、q>0 CDF 或零能量事件。对负阈值，表示、反射、范围和导数保留真实 Gaussian 值；Mills/ratio/local 的非负域没有被移除，更没有穿过 1+x 的负域极点。

**最终裁决：CORRECT。** 冻结 2 定义、7 定理及十个私有事实的证明完整保全声明和 source 语义。源码未见 sorry/admit/new axiom/unsafe/native_decide 或借用跨模块 _private 名称。本轮必要只读服务器请求成功；未执行任何 Lean 或重放已开始状态不明的操作。

仍未闭合：BE/CLT、bounded-random/bounded-endpoint 样本 Gaussian 尾界、random denominator 的 tilting/layer argument、随机删除集平均、Brownian 最大值、clock/Fourier 比较、严格 CDF 平滑误差及完整 C1/C2。GaussianTail 与 RetainedComparison 组合后仍需 raw product crossing 的实际 Gaussian 概率上界。
