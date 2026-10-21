# LindleySignedBlock 独立声明与来源审查

STATUS: CORRECT（声明阶段）

本裁决仅判断这一份提案的一个定义、四个定理签名是否数学成立、能否由真实已有接口闭合，以及是否忠实覆盖所选源引理。当前没有候选实现，本报告不宣称证明代码完成、Lean 编译通过或内核与传递公理审计通过。未运行本机或服务器 Lean；服务器仅只读核对必要 Mathlib 源码。没有修改提案、已有证明或公共文件。

## 绑定材料与范围

- 提案：C:/game/shao lean/drafts/c12/LindleyFourier-next-scope.md。
  SHA256：99f2a8c006c56569cbc34514786c9f7ac972d8892cf5171a826f4b8b5a44773e。
- 已独立审查的真实有限未来核接口：C:/game/shao lean/drafts/c12/LindleyTelescoping.lean。
  SHA256：518b7029d435ddd3b32a414f8893d6c49e26910cff18117d8da0cc6eb67bc93c。
- 原 main.tex：C:/game/shao/current/c12/main.tex。
  SHA256：beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06。
- 原 supplement.tex：C:/game/shao/current/c12/supplement.tex。
  SHA256：b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd。

本轮实际复核上述哈希，并读取提案全部声明、来源锚点和所需已有公开接口。已有依赖的证明审查结论复用，不重复运行其审计。提案所述 API 探测成功、缓存可用等作者回执没有被当作候选结论的证明。

所选结果是 supplement.tex:824–830 的 h:lem:reflection / h:eq:signedblock 及其 3050–3075 行证明；849–858 行是预期应用。它是带历史事件的有限带符号块支付，不是 Fourier 比较、clock 概率估计或完整 C1/C2。

## 第一阶段：仅按实际定义与签名重译

记样本路径 a(ω)=(X₀(ω),…,Xₙ₋₁(ω))，真实 Lindley 递推为 W₀=0、Wᵣ₊₁=max(0,Wᵣ+Xᵣ)，Qᵣ=∑ⱼ<ᵣ Xⱼ²。这里所有 W、Q 都是已有路径定义；Qₙ 是同一条样本的 energy。记

\[
 f_\ell(w,q)=\int_{\mathbb R^\ell}
   \psi\!\left(w+\sum b_j,\;q+\sum b_j^2\right)\,d\nu^{\otimes\ell}(b).
\]

这只是已有 lindleyFutureKernel 的记号，不是新定义或另选的独立核。以零基指标 r∈{0,…,n−1} 写

\[
 \Delta_r=f_{n-r-1}(0,Q_{r+1})
       -f_{n-r-1}(-U_r,Q_{r+1}),\qquad
 U_r=\max(-(W_r+X_r),0).
\]

1. **lindleyHistory 定义（提案 66–70 行）。** 对任意自然数 n、任意类型 Ω、任意函数族 X:Fin n→Ω→ℝ、任意 k∈ℕ 和证明 k≤n，定义
   \[
   \mathcal H_k
   =(\omega\mapsto(X_0(\omega),\ldots,X_{k-1}(\omega)))^{-1}
       \mathcal B(\mathbb R^k).
   \]
   此定义本身不要求 Ω 先有环境可测结构、X 可测或任何概率律。前缀保持原始坐标顺序，不是置换、反转或一个随机保留路径。

2. **lindleyHistory_eq_iSup（72–78 行）。** 在相同任意参数下，
   \[
   \mathcal H_k=\bigvee_{0\le j<k}X_j^{-1}\mathcal B(\mathbb R).
   \]
   量词覆盖全部前 k 个坐标；右侧不是只选某一类柱集。没有独立性或可测性前提，也没有完备化断言。k=0 时空上确界为 ⊥；k=n 时是整份有限样本生成的 σ-代数，未声称等于环境 σ-代数。

下面三条共同量化：任意 n∈ℕ、任意带环境可测结构的 Ω、概率测度 μ:Measure Ω 与 ν:Measure ℝ、函数族 X:Fin n→Ω→ℝ。前提逐项为所有 Xᵢ 环境可测、iIndepFun X μ、所有 Xᵢ 在 μ 下与 id 在 ν 下 IdentDistrib；任意 k≤n；任意 E⊆Ω 且 E∈𝓗ₖ；任意 Borel 可测 ψ:ℝ²→ℝ 且对所有 s 都有 0≤ψ(s)≤1。没有中心化、方差、矩、正能量、P(E)>0 或条件 iid 前提。

3. **iid_lindley_future_step_on_history（102–117 行）。** 再任取 i:Fin n，写 r=i.val，并假设 k≤r。结论精确为
   \[
   \int_E f_{n-r-1}(W_r+X_r,Q_{r+1})\,d\mu
   =\int_E f_{n-r}(W_r,Q_r)\,d\mu.
   \]
   r<n 保证 n−r−1 是所需未来长度；左侧第一坐标尚未反射，第二坐标包含当前真实 Xᵣ²。原文的一基步号是 r+1，因此 k≤r 正好表示事件在这一步之前可测。两个积分都针对原 μ 在 E 上的 set integral；未把限制测度当概率，更未断言其下样本 iid。

4. **iid_lindley_signedBlock_identity（129–144 行）。** 在上述共同前提下，
   \[
   \int_E\sum_{r=0}^{n-1}1_{\{k\le r\}}\Delta_r\,d\mu
   =\int_E\{\psi(W_n,Q_n)-f_{n-k}(W_k,Q_k)\}\,d\mu.
   \]
   sum 的 Fin n 范围和 if 条件相合，选中的正是 r=k,…,n−1，即源编号 k+1,…,n。两端是期望恒等式；不声称内部两随机变量逐点相等。

5. **iid_lindley_signedBlock_bound（146–156 行）。** 相同前提下，
   \[
   \left|\int_E\sum_{r=k}^{n-1}\Delta_r\,d\mu\right|
   \le(\mu E).{\rm toReal}.
   \]
   绝对值位于整个带符号块积分之外。没有将其替换为 ∫E∑|Δᵣ|，也没有样本长度因子。μ 是概率，故 μE 有限，右端正是实际事件概率的实数值。

## 第二阶段：来源与既有接口对应

main.tex:552–590 定义原 Sᵢ、Qᵢ、递归 Wᵢ/Uᵢ，以及基于真实独立未来样本的 f 和 Δ。已有 LindleyTelescoping:25–41 的定义与此完全一致。其 188–194 行公开半群式使用 ν 的真实有限乘积律；139–148、165–176 行分别提供核可测性与 [0,1] 界。新提案没有改写这些对象。

supplement.tex:824–830 明确量化 E∈σ(A₁,…,Aₖ)，结论是带符号块的绝对期望至多 P(E)。新 history 定义与其对应；零基 r≥k 与源一基 i>k 对应，无额外的无原子、中心化或矩前提。原源样本所属条件概率空间在此抽象为真正的 μ，原单坐标条件律抽象为真正的 ν；二者由真实 iid 和全部坐标 hLaw 关联，没有把随机保留样本的无条件律当成 iid。

supplement.tex:3052–3068 的源证明先以 Fᵢ=fₙ₋ᵢ(Wᵢ,Qᵢ) 得到历史带权一步，再在期望中有限求和为 Fₙ−Fₖ。提案的 identity 是该证明中间等式本身，并未凭空增强为逐点恒等式。3069–3073 行以两端都在 [0,1] 得到常数一。847–858 行低 clock 应用中的有限支付与本提案吻合。

所选结果不必假设原完整 Proposition 3.3 的正方差部分：有限概率乘积与 [0,1] 测试已经足够，退化的 δ₀、δ₋₁ 和非中心律都符合这些声明。省去矩、均值和正方差在数学上合法；本报告没有因此宣称已证明该原命题的正方差断言。

main.tex:595–607 的测试仍然是 1_{q>0, |w|<t√q}。这是本候选允许的一种 [0,1] 可测测试，故可以代入；新块引理本身不执行严格 CDF 与最大值的联合反转转移，也没有修改其开边界或零能量约定。既有严格 CDF 结论保持原范围。

## 第三阶段：可闭合性的独立数学论证

这是对签名的数学存在性检查，不是尚不存在的 Lean 实现的证明审查。

### 完整历史事件及环境可测性

令 pₖ(ω)=prefixPath(a(ω),k)。对任意 hE，由 comap 的定义，存在 Borel B⊆Path k，使 E=pₖ⁻¹(B) 精确成立。它不是仅几乎处处的表示，不需要 P(E)>0，也不需要假设 E 是一个矩形柱集。有限路径的乘积可测结构是各坐标 eval 的 comap 上确界；再对 pₖ 作 comap，逐项复合就是声明的各 Xⱼ。因此 history_eq_iSup 对空 k 也成立。

hX 使 pₖ 环境可测，故 𝓗ₖ≤环境 σ-代数，hE 自动给出 E 的环境可测性。未来实现仍须明确证明或调用这一点，才能合法使用 set integral 与 indicator 的转化。

本轮直接通过指定服务器 broker 只读 Mathlib 源确认：

- MeasureTheory/MeasurableSpace/Basic.lean:82–94 中 comap 的集合定义与 measurableSet_comap 的等价式确实给出精确可测前像表示。
- 同文件 104–105 行 comap_comp、136–137 行 comap_iSup 的方向与所需等式相符。
- MeasurableSpace/Pi.lean:29–32 使用实际 pi 可测结构及各 eval 的 comap；没有隐藏的有限维柱事件限制。

### 带历史权重的一步，不循环调用目标结论

固定 r=i.val≥k，把 E 写成上述 B 的前像，并在完整路径上定义 H(a)=1_B(prefixₖ a)。这是可测、取值 {0,1} 的真实历史权重，且 H(a(ω))=1_E(ω)。

原 iid path law 把 μ 下完整样本转移到 ν^{⊗n}。只转移可测、可积的实际函数 H·L 和 H·R，其中

\[
 L(a)=f_{n-r-1}(W_r(a)+a_r,Q_{r+1}(a)),\qquad
 R(a)=f_{n-r}(W_r(a),Q_r(a)).
\]

二者均在 [0,1]，故在概率测度下可积。对真实 ν^{⊗n} 使用既有 product coordinate split，把当前 r 号坐标记为 z，其他 n−1 坐标固定为 b。因为 k≤r，改变 z 不改变前 k 个坐标，从而不改变 H。真实 Wᵣ 只依赖前 r 个坐标，Qᵣ 也是同一前缀的平方和，因此二者也不变。Qᵣ₊₁=Qᵣ+z²。

固定 b 后，内层积分于是成为 H(b) 乘以

\[
 \int f_{n-r-1}(W_r(b)+z,Q_r(b)+z^2)\,d\nu(z)
 = f_{n-r}(W_r(b),Q_r(b)).
\]

此处只使用已审的真实 lindleyFutureKernel_succ，且 n−r=(n−r−1)+1 由 r<n 保证。R 的内层是常数，ν 的概率质量为一。再对 b 积分并转回 μ，得到所提带权一步。整个过程无需 CE、任何新独立副本假设、目标 weighted step 或 signed block 作为前提，也不需要 μ.restrict E 下 iid。故没有循环假设。

### 真可积性和有限望远镜

所有 kernel/test 合成项都是可测的 [0,1] 值函数；其差 Δ 和 Fᵣ₊₁−Fᵣ 的绝对值至多一。乘历史指标仍有相同界。μ、ν 及其有限乘积皆为有限测度，故 Fubini、积分相减、有限积分/求和交换所需可积性都能由这些界直接推出。无需 X 或 X² 在原律下可积；对无界增量进行的运算只是有限实数路径运算。

定义 Fⱼ=fₙ₋ⱼ(Wⱼ,Qⱼ)，0≤j≤n。已有纯量反射恒等式和真实递推给出

\[
 F_{r+1}-L_r=\Delta_r
\]

逐点成立。带权一步给出 ∫E Lᵣ=∫E Fᵣ，因而

\[
 \int_E\Delta_r\,d\mu
 =\int_E(F_{r+1}-F_r)\,d\mu.
\]

仅对 r=k,…,n−1 求和，有限 cancellation 得 ∫E(Fₙ−Fₖ)。这里 Fₙ=ψ(Wₙ,Qₙ)，因为 f₀=ψ；得到提案精确 identity。未把无权一步简单乘以随机指标；新 weighted step 是必须单独完成的真实数学工作。

### 常数一及边界

由 [0,1] test 和真实概率 future kernel，Fₙ,Fₖ∈[0,1]，故 |Fₙ−Fₖ|≤1。于是

\[
 \left|\int_E\sum_{r=k}^{n-1}\Delta_r\,d\mu\right|
 \le\int_E|F_n-F_k|\,d\mu\le\mu(E).
\]

这一路径不逐项取绝对值，不产生 n−k 因子。直接只读核对 Mathlib/MeasureTheory/Integral/Bochner/Set.lean:581–585：norm_setIntegral_le_of_norm_le_const_ae 的结论为 C·μ.real E，所需 μE<∞ 由 μ 概率给出，取 C=1 即得声明。没有额外正质量条件或除零。

- k=n：mask 中没有满足 n≤r<n 的指标，左端为零；n−k=0、Qₙ=energy，所以右端逐点为零。
- n=k=0：空样本和空和同样给零；weighted step 没有 i:Fin 0，故该量词分支为空。声明仍要求 μ、ν 概率，没有暗中利用空坐标 hLaw 来推 ν 概率。
- k=0：history=⊥，只允许空集或全集历史事件；全集分支与已有无权总恒等式相容。没有允许未来观测事件混入 time-zero history。
- μE=0：所有积分为零，完全无需条件分布归一化。
- 真实能量为零、退化增量律或非中心律：无分母、无平方根正性需求，公式仍合法。

## 对邻近错误替换的核对

提案 B1 和 B2 的手算反例已独立重算，并非 Lean 检查。B1 的 n=3、全部负号未来事件下，三个真实缺陷为 1/2、0、1，所以无历史约束的错误版本给 3/16>P(E)=1/8。B2 的余弦测试下，四次 |Δ|=1 的事件概率为 1/2、1/4、1/4、3/16，总和 19/16>1；因此逐项绝对值版本确实不能用常数一支付。实际提案没有这些错误替换。

常数一也不能统一缩小：n=1、ν=δ₋₁、E=Ω、ψ(w,q)=1_{w≥0} 时 Δ=1，支付取等。该检查同时表明正方差不是有限块结论的必要前提。

## 裁决和后续证明门槛

**CORRECT：这一份固定哈希提案的 1 定义、4 定理在声明层面数学正确，忠实覆盖所选原文 signed-block 引理及其中间等式，无需修订数学签名。**

这不把“实现能调用现有无权一步”视为证明完成。实现必须自行完成完整 history 事件表示、环境可测性、当前坐标变化下的真实前缀不变性、bounded weighted Fubini 和积分相减/求和所需的可积性。已有私有 helper 不因此成为可调用的公共接口；可重建局部事实或使用公开路径/乘积 API，但不能依赖不稳定的 _private 名称。新文件的这些证明、服务器检查和传递公理审计均尚未发生，本报告没有代替它们。

本结论只支付实际事件概率 μ(E)。supplement.tex:836–843 的 clock 概率定量界、main.tex:610–645 的实际平滑测试构造与比较目标、650–701 的实际噪声/Fourier 机制及后续导数估计仍是独立开放依赖。没有将它们当作前提，也没有把该有限块支付等同于这些定量结论或完整 C1/C2。
