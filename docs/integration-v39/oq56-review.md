# OQ56 PR157 独立验收

**结论：CORRECT；critical_gaps = []。** 冻结 head 为 `f66852c2a18f009cef4859e82a5cf41e7ce48b83`，父提交为根 v38 `63f82bd7ea2a0fba92a4ad217c4ad27bfa3ead00`，tree 为 `6e6f1d319ec59e6f27aab7e1f85b72d750d404fa`。本报告接受恰好两个模块、21 条公开定理和 3 个公开定义。P53、OQ6、RS2 保持 OPEN。

审查者 `/root/v39_oq56_accept` 与作者分离。已读 AGENTS.md、SERVER.md、TEAM.md 和 math-theorem 的验证协议；只读了服务器冻结 Git 源码、原始数学材料及既有检查输出。本轮 Lean 调用为 0，没有修改作者模块、共享库、服务器文件或合并提交。本报告不是照抄既有接受票：先独立逐步审阅数学源码与原 p53，再核对完整动态声明和机器证据。仅写本 MD 与相邻 JSON。

## 冻结身份及范围

|模块|source SHA256|字节|公开定理|公开定义|
|---|---|---:|---:|---:|
|Shao.OQ5.P53.SparseMass|93518d87f30ed5f78dd62ff142d7e6aad95241a0906f4fa89ea9344f39f0444a|13608|17|3|
|Shao.OQ5.P53.SparseMassLimits|ee34c3ca8f40697f433eba8a647057976e889c4baec9b1e22413f6006810c1af|5745|4|0|

远端 `git show <冻结head>:<path>`、停止版本地镜像、实际前缀审计的源码部分、contract-manifest 的完整源码和当前分线源码逐字节一致。两个文件分别为 309 和 138 行，全部正文及证明已经阅读。两模块 24 项完整公开类型／定义体与冻结文档的 24 个 Lean fence 逐项字面相同，没有按合取分支增加公开定理数。代码的禁止占位／新增公理／unsafe／native_decide 扫描为空；冻结提交差异检查 exit0，五个交付文件均 UTF-8、LF、无 BOM。

提交只增加两份 Lean 源码和三份范围／冻结／验收文档，共 5 文件、618 行、无删除。依赖 SparseScales（SHA `22d4f7f1972a3cbc5fedfc2efa0cadbf91616d4e1d113cbb90ef753a830b7888`）与 SparseSelection（SHA `17d134c1a8c02b07f5a5e3c3047742048775dbf36c5c1eba47f120a09622d282`）相对父提交未变。

## 原始目标和忠实性

完整读取原始 `C:/game/shao/current/oq56/inputs02/p53.md`（SHA `0bfadbb2021248859f8b15df2ff184c73c879a7203991c27fdc4f5dd6c04f561`，5686 字节）、scope01 的 p53 范围，并实际阅读 p45 §1 的平衡块恒等式和二矩推导（p45 SHA `0b799637356615cfb18a9fef016c11d682aeefde314106e0b56eb46a853c09ca`）。p54 的修正规则也已查阅；本批不借其正面概率接口扩大结论。

原 p53 固定 0<α<1，给定满足 x_n/n^δ(α)→∞ 且 x_n/√n→0 的确定序列，构造抽样前固定的稀疏 N、t、d 和 π_j=2^(−j−2)exp(−t_j^α)。最终要构造固定实 iid 法则、正半定秩一余项、全部矩和指数预算、真实分母正性，并证明尾概率的对数比趋零和高斯比趋无穷。本批只消除 §3 的无限数值质量归一化及 §4 式(7)和背景幂的数值极限义务；尚未构造概率测度，不能把数值权重称作已完成的真实法则。

对应关系精确为：π=sparsePositiveMass，m=sparseLabelMass，H_j=Σ_(l≥j)π_l，b_j=Σ_(l<j)m_l。π_0=0；m_0=1−Σπ 是实际余量，两者不能互换。正层 π、t 与原文相同。b 对应原文 q_j=P(B<j) 的数值输入，待后续实际标签测度桥接后才是概率。自然数背景指数恰为 2*(N_j−2)，保持自然数减法和自然数幂。

前驱 SparseSelection 的字面 Core、逐步选择证明和 `exists_sparseSelectionCore` 已独立回看：Core 的输入是同一个 N、N_0=1、N_j≥2^j、倍增、幅度范围及两条逐层质量不等式。前驱用真实指数衰减、有限个 eventual 条件取交、Nat.find 和 Nat.rec 构造它；没有把 N_j H_j→0 或背景幂极限作为输入，没有要求 x 单调。本批只消费这一既有 Core，不因矩阶 q、指数参数 τ 或下游结论重选 N。

## 逐步数学证明核查

### 质量和归一化

SparseMass 第20–28行的三个定义保持原义。对任意实 α、任意完整 x、N，自然数处的幅度是非负实幂乘非负平方根，故非负；实幂 t^α≥0，exp(−t^α)∈(0,1]。于是所有 π≥0，j≥1 时 π_j>0 且 π_j≤w_(j+2)，其中 w_j=2^(−j)。任意 α 的推广使用 Lean 实幂在非负底数上的约定；原文 0<α<1 的使用域当然包含在内。

第30–63行私有几何引理先真实证明 HasSum(k↦w_(j+1+k)) w_j。特别 Σ_(k≥0)w_(k+3)=1/4。第92行比较测试先取得 Summable π，而不是利用不可求和 tsum 的默认值。第104行由 π_0=0、真实尾拆分和非负比较取得 0≤Σπ≤1/4。

第133行把已有 HasSum π S 在索引0处更新为 1−S，更新后的和为 (1−S)−π_0+S=1。这给 HasSum m 1，强于仅写一个未经可求和付款的 tsum 等式。m_0≥3/4，正层 m_j=π_j，所有 m_j≥0，故数值归一化完整。

第162–224行先证明全部平移尾可求和，再拆分 H_j=π_j+H_(j+1)。有限前缀与无限尾的恒等式来自 HasSum m 1，因此仅在 j≥1 时得到 b_j=1−H_j。严格 b_j<1 用真实 π_j>0 推出 H_j>0；不是把非负误当正。b_0=0 单独处理，未声称错误的 b_0=1−H_0。所有尾均包括本层及无限多个未来层。

### 同一个子列的全部尾费用

第226–273行的四个 Core 私有引理只抽取逐层约束、正性和单调性。令 A=N_j、B=N_(j+k)，j≥1；已有 A>0、B≥A。对 l=j+1+k，Core 给 π_l≤w_l/B²，因此

\[
 A\pi_l\le\frac{w_l A}{B^2}\le\frac{w_l}{A}.
\]

代码确实保留平方实分母和非负项，先用 B² 正性清分母，再以 A²≤B² 比较，未将相邻索引错成 j+k+1 的另一层。第275行两边都是已证明的 HasSum，故可逐项比较后求无限和，得到

\[
 N_j H_{j+1}\le\frac{w_j}{N_j}.
\]

将本层 N_jπ_j≤w_j 加回，得到第297行的完整费用

\[
 N_jH_j\le w_j+\frac{w_j}{N_j}.
\]

这正对应原 p53 式(7)，两个加数和完整尾均保留，没有把未来尾截成有限和。

### 四条数值极限

SparseMassLimits 第22–34行的两个私有引理真实证明 w_j→0 及 N_j≥1。第36行以真实可求和的部分和趋向总和，减去部分和并用尾拆分，得到 H_j→0；第60行直接由 HasSum m 1 的部分和极限得到 b_j→1。两条均对所有 α、x、N 成立，不需要 Core。

第66行在同一个给定 Core 下，j≥1 时 N_j≥1，故 0≤N_jH_j≤w_j+w_j/N_j≤2w_j→0。没有假设待证成本极限；夹逼成立于最终集合，j=0 不影响 atTop 极限。

第92行保留 k_j=2*(N_j−2)∈ℕ。由 3/4≤b_j<1 得 0≤b_j^k_j≤1；Bernoulli 的实际条件 −1≤b_j 已满足，得到

\[
 0\le1-b_j^{k_j}\le k_jH_j\le2N_jH_j\to0.
\]

代码用 Nat.sub_le 再 exact_mod_cast 取得 k_j≤2N_j，未把自然数减法偷偷改成实数减法。最终两次减法恢复幂本身趋1。无需对数、幂极限连续性或未支付的概率极限。这正是原 p53 的背景幂极限。

关键 Mathlib 使用点的完整条件已核对：几何 HasSum、非负比较、HasSum.update、Summable.sum_add_tsum_nat_add、HasSum.tendsto_sum_nat、tsum_pos 和逐项求和、pow_le_one₀、one_add_mul_sub_le_pow、squeeze_zero。还实际读取了官方源文件相关作用域；不存在将原结论改名成外部依赖的情况。

## 私有、生成及所有所属声明

本批源文本共10条作者私有定理。SparseMass 的8条为 mass_dyadic_pos、mass_levelAmplitude_nonneg、mass_dyadic_future_hasSum、mass_positive_majorant_hasSum、mass_core_step_bounds、mass_core_index_pos、mass_core_current_cost、mass_core_future_term；它们的完整类型和全部证明已与公开链一并审阅。SparseMassLimits 的2条为 limits_dyadic_tendsto_zero、limits_core_index_one_le。

已有原始 prefix 输出已重新解析，按有序 Lean.Name 的 str／num 组件比对，不用点号切割名称，也不把 num 的字符串“0”误当一般字符串组件。Unit98 实际 SOURCE 为45项，其中44新所属=20公开+8私有+16生成；另1项 sparseDyadic.eq_1 是已接受97的延迟定义方程。16新生成项=14个整数算术证明+2个新定义方程 sparseLabelMass.eq_1、sparsePriorMass.eq_1。Unit99 实际 SOURCE 为7项=4公开+2私有+1个 limits_core_index_one_le 的整数算术证明。所有52项的完整实际类型和组件都已逐项阅读；算术项仅为自然数加法重排、j≥1排除j=0、后继正性及 2^j≤N_j 推出 N_j≥1；定义方程正是上述字面定义。没有额外隐藏数学前提。

原始记录重建得到98的124条（SOURCE45/DEPENDENCY34/LATE45、79个不同结构化名字），99的65条（7/51/7、58个不同名字），与 canonical 各字段一致。全部104条 SOURCE/LATE 完整类型在原始输出精确匹配，LATE无新常量，189条记录公理均在允许集合内。JSON逐条保存全部52项类型、组件、来源分类以及生产名字。

独立前缀文件的私有名含 ExactSourceAudit 路径，不能直接当作生产所属名。已将这些名字精确映射到真实 `_private.Shao.OQ5.P53.SparseMass.0.…` / `SparseMassLimits.0.…`，并在根 v39 生产 OwnedAudit 原始日志中逐项找到44/44与7/7全部51个新所属常量。进口延迟方程另作接受97依赖，不计新公开或新所属成果。

## 机器证据绑定

本轮不重跑成功 Lean。已有两次独立目标／完整源码字节前缀检查分别为：98目标4.279214411973953秒、前缀5.6690332014113665秒；99目标3.971882402896881秒、前缀6.092004081234336秒，均exit0、无证明诊断，源码及对象不变。原作者98的弃用警告和99 v1的编译失败仍保留；99 v2仅将两处未使用的 forall 证明绑定名匿名化后明确重新冻结，未伪称原raw类型逐字未变。

根统一 v39 gate 已实际 PASS。本地 `coordination/integration-v39/gate-result.json` 与服务器 `logs/integration-v39/result.json` 相同 SHA256 `a74870ea363ebb14763aaf1d336d1e0794a887ebe98b41c9b77e4659ab7ecc66`（36693字节）。七份原始日志哈希全部核对成功，所记录七项命令exit均0；构建原始日志明确包含这两模块及总入口全部成功。冻结两源哈希同时出现在 frozen_sources_sha256 与 source_files_sha256，且与本报告独立读取的 Git blob 相同。版本实际为 Lean4.36.0-rc1、Lake5.0.0和 Mathlib807d3836…。

该门覆盖277生产模块、1875公开定理、3180含生成命名空间定理、5470模块所属常量；271旧源码和1048旧对象复用不变。全库声明覆盖与传递公理白名单为 propext、Classical.choice、Quot.sound。审核只读复核证据绑定，不把全库计数归为本批产出。

module-coverage日志保留一条 mathlib 仓库 local-changes 包装警告。已只读确认 Mathlib 是指向共享源的符号链接视图；本批10个直接承重的官方源／导入文件逐字节与固定 Git 提交比对全部相同，该警告不是 Lean 定理诊断，也未发现本批依赖源码漂移。没有改动共享视图。

本审查的只读 JSON 解析探测曾把 DEPENDENCY 当成 SOURCE而访问不存在的可选字段；按实际schema纠正后完整重建通过。这些是本审查读取器错误，未改任何数学源、未运行或重跑Lean，工具对话保留原始失败输出。

## 尚未关闭的原始义务

本批直接消费者为后续 SparseLabelLaw 和稀有平衡事件概率：归一化权重可送入标签测度，b/H可桥接 Iio/Ici 事件，再消费四个极限。这里没有实际标签概率测度、B/C独立取样、实编码、全矩与指数矩付款、正秩一积分算子、真实条件矩、每个固定n的Studentizer正性、平衡事件概率公式及最终尾概率／比值结论。这些仍须沿同一个N完成。

因此原P53/OQ6/RS2继续OPEN；p35和已在v33关闭的P52是另外的已接受范围，不从本批重新得票。没有认证临界常数、每个重尾法则失败、α=1必要性、一般非线性基核分类、历史优先权或新颖性。CORRECT仅适用于本次精确冻结的数值质量与极限交付。

## 全部公开声明附录

以下24项与冻结head逐字匹配；定义保留完整字面体，定理保留全部量词及前提。更细的源码行、所有私有及生成实际类型、证据路径和根门日志哈希见相邻oq56-review.json。

```lean
def sparseLabelMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j = 0 then 1 - ∑' k : ℕ, sparsePositiveMass α x N k
  else sparsePositiveMass α x N j
```

```lean
def sparseHighMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, sparsePositiveMass α x N (j + k)
```

```lean
def sparsePriorMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, sparseLabelMass α x N k
```

```lean
theorem sparsePositiveMass_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparsePositiveMass α x N j
```

```lean
theorem sparsePositiveMass_pos (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : 0 < sparsePositiveMass α x N j
```

```lean
theorem sparsePositiveMass_le_dyadic (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    sparsePositiveMass α x N j ≤ sparseDyadic (j + 2)
```

```lean
theorem summable_sparsePositiveMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    Summable (sparsePositiveMass α x N)
```

```lean
theorem sparsePositiveMass_tsum_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    0 ≤ (∑' j : ℕ, sparsePositiveMass α x N j) ∧
    (∑' j : ℕ, sparsePositiveMass α x N j) ≤ 1 / 4
```

```lean
theorem sparseLabelMass_nonneg (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparseLabelMass α x N j
```

```lean
theorem hasSum_sparseLabelMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    HasSum (sparseLabelMass α x N) 1
```

```lean
theorem sparseLabelMass_zero_ge (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) :
    (3 / 4 : ℝ) ≤ sparseLabelMass α x N 0
```

```lean
theorem sparseLabelMass_eq_positiveMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    sparseLabelMass α x N j = sparsePositiveMass α x N j
```

```lean
theorem summable_sparsePositiveMass_tail (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : Summable (fun k : ℕ => sparsePositiveMass α x N (j + k))
```

```lean
theorem sparseHighMass_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) : 0 ≤ sparseHighMass α x N j ∧ sparseHighMass α x N j ≤ 1 / 4
```

```lean
theorem sparseHighMass_succ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) :
    sparseHighMass α x N j = sparsePositiveMass α x N j + sparseHighMass α x N (j + 1)
```

```lean
theorem sparsePriorMass_zero (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) : sparsePriorMass α x N 0 = 0
```

```lean
theorem sparsePriorMass_eq_one_sub_highMass (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) : sparsePriorMass α x N j = 1 - sparseHighMass α x N j
```

```lean
theorem sparsePriorMass_bounds (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (j : ℕ) (hj : 1 ≤ j) :
    (3 / 4 : ℝ) ≤ sparsePriorMass α x N j ∧ sparsePriorMass α x N j < 1
```

```lean
theorem sparseHighMass_future_cost (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N)
    (j : ℕ) (hj : 1 ≤ j) :
    (N j : ℝ) * sparseHighMass α x N (j + 1) ≤ sparseDyadic j / (N j : ℝ)
```

```lean
theorem sparseHighMass_total_cost (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : SparseSelectionCore α x N)
    (j : ℕ) (hj : 1 ≤ j) :
    (N j : ℝ) * sparseHighMass α x N j ≤
      sparseDyadic j + sparseDyadic j / (N j : ℝ)
```

```lean
theorem tendsto_sparseHighMass_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => sparseHighMass α x N j) atTop (nhds 0)
```

```lean
theorem tendsto_sparsePriorMass_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ),
  Tendsto (fun j : ℕ => sparsePriorMass α x N j) atTop (nhds 1)
```

```lean
theorem tendsto_sparseHighMass_cost_zero :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_ : SparseSelectionCore α x N),
  Tendsto (fun j : ℕ => (N j : ℝ) * sparseHighMass α x N j)
    atTop (nhds 0)
```

```lean
theorem tendsto_sparsePriorMass_background_power_one :
  ∀ (α : ℝ) (x : ℕ → ℝ) (N : ℕ → ℕ) (_ : SparseSelectionCore α x N),
  Tendsto (fun j : ℕ => (sparsePriorMass α x N j) ^ (2 * (N j - 2)))
    atTop (nhds 1)
```

审查时间（UTC）：2026-10-22T21:54:21.170399+00:00。
