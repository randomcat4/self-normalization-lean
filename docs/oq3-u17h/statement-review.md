# U17h StageLayerDecomposition 独立声明 / 来源 / API 审查

STATUS: CORRECT

## 1. 完整定义与类型独立盲译（先持久化）

以下先只提取冻结 Lean fence，不读取 scope 解释、路线、实现笔记或机械凭据。该模块尚无实现；这里的翻译不构成实现审查。

```lean
def sourcePositiveNormalLayerTerm (mu : Measure ℝ) (q ell h theta : ℝ)
    (n k : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * Real.exp (-ell * (h * ((k : ℝ) + 1 - theta))) *
    (Measure.pi (fun _ : Fin n => mu)).real
      {z : Shao.Path n | normalDeviation q z = h * ((k : ℝ) + 1 - theta) ∧
        z ∈ sourceTail q n}

theorem stage_source_layer_decomposition (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i)) :
    ∀ n : ℕ,
      let theta : ℝ := Int.fract ((n : ℝ) * q / dyadicMesh J)
      Summable (fun k : ℕ =>
        sourcePositiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      Summable (fun k : ℕ =>
        negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k) ∧
      Real.sqrt (n : ℝ) *
          (∫ z : Shao.Path n in sourceTail q n, Real.exp (-ell * normalDeviation q z)
            ∂Measure.pi (fun _ : Fin n => mu)) =
        (∑' k : ℕ, sourcePositiveNormalLayerTerm mu q ell (dyadicMesh J) theta n k) +
          ∑' k : ℕ, negativeNormalLayerTerm mu q ell (dyadicMesh J) theta n k
```

定义独立翻译：对任意实数轴测度 μ、实数 q/ell/h/θ 和自然数 n/k，sourcePositiveNormalLayerTerm 是 sqrt(n) 乘 exp(−ell·h·(k+1−θ))，再乘同一个真实 n 重乘积测度 μ^n 对事件 {normalDeviation q=h·(k+1−θ)}∩sourceTail q n 的实质量。定义没有以正质量、格点相容、h 正或可积性作守卫，作为实数表达式本身全部参数均有定义。

目标独立翻译：固定同一个实数轴概率测度 μ、有限阶段 J 及任意实数 q、ell，假定 μ 几乎处处落在实际四基点加前 J 个新增点的有限阶段像中。对每个自然数 n，固定实际 θ=Int.fract(nq/dyadicMesh J)，则上面真实正层项序列和已有真实负层项序列分别真正可和；sqrt(n) 乘真实 sourceTail 上 exp(−ell·normalDeviation q) 的限制积分，恰好等于这两条实数可和序列的总和。

量词/边界核读：μ/J/q/ell 在 n 外固定，没有均值、方差、ell 正性或正单点假设。目标是每个 n 的精确恒等式及真 Summable，不是仅最终 n、渐近或几何界。J=0、n=0 与任意 q/ell 保留。θ 不是任意相位，而是真实分数部分，故其范围和与 nq/h 的相容性必须真实推出。

正层使用 k+1−θ，负层使用 −(k+θ)；必须核验真实产品 AE 格点上两族恰覆盖且互不相交，尤其 θ=0 的零层只能计入一次。必须先给真实任意 ell 的可积性，不能以总化积分或 tsum 的默认值伪造分解。该目标未声称 (19) 极限、条件 Lévy、移动阈值或完整 LLT。

## 2. 来源与声明范围

盲译已先写入 40 行 / 3104 字节，阶段 SHA256=cbbc624cf61d27f10316596c78e62ecb73a4ecb34f7d8d202ad1588decc48120。此后才读取 scope55 的解释、真实 R1 及固定前置/API；本任务没有实际实现可审，也没有读取作者 future/candidate/implementation notes。

R1 396–403 给实际有限模型的 h_J 整数法向网格与实际相位 θ={nq/h_J}。400–429 在这些层上组织正负层似然权重及原(19)极限；421 与 428–429 的负层权重/截断要求先有真实层和表示。本目标仅建立这一精确支持分解，未使用或证明原文的条件 Gaussian 极限、sign-tail 或 dominated-series limit。

新正项采用 sourceTail 交层的真实质量，已有 F 负项也采用同一个交事件。它们的和是 sqrt(n)·∫sourceTail exp(−ell·M_n)dμ^n；不是两条 raw 层质量，也不是正负侧各自的条件概率。新项与 U16b raw positiveNormalLayerTerm 名称和事件不同，不应误写成相等；后续若要取上界，需另用有限概率 measureReal_mono 与非负权重。

本声明不需要正原子、真实均值、q>0、ell≥0、方差或 gap。格距的最大性不影响精确分解，支撑于该零偏移网格已经足够；不对没有正质量的格层假定实际质量非零。μ/J/q/ell 是固定输入，所有 n 共用它们，未提供按 J/n 改选源参数的存在量词。

## 3. 独立数学可行性逐门检查

以下是对冻结声明的独立数学核验及可实现性判断，不是对尚不存在证明的正确性签票。

### 3.1 真实概率、支持和产品 AE 提升

记 h=dyadicMesh J=((2:ℝ)^J)⁻¹，故所有 J（包括0）均 h>0、h≠0。ν=Measure.pi(fun _:Fin n=>μ) 是真正 n 重乘积概率，空积 n=0 也是真概率，因而每个事件质量有限，ν.real 没有 top.toReal 伪装。

已接受 FiniteNormalSpan 26–34 的公开 stageAtom_normalValue_lattice 对每个 i:Fin4⊕FinJ 给实际 Y(stageAtom i)=h·k，k∈ℤ。它来自真实 normalValue=8x−x² 的阶段算术；新增点 addedAtom j 使用 j.val+1 偏移，j.val<J 给正确 stage 格距。J=0 时四个整数法向值仍在 h=1 网格上，不需新增点存在。

由 hrange，固定每坐标的 Measure.tendsto_eval_ae_ae.eventually 得同一 ν-AE 的阶段支持；有限 Fin n 的 ae_all_iff 使所有坐标同时满足。这一步是产品 AE 事实，不能把 μ-AE 支持直接当作全部 Path 的点态支持。

已接受 SampleBoundary 88–102 的公开 stage_sample_normal_layer 完整门是固定 q、n、J、实际 z 和“∀i，z i 在实际 stage range”；它不要求均值、正原子或概率。其结论为 ∃K∈ℤ，M_n(z)=h·K−nq。内部先对每坐标取实际整数，再取有限整数和；因此对刚才的 ν-AE 同坐标支持可以直接应用，且 n=0 的空和仍合法。它是当前 F 公开导入链中的接口，不需要访问 G 的私有 helper 或重写有限和证明。

### 3.2 实际相位与整数分流

设 x=nq/h、L=Int.floor x、θ=Int.fract x。实际 FloorRing ℝ 的库给 θ=x−(L:ℝ)、0≤θ<1、(L:ℝ)+θ=x。由 h≠0 得 nq=h·((L:ℝ)+θ)，再令 m=K−L∈ℤ，即得同一 ν-AE 的 M_n=h·((m:ℝ)−θ)。这里唯一需清除的分母是正 h，不除 n、sqrt(n)、q 或 ell。

定义 P_k={M_n=h·(k+1−θ) ∧ sourceTail}，N_k={M_n=−h·(k+θ) ∧ sourceTail}。整数 m 为正时唯一写成 k+1；m=0 时取 N_0；m<0 时写成 −k，k≥1。按 Int.ofNat 0、Int.ofNat(k+1)、Int.negSucc k 三种构造也可直接给覆盖见证，避免 toNat 的符号和零点错误。

0≤θ<1 与 h>0 给每个 P_k 的法向值严格正，N_k 的值非正；因此正负两方向点态 disjoint。同方向若层值相等，由 h≠0 消去 h 后 k=l，所以每方向是 pairwise disjoint。θ=0 时 N_0 恰是零层，P_0 是 +h；θ>0 时 N_0=−hθ，P_0=h(1−θ)，仍完整覆盖相邻两格。θ=1 从未发生，不可把 fract 上界误用成含1的情况。

每个 P_k/N_k 都点态包含于 E=sourceTail。反向覆盖 E⊆(⋃P_k)∪(⋃N_k) 仅在刚建立的 ν-AE 网格上成立，足以得到 E 与该两 union 的 ν-AE set equality。无需也不允许把没有支撑约束的所有路径强行格点化。

### 3.3 任意 ell 的真实全权重可积性

固定 stage 点的公开 fixedAtom_normalValue_lower 给 Y≥−9；从 hrange 的 inl/inr 两分支映到真实 fixedAtom，可得到同一 μ-AE 的下界。对所有实 x 恒有 Y(x)=16−(x−4)²≤16，所以同一 μ-AE 有 |Y|≤16。该对称界独立于 q 和 ell 的符号，不使用仅 ell≥0 才可用的单侧 likelihood bound。

产品坐标 AE 提升后，有限和给 |∑Y(z_i)|≤16n，故 |M_n(z)|≤(16+|q|)n。于是 −ell·M_n≤|ell|·|M_n|≤|ell|·(16+|q|)n；exp 权重的实际范数等于该正实指数本身，ν-AE 被有限实常数 exp(|ell|·(16+|q|)n) 支配。

M_n 是有限坐标多项式和减常数，真实连续；exp(−ell·M_n) 连续，故 AEStronglyMeasurable。ν 真有限，Integrable.of_bound 由上述 AE 范数界给真正全空间 Integrable，再常数乘 sqrt(n) 给 scaled integrand f_n=sqrt(n)·exp(−ell·M_n) 真 Integrable。所有这一切均对任意实 ell/q 和每个固定 n 成立，常数可以依赖 n，声明未要求该常数对 n 一致。

这也说明仅固定 n 的两个 Summable 结论不需要 E/F 的严格参数 gap 或全 n 几何支配；不能把本模块当作已经替代 U16b/F 的共同截断估计。

### 3.4 可测集合、限制积分和 countable Bochner 门

sourceTail_measurable q n 的真实公开类型对所有实 q、所有 n 给 E 可测，来自 energy、有限和与真实 sqrt 的连续性；q<0 时 Real.sqrt q 的总定义也保持此可测性，无需增补 q≥0 门。M_n 连续，故每个层等值集可测；与 E 相交后 P_k/N_k 可测，其 Nat countable union 也可测。

真实全空间 Integrable f_n 经 Integrable.integrableOn 可限制到每一方向的整个 union，以及各层。这样才使用 hasSum_integral_iUnion：索引 Nat 可数、每层可测、同方向 pairwise Disjoint、全 union 上真 IntegrableOn 四门均已真实建立。API 给的是每层真实限制积分序列的 HasSum，因而同时给 Summable 和 tsum 等式，不是对可能不可和项使用总化 tsum。

两方向 union 点态 disjoint；setIntegral_union 消费两侧真实 IntegrableOn 和可测性。E 与其 union 的 ν-AE set equality 则由 setIntegral_congr_set 转换限制积分。没有把 AE 覆盖冒充点态集合相等，也没有在未证明联合可积时暗用 Fubini；本分解可直接使用实际 countable Bochner 分解 API，无需另一个产品积分交换定理。

在 P_k 上，真实等值 M_n=h(k+1−θ) 给 f_n 常数 sqrt(n)·exp(−ell·h(k+1−θ))；在 N_k 上，M_n=−h(k+θ) 给常数 sqrt(n)·exp(+ell·h(k+θ))。setIntegral_congr_fun 需要的层可测性与真实点态等式均满足，setIntegral_const 的 ν.real(层) 由真有限概率保证是实际有限质量。交换实数乘法顺序后两层积分精确是新正 DEF 与已有 F 负 DEF，正负号及 θ 参数无额外 1−θ 替换。

将两方向的 HasSum 用该逐项恒等式转换，得到两个所要求真实序列的 Summable；再取两方向 tsum，合并 union 积分，并以 integral_const_mul 将 sqrt(n) 提出，正好得到完整冻结目标。不存在漏乘 h、误加归一化常数或条件概率分母；本目标是精确加权限制积分，不是 Fourier 反演式。

### 3.5 边界和量词

n=0 时 sqrt(n)=0，两个定义的所有项为0，左侧也为0；无需正 n 或消除 sqrt(n)，空产品 ν 仍有限概率，真实 exp 权重仍可积。J=0 给 h=1，上述支撑/分流不变。ell=0、负 ell、q=0、负 q、只在少数阶段点带质量或空层均不破坏任何门。

k=0 和零层由实际 θ 正确处理，只有 N_0 在 θ=0 时为零层；不存在两侧重复零层。目标没有要求 hpos，因此不能宣称所有层都非空、格距必为最大或方差严格正。这些额外性质均不是此精确分解所需前提。

两个序列所用的 n、μ、q、ell、h、θ 完全相同。目标是 ∀n 的精确可和分解，未在 n 中重新选择源参数，也未声明 θ_n 收敛、固定层移动阈值的概率极限或 dominated-series limit。

## 4. 指定固定库实际 API 读核

只读实际固定库源，未运行 Lean、#check 或 API 探针。下列真实类型支持上述声明，不依靠作者路线中的简写来猜接口。

| 实际库位置 | 已核真实类型及满足门 |
| --- | --- |
| Algebra/Order/Floor/Defs.lean 263–265 | Int.fract a=a−Int.floor a |
| Algebra/Order/Floor/Ring.lean 311–312 | Int.floor_add_fract：floor a 的实嵌入加 fract a 等于 a |
| 同文件 438–446 | Int.fract_nonneg 与 Int.fract_lt_one，无错误含1端点 |
| Algebra/Order/Archimedean/Real/Basic.lean 37–38 | 实际 noncomputable FloorRing ℝ 实例；不是只有 generic FloorRing 假设 |
| MeasureTheory/Constructions/Pi.lean 311–313 | 每坐标概率给真正 Measure.pi 概率，包含 Fin0 空积 |
| 同文件 425–426（相关 section 有坐标 SigmaFinite） | Measure.tendsto_eval_ae_ae 给真实坐标 AE 提升；概率保证 SigmaFinite，Fin n 提供 Fintype |
| MeasureTheory/Integral/IntegrableOn.lean 171–172 | Integrable.of_bound 要求有限测度、AEStronglyMeasurable 和 AE 范数界；第3.3节均提供 |
| 同文件 164 | Integrable.integrableOn 可将真实全空间可积性限制到任意 union/层 |
| MeasureTheory/Integral/Bochner/Set.lean 77–78 | setIntegral_congr_set 输入真实 AE set equality |
| 同文件 85–87 | setIntegral_union 输入 Disjoint、第二集合可测、双方 IntegrableOn |
| 同文件 320–325 | hasSum_integral_iUnion 输入 Countable、每层可测、Pairwise Disjoint、全 union IntegrableOn；输出 HasSum |
| 同文件 327–330 | integral_iUnion 是上述真 HasSum 的 tsum 等式，没有无条件积分可数相加 |
| 同文件 73–75、520–521 | setIntegral_congr_fun 消费可测层与层上真实 EqOn；setIntegral_const 给 μ.real s •c，实际本问题所有层质量有限 |

Bochner.Set 有 public section，且公开导入 LocallyIntegrable、Bochner.SumMeasure 等；Floor.Ring 也有 public section 并公开导入实际 Floor 基础；Archimedean.Real.Basic 的 FloorRing ℝ 实例位于 expose/public section。使用实值积分时 ℝ 的完备空间/实范数线性结构均为现有实例，未发生默认 Lebesgue measure 问题：本目标积分显式指定真实 Measure.pi。

至此独立数学、来源和实际 API 语义均未发现声明阻塞。下面才检查冻结 hash、真实导入闭包与缓存/pins；尚无实现或 receipt/Audit 可作证明证据。

## 5. 最后进行的冻结、实际环境与缓存核验

所有机械检查在上述独立数学和 API 语义之后进行；仅共享 server.py 指定服务器只读执行，全部远端项目命令 taskset -c 14-17。没有 Lean/#check/API probe/build/rebuild/cachewrite/spawn/commit，未复制 raw 完整日志，未读下一 scope 或作者 future/candidate/implementation notes，未触外部 CPU0–9/80GiB 或全局资源，也未使用 ulimit-v。

实际 worktree=/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3；branch=feat/oq3-stage-layer-decomposition；HEAD=cf44108a4cc2b62b05a8a281de02d962305b56b0。git status 实际为空。此前 G 发布后的正常 HEAD 推进不改变本 H 所消费前置。两端 StageLayerDecomposition.lean 均不存在，未产生目标证明或机械 build/Audit/receipt；本票没有将任何声明可行性核对冒称实现成功。

| 冻结对象 / pins | 实核 SHA256 |
| --- | --- |
| 本地 fifty-fifth-unit-scope.md 与远端 u17h-20261021/scope.md，7064字节/48行 | 83bab854d74daa250c1a1ff68432988d82c03ce230a71d2b17f5bf25c4e37da4 |
| 原始 R1 report.md | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |
| lean-toolchain，29字节/1行 | d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4 |
| lake-manifest.json，3541字节/117行 | 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e |

实际 toolchain 文本为 leanprover/lean4:v4.36.0-rc1，实际 Mathlib HEAD=807d3836b165983210ee2ecf3cd28f239436949c。冻结 fence 独立枚举为1个完整公开 DEF、1个完整 theorem 类型；现有实际项目前置中未发现这两个拟公开名字的冲突。拟 imports 是 F 加 Floor.Ring、Archimedean.Real.Basic、Bochner.Set；未增加 G、Levy 或下一单元为依赖。

### 5.1 全部实际项目闭包

从实际 F 源递归读取 import，得到44个项目源（F本身+43个前置），逐份实核 SHA 并与已接受 F 闭包基线一致；44个对应现成项目 olean 均存在。H尚无源，因此这是冻结 imports 的真实前置闭包，不是从不存在的目标编译声称得到的闭包。

| 实际项目源 | 实核 SHA256 |
| --- | --- |
| Shao/OQ3/BinaryEntropyBounds.lean | 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228 |
| Shao/OQ3/SourceBinaryEntropyGap.lean | f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9 |
| Shao/OQ3/FiniteConstraints.lean | 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0 |
| Shao/OQ3/SourceStarter.lean | 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d |
| Shao/OQ3/SummableAtoms.lean | 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b |
| Shao/OQ3/AtomicMeasure.lean | 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39 |
| Shao/OQ3/InverseTilt.lean | c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811 |
| Shao/OQ3/EnergyBernoulliMGF.lean | e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad |
| Shao/OQ3/FiniteStageMeasure.lean | 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1 |
| Shao/OQ3/AtomProjection.lean | 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22 |
| Shao/OQ3/ResonanceArithmetic.lean | cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b |
| Shao/OQ3/FiniteNormalSpan.lean | 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de |
| Shao/Basic/FinitePath.lean | 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb |
| Shao/Probability/FiniteIID.lean | d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b |
| Shao/OQ3/SampleBoundary.lean | 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2 |
| Shao/OQ3/SourceEnergyGeometry.lean | 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a |
| Shao/OQ3/FarEnergyExponentialCover.lean | 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d |
| Shao/OQ3/PositiveRate.lean | 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b |
| Shao/OQ3/RegularCovariance.lean | 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853 |
| Shao/OQ3/NormalTangentGaussian.lean | d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39 |
| Shao/OQ3/NormalTangentMoments.lean | 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1 |
| Shao/OQ3/CenteredLogMGF.lean | 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4 |
| Shao/OQ3/CenteredSampleTilt.lean | d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501 |
| Shao/OQ3/SourceFarWeightedTail.lean | c9e4c14af297353c5358da6d3e75d72f712649e535102ba18297fc00a0e5261f |
| Shao/OQ3/LocalRateMargin.lean | 5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77 |
| Shao/OQ3/NormalTrialCost.lean | 8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895 |
| Shao/OQ3/JointNonlattice.lean | 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559 |
| Shao/OQ3/FiniteFarArc.lean | 3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71 |
| Shao/OQ3/TiltedMeasureDomination.lean | 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b |
| Shao/OQ3/ProductMeasureDomination.lean | 9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f |
| Shao/OQ3/CompactTiltDomination.lean | 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623 |
| Shao/OQ3/CharacteristicMeasureDomination.lean | ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb |
| Shao/OQ3/NormalTangentPowerLimit.lean | 819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457 |
| Shao/OQ3/NormalTangentDomination.lean | b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90 |
| Shao/OQ3/CentralFourierIntegral.lean | 4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93 |
| Shao/OQ3/NormalLayerFourier.lean | 063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3 |
| Shao/OQ3/FundamentalFourierAsymptotic.lean | aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1 |
| Shao/OQ3/NormalLayerConditionalLaw.lean | 94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a |
| Shao/OQ3/NormalLayerMassBound.lean | 66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1 |
| Shao/OQ3/CompactTiltLayerMassBound.lean | 5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7 |
| Shao/OQ3/LocalNegativeLayerTail.lean | 049361c77716896922fb1d7cd3e6abf84515b76a99103c597d8d74b63a2f1856 |
| Shao/OQ3/LocalNegativeLayerControl.lean | e94a5a8e82d2a69a946a12e16f3fb2a58b174fb036becce5632d7c600b796f01 |
| Shao/OQ3/GlobalNegativeLayerBound.lean | 57b61e6e3bfd184586083e55633a563e4176cbfcf16def62a7d860d92b5c01d8 |
| Shao/OQ3/NegativeLayerGeometricTail.lean | 8077cfb97547c4a8c5b22da6ed17a58168a6ca1f6b2654f6799292a06a8b23f4 |

本地被直接语义核读的 F、FiniteNormalSpan、SampleBoundary 源与远端上述 SHA 完全一致。实际阶段格点接口 stageAtom_normalValue_lattice、stage_sample_normal_layer、sourceTail_measurable、fixedAtom_normalValue_lower 均是已接受源中的公开声明，实际 F 导入链可达；本门不依赖不可见私有 helper。

### 5.2 实际公开导入可达性与库缓存

独立沿项目闭包的 Mathlib imports 加三个显式库 import 递归读取实际源码：共有51个直接 Mathlib 根模块，其全递归 Mathlib 源依赖为2848份。每份实际源与对应现成 olean 均存在，缺失清单为空；只读检查未下载、生成或更新任何缓存。此计数是本声明实际闭包，不涉及仍待 root 的 U18a Levy/Portmanteau 闭包，不能把后者缺项冒作本门阻塞或声称已修复后者。

按实际 module 的 public import 继续追踪，以下全部 API owner 均公开可达（而非仅在磁盘上找到源）；其实际 SHA 如下。

| 实际公开 API 所在库源 | SHA256 |
| --- | --- |
| Mathlib/Algebra/Order/Floor/Defs.lean | 58450c1ab0d8bb32bc03dadc047190856f73c66f4f36a7392e9f4a842c75de2f |
| Mathlib/Algebra/Order/Floor/Ring.lean | 4ed31dda62383dcc0e877fbc27908e34a964a39a1b8209b53d1a6c0db7f9d1d6 |
| Mathlib/Algebra/Order/Archimedean/Real/Basic.lean | 20122ee310cd4f8809cc0527edfbdbdf048d27793696d5c359ec1f6669636691 |
| Mathlib/MeasureTheory/Constructions/Pi.lean | bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef |
| Mathlib/MeasureTheory/Integral/IntegrableOn.lean | d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2 |
| Mathlib/MeasureTheory/Integral/Bochner/Set.lean | e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75 |

无需临时依赖不存在或 deprecated 的 Data.Real.Archimedean 路径；冻结已明确真实 Archimedean.Real.Basic。现成范数/概率/有限产品/实 FloorRing/可数 Nat/实完备空间实例均符合声明的实际类型。此为静态环境门，不是 Lean elaboration 或目标内核成功报告。

## 6. 最终独立声明裁决

STATUS: CORRECT

JUSTIFICATION: 冻结定义和完整目标准确表达同一真实 μ^n 上的 sourceTail 指数加权限制积分的正负层精确分解。只需所列概率与阶段 AE 支撑：实际格点经真正产品 AE 提升后给 M_n=h(m−fract(nq/h))；正整数与非正整数唯一分流，θ=0 的零层仅计入负侧。任意 ell/q 的全权重由真实 Y 双侧有界和有限产品概率给真 Integrable，再建立全部层/union 可测、点态 disjoint 与 AE 覆盖。实际 hasSum_integral_iUnion 的完整门真实可满足，同时给所需真实序列 Summable 和精确 tsum；层积分常数化恰匹配两个 DEF 的符号、相位和真实有限质量。n=0/J=0、缺正原子、空层、负 ell/q 均有合法解释，没有总化积分/tsum、无限实质量或非法 sqrt/n 除法。

来源限定在 R1 400–429 的实际格点层和表示前置，API/显式实 FloorRing/公开导入/缓存均无已知阻塞。因此批准本冻结声明进入独立实现阶段；本票不签署尚不存在的具体证明或编译，也不以 G/F 成功构建代替 H 的未来实现审查。

原(19)的 dominated-series 极限、conditional Lévy、finite-layer moving threshold/sign-tail、全19、LLT、hW、generalKL、全局率最优/极小、新颖性及根 A/B/C/D 仍 OPEN。后续若用正项 raw 上界或双侧极限，须另证相应概率比较和收敛门；本精确恒等式不自动完成这些义务。
