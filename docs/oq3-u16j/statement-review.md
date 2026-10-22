# U16j LocalNegativeLayerControl 独立声明/source 审查

STATUS: CORRECT

本票仅审冻结声明，不审尚不存在的实现。唯一 reviewer lease 1；未 spawn、Lean/probe/build、写缓存或改动其他文件。本次第一阶段仅读取 scope 的 Lean fence；以下独立翻译先于 scope 正文、来源和作者路线持久化。既有声明/证明审查上下文存在，不能把此前接受或作者预期作为本票结论。

冻结 scope SHA256: `2092cb4630dbcb797a9bd0cc93992d7064937b696b184d354d10fad1082329ad`。

## 1. 实际冻结完整定义与类型（盲读阶段）

```lean
def localNegativeNormalLayerTerm (mu : Measure ℝ) (q ell h theta delta : ℝ)
    (n k : ℕ) : ℝ :=
  if h * ((k : ℝ) + theta) / (n : ℝ) ≤ delta then
    Real.sqrt (n : ℝ) * Real.exp (ell * (h * ((k : ℝ) + theta))) *
      (Measure.pi (fun _ : Fin n => mu)).real
        {z : Shao.Path n | normalDeviation q z = -(h * ((k : ℝ) + theta)) ∧
          z ∈ sourceTail q n}
  else 0

theorem exists_local_source_negative_layer_bound (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 0 ≤ k → k / (n : ℝ) ≤ delta →
        Real.sqrt (n : ℝ) * Real.exp (ell * k) *
          (Measure.pi (fun _ : Fin n => mu)).real
            {z : Shao.Path n | normalDeviation q z = -k ∧ z ∈ sourceTail q n} ≤
          C * Real.exp (-gamma * k)

theorem exists_local_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ)
    (hb : ∀ᵐ x ∂mu, |x| ≤ 4 + Real.sqrt 10)
    (hq : 0 < q) (hell : 0 ≤ ell)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hS : 0 < normalVariance mu) (hD : 0 < (parabolaCovariance mu).det)
    (hgap : ell < q / (32 * transverseVariance mu))
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ delta gamma C : ℝ, 0 < delta ∧ 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          localNegativeNormalLayerTerm mu q ell (dyadicMesh J) theta delta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J))
```

## 2. 独立盲译（先落盘）

记 μ 为实数上的测度，P_n=μ 的真正 n 重有限产品，M_q(z)=normalDeviation q z。定义 localNegativeNormalLayerTerm 对任意实参数 q、ell、h、theta、delta 和自然数 n、k，令 u=h(k+theta)。若 u/n≤delta，则取 sqrt(n) exp(ell*u) P_n.real{M_q=−u 且 z∈sourceTail q n}；否则为 0。定义本身不要求上述参数正，不要求 μ 是概率，也不排除 n=0；实数除以零和 sqrt0 依 Lean/实数标准总化语义。分支为显式局部截断，未断言被截去部分的真实概率为零。

第一定理固定同一个概率 μ、自然阶段 J、实 q>0 与 ell≥0。要求 μ-AE |x|≤4+sqrt10，真实 Y=normalValue 的均值为 q、真实 X 的均值为 q/4，实际 normalVariance>0、实际 parabolaCovariance 的行列式>0，并有 ell<q/(32*实际 transverseVariance)。要求 μ-AE 支撑于四基点加 J 个实际 addedAtom 的活跃有限阶段，并要求每个活跃索引对应的真实单点质量正。结论存在共同正 delta、gamma、C，在所有充分大的自然数 n 上，对全部实 k≥0，只要 k/n≤delta，真实 sourceTail 与负 normal 层 M_q=−k 的交事件满足 sqrt(n)exp(ell*k)P_n.real(event)≤C exp(−gamma*k)。所有常数及最终 n 阈值在 k 之外；k=0、ell=0、J=0 未被排除。结论只管 k/n 的局部范围，没有约束事件内每条样本的切向位移。

第二定理的固定输入、真实概率、均值/协方差/严格 gap/有限支撑与活跃原子正性完全相同。它存在共同正 delta、gamma、C，在所有充分大的 n 上，对全部 theta∈[0,1]，取同一个实际 h=dyadicMesh J 后，前述局部截断项作为 k∈Nat 的实级数真正 Summable；且对全部自然截断 K，其移位尾和 Σ_k term(K+k)≤C*rho^K/(1−rho)，其中 rho=exp(−gamma*h)。常数和 n 阈值均在所有 theta/K 之外，theta=0、theta=1、K=0 包含。Summable 是结论的一部分，不能以总化 tsum 冒充。定义分支与 h 的正性、rho∈(0,1)、分母正性须在后续独立检查，不能从符号假设它们成立。

本阶段仅忠实转述完整类型。尚未判断 sourceTail 几何能否提供切向阈值、同一局部半径能否从 I 的两个比例门推出，以及库 API/导入环境是否充足。根 A/B/C/D 与 full17/19、LLT、hW、globalfar 均 OPEN。

## 3. 来源与实际接口的独立比对

盲译阶段报告已先持久化：SHA256 `d0664ac74d14a5bd5c0b68c01ce878adeaab1ff93a66cc25cb26b78bb29c09e2`，5592 bytes/70 行。其后才读 scope 正文、真实 R1 和前置源码；未读未来 J 实现或 U17a/energy/rotation 笔记。

R1 原件 `C:/game/shao/current/oq3/proofs/r1/report.md` 实际 SHA256 为 `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`。361–366 给局部双侧切向尾估计，378–388 将曲边约束接成带 exp(ell*k) 的负层指数衰减；389–391 另需远区全局 gap 才做全局控制。400–406 是真实曲边恒等式，421–429 是层权重和截断的来源。候选是已证明 I 的 sourceTail 专门化与局部几何尾和；不是 R1 中未另形式化的 Legendre 优化、全局 rate gap 或完整 (19) 的证明。

实际 `SampleBoundary.lean:19–27`：M_q=ΣY−nq；tangentDeviation q=ΣX−nq/4；sourceTail={energy>0 且 sqrt(q)/4*sqrt(n*energy)≤ΣX}。真实能量 `FinitePath.lean:31` 是 ΣX²。`curved_sample_identity`（34–39）为 (ΣX)²−n(q/16)energy=(nq/16)M_q+R_q²，因子16正确。`sourceTail_iff_curved`（53–79）明确 q>0、n>0，先正根/和符号再平方；`sourceTail_on_normal_layer`（81–86）保留 energy>0、ΣX>0，负层 d=−k 上给 nqk/16≤R_q²。没有把平方条件反推不含正和条件的 sourceTail。

实际 I 唯一公开类型已经逐字读完：`exists_local_negative_layer_tail_bound` 固定同一 μ/J/q/a/ell，接受本票全部假设（令 a=q/4 即可），给 δ0,γ,c,C>0 和在全部实 k,r 外的 eventual n，控制 {M_q=−k 且 r≤|ΣX−na|}，只需 k/n≤δ0、r/n≤δ0 和 nqk/16≤r²。I 的事件内 R 不受局部上界限制，所以可用于这里任意远的样本 R，不需额外分割事件。

**scope 路线文字包含方向纠正（不改变完整定义/类型）：** scope 句“故真实曲边事件包含I的双侧tail事件”方向写反。由平方条件实际得到
`{M_q=−k 且 sourceTail} ⊆ {M_q=−k 且 r≤|R_q|}`。
必须用这个 subset 方向才能以 `measureReal_mono` 给真实 sourceTail 概率上界。完整冻结目标没有该错误，正确方向的证明成立；这属于说明文字的可明确纠正，不是类型阻塞。冻结 scope 保持原样，本票不改它。作者后续实现仍须实际构造此正确 subset。

## 4. 首目标的数学可行性与全部门

1. 固定原 μ/J/q/ell，使用 I 的 a=q/4；本票真实 hmeanX 恰匹配。I 的 S、det、T=transverseVariance 都是同一 μ 的实际量；没有改中心或另选概率族。共同 δ0,γ,c,C 先于 n/k，保持原 hgap 的32因子；ell≥0 含0。
2. 令 δ=min(δ0,16δ0²/q)。q>0、δ0>0 保证第二项和 δ 都严格正，且 δ≤δ0。把 I 的 eventual n 与 eventual n≥1 相交；由此 N=(n:ℝ)>0。这一阈值仍在所有 k 之外。没有对 k、r、ell 或 b 作非零除法。
3. 给任意 k≥0、k/N≤δ，令 r=sqrt(N*q*k/16)。被开方数非负，故 r≥0 且 r²=N*q*k/16，I 的曲尾约束取等号。由 k/N≤16δ0²/q，得到 q*k/(16N)≤δ0²，即 (r/N)²≤δ0²。r/N≥0 与 δ0>0 才允许平方比较推出 r/N≤δ0；这不是不检查符号的“开根”。亦可先证 r²≤(Nδ0)²，再用非负平方比较后除正N。k=0 时 r=0，同一论证有效。
4. 对 sourceTail∩负层的每条真实样本，使用 `sourceTail_on_normal_layer q hq n hn z (-k) hd`；正确化简 -(N*q/16*(-k))=N*q*k/16 得 r²≤R_q²。因 r≥0、|R_q|≥0，可由 |R_q|²=R_q² 得 r≤|R_q|。再由 tangentDeviation q=(ΣX)−N*(q/4) 与 a=q/4 的实数代数，得到 I 的实际双侧事件。只取该等价的正向，不丢失 sourceTail 中正能量/正和门后声称等价。
5. P_n=Measure.pi(fun _:Fin n=>μ) 是真正概率，因而有限。实际 `MeasureTheory.measureReal_mono` 需要目标事件的 ENNReal 质量≠∞；该门由概率有限保证，不能仅因 toReal 后有限而省略。事件可测也真实成立：sourceTail 已有公开可测定理，M_q 和 ΣX 是有限连续多项式的和，层集合是连续函数的等值闭集。此 subset 概率比较本身不需新积分/Fubini/DCT；所有真指数可积/tilt 比较已经在所消费 I 的完整独立证明中审过，本票不扩展其前提。
6. sqrtN≥0、exp(ell*k)>0，故能以非负权重乘实概率上界。I 给 C exp(−γk−c*r²/N)。c>0、r²≥0、N>0 先给 c*r²/N≥0，指数单调遂给 ≤C exp(−γk)，且 C>0 允许乘不等式。这里舍去有利项，不更改 γ，也不推断实际 rate 的全局最小。

结论：首目标在原固定假设下有完整标准数学推导。delta/gamma/C 和 n 阈值没有依赖待量化 k；事件内实际切向 R 仍不受局部截断。n=0 只被 eventual n≥1 排除，不因标准0除总化获得任何缩放事实。J=0/ell=0/k=0 边界无额外排除。

## 5. 局部定义与第二目标的真正级数门

实际 `FiniteConstraints.lean:45` 定义 h=dyadicMesh J=((2:ℝ)^J)⁻¹，所以每个自然 J 都有 h>0，J=0 时 h=1。令 ρ=exp(−γh)；γ>0,h>0 给 0<ρ<1、|ρ|<1、1−ρ>0。几何常数来自 γ，不需要额外 ell>0；ell=0 仍保留。

对同一首目标常数与同一 eventual n，先固定任意 theta∈[0,1]。对每个自然 k，u=h(k+theta)≥0。定义项始终非负：true 分支为非负 sqrt、正exp和非负真实 measure.real 的乘积，false 分支为0。true 分支的守卫就是 u/N≤δ，故首目标适用实际层 M_q=−u，给 term≤C exp(−γu)。由于 theta≥0，−γh(k+theta)≤−γhk，故 term≤Cρ^k，使用 exp_nat_mul 和实数交换律；false 分支则由 Cρ^k≥0 得同一上界。theta≤1 不被这一 majorant 使用是合法较强输入，不应因此删去 theta=1 或错误补层互斥假设。

几何级数 Σρ^k 真 Summable，乘 C 后真 Summable；由非负比较得到实际 term 真 Summable，先于任何 tsum 数值比较。对每个 K 再显式建立 shifted term 的非负与 term(K+k)≤Cρ^(K+k)=(Cρ^K)ρ^k，几何 majorant 真 Summable，再得 shifted term 真 Summable；只有这两个真可和门建立后，用 `Summable.tsum_le_tsum` 和 `Summable.tsum_mul_left` 取得尾和≤Cρ^K*(1−ρ)⁻¹，等于冻结的 Cρ^K/(1−ρ)。不以“tsum 总可写”当成级数收敛。

所有常数、δ和 eventual n 仍先于 theta/K；没有逐theta选N或逐K改变δ。theta=0,k=0 允许 u=0 的零层，theta=1 与 K=0 也都在同一估计中。分支边界等号使用≤，不留下空洞。每项 false 仅表示定义的局部贡献为0，**不**断言被截去的大负层真实概率为0。此类截断项甚至对每个正n有有限活跃索引，但本推导不靠未证明的“有限支撑”跳过真正 Summable 门；直接比较与冻结级数结论相符。

## 6. 实际固定库语义（只读，未运行 Lean/probe）

- `Mathlib/MeasureTheory/Constructions/Pi.lean:311–313` 的 `pi.instIsProbabilityMeasure` 从所有坐标概率给真实 Measure.pi 概率，包含 Fin0；有概率再有有限、所有事件质量非top。
- `Mathlib/MeasureTheory/Measure/Real.lean:88–90` 的 `MeasureTheory.measureReal_mono (h:s₁⊆s₂) (h₂:μ s₂≠∞ := by finiteness)` 才由 ENNReal.toReal_mono 传到真实实质量。本票已逐项给 subset/finite，未作 top.toReal 错误。
- `Mathlib/Analysis/Real/Sqrt.lean:143–145,176–177,227–229` 的 Real.sqrt_nonneg、Real.sq_sqrt（需0≤被开方数）、Real.sqrt_le_iff 明确开根的非负门；真实双侧平方比较还需 |R|≥0。
- `Mathlib/Analysis/Complex/Exponential.lean:234–235,337–341` 的实际 Real.exp_nat_mul、exp_lt_one_iff、exp_le_one_iff 给 ρ、幂指数与正分母，不能把 Complex/Real namespace 混用。
- `Mathlib/Analysis/SpecificLimits/Normed.lean:493–497` 实际公开 `summable_geometric_of_abs_lt_one`、`tsum_geometric_of_abs_lt_one`；后者数值是 (1−ρ)⁻¹。该模块 public imports Basic、InfiniteSum/Normed 等，不是缺失 cache 的 ExponentialBounds。
- `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:531–537` 实际 `Summable.of_nonneg_of_le` 是**实数**非负比较检验，参数顺序为目标非负、逐项目标≤已知可和majorant、majorant可和；并非只能 ENNReal 使用。
- `Mathlib/Topology/Algebra/InfiniteSum/Order.lean:132–135` 的 `@[to_additive (attr := gcongr)] protected theorem Multipliable.tprod_le_tprod` 生成实际 `Summable.tsum_le_tsum`；其消费逐项≤及两侧真可和、滤子NeBot。通常自然级数滤子满足此实例。此处实际查到的是 to_additive 生成来源，未伪称源码手写一个不存在的 Summable 声明。
- `Mathlib/Topology/Algebra/InfiniteSum/Ring.lean:53–55` 的实际 `Summable.tsum_mul_left` 在真可和后抽常数；rho^(K+k) 分拆为标准 pow_add。完整实数/自然幂、Fin n、BigOperators、Filter.atTop、Set.Icc 和普通实数 Decidable 次序由拟imports及真实传递环境可见。

数学/source/API 阶段判断：两个目标与一完整定义相容，无类型层面的缺失假设或反例；唯一发现为scope路线的包含方向笔误，已明确记录正确方向。尚待最后静态环境/哈希核对后给最终 STATUS。未实现或证明任何 U16j 目标。

## 7. 最后静态环境、冻结绑定与证据限度

数学/source/API 阶段已在最后环境核对前持久化：SHA256 `bef3bf36c09a4dc0537e64769aeabb0497a75ebf49358defd9d5509bb1b641dd`，14886 bytes/118 行。其后才只读核以下两端 scope、实际前置文件、导入图、现成 olean 与 pins。J 尚无实现，所以不存在可声称为本票核过的 J build/Audit/receipt；此次没有运行任何 Lean/API probe 或构建。

| 冻结/实际文件 | 实际 SHA256 | 字节/行 | 独立核对 |
|---|---|---|---|
| 本地 forty-sixth-unit-scope.md / remote run scope.md | `2092cb4630dbcb797a9bd0cc93992d7064937b696b184d354d10fad1082329ad` | 5922/64 | 两端相同，完整fence已先盲译 |
| 实际 LocalNegativeLayerTail.lean（I，本地draft/remote工作树） | `049361c77716896922fb1d7cd3e6abf84515b76a99103c597d8d74b63a2f1856` | 12163/221 | 两端同已接受I冻结源，唯一公开完整类型实际读完 |
| 实际 SampleBoundary.lean（本地draft/remote工作树） | `7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2` | 7131/167 | 两端相同，真实M/R/sourceTail及平方门实际读完 |
| lean-toolchain | `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4` | 29/1 | `leanprover/lean4:v4.36.0-rc1` |
| lake-manifest.json | `40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e` | 3541/117 | 实际工作树pin未变 |

实际 Mathlib HEAD 为 `807d3836b165983210ee2ecf3cd28f239436949c`。所有远端读取通过指定共享 broker，host key SHA256 `+IZMFu9Xx6FSAhvQhtvZ3MpV70v2d+XNWcequAbsp+c`；没有改连接或读取凭据。

拟声明上下文为三个实际 import：`Shao.OQ3.LocalNegativeLayerTail`、`Shao.OQ3.SampleBoundary`、`Mathlib.Analysis.SpecificLimits.Normed`；namespace Shao.OQ3，open MeasureTheory Filter，open scoped BigOperators，noncomputable section。完整定义体与两个完整类型在本票第一节原样保留，不依赖 Matrix notation 新scope或额外 Lebesgue volume 实例。标准实数/自然数/Measure.pi/Fin n、一般事件实质量、可和级数所需对象均已有实际环境来源。

从前两个项目 import 实际递归读取源码，共 **35 个 Shao 模块**（已接受 I 加其34项实际闭包；SampleBoundary 已在其中）。把历史 I 的 prerequisite-hashes.json 中 `.lean` 路径键规范成模块名后，实际35项集合与每项重新计算的SHA均匹配预期，无差异；35个对应工作树 `.olean` 全部实际存在。本次规范化排序的 module→sha256 字典（JSON sort_keys=True,separators=(',',':')，UTF-8）整体SHA为 `ee24898a49f35948e6779ef543ac732b820383246583b66bf79caac754a986a2`。这只是现成依赖冻结/缓存检查，不把 olean 存在冒充 J 目标已 elaboration 或 kernel checked。

下列实际库源均由拟 import 源码图可达，且各自既有 `.olean` 实际存在；读取的是第6节所列真实API/生成来源，未猜测未来实现：

| 库模块（Mathlib前缀省略） | 实际源SHA256 |
|---|---|
| Analysis.SpecificLimits.Normed | `eee44dfd62feb67bdf3ccc6cf57e8e101f38a7408dbb9c6347e0978ce2010d41` |
| MeasureTheory.Constructions.Pi | `bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef` |
| MeasureTheory.Measure.Real | `1b9d1490fa5acbffc570eac67f465d3d6ab0520aa3e54464f7520d60d6619b8d` |
| Analysis.Real.Sqrt | `1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204` |
| Analysis.Complex.Exponential | `35d9f9e6abaf24d09a25cb1eeefbfc4180c3fe18de4d47362704c2f9f6601146` |
| Topology.Algebra.InfiniteSum.ENNReal | `88ef56c969006630d0066b7af2c74e75dd060608f3c42f0ef288ad1c6da908cc` |
| Topology.Algebra.InfiniteSum.Order | `526aed3d15913b1d7ad9de9f28fc26ac9ab023942b0d80cbc72323a293817b01` |
| Topology.Algebra.InfiniteSum.Ring | `bba1f8897f3b78060d4893ee3b47f8edf6f533d2adca7909305d0a42ee50c087` |

远端 `Shao/OQ3/LocalNegativeLayerControl.lean` 在检查时确实不存在；没有未来实现路线可被当作已经证明。此静态门不保证未来每个战术脚本一次 elaboration 成功；实现后仍须独立 fullproof/全部actualTYPE/真实机械核验，不能引用本声明 CORRECT 当成已完成证明。

## 8. 最终判定与非声明

JUSTIFICATION: **CORRECT。** 冻结一完整定义体和两个完整类型的量词/真实概率语义正确。首目标可由同一固定概率 I 的已接受实际完整接口、a=q/4 的真实中心恒等式、正n/q下的共同半径与开根门，以及正确 subset 方向的有限实概率比较得到；实际事件内R不需局部上界。第二目标的局部if明确、真实项非负，同一 γ/h 给严格几何比率，真 Summable 与移位 Summable 均能先于 tsum 比较建立，常数/N在全部theta/K外。q>0、n≥1、零层/k0、theta0/1、ell0、J0与守卫等号无隐藏排除；原点定义使用总化除法不构成任何非法归一化。上述实际固定API/公开导入/现成缓存未发现声明或环境阻塞。

唯一说明文字问题是 scope 的事件包含方向笔误，本票已显式改述所需方向，lead亦已确认正确方向；冻结scope不改，完整类型无需修订。作者实现必须使用第3–4节的正确 subset 方向。

本结论只批准 **U16j 声明/source/API门**，不声称它的未来实现/AXIOM gate已经完成。所得是实际 sourceTail 的局部负层权重上界和**显式局部截断项**的统一几何尾和，不是把远负层真实质量设0；没有生产大k/n远区或完整全负层支配、source全局rategap/Legendre最优性、完整(17)/(19)、LLT、条件Levy、hW/WC/KL或根闭合，也无最弱/最优/新颖性主张。根 A/B/C/D、full17/19、LLT、hW、globalfar 仍 **OPEN**。

本票仅写拥有的新报告；未修改source/scope/receipt/旧票/shared/cache，未spawn/Lean/probe/build/recompile/commit，未下载原始完整日志，未读排队 U17a 或未来 energy/rotation 笔记。最终报告会上传唯一授权的 remote `runs/oq3/u16j-20261021/statement-review.md`，两端另行核SHA后交lead全文阅读。
