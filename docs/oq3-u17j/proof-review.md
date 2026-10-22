# U17j StageLayerSeriesLimit 完整独立证明／来源／实际类型审查

STATUS: CORRECT

## 1. actual 定义与完整公开类型的独立盲译（先行持久化）

已知本单元的声明审查上下文存在；本节重新仅从实际实现提取公开定义完整体及唯一公开定理完整类型。此时未读取当前实现证明体、私有辅助、Audit 类型输出或作者机械材料。先落盘，之后再做来源和证明审查。

```lean
def sourceGaussianLayerWeight (mu : Measure ℝ) (q ell d : ℝ) : ℝ :=
  Real.exp (-ell * d) *
    (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (transverseVariance mu))).real
      {x : ℝ | -((q / 16) * d) ≤ x ^ 2}

theorem normalizedTailCoefficient_stage_subsequence_tendsto
    (w : AtomicIndex → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1)
    (J : ℕ) (q : ℝ) (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂atomicMeasure w) = q)
    (hmeanX : (∫ x : ℝ, x ∂atomicMeasure w) = q / 4)
    (hrange : ∀ᵐ x ∂atomicMeasure w, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < (atomicMeasure w).real
      {stageAtom (fun j : Fin J => addedAtom j.val) i})
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hphase : Tendsto (fun j : ℕ => Int.fract ((m j : ℝ) * q / dyadicMesh J))
      atTop (nhds 0))
    (hcont : ∀ d : ℕ → ℝ,
      (∃ M : ℝ, ∀ n : ℕ, |d n| ≤ M) →
      (∀ᶠ n : ℕ in atTop, ∃ k : ℤ,
        d n + (n : ℝ) * q = dyadicMesh J * (k : ℝ)) →
      ∀ A : Set ℝ,
        (ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (transverseVariance (atomicMeasure w)))) (frontier A) = 0 →
        Tendsto (fun n : ℕ =>
          (normalLayerConditionalLaw (atomicMeasure w) q (q / 4) (d n) n).real A)
          atTop (nhds ((ProbabilityTheory.gaussianReal 0
            (Real.toNNReal (transverseVariance (atomicMeasure w)))).real A))) :
    Summable (fun k : ℤ => sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
        (dyadicMesh J * (k : ℝ))) ∧
      Tendsto (fun j : ℕ => normalizedTailCoefficient sourceEll q w (m j))
        atTop (nhds ((dyadicMesh J / Real.sqrt (normalVariance (atomicMeasure w))) *
          ∑' k : ℤ, sourceGaussianLayerWeight (atomicMeasure w) q sourceEll
            (dyadicMesh J * (k : ℝ))))
```

记 μ=atomicMeasure w，h=dyadicMesh J，S=normalVariance μ，T=transverseVariance μ，Γ=gaussianReal 0 (Real.toNNReal T)。实际定义 F(d) 为 exp(−ell·d) 乘 Γ.real{x:−(q/16)d≤x²}。定义可用于任意实 ell/q/d 和任意 μ；本身并不证明 T>0。T 是方差接口，不是标准差；toNNReal 需要在实际定理前提下另核其正域。

公开定理固定非负原子权重 w 和真实 HasSum w 1，自然数 J、同一 q∈(1,103/100)。同一 μ 的真实 normalValue 均值等于 q、真实 x 均值等于 q/4；μ 几乎处处落在指定 Fin4⊕FinJ 的实际 stageAtom 像，每个该有限索引所指实际单点的 μ.real 质量严格正。它不要求整个无限索引权重全正，也没有按 n/J/子列重新构造模型。

给定 m:ℕ→ℕ，要求 m→∞（不要求单调）。沿该子列的真实相位 fract(m_j q/h)→0；未假定全 n 的相位趋0或精确为0。

额外 hcont 对每个全序列实位移 d 量化：全 n 存在共同有限实界 |d_n|≤M，且最终 d_n+nq=h·某整数，则对每个 Γ(frontier A)=0 的集合 A，实际 normalLayerConditionalLaw μ q (q/4) (d_n) n 的真实实质量趋向 Γ.real A。此类型未另要求 A 可测，hcont 仍是显式前提而非本模块生产的 Levy/弱收敛事实。它不允许未经证明直接把移动集合代入固定连续集极限。

结论的第一分支是实际整数族 k↦F(hk)（ell 固定为 sourceEll）真正 Summable。第二分支是实际 normalizedTailCoefficient sourceEll q w (m_j) 趋向 (h/√S)·Σ'_{k∈ℤ}F(hk)，使用原定义的概率与归一化。必须审查完整 sqrt 常数而非任意重命名 C_n。

k=0 和 J=0 均保留，零层须恰计一次。m 的有限初项可以为0，只有最终 n 正门可由 m→∞ 得到。定义／积分／条件律存在总化语义，证明必须真实消除相关可积／正性门。该结论并不自行证明 hcont、完整19、条件 LLT、一般 KL、hW 或根 A/B/C/D 闭合。

本节 actual 独立盲译已先行持久化；之后追加真实来源、全部证明／辅助／生成类型、最后机械证据。

## 2. 最终独立裁定与绑定范围

STATUS: CORRECT

JUSTIFICATION: 冻结327行实际实现的全部定义、公开／私有证明、局部变换、两个生成项及六个实际类型均已独立核对；真实可和性、计数测度可积、eventual 全层主控、相位／格层、零层与原 C_n 归一化顺序正确。最后读取的机械证据与这些已先完成的数学判断一致，不能反过来作为判断依据。

本报告只绑定 SHA4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d 的 StageLayerSeriesLimit.lean。第1节盲译先行检查点为4568字节／58行，SHA86b089f821c8353f3b2a3d5530eceecc72386e6b1b753ac4ce3b24278eebfbbe；终稿只更新行政状态并追加本节以后内容，第1节 actual 类型／定义／翻译原文未改。

这是一份完整独立实现审查，区别于作者 AUTHOR_KERNEL_AND_AXIOM_CHECKED 状态，也区别于先前293行声明门。hcont 仍明确未由本模块生产；在该显式条件下的原系数全层极限成立，不等于已无条件完成原15/19、Levy、LLT、hW、一般 KL 或根闭合。

## 3. actual 声明与原始来源

actual 源15–18定义及73–101完整公开类型，与冻结 scope57 的 fence 去白空格后逐字匹配；四个 Shao imports、两个 Mathlib imports、namespace/open/scoped 上下文也完全保持。没有加／删／弱化概率、正性、均值、阶段支持、相位或 hcont 假设。

只读 R1 原件 C:/game/shao/current/oq3/proofs/r1/report.md，SHA3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662，19420字节／575行。314–329的15式给固定有限模型的层常数 h/(√(2π)σ)，321–322定义 σ²=S=Var(Y)、τ²=T=det Cov(Y,X)/S；343–344的条件极限生产者仍需 Levy。本模块消费 I 的显式条件接口，未伪造该生产者。

400–409的真实相位、曲边 nqd/16+R_n² 及严格 S_n>0 sign 门，由 H 的实际相位分解和 I 的实际曲边／远 sign 尾层极限承重；不能把源事件换成仅层事件。

411–429的 g_J(d) 在 d≥0为1，在 d<0为 N(0,T) 的双侧平方阈值概率。本实际 DEF 用 Γ.real{x²≥−qd/16}：q>0、T>0 后 d≥0包括0是真全空间概率1；d<0的阈值是 |x|≥√q√(−d)/4，标准化 κ=√q/(4√T)。因此 F(d)=exp(−sourceEll·d)乘真实 g_J(d)，19式输出应是 h/√S·Σ_{ℤ}F(hk)。定义没有把 T 当标准差。

正式 Φ/CDF 重写没有在 J 中证明，不能把这份语义对应当作新增 Phi 定理；20式连续积分、尖点/EM/rotation 比较也不在本模块。sourceEll 始终是真 log(31/30)，不是1/30。

## 4. 第一私有辅助：真实 shift 可和后才有限和≤tsum（20–25）

term_le_shifted_tsum 输入 f:ℕ→ℝ、真实 Summable f、全项非负和 K。22–23先沿单射 k↦K+k 用 Summable.comp_injective 建立 shift 的真 Summable，单射来自 Nat.add_left_cancel。

24–25对这个已可和 shift 用有限集{0}的 sum_le_tsum；补集项的非负由更强的全项 h0 提供。有限和等于 f(K+0)=f K。没有用未可和实 tsum 的默认0，也没有借 ENNReal 的无条件 tsum 单调冒充实数结论。

固定库 InfiniteSum/Group.lean292–296的 to_additive 生成 Summable.comp_injective，真实要求原族可和和索引单射。InfiniteSum/Order.lean121–125的 to_additive 生成 Summable.sum_le_tsum，真实要求可和和有限集外项非负。本辅助实际消费全部门。

## 5. 第二私有辅助：先极限可和／真 count-Integrable，再 DCT（27–71）

nonnegative_tsum_tendsto 是一般实数列工具，不包含 μ、q、阶段或高斯特例。F_j、极限 L、共同主控 b 都保留完整量词：所有 j 的真实 Summable(F j)，eventual j 后对全部 k 同时成立的上界，及每个固定 k 的真实 Tendsto。

35–39先由真实闭序极限得到 L(k)≥0 和 L(k)≤b(k)。hL0 用全 j 的 F≥0；hLb 用同一个 eventual 全 k 界取固定 k 的最终界。Nat atTop 是 NeBot，所用 le_of_tendsto / le_of_tendsto_of_tendsto 的门成立。

40用实际 Summable.of_nonneg_of_le，从 b 真可和和上述非负比较证明 L 真可和。这在任何积分或 DCT 之前完成，未从总化积分返回值倒推可和性。

41–59分别建立每个 F_j、L 和 b 对显式 (Measure.count:Measure ℕ) 的真实 Integrable。每次先证明范数函数外延等于原非负实函数，再用 integrable_count_iff 的“范数族 Summable”方向。L 的可积来自刚证明的 hLs，b 来自 hbs，F_j 来自 hFs；没有以有限概率空间的常数可积误用于无限计数测度。

60–65实际调用过滤器版 tendsto_integral_filter_of_dominated_convergence，四门均真实：hFi.aestronglyMeasurable 给 eventual 可测；hbound 给 eventual j 后全部 k 的范数界，ae_of_all 转 count-AE；hbi 给主控 Integrable；每个 k 的 hlim 经 ae_of_all 给 AE 点态 Tendsto。该版本容许 eventual 界，正确保留早期未满足同界的真函数。没有用逐 k 的不同 j 截断来伪造共同主控。

66–69在各自真 Integrable 之后调用 Countable 型 integral_countable；计数测度单点实质量1，再化成真实无限实级数。不是只对 Fintype 适用的 integral_fintype。70–71返回已证 hLs 和真实积分极限化成的 tsum 极限。

这两个辅助都非递归，无隐藏状态、未审私有定义或独立选择的概率模型。

## 6. 真实 μ、正性、相位与实际两列（102–147）

102–103固定 μ=atomicMeasure w，并以真实公开 atomicMeasure_isProbabilityMeasure w hw hs 建立概率实例。HasSum w 1 是真级数条件；不要求无限索引全正。

104–105 h=((2:ℝ)^J)⁻¹>0，J0仍成立。106–111逐项把真实 stageAE 的 inl 映射 fixedAtom(inl i)、inr 映射 fixedAtom(inr j.val)，用真实 fixedAtom_bounds 上界得到同 μ 的 AE |X|≤4+√10。112用 hpos(inl i) 得四个实际基点单点质量正。

113–114调用一般 μ 的 normalVariance_pos、parabolaCovariance_det_pos，不是套仅 atomic 专用的 variance 公式。115–119定义 C=(h/(2π))√(2π/S)，以 h>0、pi>0、S>0 真证 C>0；后续提取 C⁻¹ 都有非零门。T>0及真正高斯非退化在被消费的 I 中由同 μ/hb/hbase 的一般 API 建立；J 没有把 toNNReal 总化当成正性证明。

121–123 θ_n=fract(nq/h) 始终在[0,1)⊆Icc0 1。124–128先由 h≠0 和真实 floor_add_fract 建立 h·floor(nq/h)+hθ_n=nq；没有从相位极限推出伪整数恒等式。

129–136 P_n 是 sourcePositiveNormalLayerTerm、N_n 是无 if 的 negativeNormalLayerTerm，两者都使用同一实际 μ 的 n 重产品及 θ_n。H 的真实公开分解直接给全部 n 的 P_n/N_n 各自真 Summable，包括早期和 n0；137–142逐因子给全项非负。

143–147 P_n≤rawP_n 的事件方向是“真实 sourceTail 交层 ⊆ 原始层”。product μ 真概率使上事件 ENNReal 质量不为∞；measureReal_mono 显式消费 measure_ne_top 后乘 √n·exp≥0。没有把交层与原始层声明为相等，也没有对上层质量的 toReal 使用无有限门单调。

## 7. 两侧共同几何主控在全 k 外（148–187）

148–149 U16b 的实际公开接口消费同 μ/J/q、a=q/4、sourceEll_pos、真实 hb/EY/EX/S/det/stageAE/单点pos；给 Cp>0 和先于全部 θ/K/k 的最终 n 门。150–152 G 的实际公开接口消费同 μ/J/q∈(1,1.03)、真实均值、stageAE/hpos，给 gamma>0、Cn>0和同样量词顺序的真负尾门。未默加 H/energy/variance/gap 前提。

153–160 rp=exp(−sourceEll h)、rn=exp(−gamma h) 真实都在(0,1)：下界由实 exp 正性，上界由对应严格正乘积及 exp_lt_one。161–170 bp(k)=Cp/(1−rp)·rp^k、bn(k)=Cn/(1−rn)·rn^k；两分母严格正，原值非负，且先用真实 abs<1 几何级数再乘常数，证明两主控真 Summable。

171–181通过 hm.eventually hptail 把统一 n 门沿 m 拉回，j 门仍在 intro k 之前。对该 j 的实际 θ 使用 ht，rawP 的真 Summable 和非负性先由 U16b 给，再由第一辅助将 rawP(k) 控于其 shift tsum；接真实 K=k 尾界，最后纯实 ring 把 Cp·rp^k/(1−rp)改写成 bp(k)。P≤rawP 的有限概率门已先建立。

182–187同样将 G 的统一 n 门沿 m 拉回后对全部 k，使用真实 N 原序列可和、N≥0和第一辅助的真实 shift 可和，再接 K=k 尾界得到 bn(k)。没有用局部截断序列的 if=false 假零，也没有对所有早期 j 强行加同一上界。

本段由已有全部 n 可和性和最终共同几何界分别承担不同义务，未相互循环。θ0/1、k0/K0、off-grid 或零质量层都由真实概率和原 API 保留。

## 8. 每个固定层的真全 n 门和仅沿 m 的相位极限（188–257）

正列190定义 d_n=h(k+1−θ_n)。191–199以 h>0、k≥0、0≤θ_n≤1，先 d_n≥0，再证 |d_n|≤h(k+1) 的全 n 共同有限界。没有把仅沿 m 的有界性误作 hcont 所需全序列界。

200–209给对所有 n 成立的整数见证 floor(nq/h)+(k:ℤ)+1，完整 cast 变换后由 hfloor 精确推出 d_n+nq=h·见证。210–214仅沿 hphase 得 d_{m_j}→h(k+1)；不声称 d_n 全 n 收敛。

215–222以 q>1⇒q>0、同一 μ/J/均值/stageAE/hpos、真实 d/hd/hgrid、m/hm/hdlim，实例化 I 的实际公开 weighted-layer 极限，并且显式消费 hcont d hd hgrid。源函数与 P 的定义 rfl，极限端只以结合律/ring重排同一个 C、exp 和高斯质量，没有改变阈值符号或系数。

负列225定义 d_n=−h(k+θ_n)。226–233先 h(k+θ_n)≥0、abs_neg，再证同一个形式的全 n 界 h(k+1)。234–243整数见证 floor(nq/h)−(k:ℤ)，用 hfloor 得真实负格层相容。244–248沿 hphase 得 d_{m_j}→−hk。

249–257再次消费相同实际 I/hcont。253–254逐函数外延核对 N 的正权 exp(+ell·h(k+θ)) 恰等于 exp(−ell·d_n)，没有把负层权重符号翻反；目标端同一个 C·W(−hk) 经纯结合律重排。

I 的继承语义已按绑定的真实 public type 核对：它的层事件是 M=d 且 sourceTail，原概率是同 μ 的真实 n 重积；移动平方阈值和严格 sign 条件经先产品AE energy>0/正sqrt、actual cond-map/finiteness、固定连续集夹逼和固定 K 后远 sign 尾处理。它仅要求 d 全 n 有界、eventual格层、d沿m趋常数和显式 hcont，并不要求全 n d 趋常数。最终层质量正及层常数由独立 s0 层渐近承重，非循环使用 hcont。

J 没有重做或扩大 I 的结论，也没有将其显式未证的 hcont 当已证 Levy。非正列 k0 的 d0=0 已由 I 的实际无原子平方阈值边界处理，真实极限 W(0)=1。

## 9. 真极限可和、整数零层一次与 C_n 收尾（258–324）

258–263两次调用第二私有辅助，全部参数对应已证明的全 j 非负／真可和、共同非负／真可和主控、eventual 全 k 界和逐层真实极限。返回的两个极限列 C·W(h(k+1))、C·W(−hk) 的真 Summable 在 DCT 中已经先行证明。

264–267才乘 C⁻¹，且 inv_mul_cancel₀ 的非零来自 hC>0，得到两个 W 列真 Summable。268–276 f(z)=W(h·z)，正列从 k+1 开始，负列先含0；负列沿 k↦k+1 的单射给严格负列的真 Summable。Nat.add_right_cancel 对该 shift 真实成立。

277以真实正偏移列和严格负偏移列，调用 NatInt 的 Summable.of_add_one_of_neg_add_one，给整个 ℤ 索引的真正 hfs。278的 tsum API 含一个 f0；279–281用负列真 hfn.tsum_eq_zero_add 拆成 f0+严格负列。282–290把两个自然数列的 tsum 重排成整数 tsum 时，零层恰一次。

实际有限 n 的正列首项 d=h(1−θ)>0，负列首项 d=−hθ≤0；当 θ=0 零层只在负列 k0。极限也是正+h,+2h,…与非正0,−h,−2h,…，未在两列中各放一份0。整数类型重排在真正可和性之后完成，没有靠实 tsum 对不可和族的默认0取等式。

291–297由两条真实 tsum 极限相加，使用已经证明的 hWp/hWn 的 tsum_mul_left 提取 C；只做标量和结合律。298–312接真实原归一化系数：先 normalizedTailCoefficient_eq_tilted，展开同 w 的 tiltedTailCoefficient；sourceTail_measurable 后 integral_indicator 成为真实 setIntegral；sqrt_mul 的 2π≥0 门明确，最后消费同 μ 的 H 实际积分分解。

原 normalizedTailCoefficient 是 √(2πn)·exp(n·saddleRate ell q w)乘 originalMeasure ell w 的真实 n 重概率；此处绝非凭定义重命名 P_n+N_n。U9b 的已完整验收真实换测度接口以同 w≥0/HasSum1承重，包含真实 inverse normalizer>0、产品积分／概率与自身 rate；没有偷换 law 或假定两个不同 rate 相等。

313–319的 hnorm 先用实 sqrt_div（分子 2π非负），ring 只重排实分式，再用 sqrt(2π)²=2π 与 2π≠0，得 √(2π)·C=h/√S。S>0 早已建立并用于 C>0；全链无非法 √n 约分。hcoef 对 n0 也是真恒等式；只有 I 继承的正 n 门由 m→∞ 最终提供，有限初项不改定义。

320返回 hfs，321–324将 htotal乘固定 √(2π)、以全 n 的 hcoef 作 eventual同函数替换，再 hnorm/hreindex 化成冻结完整目标。没有多余条件、未处理的剩余概率项或隐含选择另一条 m。

## 10. 全部六个实际 owned DECL／完整 TYPE 已读

先完成上面的所有 source/private/local/API 数学审查，再从真实远端 Audit.log 只选择 DECL/TYPE及全部续行阅读；此时未读取 AXIOMS、计数／PASS、receipt 或 build。不是从摘要猜生成项。

1. Shao.OQ3.sourceGaussianLayerWeight：实际 TYPE 为 MeasureTheory.Measure ℝ → ℝ → ℝ → ℝ → ℝ，四个参数顺序 μ/q/ell/d 与第1节完整定义体一致；定义体亦已完整审查，未只看类型。

2. Shao.OQ3.normalizedTailCoefficient_stage_subsequence_tendsto：真实展开的全长 TYPE 从 w、hw、HasSum、J/q区间、EY/EX、stageAE/单点pos、m/hm/hphase 到全序列 hcont，最终是整数 Summable ∧ 实际 normalizedTailCoefficient 子列 Tendsto。已逐续行对照第1节完整类型；没有隐藏实例、追加假设或换成总化 tsum 的弱目标。

3. _private.Shao.OQ3.StageLayerSeriesLimit.0.Shao.OQ3.term_le_shifted_tsum，完整 TYPE：

```lean
∀ (f : ℕ → ℝ), Summable f → (∀ (k : ℕ), 0 ≤ f k) →
  ∀ (K : ℕ), f K ≤ ∑' (k : ℕ), f (K + k)
```

4. _private.Shao.OQ3.StageLayerSeriesLimit.0.Shao.OQ3.nonnegative_tsum_tendsto，完整 TYPE：

```lean
∀ (F : ℕ → ℕ → ℝ) (L b : ℕ → ℝ),
  (∀ (j k : ℕ), 0 ≤ F j k) →
  (∀ (j : ℕ), Summable (F j)) →
  (∀ (k : ℕ), 0 ≤ b k) →
  Summable b →
  (∀ᶠ (j : ℕ) in Filter.atTop, ∀ (k : ℕ), F j k ≤ b k) →
  (∀ (k : ℕ), Filter.Tendsto (fun j => F j k) Filter.atTop (nhds (L k))) →
  Summable L ∧ Filter.Tendsto (fun j => ∑' (k : ℕ), F j k)
    Filter.atTop (nhds (∑' (k : ℕ), L k))
```

5. Shao.OQ3.sourceGaussianLayerWeight._proof_1，完整 TYPE：

```lean
(15 + 1).AtLeastTwo
```

这是数词16的 Nat.AtLeastTwo 条件，实际 Mathlib/Data/Nat/Init.lean425–431定义的唯一字段 prop:2≤n；对应实际 DEF 分母16数词所需实例。该生成项是2≤16的有限算术义务，不承重概率或方差假设。它属于 Mathlib 的 Nat 定义，不把未找到的 Lean core 路径当证据。

6. Shao.OQ3.normalizedTailCoefficient_stage_subsequence_tendsto._simp_1_2，完整 TYPE：

```lean
∀ {G : Type u_1} [inst : Semigroup G] (a b c : G),
  a * (b * c) = a * b * c
```

这是一条一般半群乘法结合律反向的生成简化辅助；它没有 μ/q/C、除法、概率或正性门。全部语义是结合律，不是额外极限结果。

源中 authored 恰1公开DEF、1公开theorem、2 private theorem；其余源只有 imports/namespace/open/noncomputable、已逐项读取的局部证明，无其它顶层 axiom/opaque/结构/定义。实际输出的两个额外生成项上面逐项确认；总6 owned=1DEF+5theorem，非按预期数量猜漏项。

## 11. 固定原库语义及公开可达

实际读取的主 API 不依赖缺失 Tannery 或未来 Levy/Portmanteau：

- OrderClosed.lean133–140、469–471的实闭序极限要求 NeBot；Nat atTop满足，输入分别为全项非负及 eventual 上界。
- InfiniteSum/Group.lean292–296 / Order.lean121–125 的生成 additive API 分别保留真 Summable 和 shift 单射／有限集外非负门；第一私有辅助在消费前已满足。
- InfiniteSum/ENNReal.lean531–537 的实 Summable.of_nonneg_of_le 保留上界族真可和门；不是 ENNReal 无条件可和实例。
- Function/L1Space/Integrable.lean748–773 的 integrable_count_iff 是范数族可和；非负实族的 norm equality 在源中逐个外延证明。
- Integral/Bochner/SumMeasure.lean177–184 的 integral_countable 要 Countable、CompleteSpace、MeasurableSingletonClass 和真 Integrable；ℕ/ℝ/count 的真实实例均匹配。
- Integral/DominatedConvergence.lean67–75 的 filter 版本具有可数生成过滤器及 eventual measurable/bound 两门；与源中所有局部假设精确一致，未误用要求所有 n 同界的序列版。
- InfiniteSum/NatInt.lean238–240、449–465 的 additive API 分别拆真可和负列零项及在正／严格负偏移列间明确增加一次 f0。
- Algebra/Order/Floor/Ring.lean310–316、437–446 提供 floor_add_fract 与 fract 的真[0,1)范围；Real/Sqrt.lean364–382 的实 sqrt_mul/div 具有明确非负分子门。

独立重新沿实际 imports 递归，并区分 module/public import 与旧非 module 导出；主要 count、DCT、整数求和、非负比较、实 sqrt、Nat.AtLeastTwo 全部在现有公开导入图可达。没有临时加导入、改实例、复制公共字符函数源或新增缓存。

## 12. 最后才核机械收据、真实产物、pins 与51前置

完成全部327行 source／局部／私有／六actual TYPE数学判断之后，才读取本地及远端作者 receipt、实际 Audit.lean、AXIOMS/PASS、既有 build 日志的哈希与尺寸、前置清单与 pins。作者路线文字仅是收据中的历史叙述，未替代独立证明审查。

本地draft、远端worktree、远端run source快照三端 SHA256 均为4c797f9f5f9b47c0f62764c0b62396b9679172782d144fca29a091b83a52e02d，16484字节／327行。scope 两端SHA5c518f0c60e229eba71b44c480ef03fdc31867cdaa77ef59cb6276ac061d73b0，6648字节／58行；已接受 statement-review 两端SHA2e44c055464df048ad7a93884270176f292d36c8f1b53d2115438258929c3563，29999字节／293行。原件 R1 hash 同第3节。

本地 U17j-receipt.json 与run receipt.json均SHA2f273913598bf5276a9bc147a766483a2d2f61f8c6d8cc0136f186775cc86c6d，11016字节／138行。历史 status 是 AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW，不能改称当时已独立终审。其 nonclaims 正确标明 J 当时无commit/PR且 hcont 等未完成。

本地 U17j-Audit.lean 与run Audit.lean均SHAeff958159d4905017d27176e33ce78b0e61fa9d74af07ad67ec60c68a2d4c315，1720字节／39行；实际脚本检查1个冻结theorem、1个DEF，枚举两个公开stem及整个本模块private前缀，对每项 Lean.collectAxioms 并拒绝新axiom和非白名单依赖。其覆盖与独立读到的全部authored／生成项一致。

实际 Audit.log SHA f1d7d4db260d868c1f01be139707ec6b138fe900d5fb45a9e23a9c57ae457dae，4470字节／72行。末阶段实际核到：FROZEN_DEFINITIONS1、FROZEN_THEOREMS1、ALL_THEOREMS5、ALL_DECLARATIONS6、AXIOM_GATE PASS。

公理结果逐项为：公开目标、公开DEF、两个私有辅助均只含 propext/Classical.choice/Quot.sound；数词 AtLeastTwo 生成项只含 propext；一般半群结合律生成项为空。全部传递依赖在标准白名单内；不存在新增公理或未覆盖的 authored 声明。

实际既有日志（只读尺寸／hash，无完整原始日志复制）：

- build-01.log 空0字节，SHAe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855；作者记录为0exit，但它只覆盖DEF+两private的partial source，不含完整公开目标。
- build-02.log SHA c1e8886fb10f5669ad44621ca4ed7d72db4aa9c17c84fc59d6ea103ce4feb774，6789字节／131行；作者记录 changed complete source exit1。
- build-03.log SHA834d4b9cac40c3afb95f1c662f74df2d6bac20593abcdb3e1f977696352a46a8，17772字节／430行；作者记录另一 changed complete source exit1。
- build-04.log 空0字节，SHAe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855；作者记录首个完整冻结327行source成功exit0。当前 olean 实际存在，首Audit记录exit0。

空日志本身不能推断退出码；退出码与partial／complete历史归属于绑定的作者执行收据。01不是失败，也不是完整模块验收；02/03后的源有改动。未宣称未改成功source或Audit被重复运行，审查者没有重跑。

作者记录目标命令是 taskset -c 14-17 lake env lean -M8192 -j4 -DautoImplicit=false -o .lake/build/lib/lean/Shao/OQ3/StageLayerSeriesLimit.olean Shao/OQ3/StageLayerSeriesLimit.lean，Audit同native限额与autoImplicit设置。这只是历史证据，非本审查再执行的命令。

真实导入闭包51份Shao、2905份Mathlib源码和现成olean全部齐（另有本目标olean）。剥嵌套注释／行注释／字符串后按真实import边枚举，未把注释示例当依赖。实际51源哈希与独立已接受I的45前置加本次六真实模块对照完全一致，再与作者run清单及receipt清单分别对照 missing0/extra0/hashdiff0。

本地 u17j-prerequisite-hashes.json 与run prerequisite-hashes.json SHA a2f27bf1b3ae49bbc0b3dff9fd65b2ea3c623dea62aeadbb7c5bbda88ec82359，5474字节／53行；全部51源路径→hash按键排序紧凑JSON指纹03b7e9377ac41e72e5de6a21555497210286812247577ca873484cef07589f06。以下完整清单绑定独立实际检查，不把收据复制当依赖验证。

```text
Shao/Basic/FinitePath.lean 898262898f9c088e2d10e6238e411b4397387b21b1b71a2b545c5edef936e1bb
Shao/OQ3/AtomProjection.lean 0d369052c7f87122765612efdeaca5d9ac71abca861e7785c86d1f9edcc74d22
Shao/OQ3/AtomicMeasure.lean 59ddc48fb7b395f362939e58cbd9d7911685a6ed6e6574142e8a6d4ab3ee0c39
Shao/OQ3/AtomicProductControl.lean 6f886635f2201e04d1004a4f4b3b4058d406be3a283f716b70f1ce1cfaa5775f
Shao/OQ3/AtomicTailControl.lean ec528d9af8b475f1db8a78c93ab917d754365d280027a86be2823825b19c2f79
Shao/OQ3/BinaryEntropyBounds.lean 291cc2afc5e632ad8326b5d98ceb619b959a41bc8d49120d2a52bd1a0b213228
Shao/OQ3/CenteredLogMGF.lean 1fb9f7b4ca976c02f5f100161da811738a443d75c47c72c2e274de54d9fb90f4
Shao/OQ3/CenteredSampleTilt.lean d042af2e3ab2f38bb94b67dc53d28d335c1370fcecd8100e93a067d9ba067501
Shao/OQ3/CentralFourierIntegral.lean 4999d8148c1ee1ba50f61d6d19c40aed239cd001d76ee71f133d1a064c668a93
Shao/OQ3/CharacteristicMeasureDomination.lean ec7032919bd8d825bb8746da15e84b29c5cb59ef97858367e4d73fdf52aa9bbb
Shao/OQ3/CompactTiltDomination.lean 6f31ac2e3b2b9d9b2ef957ebe52cfe3664a86694bb396b09c1006b890cbd0623
Shao/OQ3/CompactTiltLayerMassBound.lean 5602fd17ebac0fe40fb789067cea6b9553659dad4c8965ff88aea7e106ef5cc7
Shao/OQ3/EnergyBernoulliMGF.lean e3bb038b2b92fac9a5341b26d437eeba046a5fd954a753fe80a7058ce32432ad
Shao/OQ3/FarEnergyExponentialCover.lean 40ee1824e49f2bf38e653edfa38363774e27a7d58c3c9e1c2b97245cfc86803d
Shao/OQ3/FiniteConstraints.lean 800d9db8cb6749a31ecfe611409de92b10ea8bb2aef955bfd825ede7324f0ef0
Shao/OQ3/FiniteFarArc.lean 3a0b05d0789e53320009a44499c9c40d0fb3d892427085052c65c04456b6cf71
Shao/OQ3/FiniteNormalSpan.lean 0374da4860edf8af8bbbb9172e4e93bfe9b6c37ac57672b85a4f58392475b7de
Shao/OQ3/FiniteStageMeasure.lean 1a32fb904e6ee9d2b0b48d92c4ebb3568452bb02500ce52a1a03eb01ae0256b1
Shao/OQ3/FundamentalFourierAsymptotic.lean aab18e9f073a18a87d42f0edd3e37a95da58cacf5b9635e4a64c887d340765b1
Shao/OQ3/GlobalNegativeLayerBound.lean 57b61e6e3bfd184586083e55633a563e4176cbfcf16def62a7d860d92b5c01d8
Shao/OQ3/InverseTilt.lean c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811
Shao/OQ3/JointNonlattice.lean 51ce939232610353215fc3b7377e19b894451a9a108125e1828bf2fe8ec81559
Shao/OQ3/LocalNegativeLayerControl.lean e94a5a8e82d2a69a946a12e16f3fb2a58b174fb036becce5632d7c600b796f01
Shao/OQ3/LocalNegativeLayerTail.lean 049361c77716896922fb1d7cd3e6abf84515b76a99103c597d8d74b63a2f1856
Shao/OQ3/LocalRateMargin.lean 5e0e4f9ebb0dc514e0b55b9ed3aa7e5a9e8b9c128fdda2edfd2257bc3ad70a77
Shao/OQ3/NegativeLayerGeometricTail.lean 8077cfb97547c4a8c5b22da6ed17a58168a6ca1f6b2654f6799292a06a8b23f4
Shao/OQ3/NormalLayerConditionalLaw.lean 94e2507a83dfc232280043567f6a2f07950d39da10b45699777ac1316f24281a
Shao/OQ3/NormalLayerFourier.lean 063b6c5ce50e6c5ee33b53301cdfcd36a63a4ea06f9c3de729756513ca736fa3
Shao/OQ3/NormalLayerMassBound.lean 66ff4f217b57b319abb19ea7982e467e934219fadc2574a3487087e030a9e4f1
Shao/OQ3/NormalTangentDomination.lean b65b9f5a9d67e42e611a3841563ac07004e796415c3e5b74f177a8ca80e48e90
Shao/OQ3/NormalTangentGaussian.lean d2c55bf4d7a371c9b43cd3c75eab8ece8b3c7caa21aa4827bf19c24b4c7cac39
Shao/OQ3/NormalTangentMoments.lean 8cee48bc8f519f72b218a2ef80685d946a6debaea8b723af38a49c5bdca12cc1
Shao/OQ3/NormalTangentPowerLimit.lean 819bd0e801eb0b9adce0fbdbcd6ced6441b04787eb0501b811721933db0e9457
Shao/OQ3/NormalTrialCost.lean 8fb184ac4cf75e4f1c64e615b5c94c1a5f16c39109709a8f5dbc7fe2c5406895
Shao/OQ3/PositiveLayerTail.lean ebcef2d9ada2df9973a16ab8f1c9806c304dbaf1d01731c9de5ffcfd9d12172a
Shao/OQ3/PositiveRate.lean 8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b
Shao/OQ3/ProductMeasureDomination.lean 9f05af79e47b9f778cbce7a0d19c0addea6d457eab5f088a69bf372f660c5a3f
Shao/OQ3/RegularCovariance.lean 0add3476cc949edc593e15dc195934a6df78a41a55f4a2281f66095733d4c853
Shao/OQ3/ResonanceArithmetic.lean cd21a264d637bab30fed765bdc25ed09bb4ff56f6efb9c88ee09be4ca6e1648b
Shao/OQ3/SampleBoundary.lean 7660e23b71ce28ab43a4ad1d8df1862cf8a507b6bb9b41255e961f0bee0b93e2
Shao/OQ3/SampleChangeOfMeasure.lean d6259e330afca7b95e2e206c7021a44836e32cc0add596d14a6af8bdbda25134
Shao/OQ3/SourceBinaryEntropyGap.lean f5696cc1c953b3079f0c2987a239b3d0c0003292bb3018052c80d4f1fa9254c9
Shao/OQ3/SourceEnergyGeometry.lean 3cad1d1f12583690a6acbffc749110ace2b2786831f706049583cb755ac2253a
Shao/OQ3/SourceFarWeightedTail.lean c9e4c14af297353c5358da6d3e75d72f712649e535102ba18297fc00a0e5261f
Shao/OQ3/SourceStarter.lean 0e2a081619976f88149707c2ef9311dc909003e61d3d0f7c4e21e6c3dbbc5a6d
Shao/OQ3/StageCurvedLayerLimit.lean 71c85b128101af074034f454f40d25405b6898624989d464a69a73cc19db4d60
Shao/OQ3/StageLayerDecomposition.lean b6204bbbc39d029e221e473c76e8ebe34a42cf4765f4c3f7ccbd657d6311a8de
Shao/OQ3/StageSourceNegativeTail.lean 8b2e2eee60a9725e02653b58741cd63ba497fd5e5c5baaa0dca228fbda3ea8a0
Shao/OQ3/SummableAtoms.lean 0ea4c64fe9ef9b45fbf44d24312771a1dbfbcc5de8448564e3e87bdf17c7178b
Shao/OQ3/TiltedMeasureDomination.lean 5445a68da1ac8302f174bfe2144eb8271a0af740fd6b91a87355abb41fed739b
Shao/Probability/FiniteIID.lean d1b565489199d55af70a27c31a0f803a2b7433e78c9197a361b3c10c0598845b
```

实际库主API hash（Mathlib/ 相对路径）：

```text
MeasureTheory/Function/L1Space/Integrable.lean d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759
MeasureTheory/Integral/Bochner/SumMeasure.lean b4f63c8acdd8f1c15e4762497def59cf9073063759726a113121fd219a53098a
MeasureTheory/Integral/DominatedConvergence.lean 56394aacfe591230d26a1d93641f2a1d3e3a3eae4fcfe772775533a1da295833
Topology/Algebra/InfiniteSum/NatInt.lean 4dc1dffbdb6a0b0157e8810b20dfc0051bedf7f449b6d1fa5b8a9a47fa47f645
Topology/Algebra/InfiniteSum/ENNReal.lean 88ef56c969006630d0066b7af2c74e75dd060608f3c42f0ef288ad1c6da908cc
Topology/Algebra/InfiniteSum/Group.lean 6d99451dd1de79a2b1a6770a530e3fcd07c2c24379dd2ed266992b5ec5475f6c
Topology/Algebra/InfiniteSum/Order.lean 526aed3d15913b1d7ad9de9f28fc26ac9ab023942b0d80cbc72323a293817b01
Topology/Order/OrderClosed.lean 011a07d8a57515c2a6bf066bf4ef24ff22eeffcc4d6115afd9ff22f5d45ded9e
Data/Nat/Init.lean 806975436869c67d4bd0dddfa042b8eaac3d7309d90a4d6b03d33d7ab5a7edfa
Analysis/Real/Sqrt.lean 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204
```

实际 lean-toolchain SHA d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4，29字节／1行，固定leanprover/lean4:v4.36.0-rc1；lake-manifest.json SHA40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e，3541字节／117行；Mathlib实际HEAD807d3836b165983210ee2ecf3cd28f239436949c。

只读观察branch feat/oq3-stage-layer-series-limit，HEAD f1bf508003475318e1c4019323b54758d421753e，git status只含 ?? Shao/OQ3/StageLayerSeriesLimit.lean。源码实际LF无CR／无尾空白，禁止项sorry/admit/axiom/unsafe/native_decide/implemented_by/opaque扫描0命中。没有以branch前移替代冻结hash绑定。

## 13. 风险、非声明与最终结果

未发现需要作者修复的数学、来源、实际类型、积分总化、系数、零层或机械绑定缺口。严格保留的边界是结论本身的显式 hcont：它尚未由U18a生产，故不得称原模型无条件15/19、条件Levy、全LLT或根闭合。Phi/CDF正式等价、cusp/EM、rotation、hW、一般KL、全局最优／新颖性和根 A/B/C/D 全部 OPEN。

本审查没有运行Lean/#check/probe/build/rebuild、没有下载完整原始日志或写缓存、没有spawn/commit、没有修改source/scope/receipt/旧票/shared或撤回他人修改。所有远端实际项目命令均 taskset -c 14-17 的只读操作；未用ulimit-v，未触外部CPU0–9/80GiB任务或全局资源。唯一写入是本新票及其授权run副本。

FINAL STATUS: CORRECT
FINAL JUSTIFICATION: 全部实际327行和六owned类型在真实标准库及冻结前置语义下成立。真shift可和先于单项≤tsum，真极限可和/count-Integrable先于eventual统一DCT，实际P≤rawP有限概率、全n有界/精确整数格层、仅沿m相位极限、零层一次和原C_n的√(2π)常数全部逐步核对；机械证据最后完成绑定且与独立结论一致。批准该冻结实现发布，hcont及所有原根未闭义务保持OPEN。
