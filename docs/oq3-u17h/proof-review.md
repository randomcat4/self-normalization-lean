# U17h StageLayerDecomposition 完整独立证明审查

STATUS: CORRECT

## 1. 实际公开定义和完整类型独立盲译（先持久化）

承认已有独立声明审查的历史上下文；本轮仍从实际实现重新提取完整定义体与完整目标，在读取本轮实现证明、scope解释、作者receipt或机械证据之前独立翻译。下列文本是实际源，而非以冻结声明替代实现。

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

定义独立翻译：对任意实数轴测度 μ、实数 q/ell/h/θ、自然数 n/k，新正层项为 sqrt(n)·exp(−ell·h·(k+1−θ))，再乘同一真实 n 重乘积测度 μ^n 对 {normalDeviation q=h(k+1−θ)}∩sourceTail q n 的实质量。定义没有 if、条件概率归一化、局部截断或额外正性守卫。

目标独立翻译：固定同一个实数轴概率 μ、有限阶段 J 和任意实 q、ell，只假设 μ 几乎处处支撑在实际四基点加前 J 个新增点的阶段像中。对每个自然数 n，取实际相位 θ=Int.fract(nq/dyadicMesh J)。真实正层项与已有真实负层项两条序列分别真正可和；sqrt(n) 乘真实 sourceTail 上 exp(−ell·normalDeviation q) 的限制积分，精确等于它们两条实数 tsum 之和。

量词与门：μ/J/q/ell 在全部 n 外固定，没有均值、q或ell符号、方差、正单点或严格gap前提。θ由真实分数部分确定，必须真实满足0≤θ<1并与 nq/h 相容。每个固定n的可和与恒等式不等于全n共同尾估计；n=0/J=0、负q/ell及空层均保留。

实际证明必须核真产品AE格点、两方向互斥覆盖、θ=0零层仅一次、任意ell真可积和可数Bochner分解的所有门，不能以总化积分/tsum或单侧ell≥0界代替。这一阶段仅记录实际类型含义，尚未判定实现或机械凭据。

## 2. 冻结声明与真实来源

实际完整 DEF/type 的盲译已先持久化为40行/3011字节，阶段 SHA256=290fff437da3234a0320bc2ca80ea62c83bff74df0f364f683c6be4614fa7fb0；随后才读 scope55、R1 和本轮实现。已有声明票是历史上下文，不替代本轮226行实际证明审查。

R1 396–403 的实际 stage 法向格距与 θ={nq/h_J} 给本模块的源格点对象；400–429 的正负层权重和原(19)需要先有真实层表示。本实现证明的是 sqrt(n) 乘 sourceTail 上指数权重的精确限制积分分解，不声称原(19)极限已完成。原文408–409的 sign-tail、421–426条件极限/级数极限没有被此恒等式自动证明。

新 DEF（实际13–18）使用真实 sourceTail 交正层质量，而不是 U16b 的 raw positive 层质量；负项沿用 F 的真实 sourceTail 交负层 DEF。不存在条件概率分母、额外 h/σ 归一化、局部 if 或删除大层的守卫。μ、q、ell、n 和实际相位在两侧完全相同。

本公开类型只给 μ 真概率与阶段 AE 范围，q/ell 任意；不增均值/正原子/方差/gap 前提，也未提供按J/n重选源参数的存在量词。实际固定n可和性和精确分解不等于对n共同几何尾、条件 Lévy、移动阈值/sign-tail、完整19或任何根闭合。

## 3. 全226行实际证明、全部 locals 和承重语义

已逐行读取实际1–226。1–4是冻结四个imports，6–11为namespace/open/noncomputable；13–18是唯一公开定义，20–34是唯一公开完整目标，35–223为完整证明，225–226结束作用域。实际源无 authored private；实际生成枚举在类型阶段另核，不能从源码表面猜测。

### 3.1 实际对象、正格距与产品 AE（35–54）

35–45 在 intro n 后固定 ν=Measure.pi(fun _:Fin n=>μ)、h=dyadicMesh J、θ=fract(nq/h)、f=sqrt(n)·exp(−ell M_n)，及实际 P_k、N_k 交 sourceTail 事件。这里的 ν 由原 μ 的真实 Fin n 产品定义，概率实例可化简 let ν 后由每坐标概率取得；不是总化tilt或替代测度。

46 给 h=((2:ℝ)^J)⁻¹>0，所有J包括0均成立。47–48 消费真正 FloorRing ℝ 下的 fract_nonneg、fract_lt_one，得0≤θ<1；没有把θ当任意[0,1]中的参数。

49–54 对每个i:Fin n用 Measure.tendsto_eval_ae_ae.eventually hrange，再通过 ae_all_iff 合并，得同一ν-AE的全部坐标阶段支持。Fin n可数有限，μ概率保证坐标SigmaFinite；这不是把μ-AE直接当全部path点态支持。n=0时∀i:Fin0为空，步骤照常合法。

### 3.2 真正双侧法向界与任意 ell 可积（55–96）

55–65的local hY从真实stage range见证取i，inl基点映到fixedAtom(Sum.inl i)，inr j映到fixedAtom(Sum.inr j.val)。已接受公开 fixedAtom_normalValue_lower 对这些真实点给Y≥−9。上界用 normalValue=8x−x²=16−(x−4)²≤16，由实际平方非负性给出。因此|Y|≤16，不是由单侧Y下界偷换绝对值界。

66–80从hcoords逐坐标使用hY，Finset.abs_sum_le_sum_abs及有限和单调先得|∑Y|≤16n；再用真实绝对值三角不等式、|nq|=n|q|（n≥0），得ν-AE |M_n|≤(16+|q|)n。没有对q施加符号条件。

81–83证明实际M_n的连续性：normalDeviation是有限normalValue坐标多项式之和减nq。84–95在真正有限概率ν上调用Integrable.of_bound，连续exp给AEStronglyMeasurable，实际范数由exp正性化为其本身；逐步用 −ell M≤|−ell M|=|ell||M|≤|ell|(16+|q|)n 给有限常数支配。因此hg是任意实ell/q下的真正全空间exp Integrable。

96才以hg.const_mul给scaled f真Integrable。没有使用只对ell≥0成立的单侧likelihood估计，没有先交换积分或用总化积分默认0。n=0时常数界为exp0=1、f=0，真实可积性同样成立。该有限界可依赖n，证明未冒称它是共同n支配。

承重 SampleBoundary 104–115 的Y下界真实逐基点值/新增点Y=6+dyadicMesh(j+1)>6证明；normalValue确为8x−x²。F只提供负项定义和公开导入链；本H没有调用其要求均值/方差/gap的几何尾定理来假装任意ell均有共同尾界。

### 3.3 相位代数与真产品格点（97–108）

97–101的hphase先用Int.floor_add_fract取得floor(nq/h)+θ=nq/h，然后在hh.ne'即h≠0下用mul_div_cancel₀，严格得到h·floor(nq/h)+hθ=nq。这里不除n、sqrt(n)、q或ell。

102–108仅在hcoords给出的ν-AE坐标支持上，消费公开stage_sample_normal_layer q n J z hz，得∃K∈ℤ，M_n=hK−nq。取m=K−floor(nq/h)并用真实Int.cast_sub及hphase代数重排，得到M_n=h(m−θ)。没有从原文直接赋网格，也没有错误加入非零offset。

已核该公开前置完整真实门（SampleBoundary88–102）：只要求每个坐标在实际stage range；内部stageAtom_normalValue_lattice逐点给整数，取有限整数和后减nq。它与本轮ν-AE hz正好匹配，未调用G的私有辅助。j.val<J及addedAtom j使用dyadicMesh(j+1)的真实偏移由已有阶段格点定理保障，J0依旧成立。

### 3.4 每层可测、同向与跨向 disjoint（109–142）

109–112以实际M_n连续等值集闭可测，与sourceTail_measurable q n相交给每个P_k/N_k可测。sourceTail的公开可测性对任意q/n成立，来自真实energy、有限坐标和、Real.sqrt连续性，不隐含q正性。

113–119同向P若有共同路径，两个M_n等值相减并在h≠0下mul_left_cancel₀，再实数线性代数及Nat实嵌入单射给k=l，与hkl冲突。120–126先对N的两负等式用neg_injective，再同样消去非零h，故负向也pairwise disjoint。

127–136证明跨向：P的h(k+1−θ)>0，明确使用θ<1、k≥0、h>0；N的−h(l+θ)≤0，明确使用θ≥0、l≥0、h≥0。因此跨向绝无共同路径。137–142从两个iUnion成员分别提取实际Nat索引后消费hPN，给两union点态Disjoint；没有只建立AE不交却误用更强API。

### 3.5 AE完整覆盖及零层唯一（143–173）

hcover的forward只在hgrid给出的ν-AE网格上进行。取真实整数m后：Int.ofNat0进入N0，等式h(0−θ)=−h(0+θ)由真实环代数给；Int.ofNat(succ k)进入P_k，实嵌入就是h(k+1−θ)；Int.negSucc k进入N_(k+1)，其等式为h(−(k+1)−θ)=−h((k+1)+θ)。负整数没有错误使用toNat0，也没有遗漏m=0。

反向168–173从任何P或N的成员直接取其sourceTail分量，故两union点态包含sourceTail。结合forward仅AE成立，hcover准确是sourceTail=ᵐ[ν](⋃P)∪⋃N。使用propext将实际成员等价化成Prop相等，属于标准允许公理；未把AE set equality升级成所有path的集合相等。

θ=0时仅N0是真零层，P0从+h开始；θ>0时N0=−hθ<0、P0=h(1−θ)>0，仍按实际格点唯一分流。θ=1不是实际fract值，证明没有使用错误的端点覆盖。

### 3.6 层积分确实等于实际两DEF（174–207）

174–189的hPi先对可测P_k用setIntegral_congr_fun，将同一f中的真实M_n替为层值h(k+1−θ)，再用setIntegral_const将常数限制积分写为ν.real(P_k)乘实际scaled指数，最后只交换实数乘法顺序得到完整新正DEF。q/ell/h/θ/n/k、实际ν和交sourceTail事件均保持。

190–207的hNi同样先用可测N_k和真实M_n=−h(k+θ)，把−ell·M_n通过环代数变为+ell·h(k+θ)，得到已有F负DEF。`congr`/`ring`只证明实指数内的符号恒等式，未用ell≥0或把θ参数改成1−θ。

ν是真有限概率，所以这些ν.real层质量是实际有限ENNReal质量的toReal，而不是top.toReal的默认0。setIntegral_const虽可在一般语境定义，这里实际有限门独立真实成立。每层f限制积分的真可积性也已由96的hf提供，而非靠常数化掩盖不可积。

### 3.7 真 HasSum 后才 Summable 与精确总和（208–223）

208–215分别调用实际hasSum_integral_iUnion：索引Nat可数、hPm/hNm每层可测、hPd/hNd同向pairwise disjoint，且hf.integrableOn给每一整个union上的真IntegrableOn。该API返回真实每层积分的HasSum；`simpa only [hPi]`与`[hNi]`把它们逐项改写为两个真实DEF序列。因此216的hsP.summable、hsN.summable是真可和证据，不是只给totalized tsum等式。

217–219将左侧sqrt(n)提出/移回同一ν的限制积分，对应真实f。220只用hcover的AE set equality及setIntegral_congr_set转换积分域。221–222用真实两union Disjoint、负union的MeasurableSet.iUnion hNm、两侧hf.integrableOn，合法调用setIntegral_union。223最后才用已获HasSum.tsum_eq，将两真实积分与tsum相等，得到精确目标。

没有在未证明真可积时暗用Fubini；这里的主要countable Bochner分解直接消费全union可积性。没有漏h、sqrt(n)或源权重，也未引入无关Fourier归一化或条件概率分母。两条序列可和已经在恒等式之前独立证明。

### 3.8 边界、参数和未声明结果

n=0时ν为真实空产品概率，M0=0、θ=fract0=0、f=0，两个DEF每项为0，HasSum和恒等式均合法；整个证明无正n或sqrt(n)非零假设。J=0有h=1、四基点整数法向网格，不需存在新增点。

任意负/零q与ell均由绝对值界处理；μ可只对部分stage点赋质量，无hpos要求；空层实质量0，分解仍成立。μ/J/q/ell在intro n之前固定，两侧始终同一个n和实际fract相位，没有隐含均值或协方差假设。

H仅给每个固定n的真可和和精确表示；共同尾需另外消费U16b/F/G接口及真实概率比较。actual phase的本精确枚举已证明，但双侧有限层极限/zero-layer极限处理、moving threshold/sign-tail、conditional Lévy、full19、LLT、hW、generalKL和全部根仍未由本票闭合。

## 4. 指定固定库实际主API语义（只读，无探针）

本轮重新只读指定服务器实际库源。数学判断先于receipt和机械PASS，未运行Lean/#check/API探针或旧target/Audit。

| 固定库位置 | 实际门及本实现消费 |
| --- | --- |
| Floor/Defs264–265、Floor/Ring311–312/438–446 | fract=x−floorx、floor+fract=x、0≤fract<1；47–48/100真实消费 |
| Archimedean/Real/Basic37–38（public section） | 实际FloorRing ℝ实例，由明确第三import提供 |
| MeasureTheory/Constructions/Pi311–313/425–426 | 真μ概率给真产品概率；实际tendsto_eval_ae_ae用于54逐坐标AE提升 |
| Algebra/GroupWithZero/Units/Basic457–458 | mul_div_cancel₀ a (b≠0):b·(a/b)=a；101先有hh.ne' |
| Algebra/GroupWithZero/Defs56–57 | mul_left_cancel₀要求实际因子非零；117/124明确hh.ne' |
| Integral/IntegrableOn171–172 | Integrable.of_bound需要有限测度、AEStronglyMeasurable和AE范数界；84–95逐项给出 |
| 同文件164 | Integrable.integrableOn将hf真限制到每个union/层 |
| Integral/Bochner/Set73–78 | setIntegral_congr_fun需可测层+真实EqOn；setIntegral_congr_set只需真实AE set equality |
| 同文件85–87 | setIntegral_union需真实Disjoint、第二集合可测、两边IntegrableOn；222全部显式提供 |
| 同文件320–325 | hasSum_integral_iUnion需Countable、每层可测、pairwise Disjoint和全union IntegrableOn；211/215全部实际消费 |
| 同文件520–521 | setIntegral_const=μ.real s •常数；实际ν概率令所有层质量有限 |
| Integral/Bochner/Basic288–290 | integral_const_mul实际实标量线性；219用于同一限制测度 |

InfiniteSum/Defs107–116及198–199的to_additive加法版本定义HasSum为有限集合部分和的真实Tendsto，Summable为存在真实和；HasSum.summable给该和见证。333–334的to_additive版本HasSum.tsum_eq消费已有HasSum。故216/223没有利用不可和序列tsum默认0。

已接受前置的真实normalValue、stageAtom/fixedAtom和样本定义与本轮读核相符；stage_sample_normal_layer及sourceTail_measurable是一般μ/任意q所需的公开接口，不是仅atomicMeasure版本。未重做其成功构建。

至此全部实际证明及承重语义未发现数学或来源缺口。下一阶段读取全部实际DECL/TYPE，作者receipt/机械证据继续最后读取。

## 5. 全部实际 DECL / TYPE（包含全部续行）

本轮先只读服务器既有Audit.log的全部DECL/TYPE与续行，排除AXIOMS/PASS行完成类型判断，随后才读作者receipt和机械摘要。实际2项如下；定义的完整实际body已在首节独立提取并在第3节核读，不能只靠其TYPE代替body。

```text
DECL Shao.OQ3.stage_source_layer_decomposition
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (J : ℕ) (q ell : ℝ),
  (∀ᵐ (x : ℝ) ∂mu, x ∈ Set.range fun i => Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i) →
    ∀ (n : ℕ),
      have theta := Int.fract (↑n * q / Shao.OQ3.dyadicMesh J);
      (Summable fun k => Shao.OQ3.sourcePositiveNormalLayerTerm mu q ell (Shao.OQ3.dyadicMesh J) theta n k) ∧
        (Summable fun k => Shao.OQ3.negativeNormalLayerTerm mu q ell (Shao.OQ3.dyadicMesh J) theta n k) ∧
          (√↑n *
              ∫ (z : Shao.Path n) in Shao.OQ3.sourceTail q n,
                Real.exp (-ell * Shao.OQ3.normalDeviation q z) ∂MeasureTheory.Measure.pi fun x => mu) =
            ∑' (k : ℕ), Shao.OQ3.sourcePositiveNormalLayerTerm mu q ell (Shao.OQ3.dyadicMesh J) theta n k +
              ∑' (k : ℕ), Shao.OQ3.negativeNormalLayerTerm mu q ell (Shao.OQ3.dyadicMesh J) theta n k
DECL Shao.OQ3.sourcePositiveNormalLayerTerm
TYPE MeasureTheory.Measure ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℕ → ℝ
```

公开定理保留同一μ/J/q/ell、真实阶段AE门、全部n、实际fract相位、两条真Summable与精确限制积分等式，无隐藏均值/方差/gap或正单点条件。打印器将let显示为have绑定，不改变实际θ的定义。定义TYPE是Measure及四个实参数q/ell/h/θ、两个Nat参数n/k到ℝ；完整body精确使用sourceTail交事件和同一真实Measure.pi。

独立源枚举只有这1def+1theorem；实际owned枚举也恰为这两项。确认owned=2、theorem=1、公开目标=1、公开定义=1、authored private=0、generated=0。所有locals均已在第3节逐段核对，没有把源码无private推测成没有生成项。

## 6. 最后读取的作者/机械证据

所有机械读取在数学、完整实现和上述全部实际TYPE之后，经共享server.py指定服务器只读完成；全部远端项目命令taskset -c 14-17。没有Lean/#check/API probe/build/rebuild/cachewrite/spawn/commit或raw完整日志复制，没有改source/scope/receipt/旧票/shared或回退他人编辑，没有使用ulimit-v、干预CPU0–9/80GiB外部任务或全局资源。

实际worktree=/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3；branch=feat/oq3-stage-layer-decomposition；HEAD=cf44108a4cc2b62b05a8a281de02d962305b56b0。git status仅有 ?? Shao/OQ3/StageLayerDecomposition.lean。当前H未commit状态与author-check时nonclaims相符；本终审不做提交或发布。

| 对象 | 实核字节/行 | SHA256 |
| --- | --- | --- |
| 本地draft、远端worktree、run源码快照（三端相同） | 10202/226 | b6204bbbc39d029e221e473c76e8ebe34a42cf4765f4c3f7ccbd657d6311a8de |
| 本地scope55与run/scope.md | 7064/48 | 83bab854d74daa250c1a1ff68432988d82c03ce230a71d2b17f5bf25c4e37da4 |
| 本地声明票与run/statement-review.md | 24309/223 | c1ee20991a1c9dd15ffd1fff3d677861100fc05f4a1448afdd6c6c5b72b0d118 |
| 本地U17h-receipt.json与run/receipt.json | 9542/128 | 112a7aa3174c2812a941984e6d35435b9e0fa51ceeb8fc72001665e314298c34 |
| 本地U17h-Audit.lean与run/Audit.lean | 1709/39 | 4bd4546b4883bc2fdd62f92f32acfcb3f1365fe859063d6b467078fa5133cb31 |
| 真实远端Audit.log | 1320/21 | 07c0d159ba40c60559a8d62b1d82f510494fd49d5af6e27fbec040031981d4cd |
| 本地与run/prerequisite-hashes.json | 4716/46 | 845cee6dbed8470521eec5e0482d8b7e3d59e530962def79e73e05a9dfcc24f4 |
| 真实只读原R1 report.md | 19420/575 | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |
| lean-toolchain | 29/1 | d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4 |
| lake-manifest.json | 3541/117 | 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e |

独立完整body与完整type逐项去空白比较，均与冻结scope fence相同；实际imports恰为F、Floor.Ring、Archimedean.Real.Basic、Bochner.Set。源扫描无CR、尾空白、sorry/admit/axiom/unsafe/native_decide/implemented_by。

### 6.1 首次成功构建的真实警告与保留历史

不能记成空日志：实际首次成功是build-05，1509字节/21行，作者receipt记录exit0且warning_only_first_success=true。远端实际诊断header为7条warning、无error header，全部是以下样式问题：146:4、160:10、166:8三条无作用change；167:27和167:41两条<;>可用;或删除；同两位置另有两条tac1 <;> tac2可写tac1;tac2的样式提示。

这些诊断对应已逐行审过的覆盖证明中冗余change与顺序语法，没有削弱前提、改变数学对象或引入未完成证明；不构成数学缺口。源在首成功build05冻结，未为清理警告重复成功目标。本reviewer既未编辑它们，也未重跑target/Audit。

| 历史日志 | 实核字节/行 | 实核SHA256 | receipt记录exit |
| --- | --- | --- | --- |
| build-01.log | 1848/36 | 13af9f802cbbc40a3e1ffebb2a613266fd13c715ad60a6dc86309c6be7035717 | 1 |
| build-02.log | 2148/43 | c8e2d642fbd905d195b09eb0dbc565fdf250c3ff33de8b7ac3b4a5bcad572ed0 | 1 |
| build-03.log | 218/6 | 05cacdc3277b9d1750127ac2abb37bb418cfa8b9655d530e99de4f148b48bb6b | 1 |
| build-04.log | 238/6 | 27c6845a6de3af493faa673fcda217b3c98607a24ad0753a2eea3f16ee1abe79 | 1 |
| build-05.log | 1509/21 | 9b79a4b09096c974801297d615190fb5d1c4a7b31513c1e14bcc6f0fc7c0911c | 0 |

本轮只读核实这些既有文件的hash及build05选定诊断header，不复制raw完整日志。历史exit值明确来自hash绑定的作者receipt记录，日志文件本身不独立编码过程退出码；没有把读取日志冒称重新执行。失败历史原样保留，没有以失败版本替代当前冻结源码。

receipt的target/Audit命令均为taskset -c 14-17 lake env lean -M8192 -j4 -DautoImplicit=false；Audit作者记录首exit0。没有ulimit-v或证明语义/心跳配置降低。

### 6.2 实际Audit覆盖

最后全文读取实际Audit.lean：它检查冻结目标确为theorem、冻结DEF确为defnInfo；遍历两个公开stem及整个_private.Shao.OQ3.StageLayerDecomposition前缀，对每项collectAxioms并拒绝新project axiom或非白名单传递公理。实际枚举与完整源一致，两个TYPE已经在第5节逐项读取。

Audit的定义TYPE/defnInfo检查本身不是完整body文本审查；本票的body证据另由首节完整实际定义、人工语义审查、三端source hash与最后full-body规范比较建立，不混淆两者。

真实Audit.log两项AXIOMS均为[propext, Classical.choice, Quot.sound]；最终U17H_FROZEN_DEFINITIONS 1、U17H_FROZEN_THEOREMS 1、U17H_ALL_THEOREMS 1、U17H_ALL_DECLARATIONS 2、U17H_AXIOM_GATE PASS。机械门验证既有内核/公理记录，未替代第3节数学判断。

作者receipt状态仍为AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW，nonclaims说明author-check时终审pending、未commit/PR；它们是正确历史时点记录，本轮新的独立最终裁决不倒改该receipt。

### 6.3 全部44份实际项目闭包

独立从实际目标imports递归枚举前置，剔除当前目标后为44份Shao源。每份真实SHA重算后的字典与本地JSON、run JSON、receipt依赖字典三方完全相同；44份对应现成olean均存在。以下是完整实核清单。

| 实际前置源 | SHA256 |
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

实际项目闭包直接引用51个不同Mathlib根模块，递归Mathlib依赖2848份；对应源码/现成olean缺项清单为空。仅静态只读检查，没有补缓存或重编旧target。G不在H的直接/传递项目依赖中，H并未消费其sourceEll专用尾定理来替代任意ell的积分分解。

### 6.4 固定pins与实际公开库源

真实toolchain=leanprover/lean4:v4.36.0-rc1；Mathlib实际HEAD=807d3836b165983210ee2ecf3cd28f239436949c。下列实际主API owner按真实module/public import图均公开可达，不是仅磁盘上有源码；hash也在最后只读重算。

| 实际Mathlib源 | SHA256 |
| --- | --- |
| Algebra/Order/Floor/Defs.lean | 58450c1ab0d8bb32bc03dadc047190856f73c66f4f36a7392e9f4a842c75de2f |
| Algebra/Order/Floor/Ring.lean | 4ed31dda62383dcc0e877fbc27908e34a964a39a1b8209b53d1a6c0db7f9d1d6 |
| Algebra/Order/Archimedean/Real/Basic.lean | 20122ee310cd4f8809cc0527edfbdbdf048d27793696d5c359ec1f6669636691 |
| MeasureTheory/Constructions/Pi.lean | bb89dee63d412cd1cc1f7f9fd7a81d64074139571960b2f0fcb66d8b763cd6ef |
| MeasureTheory/Integral/IntegrableOn.lean | d1108ec5e836af0af6bc62c8ad5dd94a371dbc8df3e51698049d51221b3663c2 |
| MeasureTheory/Integral/Bochner/Set.lean | e4d90b9fde463a9123e1ac3321ce25c0714e19ce92e172f297e062d9de16be75 |
| MeasureTheory/Integral/Bochner/Basic.lean | 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 |
| Topology/Algebra/InfiniteSum/Defs.lean | 1213ea126c48b375a75023efffdd982a1f837ee2a7bf6cdd6ea4c736365ffd40 |
| Algebra/GroupWithZero/Defs.lean | fb85527ccab74eb4340c5c49c235028f63564b82c0ff866dc75c78119af67fb4 |
| Algebra/GroupWithZero/Units/Basic.lean | 1e7324f9db0a7a93972e83d49fee90d9503d27bca407912a7ad30191430d302f |

## 7. 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 实际完整DEF/type与冻结scope相同，226行实际proof及全部locals已独立核读。真实产品AE支持给有限和格点，正h和实际floor+fract后才清分母；正负整数分流、同向与跨向disjoint、AE完整覆盖与θ0零层唯一均成立。任意实q/ell的真实双侧法向界先给whole weight及scaled f的Integrable，再给每层/union可积、可测和countable Bochner HasSum；逐层常数积分精确匹配两个实际DEF后，先Summable再取tsum，完整得到同一ν/θ/n的限制积分恒等式。n0/J0、空层和没有正原子前提均合法。

全部实际2项DECL/TYPE与源码/生成枚举一致，无隐藏private/generated；三端源hash、44前置、pins、真实首成功带样式警告的build05及首Audit标准三公理门均绑定一致。7条非阻塞样式诊断已如实记录，绝未将本构建记成空日志或为清理它们重跑成功项。独立数学裁决与作者机械状态明确分开。

本轮只写此新终票与指定remote副本，待lead全文读取后决定发布。H完成精确实际相位层表示和固定n真可和；共同n尾、conditional Lévy、finite-layer moving threshold/sign-tail、完整19/LLT/hW/generalKL、全局极小/最优/新颖性及根A/B/C/D仍OPEN。
