# U17g StageSourceNegativeTail 完整独立证明审查

STATUS: CORRECT

## 1. 实际公开类型盲译（先持久化）

本轮已有独立声明审查的历史上下文；以下仍从冻结实际实现重新提取唯一公开完整类型，在读取本轮实现证明、scope 解释、作者 receipt 或机械结果前独立翻译。本轮无公开定义体。

```lean
theorem exists_stage_source_negative_layer_geometric_tail (mu : Measure ℝ)
    [IsProbabilityMeasure mu] (J : ℕ) (q : ℝ)
    (hq0 : 1 < q) (hq1 : q < 103 / 100)
    (hmeanY : (∫ x : ℝ, normalValue x ∂mu) = q)
    (hmeanX : (∫ x : ℝ, x ∂mu) = q / 4)
    (hrange : ∀ᵐ x ∂mu, x ∈ Set.range (fun i : Fin 4 ⊕ Fin J =>
      stageAtom (fun j : Fin J => addedAtom j.val) i))
    (hpos : ∀ i : Fin 4 ⊕ Fin J, 0 < mu.real
      {stageAtom (fun j : Fin J => addedAtom j.val) i}) :
    ∃ gamma C : ℝ, 0 < gamma ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
        Summable (fun k : ℕ =>
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n k) ∧
        ∀ K : ℕ, (∑' k : ℕ,
          negativeNormalLayerTerm mu q sourceEll (dyadicMesh J) theta n (K + k)) ≤
            C * Real.exp (-gamma * dyadicMesh J) ^ K /
              (1 - Real.exp (-gamma * dyadicMesh J))
```

独立数学翻译：固定同一个实数轴概率测度 μ、有限阶段 J 及实数 q，满足 1<q<103/100。实际 Y(x)=8x−x² 的 μ 均值为 q，实际 X(x)=x 的 μ 均值为 q/4。μ 几乎处处位于同一阶段的四个基点与前 J 个新增点组成的有限像中，且这些阶段索引对应的每个实际单点都具有严格正的 μ 实质量。

则存在同一对严格正实常数 γ、C，及自然数的共同最终阈值；对阈值后的全部 n，并对每个 θ∈[0,1]，由真实 μ 的 n 重乘积测度、同一 q、固定 sourceEll、同一阶段格距 dyadicMesh J 构成的无局部截断负层项序列，在实数意义下真正可和。对每个自然数 K，其从 K 起的真实移位尾和不超过 C·exp(−γ·dyadicMesh J)^K /(1−exp(−γ·dyadicMesh J))。

量词核读：γ、C 和 n 的最终阈值位于全部 θ、K、求和指标之外；q、μ、J 始终固定。输入没有另加 H、能量上下界、紧支持常数、S/det/T 正性、ellgap 或 ell·q 数值间隙；实际实现必须从所列阶段、正原子和均值前提推出它们。sourceEll 没有被存在量词重新选择。结论要求真 Summable，不能用总化 tsum 的默认值代替。J=0、θ=0/1、K=0 和零层均保留。

此阶段只记录实际类型的数学含义，尚未判定实际证明、生成项、来源或机械凭据。

## 2. 来源、冻结声明和实际输出

盲译阶段已先写入 35 行 / 2717 字节，阶段 SHA256 为 fdf22b77a14fa52c1b15e86c42b9a3f4ddcad1dfe53b7e3aad458160e73a4f79。随后才读取 scope54、真实 R1 和实际证明。本轮未读取作者 future/candidate/implementation notes，也没有读取下一 scope。

R1 113–130 的有限阶段是四个基点加前段新增点，有限阶段与极限保持同一组矩约束。实际 addedAtom j 用 dyadicMesh(j+1)，与原文从正整数开始的点编号相符。本定理给定 μ、J、q 并接受真实阶段门，未重新证明源概率族的存在性，也未给按 J 或 n 重选 q 的权限。

R1 239–256 的实际 Δ=Cov(X,X²)、S=Var(Y)、T=detΔ/S=τ²，以及 T≤VarX=q−q²/16 和 q/(32T)>1/30>ell，正是本实现消去手工方差/间隙门的数学内容。T 不是 τ，也不是任意辅助参数。R1 256 明确同一证明适用于每个有限阶段。

R1 378–391 的真实负层加权指数界及 421–429 的负层截断，是本单元的直接来源义务。本单元消费已经完整接受的 E/F 证明，将 F 的充分输入由真实阶段前提推出；未复制或认可原文未经本链证明的 Legendre 优化或全局率唯一极小叙述。

实际 negativeNormalLayerTerm（F 源 8–13）是 sqrt(n)·exp(ell·h·(k+θ)) 乘 μ^n 对 {normalDeviation q=−h(k+θ)}∩sourceTail q n 的真实实质量。normalDeviation q=∑Y−nq；sourceTail 要求真实 energy>0 和 sqrt(q)/4·sqrt(n·energy)≤∑X（SampleBoundary 19–27）。定义没有 if、局部 δ、替代权重或替代概率测度。

结论仅是这一实际无截断负层序列的真可和及共同几何尾界。尚未给全层相位枚举、双侧零层处理、finite-layer moving threshold/sign-tail、conditional Lévy、完整(19)、LLT、hW、generalKL 或任何根闭合。

## 3. 完整实际证明及承重语义

本轮逐行读取实际实现 1–95 行。结构为唯一 import F、namespace/open/noncomputable、一个私有定理、一个公开定理；此时未用 receipt 或机械 PASS 作数学依据。

### 3.1 私有 stage_abs_bounds_ae（8–16）

hrange 的 Set.range 见证是 i:Fin4⊕FinJ。取得见证后，inl i 的实际 stageAtom 定义化简为 baseAtom i，与 fixedAtom(Sum.inl i) 相同；inr j 的实际点是 addedAtom j.val，与 fixedAtom(Sum.inr j.val) 相同。直接消费 fixedAtom_bounds 得到 AE 的完整二重界 1≤|X|≤4+sqrt10。

该辅助不要求概率、积分或任何质量正性，只有所显示的阶段 AE 范围前提。J=0 时只剩 inl 分支，不需选择 Fin0 元素。它没有把有限索引的 hpos 扩大为全无限 AtomicIndex 的正质量。

承重 fixedAtom_bounds（SummableAtoms 214–234）对四个实际基点分别验算；新增点用 addedAtom_gt_four 与 addedAtom_lt_limit 得到绝对值双界。stageAtom=Sum.elim baseAtom x（FiniteConstraints 57–58），fixedAtom=Sum.elim baseAtom addedAtom（SummableAtoms 25），故这里的类型化简确实绑定同一组点。

### 3.2 H 与真实能量支持（35–54）

35–36 从私有二重界提取 hb；37 固定 H=25+8sqrt10，既不依赖 n/k/θ，也未重新选择 μ 或 q。38–41 使用固定库 Real.lt_sqrt 与 Real.sqrt_lt，在各自非负门已经 norm_num 证明后，检验 (25/8)²=625/64<10 和 10<(13/4)²=169/16，得到 25/8<sqrt10<13/4。因此 42–43 严格得到 50<H<51。

44 的 B=4+sqrt10≥0 由真实 sqrt 非负性成立。45–47 使用 sqrt10²=10（输入 0≤10）给 B²=26+8sqrt10=1+H。没有对负数平方根总化作错误反推。

48–54 对每个 AE 点分别使用 sq_le_sq₀ 的两边非负前提：1≤|x| 给 1≤|x|²=x²，|x|≤B 给 |x|²≤B²=1+H。下能量界来自完整 hbounds.1，并非仅从 hb 上界猜出。所获 henergy 是同一 μ 的真正 AE 1≤X²≤1+H。

### 3.3 实际基点正性与一般 μ 协方差（55–60、80–81）

55–57 取 hpos(Sum.inl i) 后按 stageAtom 定义正好得到 μ.real{baseAtom i}>0。未借助另一测度、另一组权重或原子测度专用构造。

58–60 对同一 μ、hb、hbase 调用公开 normalVariance_pos、parabolaCovariance_det_pos、transverseVariance_pos，得 S>0、detΔ>0、T>0。80 同样调用公开 transverseVariance_le_variance_id。它们的完整类型均接受一般实数轴概率 μ；本实现没有调用仅 atomicMeasure 可用的 atomic_id_variance 或 atomic_transverse_bounds。

已接受 RegularCovariance 的真实定义为 Δ=[[VarX,Cov(X,X²)],[Cov(X,X²),Var(X²)]]、S=Var(8X−X²)、T=detΔ/S。其一般 μ 证明先使所有居中二次/四次多项式真实可积，再绑定居中二次型与 Δ。积分为零会在实际正质量基点 −1、1、2 上取零，迫使非零二次式的两个系数均零，从而给正二次型及 detΔ>0。S 对实际系数 (8,−1) 严格正；T 正性用正 detΔ、正 S；T≤VarX 清除正 S 后归于 (8VarX−Cov(X,X²))²≥0。这些是实际一般 μ 语义，不是从任意 det>0 或总化 variance 猜来的结论。

### 3.4 先真可积，再同一 μ 二阶矩和 variance（61–79）

61–64 分别给出 X 与 X² 真 Integrable：公开 integrable_continuous_of_fixed_bounds 对同一概率 μ、hb 和真实连续函数适用。该 helper 在紧 Icc[−B,B] 上取得统一有限函数界，然后由连续→AEStronglyMeasurable 和概率有限性给 Integrable；没有使用积分默认零。

65–68 先有 (hX.const_mul 8) 与 hX2，才使用 integral_sub 将真实 Y=8X−X² 的积分拆成 8EX−EX²，再用 integral_const_mul。69–71 代入已给 EY=q 与 EX=q/4，得 q=2q−EX²，故实际 EX²=q。

72–74 另行建立真正 MemLp X 2 μ：continuous_id.aestronglyMeasurable，加 hb 经 Real.norm_eq_abs 转为 AE 范数界，再用概率蕴含有限测度下的 MemLp.of_bound。此门在 76 使用 variance_eq_sub 之前真实存在。

75–79 固定库 variance_eq_sub 消费 hLp，输出 VarX=∫X²−(∫X)²；随后代入 hsecond 与 hmeanX，用 ring 得 VarX=q−q²/16。没有把非可积 X 的总化 variance/toReal 当作实方差，没有把 hmeanY 当成 X² 均值直接改写。

### 3.5 正分母与严格数值间隙（80–90）

80–81 已得 T≤q−q²/16。82–84 先由 hT 给 32T>0，再 apply lt_div_iff₀；所需代数是 (32T)/30<q。独立检查：由 (q−1)²≥0 得 q²≥2q−1，所以 32T≤32q−2q²≤28q+2<30q（最后一步用 q>1）。因此 1/30<q/(32T) 严格成立。没有在 T=0 时消去总化除法，也没有颠倒正分母不等式方向。

85–86 真 sourceEll_lt_one_div_thirty 与上式严格传递，得到实际 log(31/30)<q/(32T)。sourceEll 定义为 Real.log sourceU、sourceU=31/30；SourceStarter 45–46 的 sourceEll_pos 是真实 log_pos。RegularCovariance 200–205 的上界由 log_lt_sub_one_of_pos 在 31/30>0 且 ≠1 时给出严格 log(31/30)<1/30，绝非取 ell=1/30。

87–90 先由 q>1 得 q>0，才将 sourceEll<1/30 右乘 q：sourceEll·q<q/30<103/3000<7/200。末尾常数严格差为 7/200−103/3000=1/1500>0。因此 hellq 是真正严格充分间隙；未将 7/200 误称为比 103/3000 更小的界。

### 3.6 完整 F 调用与量词（91–92）

下表列出 F 的每个实质输入及本实现对应证据，所有实参都属于同一 μ/J/q。

| F 输入 | G 的实际证据 |
| --- | --- |
| μ 是概率、J、q | 原公开参数/实例原样传入 |
| H、ell | H=25+8sqrt10；ell=sourceEll，均不按 n/θ/K/k 选择 |
| hb、1<q、q<103/100 | 36 的 hb；原 hq0、hq1 |
| 50<H、H<51 | 42–43 的 hHlo、hHhi |
| 0≤ell、ell·q<7/200 | sourceEll_pos.le；87–90 的 hellq |
| AE 1≤X²≤1+H | 48–54 的 henergy |
| EY=q、EX=q/4 | 原 hmeanY、hmeanX，未改测度 |
| S>0、detΔ>0 | 58–59 的 hS、hD |
| ell<q/(32T) | 85–86 的 hgap |
| 阶段 AE 支持、所有活跃索引单点正性 | 原 hrange、hpos 完整原样传入 |

该调用的返回类型与公开目标逐项相同，直接保留 F 的 γ,C>0、统一 eventual n、全部 θ∈[0,1]、真 Summable 与全部 K 移位尾界。这里不是把缺失门当隐藏假设重新包装：每个新增充分门已经在上文推导。F 自身先由 E 得全实非负层位移界，再以真几何 majorant 建立原序列及各移位序列的真实可和，双方真 Summable 后才比较实 tsum；无总化默认零或 ENNReal 无条件单调替代。

### 3.7 边界与非声明

J=0 保留四个正质量基点，hrange 的 inr 分支为空；协方差不退化依赖这些实际基点，不依赖存在新增点。dyadicMesh0=1，所有 J 的 dyadicMesh 正，故继承 F 的 0<rho<1 和正 1−rho。

θ=0/1、k=0、K=0 及可能的 off-grid/零层全部是 F 实际序列，未删项也未把局部守卫 false 分支冒充零概率。n=0 没有被用来非法消除 sqrt n 或 n；G 自身无 n 除法，继承的是 F 的最终 n 结论，有限初项不声称满足同一尾常数。

本定理没有实际全层 phase 枚举、双侧零层消重、条件 Lévy、移动阈值/sign-tail 或完整(19)；也没有证明新一般 KL、最弱前提、最优常数、新颖性、全局极小或任何根 A/B/C/D 闭合。这里只证明原有限模型已有均值与正支持门足以消费真实负层几何截断。

## 4. 实际固定库核读（无 Lean/API 探针）

在指定服务器只读实际源码，核读下列使用类型及前提；没有执行 Lean、#check、target 或 Audit。

| 固定库位置 | 实际数学门与本实现消费 |
| --- | --- |
| Analysis/Real/Sqrt.lean 394–395 | Real.lt_sqrt (0≤x)：x<sqrt y ↔ x²<y；下有理界 x=25/8≥0 |
| 同文件 231–232 | Real.sqrt_lt (0≤x)(0≤y)：sqrt x<y ↔ x<y²；x=10≥0，y=13/4≥0 |
| 同文件 177 | sq_sqrt 的输入 0≤10 已明确 |
| Algebra/Order/GroupWithZero/Basic.lean 758–759 | sq_le_sq₀ 双方非负后才能以平方比较，50–51 两次均满足 |
| 同文件 1136–1137 | lt_div_iff₀ 消费严格正分母；83 明确 mul_pos 32 hT |
| MeasureTheory/Integral/Bochner/Basic.lean 261–264 | integral_sub 必须两函数 Integrable，68 显式提供 |
| 同文件 288–290 | integral_const_mul 的实际标量线性；已单独确保 X 可积 |
| MeasureTheory/Function/LpSeminorm/Basic.lean 631–633 | MemLp.of_bound 需要有限测度、AEStronglyMeasurable、AE 范数界，72–74 均真满足 |
| Probability/Moments/Variance.lean 226–228 | variance_eq_sub 必须真实 MemLp X 2，不只是 AEMeasurable；76 消费 hLp |

静态语义审查至此未发现数学或来源缺口。下面才核实际 TYPE，机械凭据继续后置。

## 5. 全部实际 DECL / TYPE（完整续行）

只读服务器既有 Audit.log，先独立读取全部 DECL、TYPE 及其全部续行，排除 AXIOMS/PASS 等机械行后完成类型判断；此后才读取作者 receipt、Audit 源和机械摘要。实际日志 1–4、6–27 覆盖以下两个完整类型。

```text
DECL _private.Shao.OQ3.StageSourceNegativeTail.0.Shao.OQ3.stage_abs_bounds_ae
TYPE ∀ (mu : MeasureTheory.Measure ℝ) (J : ℕ),
  (∀ᵐ (x : ℝ) ∂mu, x ∈ Set.range fun i => Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i) →
    ∀ᵐ (x : ℝ) ∂mu, 1 ≤ |x| ∧ |x| ≤ 4 + √10
DECL Shao.OQ3.exists_stage_source_negative_layer_geometric_tail
TYPE ∀ (mu : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure mu] (J : ℕ) (q : ℝ),
  1 < q →
    q < 103 / 100 →
      ∫ (x : ℝ), Shao.OQ3.normalValue x ∂mu = q →
        ∫ (x : ℝ), x ∂mu = q / 4 →
          (∀ᵐ (x : ℝ) ∂mu, x ∈ Set.range fun i => Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i) →
            (∀ (i : Fin 4 ⊕ Fin J), 0 < mu.real {Shao.OQ3.stageAtom (fun j => Shao.OQ3.addedAtom ↑j) i}) →
              ∃ gamma C,
                0 < gamma ∧
                  0 < C ∧
                    ∀ᶠ (n : ℕ) in Filter.atTop,
                      ∀ theta ∈ Set.Icc 0 1,
                        (Summable fun k =>
                            Shao.OQ3.negativeNormalLayerTerm mu q Shao.OQ3.sourceEll (Shao.OQ3.dyadicMesh J) theta n
                              k) ∧
                          ∀ (K : ℕ),
                            ∑' (k : ℕ),
                                Shao.OQ3.negativeNormalLayerTerm mu q Shao.OQ3.sourceEll (Shao.OQ3.dyadicMesh J) theta n
                                  (K + k) ≤
                              C * Real.exp (-gamma * Shao.OQ3.dyadicMesh J) ^ K /
                                (1 - Real.exp (-gamma * Shao.OQ3.dyadicMesh J))
```

私有项只有实际阶段 AE 范围门，没有隐藏概率或质量条件；公开项保持实际全部输入与统一量词，sourceEll、dyadicMesh J 和同一 μ 的真实层项没有替换。省略的可推断 Fin 类型与 actual 源中明确的 Fin4⊕FinJ 相符；完整公开 hpos 类型也再次绑定该有限索引。

独立核对实际源中 authored 声明枚举只有上述 private theorem 与 public theorem；实际 Audit 枚举也是恰好这两项。确认 owned=2、theorem=2、公开目标=1、公开定义=0、authored private=1、generated=0。未用作者预估数量推测生成项。

## 6. 最后读取的机械证据与绑定

下列事实是在独立数学/全部实际 TYPE 审查之后，经共享 server.py 的只读连接取得；所有远端项目命令以 taskset -c 14-17 开始。没有 Lean/API 探针、build/Audit 重跑、缓存写入、raw 完整日志下载、source/scope/receipt/旧票修改、commit/PR 或 spawn。未触外部 CPU0–9/80GiB 任务、全局资源或 ulimit-v。

当前远端 worktree=/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq3；branch=feat/oq3-stage-source-negative-tail；HEAD=bdf206fe5a5a22fcca24d180923c7e2cf05425f8。git status 实际只有 ?? Shao/OQ3/StageSourceNegativeTail.lean；未提交状态与 author-check 的 nonclaims 相符。

| 对象 | 实际字节 / 行 | SHA256 |
| --- | --- | --- |
| 本地 draft、远端 worktree 源、run 源快照（三端相同） | 4551 / 95 | 8b2e2eee60a9725e02653b58741cd63ba497fd5e5c5baaa0dca228fbda3ea8a0 |
| scope54：本地与 run/scope.md | 5024 / 37 | f9eed04fd530169ad4c59e0b3acaaa8b194c1f4dbdba96ab1ba0c40ab5af39fa |
| 已接受声明票：本地与 run/statement-review.md | 20619 / 201 | 307b7ac585470a167d55da0f07004fd77bdd4e95cdb57878e299a5a1ecba89ed |
| 作者 receipt：本地 U17g-receipt.json 与 run/receipt.json | 8786 / 103 | db6309a3ca586c8f2458791f08d72101def37b0d663791e9004749f92c17608c |
| Audit 源：本地 U17g-Audit.lean 与 run/Audit.lean | 1637 / 38 | 1760f1df7c8846486b2be7137e24bbf01f898f970100c8808f391d41c681d7fc |
| 真实远端 Audit.log | 1823 / 32 | 31d11e9cae2e9ab489f952d45e05c5c6530b246cf160cde1125b134711a3a015 |
| 前置 JSON：本地与 run/prerequisite-hashes.json | 4716 / 46 | 845cee6dbed8470521eec5e0482d8b7e3d59e530962def79e73e05a9dfcc24f4 |
| 真实远端 build-01.log | 0 / 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| 只读原始 R1 report.md | 19420 / 575 | 3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662 |
| lean-toolchain | 29 / 1 | d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4 |
| lake-manifest.json | 3541 / 117 | 40e8e3385f2b0c8ae56fa9de6947301472379cb62eeb83247944827c38b8af6e |

实际源唯一 import 为 Shao.OQ3.NegativeLayerGeometricTail，零公开定义。独立提取实际完整公开类型与 scope fence 在去除空白后比较相同；扫描源得到无 CR、无尾空白、无 sorry/admit/axiom/unsafe/native_decide/implemented_by。

receipt 的 build/audit 命令记录均是 taskset -c 14-17 lake env lean -M8192 -j4 -DautoImplicit=false，作者记录两次 exit_code=0；真实现存 build-01.log 为上述空文件，真实现存 Audit.log 的覆盖与门另经只读核查。空日志本身不编码历史退出码；本报告没有把读取空文件说成重新执行成功。

读取实际 Audit.lean 1–38：它验证唯一冻结目标是 theorem，defs 为空，遍历公开 target stem 和整个 _private.Shao.OQ3.StageSourceNegativeTail 前缀，对每项调用 collectAxioms 并拒绝新 project axiom/非白名单传递公理。结合实际源恰两个声明与上一节全部 TYPE，未遗漏独立 authored 项或生成项。

真实 Audit.log 两项 AXIOMS 都是 [propext, Classical.choice, Quot.sound]；最终记录 U17G_FROZEN_THEOREMS 1、U17G_ALL_THEOREMS 2、U17G_ALL_DECLARATIONS 2、U17G_AXIOM_GATE PASS。该证据是既有内核/公理门的绑定，不代替第3节数学判断。

作者 receipt 状态 AUTHOR_KERNEL_AND_AXIOM_CHECKED_AWAITING_INDEPENDENT_PROOF_REVIEW 以及独立终审 pending、当时未 commit/PR 的 nonclaims 是 author-check 时刻的记录；本独立终票现在给出另一个明确裁决，没有将历史 receipt 的待审状态改写为已终审。

### 6.1 真实项目闭包逐文件核 hash

从指定 worktree 的实际 import 递归得到 44 个 Shao 前置，独立重算每份实际源 SHA；其字典与本地 JSON、run JSON、receipt imported_project_sources_sha256 三方完全相等，无漏项、多项或不匹配。以下给出完整实核清单；这不是仅照抄作者声明。

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

44 份前置对应的现成项目 olean 均存在；实际项目闭包直接 import 的 49 个不同 Mathlib 模块，其源码与 olean 亦均存在，无下载或补缓存。此处的 49 是项目闭包直接引用模块的集合计数，不冒称 Mathlib 全传递依赖只有 49 份。

公开 API 的实际导入链可达：F→E→D/J；D→CenteredSampleTilt→CenteredLogMGF→NormalTangentMoments→NormalTangentGaussian→RegularCovariance；EnergyBernoulliMGF→InverseTilt→AtomicMeasure→SummableAtoms→SourceStarter；SampleBoundary→FiniteIID→已缓存概率矩库；现有积分/Lp 源提供本轮直接使用接口。没有依赖 root 未补的 Lévy/Portmanteau 或缺失公共 characteristic 模块。

### 6.2 固定环境与已消费库源

实际 lean-toolchain 文本是 leanprover/lean4:v4.36.0-rc1；实际 Mathlib git HEAD 是 807d3836b165983210ee2ecf3cd28f239436949c。库源均在指定 worktree/.lake/packages/mathlib 中读取，核心已消费库文件的实核 SHA 如下。

| 固定 Mathlib 源 | SHA256 |
| --- | --- |
| Mathlib/Analysis/Real/Sqrt.lean | 1f19e1d6722b2f51c2cd676d0b28ede856c7915ac815b597cef4b3919040c204 |
| Mathlib/Algebra/Order/GroupWithZero/Basic.lean | 28c0432242f3766a643689abd852cbf92fee391d314f76815e6977e64854103c |
| Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean | 8e7b53565147a97607ebb09d26073084d0e926edbc9349db90f69859990762cd |
| Mathlib/MeasureTheory/Integral/Bochner/Basic.lean | 66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670 |
| Mathlib/Probability/Moments/Variance.lean | 0bcf0e00025e061b358fbde009fc35cd2e6dc28749d724513d08caa76e69415e |
| Mathlib/Analysis/SpecialFunctions/Log/Basic.lean | 0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97 |

## 7. 最终独立裁决

STATUS: CORRECT

JUSTIFICATION: 实际公开完整类型与冻结 scope 相符，来源义务明确限定为真实原有限阶段负层序列的可和/统一截断。95 行完整实现及唯一私有辅助已逐项核读：stage→fixedAtom 的 AE 双界真实；H 与能量双界严格成立；同一 μ 的一般协方差接口给 S、detΔ、T 正；X/X² 可积先于积分线性，真 MemLp2 先于实际方差公式；T>0 先于清分母；实际 log(31/30) 的严格上界和 q 范围给全部真实间隙。F 的每个显式门均由实际输入推出，并原样保留同一 μ/q/J 和全 θ/K 外的常数与最终 n 阈值。

全部两项 actual DECL/TYPE 与全部证明、私有/生成枚举相符，无隐藏定义、生成或额外义务。最后只读核得三端源/冻结接口/44前置/pins/现有构建与完整传递公理门一致；没有以机械 PASS 替代数学或来源审查，也没有重跑成功构建或 Audit。本轮只写此新终票及其指定远端副本，等待 lead 全文读取后决定发布。

根 A/B/C/D、actual phase/双侧零层处理、conditional Lévy、finite-layer moving threshold/sign-tail、完整(19)、LLT、hW、generalKL、最优性/全局极小与新颖性均未由本票闭合。
