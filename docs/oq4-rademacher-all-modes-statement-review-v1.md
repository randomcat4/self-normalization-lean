# OQ4 全部模态真实有限幂与未化简生存谱：独立来源语义审查 v1

STATUS: CORRECT
REVIEW_KIND: INDEPENDENT_SOURCE_TO_FROZEN_STATEMENT_ONLY
PROOF_REVIEW: NOT_PERFORMED
LEAN_CERTIFICATION: NOT_PERFORMED
SPECTRUM_STATUS: OPEN
ROOT_STATUS: OPEN

本裁决仅确认指定原始来源到新冻结 D1、D2 数学接口的翻译忠实性及范围划分正确。没有补写、核验或接受 D1、D2 的证明，也没有把上游尚未全部形式认证的实现当作证据。无需修改本次冻结文件；后续匿名数学证明、独立数学审查及上游完整形式认证仍是独立门。

## 1. 固定输入与身份核对

本轮直接读取以下原文与冻结数学接口，并逐文件核对 SHA256、字节数。原始来源提交标识按任务及冻结记录固定为 `35d4580b61e22e7145f47730045a09874ef93259`；本轮不执行 Git 查询。

| 文件 | 字节数 | SHA256 |
| --- | ---: | --- |
| `C:/game/shao/current/oq4/c01/spectrum01.md` | 4306 | `b65f9e0c2f9b40a28d092491b479bd20d0b8ee8a9ac940c3c4760cfff7d2670b` |
| `drafts/oq4/frozen-rademacher-all-modes-v1.md` | 6845 | `dac2fd30e7c759137e14ebd64c4d7457155a201da04a7226449304d0b4abbe10` |
| `drafts/oq4/frozen-rademacher-iteration-v1.md` | 5464 | `15851002ccadaa118035107c8b9b8266dd825fdebdf36728f3ac7a97f7330b80` |
| `drafts/oq4/frozen-rademacher-finite-basis-v1.md` | 9862 | `4672baa6bc550de2a97ca9adc0730b5633f71458b2c3da8b02c2318131e05a7f` |

表中相对路径均以 `C:/game/shao lean/` 为根。新冻结的哈希、6845 字节与本次任务锁定值完全一致。上游冻结文件中的历史 pending 标签不在本轮改写；任务及新冻结第 9 行说明上游数学已经独审通过、形式认证尚未全部完成，本轮只使用它们已固定的数学接口。

必要的已认证公共对象读取记录如下；哈希只固定本轮实际所读副本，不构成本轮新形式认证。

| 文件 | SHA256 |
| --- | --- |
| `drafts/oq4/rademacher-cosine/declarations.md` | `e9ec045fccfd4ed68f5b6515f1b28310ab90bf71609cb7bba87a0c1b4d7f850c` |
| `library/Shao/OQ4/KilledKernel.lean` | `f90c1996f4c220473371b0f5ea3c74a7b8287e8f997f1a2cd3f0831cd6bd626f` |
| `library/Shao/OQ4/KilledIteration.lean` | `03b97e5708ffa552cfa4eccec5cf3c042da9805f9ab69561f4cb3e2701a690b5` |
| `library/Shao/OQ4/KilledPathLaw.lean` | `1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f` |
| `library/Shao/Basic/ClosedSurvival.lean` | `bb6f334d2a7956ebf2d727d2feabd0765c30af33da4e8b4197f1fd658921811f` |

RademacherCosine 只读取 lead 明确授权的声明账区段 148–179、213–224、240–259、518–622，没有读取其实现文件。声明账中的 `angle.eq_1`、`halfENNReal.eq_1`、`law.eq_1`、`rho.eq_1` 与已注册 `law_isProbabilityMeasure`，分别固定实际角度、二分之一权重、二点概率律及主特征值；与新冻结第 26–29 行一致。

## 2. 原始来源到冻结对象、量词的逐项映射

| 原始来源位置及内容 | 新冻结位置及精确对应 | 审查判断 |
| --- | --- | --- |
| 第 5–7 行只固定 Rademacher 增量、零起点随机游走 | 第 26 行固定现有 `RademacherCosine.law`，使用内部概率实例 | 没有引入自由分布、自由概率性或一般分布结论。 |
| 第 11–13 行 `h≥1`、`m=floor(h)`、整数状态 `-m,…,m`、吸收点 `±(m+1)` | 第 23–24、33、69 行：`m:ℕ`、`1≤m`、`m≤h<m+1`、`r∈I_m` | 对原 `h≥1` 分支，固定自然数 m 和该半开阈值区间与取整相容；完整保留整数 h，尤其 h=m。 |
| 第 16–20 行 `j=1,…,2H-1`、同一正弦相位、范数 H | 第 25、27–30 行：`J_m=Icc 1 (2*m+1)`，同一 θ、μ、φ、v、系数 `1/H` | `2H-1=2m+1` 的源指标完整对应；没有循环重标号、漏首末项或改为状态数归一化。 |
| 第 13、20–21 行在整个有限整数状态集上的核与特征向量关系 | 第 24、31、33、35、39–47 行覆盖每个合法整数起点 r | 任意合法 r 是源有限状态机制的明确中间接口。原 p(n,h) 的游走仍是零起点；没有把任意 r 的移位生存事件改名为原零起点事件。 |
| 第 21 行一步关系及第 24–30 行有限时谱表达之间的承重连接 | 第 39–49 行 D1：实际核积分、实际 action、所有模态的自然数幂 | 这是应另证的后继义务，冻结把它明确写出，没有把原文的“因此”当作已经提供完整证明。 |
| 第 20 行范数 H、第 24–30 行无权生存概率谱和 | 第 53–65 行 D2：F=1、固定 q、实际 killedMass、未化简的全模态谱和 | 符合常数一展开这一中间步骤；完整显式 S1 仍待零起点及 cot 化简。 |
| 第 24、33 行包含每个整数 n≥0，并以空路径说明零步 | 第 33、70–71 行全部 `n:ℕ`，特别包括 0 | 没有增加正时间、长时间或尺度条件；零步 Dirac 及自然数幂约定被保留。 |
| 第 34 行允许负特征值、没有非格点前提 | 第 70–73 行保留零/负谱、所有模态、整数弱边界与全部时间 | 没有添加正谱、非零谱、无周期或奇偶筛选前提。 |

具体量词合同为：对每个 `m:ℕ` 且 `1≤m`，对每个 `h:ℝ` 且 `(m:ℝ)≤h<(m:ℝ)+1`，对每个 `r:ℤ` 且 `r∈I_m`，对每个 `n:ℕ`；D1 再对每个 `j:ℕ` 且 `j∈J_m`。H、I、J、ν、θ、μ、φ、v、c、G 都由这些固定对象定义，不是额外输入。

φ 是全实轴上的明确正弦函数，v 是其整数强制转换后的有限向量；把 φ 放在实测度下积分、把 v 放在有限整数状态集上求和，两者没有混淆。新 G 与上游 Iteration 的整数网格相同，不能用仅有实区间支持代替整数网格保持。

## 3. D1 的接口忠实性

D1 同时要求真正的 `Integrable φ_m,j (killedIterKernel ν_R h n (r:ℝ))` 与实际积分等式。可积性是独立写明的数学交付；不能以 Lean 的不可积时总化积分值冒充它。

已认证 `KilledIteration.lean` 第 19、22–23 行的定义为实际 monoid 核幂和该幂核下的实积分：`killedIterKernel ν h n=(killedKernel ν h)^n`，`killedAction ν h n f z=∫w,f w∂killedIterKernel ν h n z`。所以新冻结第 45–46 行只是同一 action 的展开，不需要另造递归 action；第 46–47 行的 `μ^n*v(r)` 才是新的承重目标。

明示可调用的上游数学接口只有固定的整数网格保持、B0–B3：其中 B3 是所有合法整数点、所有 j 的真实一步关系，B0 只是首模态兼容。它们不能换成关于自由核、自由特征值或自由特征关系的新假设；也不能从主模态 j=1 的幂等式直接宣称全 J_m 已完成。后续证明及实际导入必须分别经过既定数学门和上游形式认证门，本审查没有读取或认可待认证实现。

## 4. D2、真实质量与概率桥的接口核对

上游有限基冻结第 71–72 行 B2 已明确给出对所有 `F:ℤ→ℝ`、所有 `r∈I_m` 的显式完整重建，系数正是 `(1/H)∑_s F(s)v_j(s)`。本轮只在 F₁(s)=1 处调用该固定数学接口；B2 不是新增的自由完备性假设，也没有要求本轮重新证明 B2。故新冻结的 `q_m,j=(1/H)∑_{s∈I_m}v_m,j(s)` 与源范数 H 完全一致；内外两层有限和都不除以 `2m+1`。

`KilledIteration.lean` 第 26–27 行实际定义 `killedMass ν h n z := killedAction ν h n (fun _ => 1) z`。第 82–83 行公开签名 `killedMass_eq_real` 对任意 n、h、z 给出与 `(killedIterKernel ν h n z).real Set.univ` 的相等，背景仅有 `ν:Measure ℝ` 及 `[IsProbabilityMeasure ν]`。因此新冻结第 59–60 行应理解为已有公开等式，不能误说 killedMass 本来就定义成 real-univ。

有限性由旧公共接口内部供应：第 32–33 行对每个 n、z 的实际行质量给出 `≤1`，第 46–47 行为每个 n 注册 `IsFiniteKernel (killedIterKernel ν h n)`。无需也不得给本 Rademacher 特例增添自由的行测度有限性假设。第 72–73 行还有对可测且全局有界 f 的真正可积性公开签名；本轮只核对它的条件，不以该签名替代 D1、D2 的新证明。

`KilledKernel.lean` 第 25–26 行固定在闭区间 `Set.Icc (-h) h` 上限制平移核；第 36–37 行的公开行等式是 `(ν.map (fun y => z+y)).restrict (Set.Icc (-h) h)`。这是保留丢失质量的被杀死测度，既没有条件存活归一化，也没有要求总质量恒为一。新冻结明确不除以 killedMass，零质量时同一等式仍是目标，没有隐藏正生存前提。

两条路径概率桥的完整相关参数与条件如下，均在 `KilledPathLaw.lean` 的背景 `ν:Measure ℝ`、`[IsProbabilityMeasure ν]` 下：

- 第 165–166 行 `killedMass_eq_path_probability (n:ℕ) (h z:ℝ)`，结论是 `killedMass ν h n z = (Measure.pi (fun _ : Fin n => ν)).real (shiftedClosedSurvival h z)`。没有额外 h 非负、z 位于条带内、正时间或可积性参数。
- 第 259–260 行 `killedMass_eq_closedStrip_probability (n:ℕ) (h:ℝ) (hh:0≤h)`，结论是 `killedMass ν h n 0 = (Measure.pi (fun _ : Fin n => ν)).real (Shao.closedStrip h)`。这里的 `0≤h` 必须保留；本冻结由 `1≤m≤h` 供应，而非删掉该条件。

`shiftedClosedSurvival` 的实际定义（第 15–16 行）只监测 `1≤k≤n` 的 `|z+prefixSum a k|≤h`；`closedStrip` 的实际定义（`ClosedSurvival.lean` 第 26–27 行）监测全部 `k≤n`，包含 k=0。旧第 248–249 行的零起点事件同一性也显式要求 `0≤h`。因此这两条桥正确支持全部 n，包括空路径；没有将零步提前杀死。新冻结只使用乘积律的真实概率，不需另增一个路径桥义务。

## 5. 必须保留的边界检查

1. 弱端点：h=m 时 ±m 仍在实际闭区间内；相邻外跳抵达 ±(m+1) 后才丢失。不得改 strict strip，也不得把边界行归一化。新冻结第 69 行保留了这一点。
2. 完整指标：j 从 1 到 2m+1，含 j=m+1 的零特征值、j>m+1 的负特征值及最末模态。不能用仅主模态、仅正谱或仅奇数 j 代替 D1/D2。
3. 零步：自然数幂使零特征值也满足 `0^0=1`；实际零步核是起点 Dirac。D1 的零步目标恢复 v_j(r)，D2 的零步目标恢复 1。源第 55 行“零特征值没有贡献”属于 S2 长时语境，不能用来删去有限谱在 n=0 的零模态项。
4. 谱符号与周期：μ^n 必须保留符号，不能改成 |μ|^n。冻结没有引入无周期、平稳/不变概率律、混合、μ>0、μ≠0、奇偶匹配或正生存假设，周期消去仍由原有限和表达。
5. 起点与低阈值：合法起点是全部且仅为整数 r∈I_m。没有扩展到其他实起点的平移格点类，也没有删除合法起点条件后声称零步全局成立。m=0、原 `0≤h<1` 的正时间零概率分支仍不在本叶。

上述都是冻结接口必须满足的语义检查，并非本轮对 D1/D2 作出的证明。

## 6. 承重义务与尚未关闭的范围

D1、D2 是源谱链中的待证后继义务。源第 21 行的一步关系、第 20 行范数/正交及第 24 行简略“因此”，不能直接获得本叶证明通过状态；上游数学独审通过也不等于上游 Lean 全认证，更不等于本叶已实现。

本叶只处理常数一的未化简质量谱。上游有限基冻结第 105 行的较宽 D2 缺口清单还提到逐原子核谱、任意有限数据或有界可测测试函数的完整谱表示；新冻结第 17 行明确把这些排除在本薄模块公开目标之外。因此本次 D2 仅对应旧缺口清单中的 F=1 分支，不能因复用编号而宣称旧清单全部完成。

原第 22–23 行的 `v_j(0)=sin(jπ/2)`、偶数模态零贡献、奇数模态有限正弦和的 cot 恒等式，以及原第 27–30 行 S1 的显式奇数指标、符号和系数，均明确留到下一叶。虽然现有零起点闭条带桥可把真实质量接到原概率，本叶仍没有给出完整显式 S1，也没有把主余弦加权积分等同于无权生存概率。

S2 的正负配对、统一余项及其 `H→∞`、`n/H²→∞` 条件，S3 的布朗基准比较，S4 的实阈值位移及 `h→∞`、`n/h²→∞`、`n/h³=O(1)` 等渐近条件，都未由本叶关闭。原严格事件及临界子列/后续必要性分析也未纳入。一般分布 OQ4、Spectrum 和 OQ4 根仍开放。

## 7. 独立性、访问边界与执行记录

已读工作区 `AGENTS.md`、`SERVER.md`、`coordination/TEAM.md`，以及 math-theorem 的技能正文、提示词库、公开工作流和 Lean 核验指引；另读中文输出与 Windows shell 指引。所有 shell 的 workdir 均为 `C:/game/shao lean`。

没有读取任何其他 intake、candidate、review 推理、匿名证明、作者 checkpoint 或新 RademacherIteration/RademacherFiniteBasis/RademacherAllModes 实现；没有执行 Lean、重计算、Git、服务器操作或任何实现修改。只读取 `library/lean-toolchain` 的版本文本，未据此作工具可运行或机械认证声称。唯一写入文件就是本报告，未修改冻结接口或其他工作者产物。

访问范围的小量意外重叠在此披露：为读取旧已认证接口，区段提取曾同时展示 `KilledKernel.lean` 第 30–33、38 行的旧 helper 证明体，`KilledIteration.lean` 第 74 行的证明开头，以及 `KilledPathLaw.lean` 第 167–168、250、261–262 行的旧桥/helper 证明开头或短体。lead 已明确允许在如实披露后继续；这些内容没有涉及本轮新实现、匿名证明或其他审查，也没有被用作接受新 D1/D2 的证明证据。其后只补读 lead 授权的旧声明账及必要透明定义，不再扩读证明体。

最终裁决：CORRECT。该冻结是忠实、边界明确的源到后继数学接口翻译；没有发现必须修正之处。该裁决只释放本叶下一数学门，不释放 Lean 实施或 canonical 写入，也不提供任何新的 PROVED/LEAN_FULLY_CHECKED 或根关闭结论。
