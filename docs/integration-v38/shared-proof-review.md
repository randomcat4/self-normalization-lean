STATUS: CORRECT
JUSTIFICATION: 冻结的三个定义忠实实现真实指数可积域、域内实值对数配分及整个域上的扩展实上确界；四个完整证明逐行成立。严格分离测试直接给出每个不同尾域点的严格率比较，覆盖无限率值，未将待证全局率结论作为前提。本裁决仅认证该公共泛型模块。

# 独立完整证明审查 v1

审查者为全新、非作者上下文 `/root/global_rate_proof_review`，按 math-theorem 的新上下文验缝与 Lean 忠实性协议工作。完整读取冻结源码的114行、所有证明体及冻结声明，未以已有声明审查、作者说明或一个 PASS 标签代替证明审查。仅写本报告及同名 JSON；未修改生产源码、共享定义、版本、缓存或引用入口。没有运行 Lean、probe、Audit 或构建。服务器只读取证命令固定 CPU10–13；未操作外部 CPU0–9/80GiB 工作负载。

## 1. 精确绑定

| 对象 | 精确值 |
|---|---|
| 作者 head | `b7ed3c74a09cc53dc25753656267e9d3a408d25e` |
| 唯一父提交 | `ded5b45059cf80861712f61c86170243d5e87fc2` |
| 生产文件 | `Shao/Probability/BivariateLegendre.lean` |
| 完整源 SHA256 | `d8bd5dc7099ffdbf52282ebb41ad03145a50b42547dec55bb42caacb31ed5f58` |
| 冻结声明/定义值 SHA256 | `0b2bafc5965881e4ada01f8ebbeafc8d705ffc78980db711a29fd93dc10d8b81` |
| 作者收据 SHA256 | `663545694dfe3296d3a7601bc95a961f9a5e9528961a8ff7d1737991ce7e3182` |
| 作者 MANIFEST SHA256 | `2150bff69c64a9d14b92c1f9e6421cc6890c89c2532e68b0792400430762abe2` |
| actual-declarations SHA256 | `f8a1915b0dae26a02dcd64bf276466a3b8fb7dfd8b7de2dae37224e3fc9fe948` |
| Audit 源 SHA256 | `5b38bb8868c79fb986ea7d92daec5885ca5c852010d4bd15dcb4b425d4475a70` |
| 作者编译对象 SHA256 | `0379679ed486ae83d6e50e68a24bd3a5520f2f06025dae6439b5a4b6a8ba6e25` |
| root v38 gate-result SHA256 | `4c487fe9a51642a0eaa55bcffc9dce94b21d0f73448863474b263ba56a4a9667` |

实际用 `git show <head>:<path>` 读取作者提交中的收据、MANIFEST 和完整实际类型导出。逐个核对 MANIFEST 的全部条目与该 head 的 Git blob；核对远端当前源、head 源、成功 target-03 输入快照与本地审查源的字节哈希；重建三个完整定义值加四个定理签名，得到与冻结文本逐字相同的声明快照。最终源只补足匿名 `noncomputable section` 的闭合 `end`，没有改动定义体、前提、量词或结论。

## 2. 三个定义的逐行忠实性

令 `Fθ(z) = θ.1*z.1 + θ.2*z.2 - K(θ)`。

- 第20–22行的 `bivariateMGFDomain μ W` 恰为所有使 `exp(θ·W)` 对同一 μ 真正 `Integrable` 的二维实参数。没有换成零点邻域、紧参数集、有限参数列表或已知鞍点集合。无需另假设整个 W 可测：每次使用的指数函数已有该参数自己的可积性，包括其几乎处处强可测性。
- 第24–27行的 `bivariateLogMGF` 只接受该完整域的子类型元素，并要求 `[NeZero μ]`；值是实际 Bochner 实积分的 `Real.log`。后续第43行证明该积分严格为正，因而没有利用不可积积分总化为零或 `log 0 = 0`。对非概率的一般非零测度没有擅自宣称 K(0)=0 或率非负。
- 第29–33行的 `bivariateLegendreRate` 在整个上述子类型上取 `EReal` 的 `iSup`。每个 `Fθ(z)` 先在 ℝ 中算完，再整体嵌入 EReal。EReal 是 `WithBot (WithTop ℝ)`，具有 `CompleteLinearOrder`；上确界无有界性、紧性或非空前提。不存在扩展实减法的无穷减无穷问题，也没有把全局率强转回实数。

三个定义值已按冻结文本和被成功编译的精确源逐字审查。`actual-declarations.txt` 导出了七项实际 TYPE、LEVEL_PARAMS 与 AXIOMS，**没有另行导出这三个定义的内核 VALUE**；`Audit.lean` 的 `collectAxioms` 确实递归检查定义体。本报告不冒称读过不存在的内核值导出。由于冻结值、实际编译输入、编译后对象哈希及实际类型已绑定，且定义值本身完全显式，这一呈现限制没有留下本模块的具体实质证明盲点；没有为输出格式重跑已成功检查。

## 3. 四个完整证明

### `bivariateLogMGF_spec`，第35–44行

θ.property 按域定义正好是 `Integrable (exp(θ·W)) μ`。第43行调用的 pinned `MeasureTheory.integral_exp_pos` 仅要求该可积性和 `[NeZero μ]`，没有遗漏概率性、有限测度或全局可测 W 等条件。它给出正实配分。第44行用 `Real.exp_log hpos`，展开 K 后恰好得到第二合取项。既证明正性，又证明 exp/log 的真实还原。

### `bivariateLegendreRate_test_le`，第46–54行

第52–54行的函数逐项就是第31–33行定义的同一个 EReal 测试族。`le_iSup` 给出指定域内 θ 的值不超过该完整上确界。它没有把无界上确界当实数上确界，也没有额外假设全域可积性。

### `bivariateLegendreRate_eq_of_attained_bound`，第56–71行

第68行将每个实上界 `hupper θ` 经 `EReal.coe_le_coe_iff.mpr` 转成 EReal 上界，再由 `iSup_le` 得到 `rate(z₀) ≤ ↑L`。第69行调用上一完整定理，给出 `↑Fθ₀(z₀) ≤ rate(z₀)`；第70行仅用实等式 hattain 将左边改为 ↑L。反对称性得到精确等号。θ₀ 是真实域元素，因此候选值存在、非空域与有限 L 均被正确使用，没有把“rate(z₀)=↑L”本身作为假设。

### `bivariateLegendreRate_unique_minimizer_of_tests`，第73–110行

第93–94行由上一完整定理得到候选值；所有 μ、W、z₀、L 与其测试证据均保持相同。第96行量化任意 z∈D。第97–99行处理 z=z₀，最小性与双向等号唯一性均反身成立。第100行在 z≠z₀ 分支使用原封不动的 `hsep z hz hzz`，取得一个真实可积参数 θ 及实严格不等式 `L < Fθ(z)`。第102–104行得到

`rate(z₀) = ↑L < ↑Fθ(z) ≤ rate(z)`。

由严格比较得到最小性；第107–108行用 `hrate.ne heq.symm` 排除相反方向的率等号，方向正确。第109–110行在此分支用 hzz 排除 z=z₀，给出所需逆向蕴含。最终结论确实是每个 z∈D 的最小性与 `rate(z)=rate(z₀) ↔ z=z₀`，没有只证某个存在极小点、局部极小、可实现均值子域或一侧等号蕴含。hz₀ 在计算中不需使用，但该成员性前提完整保留，且保证极小点属于 D。

## 4. 边界与隐含前提攻击

| 风险 | 实际覆盖 |
|---|---|
| μ=0 | K 与 rate 的类型显式要求 NeZero；没有给零测度不真的正配分。域定义本身可以用于零测度，未声称其上有本定理实例。 |
| 非零无限测度、空 domK | 可以出现；空上确界就是 EReal.bot。T1/T2 需要域内 θ，T3/T4 需要 θ₀，空域不能制造这些证据，因此没有虚假的有限候选值。 |
| 概率测度但任意 W | 零参数给恒一可积测试，域非空；这一事实仅解释边界，本模块未假设所有非零测度都有零参数。 |
| D=∅ | T4 的 hz₀ 无法成立；没有从空集合捏造候选。D 为单点时 hsep 允许空真，结论正确。 |
| 不同点的率为 +∞ | 严格有限测试值嵌入后仍≤+∞，证明完全成立，不强迫其他点有限。 |
| 不同点的率为 −∞ | 与 hsep 提供的有限测试严格大于有限 L 不相容；没有漏掉可成立的反例。 |
| 非开域、无极值参数紧性、不可微 | 证明只使用完整上确界的序性质与给定 θ₀；无需这些条件。 |
| 只有逐点分离，没有统一 gap | T4 只得到逐点严格比较；没有声称 D\U 上存在一致正间隙或任何概率指数估计。 |
| 结论伪装成前提 | hupper/hattain/hsep 只涉及实有限测试、可积域及 K；没有出现待证 rate 最小性、KL 识别或 Hessian 结论。它们是可由模型单独证明的充分接口。 |

## 5. 实际七项声明、私有/生成项与公理

完整实际导出具有七个不同 OWNED_DECL，每个均有一个未省略 TYPE、LEVEL_PARAMS `[u_1]` 和传递 AXIOMS 行。三个定义的输入、NeZero 位置、域子类型、结果类型与四个定理的全部量词均与冻结签名一致；导出中未见 `...` 或 `⋯`。

| 声明（均在 `Shao.Probability`） | 种类 | 实际传递公理 |
|---|---|---|
| bivariateMGFDomain | definition | propext, Classical.choice, Quot.sound |
| bivariateLogMGF | definition | propext, Classical.choice, Quot.sound |
| bivariateLegendreRate | definition | propext, Classical.choice, Quot.sound |
| bivariateLogMGF_spec | theorem | propext, Classical.choice, Quot.sound |
| bivariateLegendreRate_test_le | theorem | propext, Classical.choice, Quot.sound |
| bivariateLegendreRate_eq_of_attained_bound | theorem | propext, Classical.choice, Quot.sound |
| bivariateLegendreRate_unique_minimizer_of_tests | theorem | propext, Classical.choice, Quot.sound |

Audit 根据 `getModuleIdxFor?` 的精确模块所有权枚举全部环境常量，再递归 `collectAxioms`；不是依赖公开命名前缀。实得3 definitions、4 public theorems、4 all theorems、7 all module-owned constants，额外私有/生成项为0。它拒绝新增模块所有的 axiom，也拒绝白名单外的任何传递公理。完整源的禁用词扫描无 sorry/admit/axiom/unsafe/native_decide；五个 imports 全为 Mathlib，没有 Shao.OQ3 反向 import。

独立窄读实际支持 API，并以 Git pinned blob 比较确认五个文件字节一致：Bochner/Basic 的 integral_exp_pos、Log/Basic 的 exp_log、EReal/Basic 的完整序及实嵌入、CompleteLattice/Basic 的 le_iSup/iSup_le、Probability 的概率测度 NeZero 实例。Mathlib overlay 存在继承的 local-change 警告；这五个实际解析到共享 mathlib 源的文件均匹配 `807d3836b165983210ee2ecf3cd28f239436949c`，没有把警告抹除或把 overlay git status 说成干净。

## 6. 完整机械历史与 root 整合门的只读核对

作者实际使用 Lean4.36.0-rc1 / commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`、mathlib pin `807d3836b165983210ee2ecf3cd28f239436949c`。命令先 activate 再进入专属 worktree，所有 Lean 命令 CPU10–13、`-M8192 -j4 -DautoImplicit=false`，顺序执行。

| 尝试 | exit | 已核原因/结果 |
|---|---:|---|
| target-01 | 127 | `/usr/bin/time` 不存在，Lean 尚未启动；不能计通过。 |
| target-02 | 1 | 最后的命名 `end` 遇匿名 section；完整失败保留。 |
| target-03 | 0 | 成功完整编译最终源并写指定 .olean；与 target-02 的唯一源差异为末尾补 `end`。 |
| audit-01 | 1 | 未识别输出选项 pp.maxDepth；不能因枚举完成就算通过。 |
| audit-02 | 0 | 仅删除该未知选项后，完整 owner 类型/公理审计成功。 |

逐项核读五次 command、exit、start/end、源快照差异及失败/警告诊断；作者收据列出的十个原始 stdout/stderr 日志均在服务器原路径重新计算哈希并匹配。原始日志没有复制到本地或审查报告。保留成功 target 的 hz₀ 未使用警告和继承 mathlib 警告；没有把它们声称为无警告编译。

独立数学审查完成后，只读核对 root v38 整合收据：本源 frozen/source 哈希均为上述 d8bd5d…；服务器 result.json 与本地 gate-result.json 的 SHA256 同为上述4c487f…；七个整合日志均重新计算哈希匹配记录。build 日志明确 `Shao.Probability.BivariateLegendre 0`，聚合入口也通过；theorem audit、全部 module-owned constants 审计与 module coverage 均 exit0。整合的 OwnedAudit 同样按所属项目模块识别定义、私有和生成项，逐个递归检查三公理白名单。此为 **root 执行的已有成功门，本审查者未执行或重跑**。整合收据报告复用266个旧源/1043旧对象，并记录271模块、1831公开定理、3051含生成命名空间定理、5249所属常量；这些是整合事实，不是本模块贡献或根闭合计数。

## 7. 对原契约、R1 与 PR146 消费者的对应

实读 `drafts/oq3/root-contract.md`（SHA `a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a`）及完整 R1（SHA `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662`）。根契约§2的真实 domK、域内正配分、全域 EReal Legendre 语义在本模块中得到通用实现；§3实际正尾唯一全局极小性的模型适配仍须在下游完成。R1 的 KL(9)/(10) 没有被当作新公理或泛型桥的前提。

实读 PR146 的 `SourceGlobalExponentialTests.lean`（SHA `24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df`）和其两个完整实际公共类型；PR146 author head为 `5d14dbdb619fd7d2eb97ec31e049053de53be871`。它们可在同一个 q、w、原律 `μ=originalMeasure sourceEll w` 和 `W(x)=(x,x²)` 下供应本模块的有限测试接口：

1. 从四条约束的第0条取得 HasSum w 1，再由实际 `originalMeasure_isProbabilityMeasure` 产生概率类及 NeZero。必须使用逆倾斜的 originalMeasure，不能换成 atomicMeasure。
2. `source_saddle_exponential_value_bound` 给所有实 s,t 的真实可积性、候选 `(q/4,q)` 的测试上界，以及 θ₀=`(8*sourceEll,-sourceEll)` 处达到 `L=saddleRate sourceEll q w`。将 θ₀ 连同其可积证据装入完整域后，正好供应 hupper/hattain。
3. `exists_source_tail_exponential_separator` 对全部 `c>0` 且 `(sqrt q/4)*sqrt c≤a` 的不同点提供一个真实可积、严格超过 L 的有限实测试；不限于支撑凸包或可实现均值。pair 不等式转换为 `a≠q/4 ∨ c≠q` 后正好供应 hsep。候选属于 D 要由 `q>0` 与 sqrt 恒等式另行给出；不得悄悄纳入 c=0。

这些对应显示公共桥可用，**不等于已经实现、编译和验收 OQ3 实际律 adapter**。本模块不导入模型源，不证明一般 KL 对偶、导数/Hessian、均值逆图有限率识别、D\U 统一率间隙、远区概率上界或完整固定律反例根。T4 的存在分离器也没有蕴含统一分离常数。没有新颖性、历史首次或原研究根 CLOSED 声明。

最终裁决：冻结公共泛型模块的三个定义与四个完整证明 **CORRECT**；未发现需修复的关键缺口。实际 OQ3 适配及其余源界定根义务由后续独立交付承担。
