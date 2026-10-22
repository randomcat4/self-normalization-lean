# Shared bivariate Legendre v1 — independent statement review

STATUS: CORRECT

JUSTIFICATION: 提案的三个定义和四个候选定理，在其明写的量词与前提下数学正确，且能忠实消费 PR146 的同一原律、q、w 的两个实际指数测试定理；没有发现须改前提的关键缺口。本票仅为声明及来源语义审查，不是生产证明审查、Lean elaboration/编译、公理审计、缓存准备票或任何 OQ3 原根闭合。

## 1. 身份、冻结对象与执行边界

独立审查上下文：`/root/global_rate_statement_review`；声明作者：`/root/global_rate_scope`。审查时间：2026-10-22 18:55 UTC。未写或修改提案、source-map、checkpoint、分线文件、生产 Lean、共享定义、缓存或 Git 状态。仅本报告及配套 JSON 为本上下文所有。

本票绑定原始字节，不承接作者自评。提案仍标记 PROPOSED/NOT_FROZEN；本审查接受下面的不可变快照供 root 决定冻结，不擅自代替 root 作冻结决定。

- 完整提案 SHA256：`fdd3909511d5f0d5cedf1fb12dd3cdbecdc2298923481bf57ce9a61e060ea762`。
- source-map SHA256：`0e90976c74d756d6afe3058f0528c17d68c69a4b7980b7b1675f308c22addb71`。
- **冻结声明快照 SHA256：`0b2bafc5965881e4ada01f8ebbeafc8d705ffc78980db711a29fd93dc10d8b81`。** 算法：按顺序取提案前五个 `lean` 围栏正文（imports+三个定义、T1、T2、T3、T4），保留原 LF 正文，以两个 LF 连接并追加一个 LF，按 UTF-8 哈希；围栏及 PR146 消费者赋值块不计入。逐块行号和哈希见 JSON。
- 基线只是提案绑定的 v36：main `82294da791784f3ac34ca52b96e21ef23f8a5329`，accepted `f2a39a09ebd50648bd61d68d7018aa01a9810ea0`，tree `b6e72c992deceb0df88e772e50b2c42ba58ac4b4`。本票没有重新判定线上合入状态。
- PR146 固定 head：`5d14dbdb619fd7d2eb97ec31e049053de53be871`；实际源 SHA256：`24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df`。通过只读 `git show` 读取完整对象并重新哈希，与 actual-declarations 导出的两个完整 TYPE 逐字比对。
- pinned mathlib 实际只读 `rev-parse`：`807d3836b165983210ee2ecf3cd28f239436949c`；Lean pin 文件：`leanprover/lean4:v4.36.0-rc1`，只读取，未执行 Lean。

远端仅有三次成功的源码/固定 Git 对象读取，均通过已存在的 broker，轻量读取进程固定 CPU10–13。没有 Lean/probe/build/#check、缓存读写操作、工具链探测、下载、重启 broker，未读取或输出令牌/密钥。未查询或操作任何外部任务进程；受保护 CPU0–9/80GiB 任务未被终止、改绑、改优先级或改限额。

## 2. 三个定义逐字审查

### D1 — bivariateMGFDomain（提案 34–36）

定义确为全部有限实参数 `θ : ℝ × ℝ` 中使 `exp(θ₁W₁+θ₂W₂)` 对 μ **Integrable** 的集合。这里不是“Bochner 积分返回一个实数”的伪条件，也不是局部开集、内部、支撑参数或预先挑选的测试集合。参数任意有限实数；没有替无界律断言全域有限矩生成函数。

μ 可为任意测度，W 可为任意函数。每个域内指数的 AEStronglyMeasurable/有限积分已包含在 Integrable 中；本接口只需这些指数可积，无需推出 W 自身可测、各坐标可积或存在任何矩。下游作为随机变量使用 W 时仍须另有可测性，提案已明示，故无隐含删前提。

### D2 — bivariateLogMGF（提案 38–42）

参数为 D1 的子类型，因而每次合法调用都有 `θ.property` 的真实可积性。另有 `[NeZero μ]`；固定 mathlib 的 `integral_exp_pos`（Bochner/Basic 792–798）恰只需这两项。指数处处严格正、支持是全空间，非零测度保证其支持测度为正；可积性保证 Bochner 积分是真实有限积分，所以配分严格正。

因此 Real.log 仅作用于真实正有限配分，T1 的 exp/log 还原成立。对 μ=0，域本身仍可定义，但无法合法构造 NeZero 实例来调用 D2/D3；对 θ∉domK，θ 不能作为 D2 的子类型参数。没有通过 `integral_undef=0` 或 `Real.log_zero=0` 混入域外 K。不同可积证明不影响 K：正文只依赖 θ 的实数坐标，证明项无数值作用。

### D3 — bivariateLegendreRate（提案 44–48）

每个测试先在 ℝ 中完成 `θ·z−K(θ)`，整体嵌入 EReal 后，才对 **完整 domK 子类型**取 iSup。EReal 在固定库中具有 CompleteLinearOrder（Basic 33–46），因此无需 BddAbove/紧性/可达到性就有真实扩展实上确界；该表达式等于测试像集的 sSup（CompleteLattice/Basic 201–202）。没有 EReal 减法、∞−∞ 或 toReal。

这不是把 saddleRate 直接定义为率，也没有把率偷换成 KL 下确界。任意非零无限测度可能 domK 为空，此时值为 bot；一旦域非空，至少含一个有限实测试，值便严格高于 bot；它仍可为 top。

## 3. 四个完整类型及数学理由

四个签名都保留 Ω/可测空间、同一 μ/W、全部显式参数；本节验证其数学含义和可核验库条件，不把以下理由当作已通过的 Lean 证明体。

| 候选 | 裁决 | 完整理由 |
|---|---|---|
| T1 bivariateLogMGF_spec，64–71 | CORRECT | θ.property 正是固定指数的 Integrable，μ 非零由 typeclass 提供；独立读取的 integral_exp_pos 给第一合取。将 D2 展开后，对这一个正积分应用 Real.exp_log（Log/Basic 59–61）给第二合取。无需概率或有限测度。 |
| T2 bivariateLegendreRate_test_le，79–84 | CORRECT | D3 的 iSup 在 θ 处含有类型中完全相同的有限测试；CompleteLattice 的 le_iSup 直接给比较。率可为 top，结论仍有效；无需上界、KL 或几何条件。 |
| T3 bivariateLegendreRate_eq_of_attained_bound，92–102 | CORRECT | hupper 遍历全部 domK，而非候选附近；实数上界由 EReal.coe_le_coe_iff 转成每个测试≤coe L，再由 iSup_le 得 I(z₀)≤coe L。θ₀ 是域子类型，hattain 将 T2 在 θ₀ 的左端精确改为 coe L，从而 coe L≤I(z₀)。反对称性给等式。θ₀ 排除空域；L:ℝ 排除候选为 top/bot。 |
| T4 bivariateLegendreRate_unique_minimizer_of_tests，110–128 | CORRECT | 先由 T3 得 I(z₀)=coe L。若 z=z₀，全域比较及等号双条件直接成立。若 z≠z₀，hsep 为这个 z 给域内 θ，且 L<θ·z−K(θ)；EReal.coe_lt_coe_iff 与 T2 得 I(z₀)<I(z)。因此既有 I(z₀)≤I(z)，又不可能 I(z)=I(z₀)。反向 z=z₀ 则由替换给等号。hz₀ 明写 z₀∈D，所以候选确实属于极小化集合，不是空域或域外候选的真空唯一性。 |

T4 的 hsep 顺序为 `∀ z ∈ D, z ≠ z₀ → ∃ θ : domK, ...`；θ 可逐点依赖 z。它没有要求一个统一参数分离所有点或统一正间隙。结论确实同时包含“全域最小”和“只有候选同值”；也可在普通逻辑中推出 D 上唯一的全局极小点。并不声称 θ₀ 唯一，亦不声称某个分布 ρ 是唯一 KL 极小分布。

## 4. 边界攻击结果

| 边界 | 核查结论 |
|---|---|
| μ=0 或 Ω 为空而只存在零测度 | D2/D3 与 T1–T4 的 NeZero 门禁止非法使用；D1 仍合法。 |
| 非零无限测度且 domK 为空 | iSup 为 bot。例：ℕ 上无限计数测度、W≡(0,0)，所有指数恒1而不可积。T2 没有 θ，T3/T4 没有 θ₀，不能从空域制造有限候选。 |
| 概率测度、甚至 W 不可测 | θ=(0,0) 的指数恒1，可积且积分1；K(0)=0。故 domK 非空，且 T2 给所有 z 的 I(z)≥0，排除 bot。没有由此推断 W 可测或矩存在。 |
| 非概率非零有限测度 | 零测试为 −log(μ.real univ)，率不必非负；四类型没有误加非负结论。 |
| domK 单点、非开、有边界或无内部 | 三定义与序论理由仍正确；没有任何可微性、局部逆或邻域有限性被暗用。 |
| I(z)=top | off-candidate 的严格有限测试仍给 coe L<I(z)。T4 不需这些点率有限；从未对 top 取 toReal。 |
| D=∅、z₀∉D | hz₀ 排除。D={z₀} 时 hsep 真空成立，且确为唯一全域极小点。 |
| D 非闭或非紧、z 趋近 z₀ | T4 仍成立，但逐点严格不等不产生统一 η>0；没有偷推 D\\U 的正间隙、Cramér 上界或远区指数概率界。 |
| 源尾域的 c=0 | 精确 D 明确排除 c=0，符合 root-contract；弱尾边界包含等号，不把 c>0 的域误叫作全 ℝ² 的闭集。 |
| 源 c<1、c>1+H、c=1、c=1+H、Bernoulli p=0/1、不可实现矩点 | PR146 第二完整 TYPE 只要求 c>0、弱尾和非候选，不删除这些情形。共享 hsep 原样接收，未缩为支持可实现域。 |

未发现反例或必须增加的数学前提。尚未执行的 elaboration、imports 闭包、实例综合、具体证明体及公理审计属于后续机械/证明门，不能因本声明票而视为通过。

## 5. PR146 的同一 P/q/w 消费者核对

固定 PR146 的同一个 q、w、hw、hm，且不重选律：
`μ=originalMeasure sourceEll w`，`W(x)=(x,x²)`，
`z₀=(q/4,q)`，`θraw=(8 sourceEll,−sourceEll)`，
`L=saddleRate sourceEll q w`，
`D={(a,c) | 0<c ∧ (sqrt q/4)*sqrt c≤a}`。

| 共享前提 | 来源与精确对应 |
|---|---|
| IsProbabilityMeasure μ，进而 NeZero μ | hm 的 k=0 行化简为 HasSum w 1；hw 与此行交给 InverseTilt 51–55 的 originalMeasure_isProbabilityMeasure。其 μ 正是 atomicMeasure w 的逆指数倾斜（23–24），不是 π，也不是把未归一化密度当概率。固定 mathlib Probability 84–88 再给 μ≠0/NeZero。 |
| 任意 θ∈domK 的 hupper | source_saddle_exponential_value_bound 的第一合取是 ∀s t:ℝ，给 Integrable、正积分与上界。对 θ 两坐标取值，W 的展开使指数、实积分、K 和 θ·z₀ 与公共类型逐字相同。实际上该源还给此 μ 的 domK=全空间；公共接口无需也未把此特例推广给无界概率律。 |
| θ₀∈domK | 同一第一合取在 (8 sourceEll,−sourceEll) 返回真正 Integrable，构造域子类型证人。不能仅凭后面的等式推断可积；提案没有这样做。 |
| hattain | source_saddle_exponential_value_bound 的第二合取正是 θraw 的值=L；定义展开后与公共 hattain 相同。 |
| hz₀ | 1<q 给 q>0，sqrt(q)²=q 使 (sqrt q/4)*sqrt q=q/4；故候选确实在 c>0 的弱尾边界。 |
| hsep | z=(a,c)∈D 给 hc0/htail；z≠(q/4,q) 在经典逻辑下给 a≠q/4∨c≠q。exists_source_tail_exponential_separator 在同一 q/w/hw/hm、同一 a/c 处给有限实 s/t、真实 Integrable 和严格测试值>L；以该 Integrable 构造 θ∈domK 即得共享 hsep。 |

所以未来适配可得此 **同一个原律** 的 canonical domK/EReal 率在候选等于 coe L，并在完整正尾域上唯一极小。逐点调用的参数依赖 z，不改变 q/w/P；本桥不重新选择固定律、不依赖样本量 n，也没有有限阶段替代最终律的量词交换。

仅 hw≥0 加四约束不自动给严格 L>0；需要保留 PositiveRate 142–146 的实际前提 `ell≠0`、`∀i,0<w i` 与同一 hm，再消费 saddleRate_pos。特别是最终 limitingMass 的正性及 hm 必须由最终同一构造给出。本共享模块不声称独立关闭这项生产义务。

## 6. root-contract 与 R1 范围裁决

root-contract §2 要求真实可积 domK、域内正配分与全 domK 的扩展实 Legendre supremum；D1–D3 精确覆盖这部分。其 §3 根 A 的正尾域取 `x₀=sqrt q/4`、`(a₀,q₀)=(q/4,q)`；T4 加 PR146 消费者正好给“同一 canonical 率的候选值与唯一全局矩点极小性”。并未将 c>0 改成 c≥0。

R1 146–159 固定了逆倾斜原律、同一 q/a/x₀/θ₀ 与 Λ₀=ell*q+log Z；161–241 用 (9) 相对熵恒等式、(10) Bernoulli data processing 和三段估计说明全局正尾性质。这里由 PR146 已产出的真实指数测试直接接到 Legendre 上确界，确实消除了“有限实测试结论→canonical 全局率”的缺口；不需要把一般 KL 变分对偶作为新增未证前提，也不宣称本公共接口已经证明 R1(9)/(10) 或唯一 KL 分布结论。

R1 243–268 的协方差正定、κ²/2>ell、Λ₁ 和几何尺度，root-contract 的 ∇K/∇²K、t₀<0、局部逆图、canonical Hessian 识别，以及有限阶段/最终律概率渐近的装配均超出本票。根 B 的无界情形仍需邻域有限 K、局部分析、D\\U 正率间隙和另列的真实远区概率估计；四类型不提供其中任一概率结论。

允许的后续结论仅为：root 可按此字节快照冻结并实现 `Shao/Probability/BivariateLegendre.lean`，公共模块不得 import OQ3。正式实现之后仍需服务器 CPU10–13 的机械门和新的完整证明审查；再由下游适配 PR146。原 OQ3 根不因本票改变为 CLOSED。一般 KL、导数/Hessian 和远区概率义务仍 OPEN。

## 7. 输入字节与独立证据

本地实际读取/哈希如下；精确读取范围说明及远端对象绑定见配套 JSON。SNAPSHOT、handoff 的历史状态只作绑定，不作本次机械通过证据。

| 本地输入 | SHA256 |
|---|---|
| `C:/game/shao lean/AGENTS.md` | `7bdcd9cd2af52ad99fa265b31222b9bb8926f4805b3a62bc74329b0998e6b983` |
| `C:/game/shao lean/SERVER.md` | `382428147ddb6a07e35da38b00011a721f7698577284e6fa2e9be1ebe498f246` |
| `C:/game/shao lean/coordination/TEAM.md` | `7b6ac0fdfbe6eb0d9f0abe1aeefccfd437d4119baca739c32c981f9ea7143744` |
| `C:/Users/UIO/.agents/skills/math-theorem/SKILL.md` | `062c52873e6fb70ffcf8bca993c94ee6313ace7684dd7b783cd0c45abda66a8d` |
| `C:/Users/UIO/.agents/skills/math-theorem/references/prompt-library.md` | `6cf283b9b36027428240329f6e070222c0f53f7e489f52abb22cd01f9c731171` |
| `C:/Users/UIO/.agents/skills/math-theorem/references/openai-workflow.md` | `cc0fa5b42793a1b0e4389fe7004ed33cea39e57f3b4ed21f599f368f81bead84` |
| `C:/Users/UIO/.agents/skills/math-theorem/references/lean-verification.md` | `58ef00c297dd6be325b115e0a7f74404d1b91f9c72623576e3e1b2bccde676f3` |
| `C:/Users/UIO/.codex/skills/windows-shell7/SKILL.md` | `f023f240411a75bbd052cdc859443c034d8e85e1cc9e04bd1cf98f39c04c086e` |
| `C:/game/shao lean/drafts/shared-global-rate/declaration-proposal-v1.md` | `fdd3909511d5f0d5cedf1fb12dd3cdbecdc2298923481bf57ce9a61e060ea762` |
| `C:/game/shao lean/drafts/shared-global-rate/source-map.md` | `0e90976c74d756d6afe3058f0528c17d68c69a4b7980b7b1675f308c22addb71` |
| `C:/game/shao lean/drafts/shared-global-rate/checkpoint.json` | `1c7370c5455debf982823861e42cdc669f86de754279266ba7e3c35b69d12394` |
| `C:/game/shao lean/drafts/oq3/root-contract.md` | `a3a55ceb4dcdd848967d979ec5eb1c277ac4539476728e7fdce119f01fd2757a` |
| `C:/game/shao/current/oq3/proofs/r1/report.md` | `3473d34ff20bd0d334b9ef3ea3c3ee167fba4d5cc3a742849820ce54d639e662` |
| `C:/game/shao lean/drafts/oq3/u19a-actual-declarations.txt` | `37c55eb82cbf85ff728655666f5113acd3e7fe1a55eb780d932b9487adf8f3f2` |
| `C:/game/shao lean/drafts/oq3/u19a-pr-handoff.json` | `a78322ab3354dc4a6bf5591f0a3e01197c9f835e9660df4f9822655c9eec6ee0` |
| `C:/game/shao lean/library/Shao/OQ3/InverseTilt.lean` | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| `C:/game/shao lean/library/Shao/OQ3/PositiveRate.lean` | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| `C:/game/shao lean/library/SNAPSHOT.json` | `c0b57bab2f300022efd833d96daf616d2b331c88ff68fac29d9deee9a17642da` |
| `C:/game/shao lean/library/lean-toolchain` | `d581a24b57a4ae9e0b2132ca8ac7cc3ac336a9fc2751fe6b29414e2d434d54c4` |
| `C:/game/shao lean/tools/server.py` | `6f8812c3749030efe89bb33834090a8b498db54715041f086b6780b43658a878` |
| `C:/game/shao lean/tools/transport_client.py` | `bb0d3003815b2e65fbde3eefdb3678345ccfe88e50313aa2ad53a8b9d2e02058` |

远端源码独立读取及整文件 SHA256：

| 远端路径 | SHA256 |
|---|---|
| `Shao/OQ3/SourceGlobalExponentialTests.lean` | `24c7029298efc869d785ad4e08dae1a6ea0ca788bf47357355a4e5c564a513df` |
| `Shao/OQ3/InverseTilt.lean` | `c7e7d19e8b70481b663bec1fd12ea9301d73313faaf35997e85aa9ba99f21811` |
| `Shao/OQ3/PositiveRate.lean` | `8e727078d3a4f1db2392384b84cc31235ff69efa13dd5e44b23eac818a788f7b` |
| `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` | `66837a733a5514a0fd824591ac10d43063c5a5cd94c9bdbbf80025686c16c670` |
| `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` | `00ef2a106c0ae4032944cec021ad58d04c370cc9b84547bed95462ca5205e25b` |
| `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` | `d80e3495465030c1accca450935e4bfafcfe31d9b695e17f23ee9cfcea537759` |
| `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `0c2f73c5a7d1a27efc9e44d02ead60112bfe10e3cfbba2407ad3dbcd1c363a97` |
| `Mathlib/Data/EReal/Basic.lean` | `ba85dea4b9ae08516ad8f1926ac2403cc7a386a8eaf6e057c55e668c427a1301` |
| `Mathlib/Order/CompleteLattice/Basic.lean` | `5af0d412e8f8a41c572908d31d9fc0a4745b3ede9165c846d0f788155d207e1f` |

全部远端操作 exit_code=0，stderr 空。mathlib API 行段及完整 PR146 源的真实读取而非作者转述支撑本票。未运行 Lean；`lean_status=NOT_RUN_STATEMENT_REVIEW_ONLY`。本票没有发行任何原源证明的重新认证、完整公理票或新颖性判断。

## 8. 裁决

**CORRECT（仅冻结声明及来源语义）。关键缺口：无。** 无需修改数学前提或缩小量词。root 冻结决定仍待 root；生产实现、服务器 Lean、公理审计和新上下文完整证明审查保持各自独立的后续门。
