# SourceTerminalEnvelope 独立完整最终数学与证明审查

数学裁决：**CORRECT**。精确冻结的七项公共定理及其全部新证明，忠实建立原文的实际停止终端 E 包络与 cutoff 处 CR² 预算；没有发现数学缺口。当前流程验收裁决：**NEEDS_FIX_PROCESS_PROVENANCE_ONLY**，仅等既有记录补足每个私有辅助头先冻结、后写证明体的操作来源；不把这一过程来源限制称为数学反例或内核失败。

审查者 `/root/terminal_envelope_final_review`，非作者，fresh context，gpt-6.1-sol / xhigh；未再委派。使用 math-theorem，未使用 math-ultra。没有写任何生产源、改变命题、重跑 Lean、递归公理审计或旧 producer。输入、缓存输入、输出、推理子集 token 均不可见，分别记 null；没有把 token 数量换算成订阅百分比。

## 精确范围与不可变证据

- 源：`drafts/c12-terminal-envelope-production/SourceTerminalEnvelope.lean`，3040 行、146265 bytes、UTF-8/LF、无 BOM，SHA256 `5a76818ca654409719ab3a7ba00bc254605f135678eb5dd4e9f12102b44abd80`。
- 原成功对象：`outputs/common-terminal-envelope-v75/producer49.olean`，SHA256 `64de9b7b09f22ba6b5e50ea322f69076ddf3c559228267f6edb4aff41ccb6255`。服务器当前可导入对象与此原对象完全相同，`source49.lean` 与上述冻结源字节完全相同。
- [草稿 PR292](https://github.com/randomcat4/shao-lean/pull/292)，head `f65595902d2dabb772b1decc84983d1c1f464048`，仅新增目标源，未合并。只读服务器观察确认此 head，工作树干净。
- 作者不可变 `final-receipt.json`：`a6ba7fc715a3a57a090cbe82b3041c9065bbbe449daa94713ab0917e0c78ba9a`；作者 `RELEASE.json`：`c82038dfc4a8490abffe6eb7b2fe3793676f13f802792cb3ed62c918cd381908`。独立核对 RELEASE 所绑定全部 69 文件的大小和 SHA256，全部相符；目标源写入、排队写入、Lean/AX、传输均为零在途，writer/execution 权限已释放。
- `original-evidence-bindings.json`：`1ffef3dff2868f2afd3c3ab2203d95381b6df004d0b793093d10f66e81374c2d`，记录 168 个原远端证据路径。本审查只重新读取必要的原对象/源/日志哈希及导出边界，不复制日志、不重算数学。

实际 owner 总数 153：7 个显式公共定理、53 个显式私有定理、90 个生成 theorem，共 150 theorem；另有 3 个编译器生成非 theorem。显式源码 definition 和 instance 均为零。绝不由“零显式 definition”推断“没有 helper”或“零生成值”。

## 完整阅读与独立还原

完整读过全部 3040 行声明、let 值、证明和所有分支；原文定位完整读过只读 `C:/game/shao/current/c12/main.tex:1107–1121` 与 `supplement.tex:4604–4665`。没有将作者 source-mapping 当作正确性证明。

全部实际 TYPE 与三个 VALUE 使用无损完整等价表示阅读：1937 个完整 literal tails、241 个完整递归有序 block，以及全部 6483 个有序 context record（TYPE 5664、VALUE 819）。完整 display 共 2588 行，分批覆盖 1–380、381–760、761–1140、1141–1520、1521–1900、1901–2050、2051–2230、2231–2400、2401–2588；每批均未截断。此处没有抽样、只读词典、删略实际类型或用规约类型替代原始类型。

自行编写的独立 decoder 不导入作者 encoder，分别递归展开有序 blocks 和线性 encoded rows；两种展开都逐字节等于原始文件，并独立重建全部 display 字节：

| 工件 | bytes | SHA256 |
|---|---:|---|
| all-owned-types.txt | 1040887 | `e9ec1e78465cb78d77a2ebb3395f6407eb60e3e25c4ee9be63b05155b55bc4b3` |
| all-owned-non-theorem-values.txt | 261388 | `f6d4a0360dc2fe81c596d517cf9855d6b5e3f9fc7016eb806dc4f315f6b65a72` |
| lossless-full-types-values.json | 1068792 | `41506ed65e141686a71dc432fd1b6d1a9d8f546ee05266afddc1bf88d90af9b5` |
| lossless-full-types-values-display.txt | 219867 | `355bc5fe7315b7f300cf2803469ba272f5e346161515fe5c18e7f65d7a6abdeb` |

还独立解码冗余的 generated-only 包，精确还原其 470219 bytes / 5901 行。该包包含的三个实际类型和完整值，已经在上述 full 包中逐项完整阅读，未把冗余副本当成额外数学证据。

随后在原服务器直接从原 `owned-diagnostic49.log` 提取全部 153 TYPE 与全部 3 VALUE；每一完整块的哈希均与本地实读原始文件中的对应块完全相同。此项核对封住了“无损包虽然自洽、却不是原对象导出”的风险。`original-export-binding.json` 和 `byte-verification.json` 保存独立核对结果。

## 原内核与公理审计失败边界

实际内核成功的是 **check49.rc = 0**。原 `check49.log` SHA256 `b2dadc3cdde3c836c4314d6e42795ca84bce3b4f263538b0890a42f2ebef44fb`；其中尾部是 linter warning，不是 error。

同一次流水线的初始 owner gate 为 **owned-audit49.rc = 1**，日志 SHA256 `93abfde55b3fad9268b32692da610fa45fb040e412cb1648e29993aaa50f1015`。它在第一个生成 definition 处触发零定义要求，只完成了 63 项 TYPE，所以它本身不是完整 owner 审计。组合流水线 **whole49.rc 仍为 1**；不能把组合结果写为 exit0。

完整 diagnostic 为 **owned-diagnostic49.rc = 1**，原 JSON 状态 `FAIL_NONZERO_DEFINITIONS`，JSON SHA256 `3aebe8ac784bcb986232f37a8e4cb1ff7cb8f9e60c8f6f2e09eb3f3343a975c5`，日志 SHA256 `7c8dc500b9fc8c670917290f17fec142838541efb871e06bf3f0798ed9648fd3`，driver SHA256 `b6d7fd4510c7f6a75c418f034f45fdf0f25a4adeb0edd373b4d82c6b8877a562`。

独立完整读过该 driver 并核对原日志末尾：按 `env.getModuleIdxFor?` 选全部真实模块 owner；对每项先执行递归 `Lean.collectAxioms` 并拒绝白名单之外公理，再导出完整 TYPE，遇 definition 再导出完整 VALUE。全部 153 项、三个 VALUE、完整 JSON 写入及 `AUDITED_TARGET_CONSTANTS 153 PUBLIC 7 THEOREMS 150 DEFINITIONS 3` 均完成，才在最后 `definitionCount == 0` 断言失败。所有递归公理集合均包含于 `propext, Classical.choice, Quot.sound`。

根的 exact-generated scope `0806eb597044dabd64a4ada856b4596f3a003dc3c35eb79fc0ff54ff7aa0bb37` 仅允许精确三名编译生成 definition 的确定性分类补正。独立比较原 153 rows 与补正 `owned-audit.json` rows 完全相同，并逐字节核对三名完整 TYPE/VALUE payload 的 scope 哈希。`classification-validation.json` 的 rc0 是**分类元数据验证成功**，不是把原 diagnostic 改为 rc0。没有任何新 Lean/AX/producer 执行，所有失败字节保留。

三名非 theorem 的完整语义：

1. 私有 `te_interior_signs.match_1` 是冻结的三种 MonitoredDomain 分支消去，返回 upper `{1}`、lower `{-1}`、interval `{1,-1}`；完整 VALUE 为 `MonitoredDomain.casesOn`，AX 空。
2. 它的 `.splitter` 完整 VALUE 是同一 matcher 的别名；TYPE 相同，AX 空。
3. `actual_fixed_suffix_terminal_corridor_budget.match_1` 是公共定理证明体的依赖消去器。完整 TYPE/VALUE 把先前已经推导的 `hd` 和 `hdom` 泛化为参数，每个域分支把它们传给相应 branch method；没有增加公共头前提或偷用目标预算。AX 正好在标准三项白名单内。

当前 `SourceTerminalEnvelopeOwnedAudit.lean` 是未执行模板；实际原初始 driver 是 separately archived `SourceTerminalEnvelopeOwnedAudit-check49.lean`，完整原导出使用 Diagnostic49。不能把未执行模板当成功收据。

## 冻结接口与过程来源

独立解析生产源和冻结源，逐项比较全部完整声明头，保留所有 let 值和每个域、尺度、量词。7 个公共头与根冻结 `956c7954d883e5afde8d0ca21bb0fff5a9496876e2a3748ee8652c27abcf6de4` 加两项明确语法追加说明一致：第四头把保留字 `prefix` 只作 `«prefix»` 标识符转义；第二头仅加括号，使 near 与 far 两项共同在每个 eta 的求和内。没有数值系数、严格性、范围或假设变化。

全部 53 个实际显式私有头与 helper-heads01–22、24、26 的完整冻结文本一致；23、25 是保留的未实现提案，24、26 具名长度/秩证明 binder 只修复作用域，不改变公共数学。声明源与 actual TYPE 对应，未出现未声明隐式数学前提。

尚待过程来源补证的仅是逐 helper **头写入先于第一次证明体写入**的原始事件链。当前 helper 文件、hash bindings、check ledger 和作者过程声明可以核对精确头、迭代及首次核检查；仅凭它们或 mtime，不能独立推出更强的写入时序。根已明确说明没有逐项实时观察，并正从已有工具/传输记录抽取，不改 69 个不可变生产证据、不恢复数学源写入/执行。审查数学无需重做。

## 七个公共结果的源到命题与证明评价

| 公共定理 | 源行 | 评价 |
|---|---:|---|
| actual_backward_stopped_suffix_integral | 322 | CORRECT：实际后缀选择器与原 iid 产品积分恒等式 |
| actual_brownian_bridge_noise_maximal_tail | 785 | CORRECT：真实 Brownian bridge law 的双边最大尾 |
| actual_source_terminal_corridor_envelope | 1264 | CORRECT：原 live/completion/cutoff 语义下逐样本 corridor 包络 |
| actual_backward_terminal_raw_data | 1844 | CORRECT：已合格逆向 Wald/Doob 原对象回原尺度及严格 cutoff 几何 |
| actual_fixed_suffix_terminal_corridor_budget | 2222 | CORRECT：真实固定 iid 前缀下可积 corridor 预算 |
| actual_stopped_terminal_envelope_budget | 2663 | CORRECT：原随机停止终端最大差预算 CH/(nσ²) |
| actual_terminal_at_energy_cutoff | 2949 | CORRECT：原 cutoff 点单差预算 CR² |

布朗桥尾的证明不输入任何目标尾界。实际 Brownian 的 Gaussian 单点律给指数可积性和 MGF，未来独立增量给有界 past 权重因子分解。有限有序网格最早越墙指标严格分割，重复时间不破坏划分，空网格也覆盖。指数方法得到一侧 exp(-v²/2)，再对 B、-B 取并得到两侧。连续性把稠密可数网格控制延拓全区间，真实 bridge `B(t)-tB(1)` 的 norm 至多两倍 Brownian norm。对 v 从下逼近 u/2 处理闭尾，u=0 单独使用单位概率界，得 2 exp(-u²/8)。此方法仅放大通用常数，没有伪装反射公式输入。

逐路径 corridor 使用原 `sourceAlive`，其中含 Q>0、终点严格内点及从零秩开始的严格 path survival；`sourceValue` 使用原 `completionExt` 和真实 eventCompletionKernel。U=0 时，剩余平方和为零使所有后续和等于终点，原可达 T=0 延拓使每个 source value 等于 terminal indicator；dead 分支同样一致。x=0 的 rank-zero strict interior 不可能。故没有以“几乎处处”删去零能量或原子。

若某个 0<w≤2J，则 discrepancy≤1 由该 closed near 项支付，w=2J 保留在 near。若所有 w>2J，则所有后续点及两个完成端点距相应墙至少 w/2；剩余桥方差 T≤U，真实 bridge norm 尾支付每墙 2 exp(-w²/(32U))。区间使用 upper/lower 失败并的概率界，lower 的符号为 -1，缩放正确。每墙两项实际共同位于同一个 eta 求和内。w≤0 两项均为零，alive 条件要求的正距离也由原严格内点得到。

后向数据严格复用合格 SourceBackwardStoppedEnergy 原对象；正尺度 c=√(nσ²) 的实际产品 pushforward 同时保持 NH、N，能量缩放 c²、位移缩放 c。有限二阶矩支付可积性，raw mean=0 只用于所需的中心化预算。闭反向 first hit 达到 H，原向 cutoff 第一次严格 T<H，因此 off exceptional 有 κ=n−NH+1，再得到 τ=r 或 r+1；H 等号和有原子 law 均未删去。恢复 EN≤7H/σ²、EU=σ²EN、EJ²≤16σ²EN、P(exceptional)≤12H/(nσ²)，无更高矩、支持有界、对称或无原子前提。

实际 N=t 的选择器分为 t<m、t=m（含 t=L）、m<t<L、t=L 的精确分支，只依赖最后 t 个原坐标的 energy 和倒序 t−1 平方和。原 iid 产品测度经坐标等价拆分成前缀×后缀；有界可测 selected integrand 先获得 Bochner 可积性，再用 Fubini。证明没有声称关于正向自然 filtration 的停止性质，也没有对总 Q 条件化后误用 iid。

固定 suffix b 的 U=energy(b)、J=max|prefixSum(b)| 均来自实际拼接。严格 alive 含于每墙闭随机墙 survival 集 A，此为上界所需集合包含，不反向偷换事件。U=0 和 x=0 先归零；其余 T'=32(U+J²)>0。每墙 near+far≤(e+2)exp(−max(w,0)²/T')，因此无需假设高阶矩即可调用已合格 genuine Gaussian profile：q=U，T=T'，d=b=0，closed=true，至多两墙。这里 d=b=0 是 profile 的位移参数，不是固定 suffix b=0。实际可积性由 measurable 与单位界独立给出，然后才积分单调。原同律前缀比较给 rσ²R_r²≤nσ²R_n²=h/4≤H/4，从而 Cfix=64(e+2)Cp 在所有 law、Brownian law、n 与 suffix 之前选择。

随机停止装配没有输入目标期望：令 cost(b)=2Cfix(J²+U+H)/(nσ²)，Phi=D_fixed−min(cost,1)。两个被减量均在[0,1]，故 |Phi|≤1；每个 suffix section 的固定前缀期望既≤cost又≤1，得到其中心化积分≤0。按有限 N=t 分块调用前述真实 bounded Fubini，再求和得到 E Dr≤E min(cost,1)≤E cost。真实 U、J² 的可积性先于解截断和积分单调，E(J²+U+H)≤17σ²EN+H≤120H，因此 E Dr≤240CfixH/(nσ²)。off exceptional，τ≥r，原最大差受 Dr 控制；exceptional 再支付 12H/(nσ²)。C=240Cfix+18 也覆盖 n≤3（H≥σ²/2、nσ²≤6H）和 R>1/2（H≥4nσ²R²>nσ²）分支。n=1 在小 n 分支真实覆盖，并非需要 n≥4 的后向 producer 的漏例。

最后取 H=h、m=0，真实 κ≤n，cutoff 单差属于已控最大差；该单差的可测性和单位界另证可积，之后积分单调，h/(nσ²)=4R²，得到通用常数 4C。没有把有限离散恒等式称为原 root 定理。

## 精确依赖复用与集成边界

只复用合格旧证明及原对象，审查其接口与调用条件，不再完整重审旧证明。`accepted-dependency-bindings.json` 保存以下根资格文件字节与原字段：

- SourceBackwardStoppedEnergy 源 `5476ba61888e6e4e7177960d5418e2f1dd92c15952faa74a30420f2c18a27f54`，实际导入对象 `f85c2d1f488c14b89414c6b2b0099d962e049f2e52516cb310bfef1491360306`；原 bounded Wald/Doob 精确声明足以支付所有新调用。
- SourcePermutationReveal 源 `eb8ca14665fddaa34b063f3d53a42333db4dcf813c635e4978751b5251287b5a`，对象 `83903b0cd75d5cdf839393b729c46ee5a3b5df1e617bbfa95cc65fe48372139d`；实际 source/energy/cutoff 定义及零状态未漂移。
- SourceSuffixMomentBudgets 源 `c0457040fec0cee18355f5028c7731e0ad8525deee28185aa0cf3b7a088d3c7b`，对象 `feb6b5c085f1be3dc9e5ccbc5a8414a1b99a022a9a238abf87a063d7092bb08f`；base worktree 本来没有该源副本，使用已资格原导入对象。独立核对 library 中源字节和服务器实际导入对象均为此版本。首次只读元数据脚本误假定 base 包含其源而报 FileNotFound；保留该观察失败，修正定位后读取，不重跑数学。
- SourceTrueWallProfile 源 `c22326bc59064fcabc05de2c718bc13b7e1ed47b0e753b587eaa475b7e745449`，对象 `bc7d012096eba0f0e00a5e6af23877a697e8f0f9d35e2cbea5432b65d37bfa3b`；genuine closed Gaussian profile 在有限二阶矩下适用。
- SourceTrueEnergyStrip 源 `b935aed89d0c0b0779d657c4790e33d6faf8ba8a550147e72fca2ccb661ff70e`，对象 `9a53771d5fa32f66796e591a2de1b1c1b762fba1dec7ae4f94d34a7664725e12`；通过合格 profile 接口复用真实平方 strip。BrownianBridgeLaw 使用真实桥对象；OQ4.BoundaryOccupation 新 import 只供显式限定名的 append 前缀代数等式，完整实际类型与全 owner AX 未发生作用域或额外假设漂移。

153 是此模块实际 owner 分母，不是 153 个净新增数学声明。其中 actualWall.eq_1 和 eventCompletionKernel.eq_1/2/3 是导入定义的 lazy equation theorem，必须在根集成按真实名字取并；完整 TYPE 均已逐项核对。

本结果关闭的是这一精确来源、0≤x≤1、原零均值有限正二阶矩下的实际终端 E 依赖。原文一般条件 terminal lemma 的任意 x≥0 与输入 strip 版本不是本公共最终预算的量词范围。没有声称 initial G、局部 Taylor、overshoot、原 C1/C2 或其他原研究 root 已闭。所有原 root 仍 OPEN；OQ3 仍 PAUSED_BY_USER。

两个非阻断文档措辞保留说明：source-mapping.md 末段仍出现“零非 theorem value”旧说法，实际以 final receipt、根 exact-generated3 scope 和本完整三值审查为准；generated-owner-source-map.md 较早的“重跑 owner/AX”措辞已由同文件追加的精确范围与0新Lean/AX记录取代。未改不可变作者证据。

完整逐 owner TYPE / 源到证明语义 / transitive AX 评价在伴随 JSON 的 `owner_coverage` 中逐项给出；下表亦列全部 153 项，不以个别公共头代表私有或生成范围。

逐 actual owner 覆盖（153/153；完整类型均已实读，三个 definition 的完整值另已实读）：

| # | actual owner name | kind | 源位置 | TYPE/证明语义/AX |
|---:|---|---|---|---|
| 1 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs` | theorem | 1093–1113 | CORRECT |
| 2 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_cutoff_measurable._simp_3` | theorem | 1411–1436 | CORRECT |
| 3 | `Shao.Probability.actual_stopped_terminal_envelope_budget._proof_7` | theorem | 2663–2948 | CORRECT |
| 4 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_centered_sections._proof_3` | theorem | 2511–2662 | CORRECT |
| 5 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._simp_3` | theorem | 1585–1843 | CORRECT |
| 6 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_suffix_displacement_bound._proof_1` | theorem | 1123–1140 | CORRECT |
| 7 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_remaining_antitone` | theorem | 886–893 | CORRECT |
| 8 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._simp_6` | theorem | 1585–1843 | CORRECT |
| 9 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_random_discrepancy_data` | theorem | 2390–2428 | CORRECT |
| 10 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_budget_at._proof_1` | theorem | 2472–2510 | CORRECT |
| 11 | `Shao.Probability.actual_brownian_bridge_noise_maximal_tail` | theorem | 785–856 | CORRECT |
| 12 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_zero_remaining_source` | theorem | 909–952 | CORRECT |
| 13 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_suffix_squares._simp_2` | theorem | 143–182 | CORRECT |
| 14 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_merge_at_data` | theorem | 2429–2471 | CORRECT |
| 15 | `Shao.Probability.actual_backward_stopped_suffix_integral._proof_1` | theorem | 322–426 | CORRECT |
| 16 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_energy._simp_1` | theorem | 1437–1462 | CORRECT |
| 17 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_split_at_measure_preserving` | theorem | 248–264 | CORRECT |
| 18 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_scale` | theorem | 1477–1509 | CORRECT |
| 19 | `Shao.Probability.SourcePermutationReveal.actualWall.eq_1` | theorem | 1–11 | CORRECT |
| 20 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_scale._proof_4` | theorem | 1477–1509 | CORRECT |
| 21 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_cutoff_measurable` | theorem | 1411–1436 | CORRECT |
| 22 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_far_corridor_data` | theorem | 1141–1190 | CORRECT |
| 23 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_alive_measurable` | theorem | 1951–1975 | CORRECT |
| 24 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_cutoff_measurable._proof_3` | theorem | 1411–1436 | CORRECT |
| 25 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_suffix_squares._proof_2` | theorem | 143–182 | CORRECT |
| 26 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_sequence_absolute` | theorem | 727–748 | CORRECT |
| 27 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_sequence_upper._simp_3` | theorem | 689–726 | CORRECT |
| 28 | `Shao.Probability.actual_stopped_terminal_envelope_budget._proof_2` | theorem | 2663–2948 | CORRECT |
| 29 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_sequence_upper._simp_4` | theorem | 689–726 | CORRECT |
| 30 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_sequence_upper._simp_2` | theorem | 689–726 | CORRECT |
| 31 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_7` | theorem | 57–127 | CORRECT |
| 32 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_bridge_dense_domination` | theorem | 749–784 | CORRECT |
| 33 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_prefix_squares_monotone` | theorem | 183–194 | CORRECT |
| 34 | `Shao.Probability.actual_backward_terminal_raw_data` | theorem | 1844–1912 | CORRECT |
| 35 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_centered_sections._proof_4` | theorem | 2511–2662 | CORRECT |
| 36 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs.match_1.eq_3` | theorem | 1093–1113 | CORRECT |
| 37 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_order` | theorem | 24–56 | CORRECT |
| 38 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs.match_1.eq_1` | theorem | 1093–1113 | CORRECT |
| 39 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_corridor_payment_profile` | theorem | 1913–1950 | CORRECT |
| 40 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_budget_at` | theorem | 2472–2510 | CORRECT |
| 41 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity._proof_6` | theorem | 1540–1584 | CORRECT |
| 42 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_scale._proof_2` | theorem | 1477–1509 | CORRECT |
| 43 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interval_deficit_le` | theorem | 1191–1204 | CORRECT |
| 44 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_3` | theorem | 57–127 | CORRECT |
| 45 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_1` | theorem | 57–127 | CORRECT |
| 46 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_sequence_upper` | theorem | 689–726 | CORRECT |
| 47 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector` | theorem | 57–127 | CORRECT |
| 48 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_bounded_selected_fubini_at` | theorem | 265–321 | CORRECT |
| 49 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._simp_8` | theorem | 57–127 | CORRECT |
| 50 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs.match_1.eq_2` | theorem | 1093–1113 | CORRECT |
| 51 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_lower_completion_tail` | theorem | 1067–1092 | CORRECT |
| 52 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_9` | theorem | 57–127 | CORRECT |
| 53 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_scale._proof_3` | theorem | 1477–1509 | CORRECT |
| 54 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._proof_3` | theorem | 1585–1843 | CORRECT |
| 55 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_4` | theorem | 57–127 | CORRECT |
| 56 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_finite_set_upper` | theorem | 665–688 | CORRECT |
| 57 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_append_suffix_data._proof_1` | theorem | 2060–2104 | CORRECT |
| 58 | `Shao.Probability.actual_backward_stopped_suffix_integral` | theorem | 322–426 | CORRECT |
| 59 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_energy` | theorem | 1437–1462 | CORRECT |
| 60 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_8` | theorem | 57–127 | CORRECT |
| 61 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_closed_wall_survival_measurable._simp_1` | theorem | 2040–2059 | CORRECT |
| 62 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_order._proof_1` | theorem | 24–56 | CORRECT |
| 63 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_suffix_displacement_bound` | theorem | 1123–1140 | CORRECT |
| 64 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs.match_1` | definition | 1093–1113 | CORRECT；完整 VALUE |
| 65 | `Shao.Probability.actual_fixed_suffix_terminal_corridor_budget._proof_1` | theorem | 2222–2389 | CORRECT |
| 66 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_scale._proof_1` | theorem | 1477–1509 | CORRECT |
| 67 | `Shao.Probability.actual_terminal_at_energy_cutoff` | theorem | 2949–3040 | CORRECT |
| 68 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_suffix_squares._proof_3` | theorem | 143–182 | CORRECT |
| 69 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_zero_remaining_source._proof_1` | theorem | 909–952 | CORRECT |
| 70 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs._simp_3` | theorem | 1093–1113 | CORRECT |
| 71 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_upper_completion_tail` | theorem | 1043–1066 | CORRECT |
| 72 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_split_at_measure_preserving._proof_1` | theorem | 248–264 | CORRECT |
| 73 | `Shao.Probability.actual_fixed_suffix_terminal_corridor_budget.match_1` | definition | 2222–2389 | CORRECT；完整 VALUE |
| 74 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._proof_1` | theorem | 1585–1843 | CORRECT |
| 75 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_far_corridor_data._proof_1` | theorem | 1141–1190 | CORRECT |
| 76 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_profile_domination` | theorem | 2115–2221 | CORRECT |
| 77 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity._proof_1` | theorem | 1540–1584 | CORRECT |
| 78 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_centered_sections` | theorem | 2511–2662 | CORRECT |
| 79 | `Shao.Probability.actual_stopped_terminal_envelope_budget._proof_1` | theorem | 2663–2948 | CORRECT |
| 80 | `Shao.Probability.actual_stopped_terminal_envelope_budget` | theorem | 2663–2948 | CORRECT |
| 81 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._simp_9` | theorem | 1585–1843 | CORRECT |
| 82 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_suffix_squares._simp_3` | theorem | 143–182 | CORRECT |
| 83 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_source_measurable` | theorem | 1976–2011 | CORRECT |
| 84 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_first_hit_partition` | theorem | 503–539 | CORRECT |
| 85 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_finite_grid_upper` | theorem | 540–664 | CORRECT |
| 86 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_normalization` | theorem | 1372–1410 | CORRECT |
| 87 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_source_bounds` | theorem | 876–885 | CORRECT |
| 88 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity` | theorem | 1540–1584 | CORRECT |
| 89 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_zero_wall_dead._simp_2` | theorem | 953–960 | CORRECT |
| 90 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_suffix_squares` | theorem | 143–182 | CORRECT |
| 91 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_alive_mono` | theorem | 857–863 | CORRECT |
| 92 | `Shao.Probability.actual_backward_terminal_raw_data._proof_2` | theorem | 1844–1912 | CORRECT |
| 93 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity._proof_7` | theorem | 1540–1584 | CORRECT |
| 94 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_cutoff_measurable._simp_2` | theorem | 1411–1436 | CORRECT |
| 95 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_future_exponential_factor` | theorem | 438–502 | CORRECT |
| 96 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_merge_at_data._proof_1` | theorem | 2429–2471 | CORRECT |
| 97 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity._proof_3` | theorem | 1540–1584 | CORRECT |
| 98 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs.match_1.splitter` | definition | 1093–1113 | CORRECT；完整 VALUE |
| 99 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs._simp_1` | theorem | 1093–1113 | CORRECT |
| 100 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_exp_moment` | theorem | 427–437 | CORRECT |
| 101 | `Shao.Probability.actual_stopped_terminal_envelope_budget._proof_6` | theorem | 2663–2948 | CORRECT |
| 102 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity._proof_5` | theorem | 1540–1584 | CORRECT |
| 103 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_scaled_suffix_max` | theorem | 1510–1539 | CORRECT |
| 104 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_alive_wall_pos` | theorem | 864–875 | CORRECT |
| 105 | `Shao.Probability.actual_fixed_suffix_terminal_corridor_budget` | theorem | 2222–2389 | CORRECT |
| 106 | `Shao.Probability.actual_stopped_terminal_envelope_budget._proof_5` | theorem | 2663–2948 | CORRECT |
| 107 | `Shao.Probability.SourcePermutationReveal.eventCompletionKernel.eq_1` | theorem | 1–11 | CORRECT |
| 108 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_closed_wall_survival_measurable` | theorem | 2040–2059 | CORRECT |
| 109 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_6` | theorem | 57–127 | CORRECT |
| 110 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_terminal_value` | theorem | 894–908 | CORRECT |
| 111 | `Shao.Probability.SourcePermutationReveal.eventCompletionKernel.eq_3` | theorem | 1–11 | CORRECT |
| 112 | `Shao.Probability.actual_stopped_terminal_envelope_budget._proof_3` | theorem | 2663–2948 | CORRECT |
| 113 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_split_measure_preserving` | theorem | 128–142 | CORRECT |
| 114 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_discrepancy_measurable` | theorem | 2012–2039 | CORRECT |
| 115 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_2` | theorem | 57–127 | CORRECT |
| 116 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_zero_wall_dead` | theorem | 953–960 | CORRECT |
| 117 | `Shao.Probability.actual_stopped_terminal_envelope_budget._proof_4` | theorem | 2663–2948 | CORRECT |
| 118 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._simp_8` | theorem | 1585–1843 | CORRECT |
| 119 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_sign_absolute` | theorem | 1114–1122 | CORRECT |
| 120 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core` | theorem | 1585–1843 | CORRECT |
| 121 | `Shao.Probability.actual_backward_terminal_raw_data._proof_3` | theorem | 1844–1912 | CORRECT |
| 122 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_centered_sections._proof_1` | theorem | 2511–2662 | CORRECT |
| 123 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_suffix_squares._proof_4` | theorem | 143–182 | CORRECT |
| 124 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_bounded_selected_fubini` | theorem | 195–247 | CORRECT |
| 125 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_bridge_failure_budget` | theorem | 1019–1042 | CORRECT |
| 126 | `Shao.Probability.actual_backward_stopped_suffix_integral._proof_2` | theorem | 322–426 | CORRECT |
| 127 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_centered_sections._proof_2` | theorem | 2511–2662 | CORRECT |
| 128 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_completion_far_deficit` | theorem | 1205–1263 | CORRECT |
| 129 | `Shao.Probability.SourcePermutationReveal.eventCompletionKernel.eq_2` | theorem | 1–11 | CORRECT |
| 130 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_append_suffix_data` | theorem | 2060–2104 | CORRECT |
| 131 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._simp_5` | theorem | 1585–1843 | CORRECT |
| 132 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_centered_sections._proof_6` | theorem | 2511–2662 | CORRECT |
| 133 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity._proof_4` | theorem | 1540–1584 | CORRECT |
| 134 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_interior_signs._simp_2` | theorem | 1093–1113 | CORRECT |
| 135 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_energy._proof_1` | theorem | 1437–1462 | CORRECT |
| 136 | `Shao.Probability.actual_backward_terminal_raw_data._proof_1` | theorem | 1844–1912 | CORRECT |
| 137 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_capped_hit_selector._proof_5` | theorem | 57–127 | CORRECT |
| 138 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._proof_2` | theorem | 1585–1843 | CORRECT |
| 139 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_terminal_discrepancy_boundaries` | theorem | 961–1018 | CORRECT |
| 140 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_merge_at_data._proof_2` | theorem | 2429–2471 | CORRECT |
| 141 | `Shao.Probability.actual_source_terminal_corridor_envelope` | theorem | 1264–1371 | CORRECT |
| 142 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_cutoff_identity._proof_2` | theorem | 1540–1584 | CORRECT |
| 143 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._simp_4` | theorem | 1585–1843 | CORRECT |
| 144 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_raw_backward_core._simp_7` | theorem | 1585–1843 | CORRECT |
| 145 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_profile_domination._proof_1` | theorem | 2115–2221 | CORRECT |
| 146 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_finite_grid_upper._simp_2` | theorem | 540–664 | CORRECT |
| 147 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_scaled_path_data` | theorem | 1463–1476 | CORRECT |
| 148 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_fixed_suffix_centered_sections._proof_5` | theorem | 2511–2662 | CORRECT |
| 149 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_sequence_upper._simp_1` | theorem | 689–726 | CORRECT |
| 150 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_actual_cutoff_measurable._simp_1` | theorem | 1411–1436 | CORRECT |
| 151 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_sign_values` | theorem | 2105–2114 | CORRECT |
| 152 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_brownian_finite_grid_upper._simp_1` | theorem | 540–664 | CORRECT |
| 153 | `_private.Shao.Probability.SourceTerminalEnvelope.0.Shao.Probability.te_reverse_suffix_squares._proof_1` | theorem | 143–182 | CORRECT |
