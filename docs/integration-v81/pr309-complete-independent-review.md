# PR309 SourceActualTransferAssembly 独立完整最终审查

STATUS: CORRECT

结论仅适用于冻结的 actual_brownian_transfer_with_initial_gap 及其私有终端搬运引理。新源完整证明了 canonical raw iid population 与独立 uniform label permutation 上的真实 B/E 装配、三域 transfer 的数值结论和所报告各量的真正 Bochner 可积性。initialGap 仍是两个半线真实 final-minus-initial 积分差绝对值的 literal max，未获 CR 支付。实际 reflection、interval regularity、全 beta 且未来闭墙的 small Taylor 前提仍显式保留，C1/C2 原根仍 OPEN。本报告不重裁其他分线；历史文档的“所有根 OPEN”不覆盖 Root 已另行验收的 OQ4 原题范围。OQ3 保持用户暂停。

审查者 /root/actual_transfer_assembly_final_review 是新上下文、非作者，未修改证明或前提。作者 /root/permutation_reveal_candidate 的精确源/执行 RELEASE 已核实。指定模型/强度为 gpt-6.1-sol/xhigh；本上下文实际模型、强度和四项 token 遥测不可见，均在 JSON 诚实记 null。没有新 Lean、AX、旧 producer 编译、缓存请求、合并或子上下文。

## 版本、冻结与证据

PR 为 https://github.com/randomcat4/shao-lean/pull/309。head e72801970ce919ca454973262548a169b629eaaf，tree 571f2f224e7e0158174b9676a8a105e149227e6e，blob 4abdbae41060b3121c354f96a8ce5bb21b773db8。服务器只读确认工作树干净，PR 唯一变更为 Shao/Probability/SourceActualTransferAssembly.lean，已发布 blob 与本地/服务器生产源同字节。

源共 362 行、20509 字节，UTF-8 无 BOM、仅 LF，SHA256 db5e803076a7b8a276fed8d024c990caa3663520d883b90edba41f5ee796ccd6。原成功 producer006.olean SHA256 d554a5a089de38cd8306e4c9d764f78ee439e3acec61653c653afc9f80540583。

公开头与 coordination/public-actual-transfer-assembly-frozen.lean.txt（53aed33f27d61c6cdf20e8ea6e9e5d25378cce684ccadd5893e0843c69383929）逐字相同；私有头与 coordination/actual-transfer-assembly-private-heads-v1-frozen.lean.txt（b7582aa8edc18f7598fd43efe1dc1d3337a1b5cfd288dbd17e887980690268d5）逐字相同。公开冻结说明 8d9f7fb46562d94466f32d26e18466c495144464954b38b1a9abc06430be09b0、正式 activation 393d1661cf742eda09a816f939c4fedcbf7923aebdf3cc9167bfc932ae95e7ca，以及 Root 私有头冻结 JSON 均保持原字节。导入、open、autoImplicit false 和唯一 local top 实例值与冻结前缀一致；新增 Elab.async false/maxHeartbeats 只控制执行。没有超出冻结的显式全局声明。

公开 15 个完整声明内 let 依次为 Q、sigmaSq、scale、normalizedLaw、R、h、P、nu、F、FY、Vinitial、Afinal、initialGap、O、rawAbsolute；私有 10 个为 Q、sigmaSq、scale、normalizedLaw、R、h、P、nu、F、D。全部值与依赖次序均已完整核阅，未将某个 let 改为可由调用者任取的参数或额外结论性前提。

复用服务器原 attempt006.log（e5a8a4c1e1a65d6642232aca84edc4d17abdf5e2b54f8871ea5fba536471bca7）与 owned-audit.log（058bc9d84832050364f92a391a5f19b95aabdd65e95bef35df2402250d570a20），原 receipt 分别记录 exit 0。完整导出 actual-owned-types-and-values.txt 共 1030 行、87060 字节，SHA256 44ef4a82d150f689240bbb5875d62cf51b98d146ef6bb15cad454b66dd8d1636；它逐字等于原 audit log 的 TARGET_DECL 到 AUDITED_TARGET_CONSTANTS 之前的完整区段。无打印省略标记。原日志的 mathlib 本地变化提示及 linter 警告保留；未据格式猜测重跑成功检查。只读核对项目 Lean v4.36.0-rc1、mathlib 807d3836b165983210ee2ecf3cd28f239436949c 与固定 pin 一致。

作者 receipt SHA256 651b34b1cc05c8a43244bd0d1fecd2afe309df473fb48639db621fc347834746，作者 RELEASE 21a54e2912c1ece6ccaf9574fcc855bad0569e09ff039d543161aad170e2c963，原 final-publication-binding 36256d7c9c2f785261cee0a68aba57b6b68cf30eb0a1fe67ce11cecf9b57e0b6。13 个 receipt 工件逐一验哈希/字节，连同 receipt、RELEASE、publication binding 共 16 件全部在原服务器目录。私有失败 attempt001、整源失败 attempt005、局部成功 attempt002 与三个 busy/零 Lean 记录保留，未混作整源资格。

本审查首次只读绑定尝试把 PR302 的源误定位到接收工作树，因该文件不存在退出 1，记录保存在 server-readonly-binding.json。第二次只将该读取位置改为资格文件明确的原作者源路径，绑定通过；无源写入、编译或审计重放。全部新服务器命令仅限 CPU10–13 的哈希/Git/原导出读取，未触碰受保护 CPU0–9 工作。

## 原文合同与已验收依赖的消费边界

完整读原 main.tex 901–1038、1077–1109 与 supplement.tex 4560–4670；另读 main 150–162、880–900 核对正秩最大值、raw 状态和 cutoff 定义。两份原文哈希及精确范围在 JSON。原 telescope 固定完整 raw population 后揭示独立 uniform labels，禁止自然 iid stopping-time 偷换；transfer 需要同一个状态、FY、停止秩的 B/E/G；paid 给 retained 与 interval negative overshoot，terminal 第七头只对真正 κ_h 提供 CR²。本新源严格沿这些接口组合。

只完整读实际使用的旧头/定义值及必要语义边界，没有重审旧模块全证明。SourceTerminalEnvelope 第七头 actual_terminal_at_energy_cutoff 的全部量词与 lets 已读：同一实际 bridgeLaw、finite second moment、mean zero、positive second moment、n>0、0≤x≤1、三域共同 CT，给 identity seed 下 D0 真可积及积分≤CT R²。其 qualified source 5a76818ca654409719ab3a7ba00bc254605f135678eb5dd4e9f12102b44abd80、原对象 64de9b7b09f22ba6b5e50ea322f69076ddf3c559228267f6edb4aff41ccb6255 均直接复用；包含原 freeze-provenance process supplement 的 Root qualification 亦保持不变；三个已合格依赖所引用的原作者收据/释放、独立审查、owner map 和 process supplement 按实际存在的字段逐一验哈希，全部吻合。

SourceActualLocalProfileBudget 的 halflineDerivative、HalflineReflectionIdentities、actual_halfline_kernel_data、actual_energy_cutoff_measurable、iid_actual_cutoff_two_halfline_budget 已完整核其实际消费合同。PR302 的 intervalDerivative 完整值、actual_interval_kernel_data 与 iid_actual_interval_retained_negative_budget 完整头已核；其 qualified source 58eef62954931c95be1228accb921de6db3092a4d681184d6e1fef4ab2d20ef6、原对象 e20a2a3de177ff66618c294b219643a1f041e7ccb7a22f703e026fe33af97dbc 直接复用。三项新源直接 import 的实际对象均在服务器精确验哈希。

SourcePermutationReveal 的 uniformPermutationLaw（有限 count 测度的均匀归一化）、revealLaw=P.prod uniformPermutationLaw、randomReorder、remainingEnergy、energyCutoff、Interior、actualWall、completionExt、sourceAlive、sourceValue、sourceRemainder、PermutationInvariant、KernelBounds，以及 energy_cutoff_data、iid_randomPermutation_map_eq_pi、source_stopped_integrability 的消费合同已读。SourceSeparatedOvershoot 的 projection/local/source retained 与 separated 完整值、selected decomposition、parts integrability、three-domain transfer 的完整头与全部六个 let 已读。raw geometry、samplePath、reorder、实际 energy/prefix sums 亦核对定义。所读八个旧源的本地 curated snapshot 与服务器源哈希一致。

Q 确实是 bridgeLaw B PB，而非一般 Q、image candidate 或待证 Brownian 概率身份。BrownianBridgeLaw 的 leftWeight/rightWeight/pinPath/bridgeNoise/bridgeLaw 完整值、概率测度头和 AE 真桥身份，以及 BridgeDomination 的真实 bridgePath/strict event/Completion 定义已核；Q 的概率实例来自 hB。旧物理解析前提不能由这个概率实例自动消去。

## 私有证明完整复核：源 20–124 行

43–58 行在任何 Brownian 空间、样本律、n、x、J 之前取得已有共同 CT>0。D0 就是 terminal 第七头的完整 identity-seed discrepancy；R/h/P/F/κ 无替换，hBudget.1 支付真可积性，.2 支付 CT R²。h>0 由相同 normalizedLaw 的已验收 raw geometry 支付。

59–96 行对每个 population、每个 label permutation、每个秩逐点证明完整状态相等。Equiv.sum_comp 分别保持 raw square sum 与终和；reorder(reorder a σ,id)=reorder a σ。因此 remainingEnergy、actualWall、endpoint 与全部 k≤r prefix 条件相同，得到 sourceAlive 的双向等价和 sourceValue 等值。completionExt 的正时间、可达同端点 T=0、外域和非正时间分支均被相同实参完整携带。cutoff 相等使用两边 energy_cutoff_data 的“κ≤r iff T_r<h”及 κ≤n 作双向不等式，未偷换严格 < 为 ≤。最后 D(p)=D0(randomReorder p) 是逐点等式，不是仅边缘或 AE 的猜测。

97–113 行在 P=pi rho 上用真实坐标 X_i(a)=a_i，measurable_pi_apply、measurePreserving_eval 和 iIndepFun_pi 支付全局可测、同律及联合独立。旧 iid_randomPermutation_map_eq_pi 的输入逐一满足，且 samplePath X=id；推出整个 joint revealLaw 的 randomReorder map 等于 P。有限离散 permutation 的分段可测性与逐坐标评估支付 randomReorder 联合可测。没有仅把固定 σ 的 iid marginal 身份冒充 product-seed map law。

114–124 行先从 D0 的真正 Integrable 取得其对 P 的 AE 可测，再用精确 map equality 将它放到 map randomReorder revealLaw。IdentDistrib.comp_of_aemeasurable 因此合法，integrable_iff 和 integral_eq 分别搬运可积性及积分，最后由逐点 hEq 得到目标 D。两个方向及 AE 的底层测度正确，未用非可积函数默认积分。这段不需要 hReflection/hRegular/hSmall，也未暗加目标 E/map/integrability 输入。

## 公开证明完整复核：源 127–360 行

185–201 行先选 CH、CI(Csmall)、CT，再令 CB=CH+CI、C=3CB+3CT。C>0 且仅允许依赖先量化的 Csmall；选择在 Brownian law、rho、n、x、mask 之前。sigmaSq/scale/normalizedLaw/R/h 与全部 producers 相同，已验收 geometry 给 0<R≤1 和 h>0。未要求第三矩、连续律、原子消失或 n≥4。

202–226 行单独处理 x=0：sourceAlive 包含 prefix0 的严格 Interior 检查，三域均矛盾，所以 Vinitial、Afinal、O、raw remainder 全部逐点零，initialGap 与 masked quantity 也零。split_ifs 覆盖所有 rank/active/dead 分支，可积性由零函数直接支付。227 行以 x≥0 且 x≠0 得 x>0 后，才调用旧 positive-x transfer。

228–245 行按 J 的三个分支建立同一 FY 的数据。upper/lower 直接消费同一 Q 的 actual halfline 数据；interval 使用实际 intervalDerivative Q 和 hRegular，将 Interior interval 的两个严格不等式通过 abs_lt 转换，不改变范围。共同 derivative bound 为 4，event kernel 为 F J。hnum 是实际 cutoff 的可测性，hnu 是同一人口的 reveal stopping rank，cap 为实际 ν=κ_h 的反身界，没有 iid 自然滤过停止假设。

246–273 行先从 parts integrability 支付每个 J/r 的 L、O 真可积，有限绝对和 LA 真可积。interval negative sum NN 的可积性通过 max(-O,0)=(|O|-O)/2 的逐点恒等式建立，并完整分 0≤O 和 O≤0 两支。这确保随后拆积分不是对未证可积量作形式运算。

274–293 行把两半线联合界 CH R 与 PR302 的 interval 联合界 CI R 对齐。F/FY、wall、endpoint、ν、R/h 和 raw state 均相同。Finset.sum_add_distrib 与 integral_add 使用已付 hLAi/hNNi，真实得到 generic transfer 所需的四积分 B≤CB R；未遗失 interval negativeO，也未各自重复使用同一 CI 预算。

294–308 行对任意 J 用已证明私有引理给真正 E discrepancy 的 Integrable 和 CT R²。G 仅使用 le_max_left/right 给两个完整半线初值差≤literal initialGap，结论仍带该值。three-domain transfer 的每个输入：概率测度 P/Q、FY joint measurability、共同非负 derivative bound、实际 HasDerivAt、x>0、h>0、同一 measurable reveal stopping rank/cap、B、逐域 E 和半线 G，均已逐项真实支付。没有把待证 B/E 重新藏成新前提。

309–327 行只在 B/E 全部获得后用 0<R≤1 推 R²≤R。CT≥0 保持乘法方向，CB R、CT R 非负，故旧结论 B+E+G、3B+2E+2G 分别被 C R+initialGap、C R+2initialGap 吸收。rawAbsolute 的真可积性先由 (L+O).abs，再用 selected remainder decomposition 的逐点等式并有限求和得到，未从积分上界倒推出可积性。

328–360 行对每个 measurable |m|≤1 的 mask，先调用 source_stopped_integrability 的常数停止秩 n；此可积性步骤无需 permutation invariance。用排列终和/全能量保持得 T_n=0。alive 分支有 wall>0、严格 endpoint interior，reachable completionExt(w,z,0,z)=1；dead 分支两侧零，故 sourceValue_n=Afinal 逐点成立。乘以 m 后由既有真可积函数作差和代数恒等式得到 masked final-minus-initial 真可积。最后数值界仅在调用 generic masked transfer 时使用完整 PermutationInvariant m，常数由 3CB R+3CT R²+2G 吸收。没有 weighted Brownian marginal 比较。

## 全部实际所属 TYPE / VALUE / AX 覆盖

原 OwnedAudit.lean 完整读过。它按 env.getModuleIdxFor? 的精确 owner 选择，不以 namespace 前缀筛选；对每个 owner 调用递归 Lean.collectAxioms 并逐名拒绝白名单外公理。全四个常量与审计 JSON、原 log、完整导出的名字集合一致，非人为 source declaration 数量猜测。

| 实际名字（共同前缀 Shao.Probability.SourceActualTransferAssembly） | 完整导出行 | 审查覆盖 | 递归公理 |
|---|---:|---|---|
| actual_brownian_transfer_with_initial_gap.match_1 | 1–15 | 全 TYPE、全 VALUE | 空 |
| labelPermMeasurableSpace | 16–44 | 全 TYPE、全 VALUE | propext, Classical.choice, Quot.sound |
| actual_brownian_transfer_with_initial_gap | 45–764 | 全 TYPE、源中每个证明分支 | 同白名单三项 |
| _private.Shao.Probability.SourceActualTransferAssembly.0.Shao.Probability.SourceActualTransferAssembly.actual_terminal_reveal_budget | 765–1030 | 全 TYPE、源中每个证明分支 | 同白名单三项 |

所有 1030 行已原样分段完整读完，没有使用摘要代替类型或省略 dependent let/instance 值，也没有把省略打印当完整覆盖。每个 block/TYPE/VALUE 的精确 SHA256 在 coverage JSON。local 实例的全值确为离散 top measurable space；展开类型内旧 reveal module 的实例也为同一个 top，可定义相等，未更换 product seed 的可测结构。生成 match_1 的全值是 MonitoredDomain.casesOn，依 upper/lower/interval 选择相应三个分支，无额外假设或隐藏定义。两定理证明已在生产源完整读过；没有另行膨胀打印 tactic 生成证明项。

源静态扫描无 sorry/admit/新增 axiom/unsafe/native_decide。四名的递归 AX 全在 propext、Classical.choice、Quot.sound 白名单内；没有新增研究公理。

## 边界攻击与准确剩余范围

n=1 在原预算与 terminal 第七头的 n>0 全域内，只有 rank0；本装配没有 n≥4 的暗分支。n=0 明确不属于当前声明。总体有限二阶矩正并不排除单个 population 的 raw energy=0；该情形 sourceAlive 的首项假，所有相关源值及余项逐点零。随机剩余能量为零时，重排相等保留 reachable same-endpoint 约定；终点识别显式支付 T_n=0，不将非正时间误作正时间 kernel。

κ 使用首次严格 T<h，故 T=h 仍在 selected ranks；双向 cutoff 证明完全使用同一严格谓词。small-energy 判定保持 beta²≤T/2，等号没有被丢弃。crossing 的闭墙、endpoint 恰在墙上、旧 hit flag、外 endpoint、零增量及重复坐标值均保留原 definitions；σ 置换的是 distinct labels，不是按值去重。未用无原子性把严格生存改为闭 CDF。

尤其 x=0 的逐点零只说明 sourceAlive 含 prefix0 的对象为零。原 main 定义的单侧最大值取 1≤k≤n；例如 n=1、a=-1 时正秩 upper survival at wall0 可以成立，而本 sourceAlive 因 prefix0 不成立。因此本结果不能直接充当该原单侧 x=0 事件的识别或初值支付。interval/闭 CDF/归一化零能量的最终根事件仍须对应的真实消费者。

本次 E 只对公开 let ν=κ_h 组装；不扩张为所有更早 ν≤κ_h 的相同终端 CR²。原一般 H≥h、tau=κ_H∧(n-m) envelope 的更广范围由旧已合格第六头负责，没有在这里重述或窃取其全部范围。literal initialGap 的 CR 支付、实际 halfline reflection、interval regularity、全 beta/闭未来 small Taylor 与任何未支付物理 kernel 识别仍开放。已给前提下的本冻结定理证明完整，故这些未付原根接口不构成本冻结弱结论的关键缺口。

本工作是原文 transfer/paid/terminal 的源绑定辅助装配；未作数学新颖性、整篇原根闭合或订阅额度百分比声明。最终裁决 CORRECT；零关键缺口，接受范围严格限于上述精确源和冻结合同。
