# Unit188 repair01：同一独立审查员的完整改变证明审查

STATUS: SOURCE_REPAIR_REVIEW_CORRECT_NATIVE02_RC0_PENDING_ALL_OWNED_EVIDENCE

审查员仍为 `/root/oq56_row188_final_review01`，非作者；实际 runtime-ACK 已写入本新目录。旧完整源码审查及其最后 RELEASE0（00984fc231e66a2f14d95dbd1a55b50ac6eb825fb347379356c143534e7221b3）保持原字节。当前只写 `final-review-01/repair01-and-server-evidence/`，未修改旧审查、作者源、冻结或其他协作者文件，没有并行修复证明。

本轮已完整读完修复稿四个改变后的完整证明，而非只读 diff；并读完完整 repair proofnotes、12 个实际 patch hunk、更新的作用域及新增完整 API/ambient。就本精确源码的数学论证、原题语义和冻结作用域，未发现关键缺口。封包期间收到并已读 native02 的精确源自然 Lean RC0 和对象回执（见末节）；unit188 实际 owner 包仍未到，因此尚不能标记最终资格：`qualified=false`、`actualOwned=UNKNOWN`。原 native01 的 RC1/19 errors/12 warnings/无对象证据原样保留，本源码审查不消除它。

## 精确字节、补丁和输入

repair01 源 SHA256 `0b7f38c8840ffefb15fc9185c8f54c2c6907da96cc49bd5e7ee3c5ed512250fc`，38651 字节、569 LF、0 CR、无 BOM、严格 UTF-8。作者 manifest SHA256 `3882b9f29b7e9b9d89e2b59291a0f72a8ae1c42fda6d058ecfa6f9309737879b`、RELEASE0 SHA256 `e827a4e0b386c19e62e6d34ce685a14a81cbae91e9d4c734b04386ebf52ac31f` 已独立重算。

独立静态验证从旧不可变 1ac13836 源开始，在内存逐行检查旧上下文/删除行及每个 hunk 的新旧行数，应用 proof-only.patch 全部 12 个 hunk。重构文本与候选逐字相等，SHA256 精确为 0b7f38c8…；没有把重构源或 stdout 写入工作区。patch SHA256 `e1aa18c97a2042b17ba5fdc9b5e47838e6e2b7636a99d584972f15864a9ee48f`。独立逐块比较确认仅 canonical_ghost_mean、norm_integral_rpow_le_integral、ghost_row_qmoment_bound、canonical_row_qmoment_bound 四个 proof owner 改变；5 个定义及 pairSamples_measurePreserving 整块原样。

manifest/input-hashes 及本轮要求的 manifest/new-release/old-review-release 共 54 条文件绑定重新计算，哈希与提供的字节数全部相符。完整前缀、后缀、10 个声明头、5 个全局定义原值均精确冻结一致。源码自行扫描得 53 条 let/letI，全部类型与值都与 base46+amendment7、旧实际源码和更新 actual-scopes 一一对应；无额外 let 行、全局 helper/private/instance/macro/attribute 或禁止 token。30 个冻结声明/定义嵌入表达式所在的完整头/值完全不变，其原完整阅读与作用域审查可复用；未以有宏记法缺陷的 literal-substring matcher 判定数学缺口。

53 项有名数据的 ordered nested binders、附加 typed outer binders、可见数据祖先与旧 source scopes 逐项精确相同。更新 sourceLine 亦与修复稿实际行吻合。静态比较见 patch-and-input-validation.json、freeze-scope-validation.json。

## 完整四个改变证明的审读

**canonical_ghost_mean，修复稿第 40–273 行。** 完整重读包括未变的坐标独立性、真实边缘、全部四角保测、原/鬼坐标和向量 L1、good 满测集合、异索引双鬼积分和完整 Bochner 均值。四个角现在各自在 i,j,hij 下取 hfi/hfj，从正确的 fst/fst、snd/fst、fst/snd、snd/snd 实际边际 map_eq 出发，与 hjoint 一并展开 Function.comp_def/pairedEval，再实际改写边缘并展开相应 corner。它们仍只在 i≠j 分支消费坐标独立性，不涉及 r(a,a) 或产品 AE 的对角拉回。

第 138–150 行 hGhostEntry 先合成四角真实 L1，再用 Integrable.congr 给 AE 点态等式。该等式在 z 下将已有函数真正应用后，展开 Pi.sub_apply/Pi.add_apply 和四角冻结值，得到与 ghostEntry 完全相同的四项差。没有换用只需范数相等却欠缺可测性的 congr' 版本。第 206–220 行 hSectionEntry 同理：固定 AE-good x 后已有 hconst、两条真实可积规范截面 h10/h01、异索引产品项 h00；congr 的 y 只属于该证明的点态 AE 作用域，不能泄漏为 frozen sectionGhost 的新参数。

第 183–185 行产品 Fubini 后显式展开 Function.uncurry，使积分与 hcR 的真实嵌套积分一致。第 221–243 行非对角截面均值先把 h10/h01/h00 的 composition/uncurry/eval 展成实际截面，再从 integral_add/sub 取得三个完整线性等式，展开它们的 Pi 运算后重写目标。每个差和的 L1 由既有真实 L1 支付。两条 h10Integral/h01Integral 只取既有 hEvalIntegral 在相同 x 下的具体结果；规范左/右零均值分别使用 hx j 的左截面和 hx i 的右截面，双鬼项仍用 i≠j 的产品法则。原行与鬼行的有限标准基 L1 提升及第 261–273 行完整向量积分重建原样成立。所有 x 的均值结论仍是 M-a.e.，未强化为逐点。

**norm_integral_rpow_le_integral，第 275–317 行。** 完整重读 b=1/q、凹半线、连续性、两个真实 L1、Jensen、Bochner 范数积分界及最终幂互逆。hInverse 与 hconcave 现在显式经 Real.rpow_eq_pow 对齐实际主源记号。新增 hpowerNonneg(a) 是 `powerNorm a ∈ nonnegativeHalfLine` 的普通 Prop 证据，由原范数非负和实际实幂非负支付，不是额外参数。Jensen 明确 `f := powerNorm`，而且 hjensen 给出完整积分结论类型，因此同一冻结函数而非推断出的另一个记号表达式接受 hpowerInt/hcompInt。概率、闭集、凹性、连续、AE 值域与两种 L1 的全部条件均由原推导满足。最终 change 仅显示现有 powerNorm/inversePower 别名，然后桥接并使用 q*b=1；没有改变 q≥2 或增添非零积分前提。

**ghost_row_qmoment_bound，第 319–483 行。** 完整重读最前的确定性 √n 界、全部权重恢复和可积性、187 范数律、有限符号平均外积分与 186 最终常数。hDeterministic 及其 columnNorms 数据、顺序和捕获原样，仍只用于实际可积支配。hRecover 先桥接再去除 max 和使用非负实幂互逆；S≥0 来自平方和。S≤1+S^q 两个分支把目标先归一化为与主源 rpow_nonneg/self_le_rpow_of_one_le 相同的表达式后做实数比较。recoverPower 的连续复合、S 的 AE 强可测及 L1 恢复仍在没有 w 可测或 Ω 拓扑条件下支付。

全一及每个固定符号的 q 次幂可积性仍先取得真实可测性和 `(√n)^q S^q` 的真实 L1 支配，桥接后绝对值/单调/乘积幂的 calc 使用同一 `^` 表达式。冻结 signedPower、dominatingPower 和各个测度均未变。第 437–462 行固定符号真实推前律及有限求和积分完整读审；所有交换仍先有实际 L1，Bool 路径数与 2^n 正好抵消。第 463–475 行 cubePower 非负和 AE 包络继续支付 186 的精确界，桥接仅用于取幂互逆；最终常数仍恰为 2√q，不含 √n。未除以 cubePower、S 或能量。

**canonical_row_qmoment_bound，第 485–565 行。** 完整重读真实 pairSamples 保测、乘积 q L1、Fubini 的 AE q 截面、完整鬼均值 AE 事件交、向量 Jensen、rowQ 的 AE 可测/L1 支配、产品积分运输及最终矩根。新的第 564 行只显式桥接 K 的二重实幂，随后原 K≥0、q>0、q*(1/q)=1 支付互逆。A/B 仍真实非负积分，B=0 或 n=0/1 时不作除法。与旧稿相比，没有把最终行矩、外积分相等或 Jensen 作为输入。

## 新 Prop 证据与无隐藏数据的检查

hfi/hfj 是各自角分支内已证边际 map 等式的证明；hAddIntegral/hSubIntegral/hFirstSubIntegral/h10Integral/h01Integral 是固定 AE x 和非对角 i,j 分支中的积分等式证明；hpowerNonneg 是 proof-local forall a 的命题。新增的 z/y 由 Integrable.congr 的 AE 等式局部引入。这些全部取值于 Prop；没有新增函数数据初始化式、测度、选择器、实例、私有辅助声明或结论性假设。

good 的四个 b 继续是 a 下相互独立的 sibling；两个 instMM 坐标族继续独立；第 205 行 sectionGhost 仅处于 AE-good x/hx 祖先下，第 512 行 sectionGhost 仅处于 AE-mean/q-L1 x/hx/hxq 下。第 327 行 columnNorms 位于 D/W/u/hW0/hD0/hu 子证明内，仅实际捕获 n,D，仍在其后其他局部数据引入之前。原 9 个概率 letI 的完整类型和值逐字不变，没有为了清理 warning 改实例。

## 新增实际 API 的完整头、ambient 及付款

本轮读了 interface-calls 新增的四个完整绑定，并直接回到其绑定的原始 source 文本核完整头和相关 ambient。重新编码这些完整原始文本所得 SHA 与固定 source SHA 精确一致，完整头在原始文本中逐字存在；sourcePacket 自身 SHA 也与绑定一致。细目见 additional-primary-validation.json。

- Real.rpow_eq_pow：完整声明为 `@[simp] theorem rpow_eq_pow (x y : ℝ) : rpow x y = x ^ y := rfl`。实际 Real namespace 与外层 noncomputable/public section，显式 x/y 无额外正性、非零或样本拓扑条件。rpow 定义与 Pow ℝ ℝ 实例已在旧源码阶段完整阅读，本轮核与新调用相同的精确主源绑定。它适用于冻结 literal Real.rpow 到主源 `^` 的证明转换，包括零；后续逆幂仍使用明确非负底数和 q>0。
- MeasureTheory.integral_add/sub：完整头仅以两个真实 Integrable 为线性条件；活跃 `{α,G,m,μ}`、NormedAddCommGroup G、NormedSpace ℝ G 在本单元 G=ℝ 均具备。hconst/h10/h01/h00 及已知差的真实 L1 支付所有调用；将函数运算应用到样本再化简保持原被积函数。
- MeasureTheory.Integrable.congr：完整头 `Integrable f μ → f =ᵐ[μ] g → Integrable g μ`，实际 codomain ε 具有 TopologicalSpace/ContinuousENorm；本处 ε=ℝ。不要求原样本 Ω 有拓扑，不另索取 g 的可测性。两个新调用均先有 f 的真实 L1，后给明确逐点 AE 等式，符合该强同余版本。

其余已绑定并在旧报告完整审查的 API 和 185/186/187 精确资格源均无数学变化，继续复用旧独立证据；本轮没有重新审 producer 证明或执行其检查。完整真实 EuclideanSpace、两条 AE 规范边际、仅产品 AE 包络和 S^q 实际 L1 的源作用域、p54 修正及外部 Shao–Zhou 归属均无改变。

## 旧失败和当前证据边界

原 native01 的结构诊断 SHA256 `3a5274fe3d1664a29cc29dbd1eaaab019e0397261aab140f921a5bd98e4c0073` 及审查员旧 native01-failure-intake 保留。作者逐项 19 条 disposition 只是 SOURCE_REPAIR_PROPOSED_UNCHECKED；本完整数学/source 阅读亦不能使原失败变为成功，12 条 warning 不应通过改冻结字节或禁用检查来消除。

当前没有发现应退回作者的数学或冻结作用域缺口。新 0b7f38c8 精确源的实际 native02 RC0/对象与保存摘要已在封包前收到并完整读取，随后仍须由本同一审查上下文审读实际源 owner 发现得到的全部完整 TYPE、所有非定理 FULLVALUE、private/generated 和每一项递归 collectAxioms；不得 namespace 过滤、猜 actualOwned 或以源码 10 heads 代替实际数量。若后续实际 owner 检查失败，精确失败必须保留，受影响的实际改动再续审。

当前 reviewer Lean/server/network/Git/cache/upload/children/heldLocks 均为 0。请求模型/努力为 gpt-6.1-sol/xhigh；当前上下文不可见的实际模型、努力和 input/cached-input/output/reasoning-subset 一律 null。C2/C12/OQ56 继续 OPEN，OQ3 继续 PAUSED_BY_USER；不扩展为 scalar F、尾界、DC、root completion 或新颖性结论。

本源码修复审读阶段完成后释放为 SOURCE_REPAIR_REVIEW_DONE_RELEASE0；普通回合结束不等于持续后台执行。机器包到达后由父级继续同一独审，无需另派第二次完整旧证明审查。

## 封包前收到 native02：真实编译成功，完整所属证据仍待补

已完整读取 `lead-execution-01/author-kernel-02-native-summary.json`，重新核得 SHA256 `881abff3624078847e6fdd4ce661cea3fa513b372b21ec15f9db2b01a852e204`、8033 字节。它绑定实际输入 0b7f38c8/38651B，原 receipt SHA256 `2c39e90169c318fe5a1cfb4587be709dee04167f1c74a3e56a83ad5a1182f08b`。自然 Lean RC0、7.268890615552664 秒，生成对象 SHA256 `039bdc5ca03a7505762d852b8e6464c7f88de90c5b68914e6aaf6e6cb3a50d85`、834464 字节。

摘要中的 strictWrapperSuccess=false、FIRSTEMPTY=false 诚实保留，不改写成空输出机器门通过。13 条实际源码诊断全文均已读：9 条是冻结的 Prop 型 letI 样式偏好，4 条是未使用 simp 参数（WithLp.ofLp_toLp、eq_comm、Pi.add_apply、Fintype.card_fun）。没有 error、未完成证明警告或逻辑绕过提示。134B Lake stderr 对应原环境已有 local-changes 提示，精确 hash 在摘要中保持。警告不触发改冻结值、禁用检查或重新编译。

父级据此记录 manual AUTHOR-STOP SHA256 `1621225442631f30a3f8026db111286604c47fa834c809608270e3e46fe08cd6`，没有重编译 proof。进程组全结束，ownLean=[]，11206 条 FULLFP 精确保持且 gitExact。审查员只读该本地结构摘要，未访问服务器或重建 proof；实际对象的后续 import/source/owner 绑定仍需 all-owned 包核验。详情在 native02-intake.json。

因此修复源码现已获得精确自然编译 RC0/对象证据，仍不具备完整所属 TYPE/FULLVALUE/AX 终审。`qualified=false`、`actualOwned=UNKNOWN` 保持不变，等待父级正式继续同一审查上下文。
