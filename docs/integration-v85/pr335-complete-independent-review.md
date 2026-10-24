# 独立完整终审：原始 C1 全域相对误差

STATUS: **CORRECT**

本结论只认证 SHA256 `9fb2a134affb98aafead8012d9975e6b2de273fff7c2796867fb54b4b6af3b14` 的 [SourceOriginalFullRelative.lean](<C:/game/shao lean/drafts/c1-original-full-relative-production/SourceOriginalFullRelative.lean>)。已完整阅读全部 333 行、唯一公开定理的全部证明、全部 16 个实际所属常量的完整实际类型，以及全部必要消费接口和透明值；未发现关键数学或证据缺口。独立复核既有服务器 check04 成功工件，没有新增 Lean、导入测试、公理审计或旧证明重放。此报告由非作者新鲜上下文 `/root/original_full_relative_final_review` 完成；作者为另一个上下文 `/root/true_energy_strip_author`。

## 精确对象与冻结

源为 17833 字节、333 行、UTF-8 无 BOM、LF。逐字比较的是整个冻结上下文和完整数学头，不仅是定理名：注释、5 个 imports、options、section、namespace、open 和完整量词/12 个 literal lets 均精确匹配。冻结文件 SHA256 `2600b578ae63f6251ad547eb35ad038d4bd3be358773188c9459b91e39743a48`；冻结说明 SHA256 `73aca8fa7928731682402980c6928a1ef486ffb8a15024d0ee53961bb52eb098`；生产 activation SHA256 `b373c474ce9d944dcc206ee72d77015e7c2edc997db4eabfa211f08803839133`。`Elab.async false` 和 `maxHeartbeats 5000000` 已在 body 前批准。唯一公开定理，无源码 definition、global instance、private helper。禁用词扫描为空。

activation 为 2026-10-24 20:16:51 UTC，作者实际 ACK 为 20:17:51 UTC，早于服务器首个失败源快照；前三个失败快照也保留相同完整冻结头和完整 namespace 结尾。作者 RELEASE `f6cd460223e3ad504e5b47c22cca7cdd835bd3decfdaf60898b34aec5ed0b4be` 的 47 个绑定文件逐项按真实字节数和哈希验证，共 48 个作者工件保持原字节。作者 source-writer/target-execution 均已释放，target/pending operation 均为 0。

## 原题到形式陈述

已直接核对只读 `C:/game/shao/current/c12/main.tex` 的 150–207 行。原文件 SHA256 `beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，摘录与真实行区间逐字一致。目标是原稿 199–207 行 one-sided relative error，包含另一符号；不是增长子域或有限样本身份的替代结论。

1. 数值常数 `C` 在 `rhoStar`、`p`、任意原概率空间/原律、`n`、符号和 `x` 之前。`rhoStar` 是同一给定的 `0 < rhoStar ≤ 1/16`；未另取辅助小常数改变定义域。`2 < p ≤ 3`、有限 p 阶绝对矩、中心化、有限严格正二阶矩、AE 可测、独立及相同分布均完整保留。二阶可积与概率测度也保证原一阶矩确有意义，无总积分默认值漏洞。
2. `samplePath X` 的坐标就是原 `X i`；`upperMax` 是 `Finset.Icc 1 n` 上的实际 `prefixSum` 最大值。`s • population` 是逐坐标乘以 `s=±1`，故两符号分别是原 `M_n^+`、`M_n^-`，无空前缀。`rawEnergy` 是原平方和，未换成确定方差或归一化能量。
3. `sigmaSq=∫z²`、`sigma=sqrt sigmaSq`、`scale=sigma sqrt n`。真实归一化律是原律在 `z/scale` 下的推前。消费的 `truncationF z=z² min(|z|,1)` 与 `truncationBudget ν n t=n∫F((1+t)z)dν` 给出原 `R_n(t)`。`Ln` 的分子、两个分母及指数均是原定义；正方差、`n>0` 和有限 p 矩使其为正常正数。原域恰是 `t≥0 ∧ (t≤Ln^(-1/p) ∨ Rn t≤rhoStar)`，未缩成纯 moment window 或辅助律域。
4. weak crossing 是 `x sqrt(rawEnergy) ≤ signedMax`，strict survival 是反向严格不等式，墙上等号和 all-zero 样本被 crossing 保留。结论给出两指标真正可积、实际 `P(Q_n=0)` 的 Gaussian 尺度成本、两事件绝对误差以及原 `|P(crossing)/Psi(x)-2|≤C Rn(x)`。无额外 target probability、HasLaw、integrability、Brownian existence/FDD/continuity 假设。327 中的三项 HasLaw 是其输出，本定理未把它们搬到前提。

## 完整证明判断

**常数和量词（61–73、195–220）。** 从已合格 327 与 331 取得严格正的普适 `Cc,Cg`。取 `Ck=(Cc+16)/Psi(1)`，`C=1+Cg+Ck`。`Psi(t)>0` 对每个有限实数成立，故 Ck/C 正，且 C 同时支配 Cg/Ck。选 C 在引入所有原参数前完成。`original_raw_normalization_data` 在原假设下提供真实 ν 的二阶可积；据此取得 Rn 的非负性，未把预算符号或单调性当作无证明前提。

**Brownian 边际（75–194）。** 证明内部使用已接受的具体 `CanonicalBrownian.Sample/law/B` 和真实概率实例、无前提 `isBrownianReal`；对于负符号使用实际 Brownian 的 neg 闭包。抽象 `IsBrownianReal` 结构本身没有被误作存在性。`S` 是整个 `[0,1]` 的严格半线生存事件。

当 `x=0`，在 `B0=0` 的同一 AE 事件上取 t=0，S 不可能成立，直接得到 `PB.real S=0=1-2Psi(0)`。这里没有声称原离散正前缀生存事件为空。

当 `x>0`，对每个 `v<x`，令 `J=S∩{U1≤v}`、`E={v<U1<x}`。消费 qualified311 的真实 joint reflection 得 `P(J)=1-Psi(v)-Psi(2x-v)`。实际 `hasLaw_eval 1` 与 Gaussian Ioo/Ici 不交分解给 `P(E)=Psi(v)-Psi(x)`；开闭端点的转换由已合格 Gaussian tail representation 支付。`J⊆S⊆J∪E` 给出上下界。Gaussian tail 的实际可微性给连续性；沿非平凡左邻域 `v↑x` 两界共同收敛到 `1-2Psi(x)`。所有 real-measure 比较的有限性由概率测度满足；没有要求 S 在一般 AE 空间处处可测。没有重证明 reflection 或引入未付 Brownian 极限前提。

**紧窗 `0≤x≤1`（221–285）。** `sqrt(n sigmaSq)=sigma sqrt n` 的确定恒等严格对齐 327/299 所用归一化律与本头 ν。调用 327 时所有原 AE/iid/矩条件及具体 Brownian 条件均满足；从其正确的 conjunction 位置取得 survival 指标可积及 `Cc Rn(0)` 误差。299 的 `16 Rn(0)` 是真实零最终能量成本。真实 ν 二阶可积给 `Rn(0)≤Rn(x)`，且 `Psi(x)≥Psi(1)>0`，从而 `Cc+16≤Ck Psi(x)`。逐次乘法使用真实非负预算和正尾概率，得到 compact error 与零能量成本均不超过 `C Rn(x)Psi(x)`。这一步只用于紧窗。

**任意原 AE 空间的互补与相对化（286–321）。** crossing 指标逐点等于 `1-survival.indicator`，所以由 const-integrability 与已证明 survival 可积得到 crossing 真正可积。survival 又逐点是 `{1/2<survival.indicator}`，由 AEMeasurable 原像得到 NullMeasurableSet；因此有限概率测度的 `measureReal_compl₀` 合法给 `P(crossing)=1-P(survival)`。绝对误差借负号保持；最后以处处严格正的 `Psi(x)` 除法得到相对误差，未引入 0/0 或原空间完备性假设。

**增长分支 `x>1`（322–330）。** 直接消费 qualified331 的原域、相同 12 个 lets、相同原律/样本/两符号和 Gaussian-scale Q0/误差/指标可积结论。调用只把 `x>1` 放宽为其所需 `1≤x`，域证据就是原 hI。由于 Cg≤C 且 Rn≥0、Psi>0，各结论可以增大常数。没有用紧窗 `16 Rn(0)` 冒领增长域相对误差信用。

## 边界和范围

`x=0`、`x=1`、`n=1`、原子律、墙上等号、零能量、闭域端点、负符号和任意不完备原概率空间均受到上述论证覆盖。尤其 `x=0` 时原 `signedMax<0` 可以非空；它由 327 的原正前缀比较支付，未用带时间零的最大值篡改。`x=1` 由紧窗分支覆盖，与增长分支无缝。`Q_n=0` 时有限平方和全部坐标为零，crossing 的乘法约定正确保留该样本。没有全局三阶矩、无原子、处处可测或额外 Brownian 轨道前提。

只认证这一精确源对原 C1 两符号全域目标的数学忠实性和证明。没有增长域 endpoint-joint 结论、C2 双墙/导数/反演/原律返回结论或新颖性声明；既有 Gaussian/Brownian 外部事实归属于实际 Mathlib/已接受 Shao 模块。C1 原 scope 的正式验收与集成由 Root 决定；C12/C2 和 OQ56 仍 OPEN，OQ3 保持 PAUSED_BY_USER，OQ4 仅其另外验收的限定原范围。

## 旧证据的准确复用

已读完整必要接口和 literal values，并逐字绑定到实际 source，不重审旧 proof。327 原源 `ac13f6b2…46cfb` / 原 producer13 `fbb57b7d…b37af`，331 原源 `44882c03…d50a4` / 原 producer05 `af7315d5…eebc`，299、311、真实规范 Brownian 的既有完整独审/原对象/递归公理资格均核对。11 个必要 accepted 源与不可变 v84 source map 精确一致。331 的 Root 资格允许 source-bound consumption，但 `integratedInMain=false`，所以 PR331 必须在 PR335 之前或同批集成。

CanonicalBrownian 的 v55 独审收据 `e1fc5184…e62b` 明确覆盖 1123 源行、112 个完整实际类型、17 个透明值及实际 Prop 概率实例完整值和所有递归 AX；原对象收据 `265f7990…bb65` 绑定 `220e2302…9d24`。本轮读其必要具体对象/值/头而复用上述完整证据。服务器实际消费的 CanonicalBrownian 与 311 对象字节分别匹配已合格原对象 SHA256，未重新发射。全部精确全哈希和依赖明细见 `interface-binding-verification.json`。

## 原服务器 kernel / 类型 / 值 / 递归公理

物理只读验证的 Git HEAD `4773103cc202c3a9c12b1dfb092a39275e866438`、tree `68183d1f60f000956b1abb0ee3f284bc95291247`，相对 acceptedv84 `b4b38311e57fd57f721fb14fd5ab3f07f42a6ead` 仅增本源。tracked worktree clean。GitHub 连接器也独立观察 [PR335](https://github.com/randomcat4/shao-lean/pull/335) OPEN/unmerged、同一 head、1 个新增文件/333 行；未合并或发布评论。

唯一完整成功 check04 的 kernel_rc=0、audit_rc=0；原对象 `producer04.olean` SHA256 `120612e9a6ce6ba95ce5b36d809ba3c1d5e676312c2460840a04e9f395b18b52`。现有 import 路径与该原对象物理 samefile，原 check04 收据/同调用审计收据、原 kernel/audit 日志、源快照、实际 audit driver 和所有紧凑导出均在服务器逐项哈希核对。kernel log SHA256 `f54445bb623d4926b919f368743d9e6886960f99b33057caf64eec560754bb82`，audit log `10206803ac2ac585b140ea492c90e7eb153089b199c4502452b88cc15f3387e9`。日志中建议性 `ring`/deprecated/linter 消息不等于错误，实际退出码及完整目标对象为成功。

审计程序完整读过：按 `env.getModuleIdxFor?` 选择实际模块 owner，遍历所有 namespace/private/generated，无前缀过滤；逐 owner 调用递归 `Lean.collectAxioms` 并拒绝非白名单公理；对全部 owner 输出完整 TYPE，对所有非 theorem 尝试完整 VALUE。真实结果是 16 theorem、0 definition、0 non-theorem。`all-owned-types.txt` 35623 字节，SHA256 `3248ad2494c711039fc094e03fd454b272dbe2ea90ee3842bd048f672b1f3a75`；16 块均已完整逐项阅读，逐项字节/类型哈希与 owner index、原 audit log 无损匹配，零省略。0 VALUE 的实际 inventory 是明确的 `ACTUAL_NON_THEOREM_OWNERS 0 / NO_NON_THEOREM_VALUES`，不是未提供值。结构化报告逐 owner 记录完整类型阅读、语义判断和全部递归 AX。

15 个 generated `_simp` 的数字有空缺，未用最大后缀推算数量；它们只表示实际证明产生的集合成员/补集/区间、AE、双重否定和非零算术改写。其完整实际类型均为这些合法通用等式/命题，未夹带原目标前提。公开定理及 `_simp_1/_simp_2/_simp_17` 的递归 AX 是 `propext, Classical.choice, Quot.sound`；其余 12 个 generated 只有 `propext`。所有 AX 都在白名单内；未新增 axiom，无 sorry/admit/unsafe/native_decide。

check01/02/03 的真实源快照、日志和 rc=1 均物理核验并保留，无 producer01/02/03 对象，无 PASS/AX 信用；失败分别涉及 tactic 残留目标、符号和端点匹配/多余 tactic。作者 metadata-export 的首次 regex 断言失败只属提取，不是数学或 kernel 成功。本审查也保留一次只读 regex 检索失败：原 AX 列表会换行，修正确定性匹配后完成无损核对；另一次本地旧 head 检索把 `where` 误按 `:= by` 查找，修正提取边界后通过。两者均未改源、对象、旧证据或执行 Lean/AX。

钉死环境为 Lean `leanprover/lean4:v4.36.0-rc1`、Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`；实际 worktree manifest 与 Mathlib HEAD 一致，read-only packages 为 shared-v34。所有 raw 日志/二进制仅留服务器。独立物理审查、接口绑定和报告生成均为轻量只读或本审查目录写入；没有重型命令、资源 lease 扩张或其他 lane 写入。

## 交付与实际状态

配置模型/effort 是明确的 `gpt-6.1-sol` / `xhigh`。实际平台 model/effort 遥测不可见，记录为 null；input、cachedInput、output、reasoningSubset 均 null，未推算订阅百分比分配。新 Lean=0、新 AX=0、旧 proof 复审=0、原作者文件改动=0、remote mutation=0、派生 agent=0。此审查的下一依赖是 Root 对精确报告的验收及 PR331/335 集成决定。独立审查完成后释放自身唯一审查目录写入权，实际服务器 in-flight=0、pending operation=0；不以最终回复宣称持续运行。
