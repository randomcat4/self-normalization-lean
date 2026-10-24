# SourceOriginalBrownianComparison 独立完整最终审查

STATUS: CORRECT

本结论仅针对精确冻结的条件装配定理。已独立逐行阅读正式源全部 417 行、唯一公开头全部十四个 literal let、实际七个完整 TYPE、唯一非定理常量的完整 VALUE，以及七个实际 owner 的递归公理清单；没有以作者的候选证明或成功日志代替数学审查。未发现关键缺口。实际 interval interior regularity 与 all-beta/closed-future small-step Taylor 仍是公开前提，C12/OQ3/OQ56 原根仍 OPEN，OQ3 仍由用户暂停。本次没有新 Lean、公理审计、旧 producer 编译、模型子代理或合并。

## 精确对象、独立性与冻结

审查者为新上下文 `/root/original_brownian_comparison_final_review`，非作者 `/root/permutation_reveal_candidate`。分派配置为 gpt-6.1-sol/xhigh；没有独立模型或 token telemetry 接口，input/cached input/output/reasoning-subset 均记为不可得，不把请求配置或订阅比例冒充用量实测。审查只写本目录，未修改正式源、旧源或共享协调文件。

正式源 `drafts/c12-original-brownian-comparison-production/SourceOriginalBrownianComparison.lean`：417 行、25087 字节，SHA256 `f050af357d4dcf0d877a78131d3210cc1fe5574584557ac9ab9673cf0ea35d8c`。PR321 head `b0df9b9f7ca8f0ba2bbcdb9ca0a07f91a69e148f`，tree `d6e45294b21fb0495b64565f50c176a341e5e07d`。唯一公开头与冻结 `e7dfd46f7202ad0c0fbb97274b2a241ad4eb839262b008d4c1d9056f3e3801a5` 完整逐字一致，十四 let 均保留；一个 local measurable-space instance 的值仍为 top，零 source def、零全局/private helper。仅执行选项增加 Elab.async false/maxHeartbeats。源为无 BOM UTF-8、LF，零 CR；未出现 sorry/admit/axiom/unsafe/native_decide。

冻结说明、激活、作者 receipt、RELEASE 和 publication binding 的实际哈希均与分派吻合，见 local-bindings.json。源开头“candidate only/initial dependency not qualified”是原冻结历史注释；其字节未被事后改写。当前资格以 17:33:24 UTC 的 PR318 Root qualification、17:36:07 的 production activation 和后续正式源/对象收据为准，不能用该旧注释倒置实际时间顺序。

## 原文到实际陈述

重新阅读只读原文 main.tex 的统计量 149–167、R 的定义 172–175、紧水平定理 233–243、最终装配 1131–1148，以及 supplement.tex 的有限二阶矩端点/零能量接口 3959–4027。源哈希与冻结 source-bindings 一致。实际 samplePath、prefixSum、energy、absMax、normalizedEndpoint、truncationF 和 truncationBudget 的定义值也已读取，并核对到合格导入对象的 sourceSHA256。

本头确实从原 Ω 上仅 AE 可测的同一 iid family 出发：均值零、有限且正二阶矩，n>0；保留原自然顺序正前缀绝对最大值、原平方和、原总和与 Q=0 时 W=0 分支。R 使用 X/sqrt(n sigmaSq) 的真实推前律，与原文 n E[z² min(|z|,1)] 一致。C=CT(Csmall)+CI+CS 在 Brownian 空间、原 iid 律、n、x、v 之前选择，未暗中依赖它们。

四个输出分别是严格生存和弱越界的边缘比较，以及每个实数 v 的闭端点联合比较；Brownian 事件使用同一个实际 B 在全部 BridgeTime 上的严格生存/存在时间弱越界。ae_bridgeNoise_eq 使这些事件与实际连续桥加 B1 的路径事件 AE 一致；Brownian 连续路径在紧时间区间达到最大值，因此与原文 M_B 的严格/弱约定一致。没有用独立另造的 Brownian 或标量概率替代目标。

## 新证明逐段审查

- **1–74 / 75–92：**导入、local top 值、完整冻结头与常数顺序正确。CT、CI、CS 都先选择且严格正；Q 是实际 bridgeLaw，并由 hB 支付概率测度实例。R>0 使用同一 raw law 和正二阶矩，不增加原矩条件。
- **93–133：**AE 坐标可测性给 population 的 AE 可测性；iIndepFun 的真实联合 map law 与各坐标 IdentDistrib 将其推前为同一 product law P。hEvent 对 Borel 路径事件搬运概率。energy/M/W 均由 canonical Borel statistic 复合得到 AE 可测，无处处可测或 Ω 完备前提。sqrt(sigmaSq)*sqrt(n)=sqrt(n*sigmaSq) 将 scalar producer 的 R 精确对齐；B1 的实际标准 Gaussian law 支付同一全实 closed CDF。
- **134–165：**S 是原乘法严格生存 Borel 事件。原 Ω 上的事件用 AE preimage 得 null measurability；Brownian 事件由同一 `(bridgeNoise B,B1)` 的 AE 可测推前与全时间 AE 路径身份取得 null measurability。随后才作补集概率计算。两侧弱事件与严格事件的补集是精确逻辑等式，墙上等号未丢失。
- **166–191：**状态身份取自完整 qualified318 的全点结论。x=0 单独证明双方 strict 空、weak 全；弱联合仍用 endpoint closed-CDF 的 CS R。x>0 时 actual upper/lower formulas 以同一 B/PB/hB/Q 构成 HalflineReflectionIdentities，逐项对应其完整定义及显式指数式，公开头不再留下 reflection 前提。
- **192–239：**qualified314 仅消费实际 hRegular/hSmall。重排逐点保持 energy 与终值，因而保持 W 和 rawInitial；证明没有声称 absMax 保持。hAlive 的两个方向完整覆盖所有 k≤n：正前缀由 le_absMax 控制，k=0 用正墙，终点用全长重排和式；反向用真正 attained absMax。正墙推出 Q>0，故 Q=0 没有被省略。Afinal 的严格路径身份成立。
- **240–302：**lambda 是实际均匀 label law，eta=mu.prod lambda，Phi=(population,id seed) 是同一独立 seed 的 AE 联合推前。map_prod_map_of_aemeasurable 给 map Phi eta=revealLaw P；product iid 坐标 Y 满足旧随机排列定理的处处可测/独立/同律要求，其结论真正恢复 P。rank0 身份对每个 sigma、每个原 omega 使用 qualified318，而不是仅 AE 或任意 mask 因子化假设。hMasked 中 f 的真实 Integrable 来自314；A/I 的真实可积性另由 indicator 与 bounded rawInitial 支付。四个 integral_eq 沿真实 IdentDistrib/map law 搬运同一个积分，没有用不可积 Bochner integral 的默认零值逃避费用，也没有在原 Ω 上假设处处可测。本消费者沿精确联合推前搬运积分；旧生产者内的 Integrable/Fubini 资格复用，未另加未经支付的 Fubini 或期望交换前提。
- **303–332：**indicator 积分确为原 strict survival 概率；I 与原 rank0 全点一致。qualified318 的同一 Brownian marginal 初值误差加 CT R 给 (CT+CI)R；integral_sub 的两个被积函数均先证明 Integrable。weak marginal 的补集概率使用已支付的 null measurability，费用不增加。
- **333–384：**只实例化 canonical m_v=1_{W≤v}，其 Borel、界≤1 和排列不变性都已实际证明。两个 masked 被积函数先有 genuine Integrable，再作 integral_sub。乘积指标恰是 S∩{W≤v}；qualified318 的闭端点 masked 初值误差（含 integrability/原子约定）给 strict joint 的 (CT+CI)R。
- **385–417：**先用已支付 null measurability 的 inter/sdiff 恒等式，把 weak joint 写成 endpoint event 减 strict joint，再按三角不等式加 CS R。因而最终费用确为 CT+CI+CS；没有把 marginal complement 误当作 joint estimate。结尾仅关闭 namespace，无隐藏额外声明。

n=1 全部前缀和排列步骤仍成立；n=0 明确排除。重复样本数值不改变 distinct label 的均匀排列。Q=0 在 strict/alive/rawInitial/W 的实际守卫中保留，初值 Q0 费用由318/312已支付。W=v 的原子属于闭 mask，碰墙属于 weak crossing；全实 v 无删域。没有额外对称、密度、无原子、非格点、有界支撑、三阶矩或 target-error/target-integrability/pushforward 前提。

## 合格依赖复用

重读了这次使用的完整公共声明与必要定义值；旧完整 proof/TYPE/VALUE/AX/kernel 资格按精确源绑定复用，零旧完整证明重审、零旧成功检查重放。

- 314：source `42e2246229f09bb6b6c53276e0b1c7c249a07f1944173edfb92e0f2c7b1555b7`，original producer002 `3c1ad4cd4e797611d4b251c08f80833e9b2bfaa135cf88ac12c0419afacced37`，Root qualification `19f911c8ea319db8bbfb5577f6c8f415108bfc7e6b5258782c125dc9124ae9a6`。完整三域头的 mask 输出确实是 genuine Integrable 与 CR。
- 318：source `fe46483816c5314c459bc77e313b902d933c96a717bb1dea22e883951594fd29`，original producer02 `7df7b8749eb0e46fbd15799247e783ed381a03069ce1c2c2a6b1e90fd1f8284d`，Root qualification `1950ad38547e437a4b25d54061335b4d1cd463860cfe3ce9f3d344bc7cd99c16`。完整头提供每个 seed 的全点 rank0/原统计量身份，以及 genuine marginal/closed-joint integrability 与实际 Brownian 误差；其五个实际 owners 的旧完整审查资格保留。
- 312：source `2731effd3fbb3487bef30090699d675ce387d0258ad5a93800e9ba324330a459`，producer16 `84842cb7b9f3d085891172bd3fa1ba80c5e4ed8e37f2a4b885d3d6ba86af4d28`，Root qualification `de65a181861d5ba016636bc1cee91f64df9fd42cf1ce4a32f03ccabe755f9c36`。使用其第一个全实 closed-CDF 头，全部 literal lets 和尺度已核。
- 313：Root qualification `13a22518da01c5d29262a635fb08018651663337859ecc6ee2ade45bb22f0d94`。完整 bridge_upper_formula/bridge_lower_formula 的条件、同一实际 law 和两指数式已重读；两源分别 `8a91221945798ec1aefa956b8a5b51aa5edec9c47b0df5c55012958346a689b5` / `11c9d4e293b15a15b038b4df200c2eb716943861f8b42604faf7054987bac622`，原对象分别 `a21dbaf059cfade07ecb9e157a14bcb608040fb5b1e85d4ecfeaee8a2d921580` / `13e18d229916c53cad7216c0dd7565e6a93bf7eb92f91ca54dedb2ccb9e93ea4`。旧反射/CDF/affine 完整证明不重做。

## 全实际导出、公理与服务器原证据

完整直接阅读 `actual-owned-types-and-values.txt`（SHA `b22138f61f66a4be3f88457bfc8d22ce199bf8061513031e829e93b4fb7105f0`），输出截断的中段已定向补读；本模块没有采用结构摘要或省略类型。七 TYPE 是 public1、generated simp5、local instance1；完整唯一 VALUE 是 top 的实际 complete-lattice elaboration，没有额外条件。五个 generated 类型分别为交换 And、x<x=False、补集成员=非成员、¬∀=∃¬、¬a<b=b≤a，均为此次证明实际生成的辅助等式。

完整阅读 OwnedAudit.lean，确认按 getModuleIdxFor? 精确 module owner 选择全部常量，未按 namespace/public 过滤；对每个 owner 调用递归 Lean.collectAxioms，非定理 def/opaque 打印完整值，theorem 源证明由本审查完整阅读。七项的完整递归 axiom 清单均已读：四个 simp 仅 propext；simp_3、local top 和 public 仅 propext/Classical.choice/Quot.sound。没有白名单外公理或未覆盖的 generated owner。

2026-10-24 18:00:23 UTC 的只读服务器核对（server-binding.json）确认正式源、原 producer004、实际 import symlink、原成功 kernel log、原 audit script/log/JSON、全 TYPE/VALUE 文件和作者 release/publication/receipt 全部与绑定哈希吻合。原 object SHA `59a97d3ab28100fa5b96e43d45e15cebce83d3f9e8d4a3bf41e1be4e01277319`；本次不重编。整份 TYPE/VALUE 原文是原成功 audit log 的精确连续子串，末尾确为 `AUDITED_TARGET_CONSTANTS 7 PUBLIC 1 THEOREMS 6 DEFINITIONS 1`。复用原 recorded kernel/audit rc0；kernel log 仅 style/deprecation 与已知 package-local-change 警告，无 error。原四次 kernel 中三失败日志的哈希完整保留，未缩小分母。

服务器源 mtime 17:47:11，成功对象/日志 17:47:18，原 audit log 17:47:53，均在冻结激活与318资格之后。较后复制的同字节审计脚本/JSON不改变绑定的原 log/object；本次验证的是精确字节及原收据，未凭 mtime 猜测新增检查。工具链复用 leanprover/lean4:v4.36.0-rc1、mathlib 807d3836b165983210ee2ecf3cd28f239436949c。

715 个旧对象的实际链接与完整 qualified-v82 view 精确一致；必要旧源/对象以及 Mathlib.MeasureTheory.Measure.Prod 的哈希也吻合。Git clean，唯一源差异是新模块，head/tree 与 PR321 收据一致。实际无该目标 Lean/audit 进程，作者 source writer/target execution 已 RELEASE、inflight=[]。本审查没有缓存写入或 Root 集成权限。后续 Root 只需将此完整独审与精确源/对象/导出覆盖证据绑定，并处理真实集成交互；不得据此宣布尚未支付的 interval 合同或原研究根关闭。
