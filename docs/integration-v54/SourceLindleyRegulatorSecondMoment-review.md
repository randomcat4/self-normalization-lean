# 真实 Lindley 调节量平方矩消费者：独立完整最终审查

STATUS: CORRECT

接受范围仅为冻结的条件消费者模块 `Shao.Probability.SourceLindleyRegulatorSecondMoment`。未发现关键数学或证据缺口。实际有限步生存界仍为显式前提，原始无条件调节量二阶矩引理、加权能量后继及 C1/C2 根均保持 OPEN。

审查者 `/root/common_regulator_second_review`，本模块 NEVERAUTHOR，独立新上下文；按指定 gpt-6.1-sol / xhigh 执行 math-theorem，未用 math-ultra 或子代理。作者为另一个上下文 `/root/common_regulator_second_candidate`，其 writerReleased=true、无未决命令的交付已核对。本轮只写本报告及同名 JSON；未改源码、冻结、历史证据、缓存或工作树，未运行任何 Lean／公理审计。

## 精确对象与冻结

- 提交 `4f562ddb57e2cf695291db5da38aadfd2c0fbb7d`，父提交 `52b6e4727f84f23810f019a2c20c068974be3acc`，树 `aaaec446bd2dba18853fb21721f2c7e25c315ce0`。服务器 HEAD、Git blob 和唯一新增路径已只读核验。
- 源码 SHA256 `a0316591ef49be19c0372ce80a87a8eaca4608b1fae6dbf57780e89359fc9310`。本地、服务器实物与 Git blob 相同；26,078 字节、559 LF、0 CR、UTF-8 无 BOM。
- 对象 SHA256 `b2b629c25b22fda402fb989bd016d4b1cb607e20a82d68bc308c57c39ca453e3`，832,768 字节，inode 3428455，mtimeNs 1792761451529429067；现物与作者收据及审计前后清单一致。
- 根冻结 `coordination/public-regulator-second-moment-declaration-freeze.md` SHA256 `3996518297fcd75a33c584c07f5d64dd7620cec48eb16f9cd64ba6cfbb3c7813`；完整候选 SHA256 `0b2a6d15f50168cf6d29ea4642ddc8a4ac1a48985b6fae3455c0d8c089123943`；完整源合同 SHA256 `15d3984bc2ff87e553bfa99a767d757c067dfe862c5599a61861c167333ae063`。三份文件均完整阅读并核验哈希。
- 独立提取全部 7 个完整公开定理头及 2 个完整公开定义体，与候选逐字相同。JSON 保存各段冻结文本 SHA256，未仅比名称或摘要。

## 完整源到声明及证明

完整阅读只读原文 `C:/game/shao/current/c12/supplement.tex` 2176–2215，以及本模块 LF1–559 每行源码、全部私有证明和公开接口。自然语言第 i 步精确对应 j.val+1；真实 A_i=a j、W_(i-1)=lindleyState a j.val、U_i=max(-(W_(i-1)+A_i),0)；maxWithZero 包含空前缀。源律确为 cond nu {|z|≤epsilon/(1+x)}，没有更换增量、路径或中心化墙。

1. **LF19–33，定义。** 成本是实际 Measure.pi ν 上严格事件 `<` 的概率乘以负部平方。生存命题是同一真实前缀最大值的闭事件 `≤`，量化 1≤k、k<N、全部 r≥0，保留 min 1、gamma=m3/V 及 sqrt V * sqrt(k+1)。gamma 是未中心化三阶绝对矩除以真实方差。该定义只命名未支付概率界，没有产生该界或声称存在统一 C。
2. **LF35–80，点态支配。** 递推先给 W≥0，再给 0≤U≤A^-≤|A|。严格事件内平方单调；事件外 W≥A^-≥-A，故 W+A≥0、U=0。在 W=A^- 的原子处仍 U=0，没有断言严格／非严格概率相等。原文 2180–2183 的真实平方权重被逐路径支付。
3. **LF82–205，联合律。** state_prefix 只说明状态依赖真实前缀。prefix_map_pi 从实际乘积坐标的独立性和评价保测性计算整个前缀边际。terminal_state_map 在真实乘积空间实例化既有 iid_lindley_energy_identDistrib_maxWithZero，再投影得到终端状态与真实最大值同律；实际坐标完整支付旧接口的可测、独立和同分布条件。last_joint_map 用 piFinSuccAbove 真正拆出当前末坐标，交换乘积并计算 (T,id) 像律，然后代入反转结果；最后截取长样本前 j.val+1 坐标。因此得到的是长样本真实 (W_(i-1),A_i) 的联合律等于 (maxWithZero#P_(i-1)).prod ν，未把同律误作原路径相等，也未外加所需独立性。k=0 的空乘积保留。
4. **LF207–249，平方可积。** 先将实际坐标二阶矩沿保测评价拉回，再以可测 U²≤(a j)² 支配得到 L1，最后积分单调给 E U²≤m2。这里只需实际二阶矩和概率性，不需生存、第三矩、中心化或正方差，V=0 也覆盖。
5. **LF251–339，拆分。** strict_square(w,z) 正是 (z^-)² 1{w<z^-}，可测、非负并受 z² 支配。先在真实 Q.prod ν 用二阶矩得到 hH:Integrable，再沿联合像律得到路径权重可积。对每个 z，用常数指示函数积分及可测最大值的 map 公式得到真实严格事件成本；hH.integral_prod_right 支付成本可积；仅此之后使用 integral_prod_symm _ hH。调节量积分比较同时调用已证明的调节量 L1。两侧实际积分均有有限性根据，没有利用不可积 Bochner 积分默认值。
6. **LF341–421，首步与 Lyapunov。** 概率律下用 z²≤1+|z|³ 支配推出二阶可积。令 b=sqrt m2，从 (|z|-b)²(2|z|+b)≥0 得 3b z²≤2|z|³+b³；合法积分并用 b³=b*m2 得 sqrt m2*m2≤m3。MemLp 的真实方差恒等式给 V≤m2，hV 给严格正分母，所以 m2≤m3/sqrt V。首步真实 W0=0，实际坐标边际给精确负部平方积分，内部支付 L1。没有以 V=0 的除法默认值取得上界。
7. **LF423–507，通用消费者。** 首步从完整 P_N 的坐标二阶矩上界和上述 Lyapunov 得界，使用 max(1,3C)≥1，不调用生存。后续 j.val≥1、j.val<N，令 r=z^-≥0、D=sqrt V*sqrt(j.val+1)>0。只用严格事件包含于闭事件，再由 hC≥0 消去 min，得 cost≤(C/D)(|z|³+gamma*z²)。上界先由 h3/h2 得 L1，再与已经可积的成本比较积分。gamma≥0、hM2 和 V>0 支付 gamma*m2≤2m3，得到 3C*m3/D，最后以 max(1,3C)≥3C 统一全部索引。C=0 保留，未暗增 C≥1，也未把3吸入未注明常数。
8. **LF509–557，源消费者。** 原始 nu 只要求二阶可积、N*m2=1、原始均值0和冻结截断预算。旧 sourceTruncation_law_data 支付真实 rho 概率性及 rho 三阶可积；旧 sourceTruncation_variance_bounds 支付 V=m2-mu²、V>0、N*mu²≤1/4、N*V≥1/2。N>0 由归一化推出；恒等式 NV=Nm2-Nmu² 与后二界给 m2≤2V，支付通用 hM2。只余真实 lindleyPrefixSurvivalBound rho N C 箭头前提。未要求原始 nu 三阶矩，未假设条件均值0／对称性，未增加自由独立性或可积性前提。

原文 2176–2179、2180–2185、2204–2215 的条件消费部分与实现相符。原文 2186–2202 的真实带漂移有限步生存生产未支付；不能因条件消费者 CORRECT 就宣布原始无条件二阶矩结论。max(1,3C) 是显式输入 C 的函数，本轮不认证其统一来源或数学新颖性。

## 边界与既有接口

N=0 的通用 ∀j:Fin N 为空；源归一化排除 N=0。N=1 的通用生存量词为空，只需首步。零路径、零负部、r=0、W=A^- 原子正确保留；负部为0时严格成本为零，闭生存仍包含墙0。平方可积与拆分不要求正方差；全部倒 sqrt V 的结果要求 hV，源版本内部支付 hV。未把 δ(-1) 这类零方差负常数律纳入虚假的零分母上界。

只核验既有完整消费接口及接受哈希，没有重审旧证明。读取 lindleyRegulator、真实递推／前缀／反转／最大值定义，iid_lindley_energy_identDistrib_maxWithZero 全头，以及 sourceTruncation_law_data、sourceTruncation_variance_bounds 全头。9 个 Lindley 闭包模块服务器 source/object 哈希逐一等于 coordination/regulator-second-moment-lindley-install.json 接受记录；安装为只读引用，Lean 调用0。SourceFourierScale 和 SourceTruncationBridge 的 source 与 v52 source map 相符、object 与实际接受 integration-bearing-v52 对象相同。旧接口的所有调用前提均支付。

## 精确服务器内核和全部所属公理

复用首次成功 check05，direct Lean exit 0；日志 SHA256 `76d00c2c665458da32e87bbfa9857dd0b38d819346d97c57449848c4b4bb0295`。owned-audit direct Lean exit 0；日志 SHA256 `c986491e4866e056628982696d2884324d4bddd31311f42aaf54da8844c4efff`，JSON SHA256 `10df492b7d03eee3b061e4c4f41cfc3e625f7f5e2a8c8ad9f26aec9b25cbc097`，helper SHA256 `061f8af47e6edee1342fa422792fab0f0c2c6e6f50aa51ef96c8cd5737650496`。审计前后源／对象清单字节相同，现物继续相同。原始日志、对象和缓存留服务器。

完整阅读 OwnedAudit.lean：按 env.getModuleIdxFor? 的实际模块归属选择每一常量，而非名称前缀或仅公开项；逐项递归 Lean.collectAxioms，遇非白名单即报错。完整阅读服务器 owned-audit.log LF1–1107，覆盖31实际类型、3完整定义值和31项各自的传递公理。实际为31所属常量＝28定理（含私有／生成）＋3定义（2公开＋1私有），其中显式公开定理7。JSON逐 owner 绑定种类、公理、精确源／对象、实际类型摘要哈希及日志位置；3定义值全部已读并绑定。4个生成定理包括两个 _simp_1_1、可测归纳 _proof_1_1、成本 .eq_1，没有遗漏私有命名空间。

每项传递公理均在白名单内；并集恰为 propext、Classical.choice、Quot.sound。独立扫描新源码没有 sorry/admit/axiom/unsafe/native_decide。警告只有继承 mathlib local-changes 和 LF538 proposition letI 风格建议，没有为其改写成功源码或重跑。

现物固定 Lean leanprover/lean4:v4.36.0-rc1，mathlib 807d3836b165983210ee2ecf3cd28f239436949c，packages 真实路径 cache-overlays/shared-v34/packages。原始命令使用指定服务器 CPU10–13、共享 root-heavy.lock、M8192/j4/autoImplicit=false。本轮无本机 Lean、缓存写入或重复机械门。

## 原始退出码和失败分母

直接读取作者原始 rollout `C:/Users/UIO/.codex/sessions/2026/10/23/rollout-2026-10-23T20-53-07-01a168d2-7d2c-71c0-832f-a917ec28bf36.jsonl` 原工具输入第410／442行及关联完成事件第413／445行。原输入逐字等于 coordination/regulator-second-original-execution-provenance.json 索引；原行 SHA256（不含行尾）分别 `a7e1b4d0dcb89c9710e24b18f440f73f3d261c2e3c111138e9ae8640fcbf65e6`、`1d19ce97b32da4829651f763a2be485e23ef87110a95065da81af7ebf815a4f8`，独立核验相符。

check05 在 Lean 后立即 rc=$?，写 check05.exit，再 tail，最后 exit 原 rc；审计命令也先保存 direct Lean rc、写 owned-audit.exit，再 hashafter／grep，最后退出原 rc。关联完成响应 server exit_code 均为0，当前 exit 实物也为0。因此日志查看命令未掩盖 Lean 返回值。

check01–04 原失败源哈希和日志均保留，direct Lean exit 均为1，已核验并记录 JSON，不计成功。check01 日志明确为接受的 LindleyTelescoping 对象缺失；root随后按9模块原对象闭包收据安装，0次 Lean。check02–04 是成功前开发失败。check05 是最终源／对象的首次成功，本轮未重复成功内核或公理门。

## 接受边界和释放

冻结条件模块可记 LEAN_FULLY_CHECKED：复用精确源码的服务器内核和全部所属传递公理证据，且完整源到声明／证明审查 CORRECT。该标签不覆盖原始生存、无条件二阶矩或 C1/C2 根。下一未支付数学接口仍是实际 lindleyPrefixSurvivalBound rho N C 的有限步概率生产，既有 Brownian／CDF／Spitzer 条件消费者不能替代它。

审查完成，不接管生产写权限、不自行发布合并或启动下一任务。工作树另外两份既有未跟踪文件仍在、未触碰。无后台命令或未决传输；本审查旋转槽随 final 释放。
