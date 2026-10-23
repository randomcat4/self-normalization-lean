# FiniteSurvival / SourceLindleySurvival 完整独立审查

**STATUS: CORRECT。** 本审查只接受冻结的第 6、7、8 个公开声明及其两个新模块，未发现关键数学缺口、声明漂移或未支付的公共概率前提。结论绑定下列精确源码、原成功对象、完整实际所属类型及原全所属传递公理回执；根协调员的资格确认、发布和整合尚待进行。

审查者 `/root/common_finite_source_survival_full_review`，全新独立 `gpt-6.1-sol / xhigh` 上下文，非作者。使用 `math-theorem`；遵守当前 AGENTS、SERVER、TEAM 和 streamlined-acceptance；未启用 math-ultra、未创建子上下文、未跨线程发信、未修改作者或其他 owner 文件。报告完成即释放本次审查写权。精确 token 计数不可由本上下文取得，JSON 分别留空 input、cached input、output、reasoning subset；没有估算订阅百分比。

## 精确版本、冻结与证据

完整读入交接 `drafts/c12-survival-cdf/production-handoff.md`，SHA256 `7d5c779a50c91446cefd1f62813f2196754183daa0987c7d8aab540447bd966e`，及 manifest，SHA256 `30850ca713bc21ee3f6fa824ddb483b5e09a30dc625e1c574590f01f955e8bb4`。冻结文件 `coordination/public-survival-cdf-declaration-freeze.md` 的 SHA256 为 `674a688c637cc88eb5d3e1f5c43486725e8f1f64510a248ca9742b423a8db2fa`。三个新公开头逐字节等于其中对应冻结头；完整实际类型也逐一核对，参数、原始假设、真实测度、闭事件、所有常数和分母均一致。

| 模块 | 精确源码 SHA256 | 原成功对象 SHA256 | 完整覆盖 |
|---|---|---|---|
| FiniteSurvival | `155b8865c55e392f27b07a65caad1ea3aac542a70fea4ae491251ee1b3a3d816` | `b0037ea1068ddd216c6cea03781efae10b06bfeb967e95a5207f9a4fe248935a` | 584 行；8 个显式定理（7 private、1 public）；29 个生成定理；37 actual owned |
| SourceLindleySurvival | `433313fd12cfacfae54bb0ec1366d05aa47844b12fc18585fd326aae81590178` | `5eb0dd2b431314562b2ff0866addd250ae940a83fbcfedb8c8e1fe28ae8f2f48` | 170 行；4 个显式定理（2 private、2 public）；1 个生成定理；5 actual owned |

全新范围共 754 行、12 个显式证明、42 个 actual owned theorem、30 个生成定理、0 新定义、0 新定义值。计数来自实际 owner map 与完整类型集合交集核对，不由名称前缀或历史描述推算。两份源码都是无 BOM 的 UTF-8、仅 LF（CR=0）；未改冻结字节。

只读服务器核对确认 source-only commit `3993099d893ada6b91d53f6bbbadfdfaff96c123`，parent `ba7ef8674924248e6eb6fb78d8c59aaf848a6627`，tree `620a2d3cdf9d6c8833edbd86607983b103f6487e`，恰只增加 `Shao/Probability/FiniteSurvival.lean` 与 `Shao/Probability/SourceLindleySurvival.lean`。Git blob、live source、原成功 artifact source 与本地完整审查源一致；live 安装对象与原 artifact 对象一致。原环境仍为 `leanprover/lean4:v4.36.0-rc1`、mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。

原完整内核检查分别为 `artifacts/common-survival-cdf/finite-007` 和 `source-002`，均直接 rc=0，并成功输出上述 `-o` 对象。原实际所属审计均直接 rc=0。已读原检查命令：实际 Lean/audit 使用 `root-heavy.lock`、CPU10–13、`-M8192 -j4 -DautoImplicit=false`，并在显示或搜索日志前立即保存原 rc。`finite-owned-audit-response.json` 的运输 timeout 不构成证明失败；本次只读核对同一次原执行保存的 `owned-audit.exit=0`、JSON 和 native stdout，未重新执行该审计。全部旧失败/运输证据保持原样。

本审查没有运行 Lean、lake、smoke、重编译、collectAxioms 或旧依赖图遍历。服务器只读绑定检查成功，未复制 raw logs、缓存或对象到本地。数学内核结论复用原源绑定成功回执，不声称本审查再次编译。

## FiniteSurvival 全部证明

1. **L17–57，`fs_centered_third_moment_ge_variance`。** 从原 raw 三阶可积取得 `MemLp id 3`，减去实际均值后取得中心化三阶与二阶可积。实际 `variance_eq_integral` 给中心二阶积分为 V。对 `tau=sqrt V>0`，点态恒等式 `(abs(z-mu)-tau)^2*(2*abs(z-mu)+tau)>=0` 给 `3*tau*(z-mu)^2 <= 2*abs(z-mu)^3+tau^3`；积分及 `tau^2=V` 给 `tau^3<=m3c`。因此后续 beta 至少为 1，不依赖总化除零或额外归一化假设。
2. **L59–71，`fs_positiveLaplace_scale`。** 按实际原始和 s 的正负分支，用 sigma>0 保持正部的符号，证明 `positiveLaplace L (s/sigma)=positiveLaplace (sigma*L) s`。没有从实际 walk 中减去均值。
3. **L73–154，`fs_actual_payment_lower_bound`。** 实际取 `P=pi nu`、`X=prefixSum/sigma`、`law=P.map X`，支付可测性与 law 概率性。对 `law` 再除以 `sqrt k` 的闭 CDF，精确拉回为真实 iid 原始和除以 `sigma*sqrt k`。这里的局部 `hCDF` 由已合格 `iid_uncentered_berryEsseen` 产生，误差为 `epsilon=1024*beta/sqrt k+delta*sqrt k`；它不是公共前提，也不是中心化假设。取辅助 `C=epsilon*sqrt k/L`，用旧真实 Laplace layercake 消费者的 beta 参数 L，支付 `C>=0`、`L>=1` 和完整 CDF 假设。积分 pushforward 与前条缩放等式确切返回实际 `finiteSumLaplacePayment nu k (sigma*L)`。由实际 beta<=L 得端点下界 `1/2-1025*L/sqrt k-delta*sqrt k`，所有 k>=1。
4. **L156–242，`fs_drift_sqrt_series`。** 在 m>=1 取 s=exp(-1/m)，使用 `f(x)=x^(-1/2)*exp(-x/m)`。证明其在正半轴可积，在 [1,infinity) 单调递减且非负；积分比较先界 k>=2 的尾和，首项另付 `f(1)<=1`。Gamma 半阶积分给正半轴积分 `sqrt m*sqrt pi`，用 `sqrt pi<=2`、`sqrt m>=1` 合成保守但有效的 `sum s^(n+1)/sqrt(n+1)<=4*sqrt m`，同时证明真实 Summable。没有使用 totalized tsum 代替收敛证明。
5. **L244–319，`fs_corrected_laplaceW_lower`。** 构造确定性辅助序列 `B_k=min(1,A_k+delta*sqrt k)`，支付 0<=B<=1 与漂移已补偿的原 S1。只将 B 送入已接受无漂移 W 下界，不错误地将实际 A 当作中心化支付。原 A、B 的 W 级数与差均收敛；逐项 `B_k-A_k<=delta*sqrt k`，故 `W(B)-W(A)<=delta*sum s^k/sqrt k<=4*delta*sqrt m`。得到真实 A 的 W 下界，漂移项未丢失。
6. **L321–382，`fs_coefficient_bound_at_exp`。** 只要求目标 m 所对应单一 s=exp(-1/m) 处的生成函数上界。由 a 非负、有界、反单调和真实级数收敛，有限前缀 j=0,...,m-1 给 `m*s^m*a_m<=G(s)`；`s^m=exp(-1)` 与 `1-s>=1/(2m)` 给 `a_m<=sqrt2*exp1*B/sqrt m`。没有误用旧的“所有 s 同一常数”系数消费者。此处用 m 项而不是 m+1 项只造成合法常数余量。
7. **L384–452，`fs_actual_maxLaplaceMean_bound`。** A、a 都是实际 nu 的 endpoint payment 和 maximum Laplace mean。概率界、a 的反单调性均由既有实际 product-law 接口提供。真实 `actual_maximum_spitzer_laplace` 与原 payment 补恒等式产生 `G=(1-s)^(-1)*exp(-W_A)`。令 D=4*delta*sqrt m，将 `G*exp(-D)` 与 `W_A+D` 送入单点代数上界后还原 exp D，再用前条单点系数提取。常数链 `exp1*exp(1+3*1025)=exp(5+3*1024)` 正确；无 hSP 公共前提，无条件 CLT 替代，无 C1/C2 循环。
8. **L454–582，公开 `iid_closed_survival_nonzero_drift`。** 取 sigma=sqrt V、beta=m3c/sigma^3>=1、d=r/sigma>=0、L=d+beta、K=2*exp(6+3*1024)。物理尺度 `sigma*L` 严格正，且 `r/(sigma*L)<=1`。实际 `closedUpper` 与包括零前缀的 `maxWithZero<=r` 等价，旧闭事件 Laplace 界因此直接适用。对 m>=1，前条和 `sqrt2/sqrt m<=2/sqrt(m+1)` 给真实线性界；另用概率<=1、K>=1、漂移指数>=1 分支产生冻结的 `min 1 ratio`，不是不合法地将 min 随意移过常数。`(r+m3c/V)/(sigma*sqrt(m+1))=L/sqrt(m+1)` 已用 sigma^2=V 精确化简。m=0 单独分支使用 L>=1 和概率<=1；r=0 时尺度仍正，闭零记录原子原样保留。最终漂移恰为 `exp(4*(abs(mu)*sqrt m/sqrt V))`。

## SourceLindleySurvival 全部证明

1. **L17–36，`sl_drift_bound`。** 在 N>0、V>0、N*abs(mu)<=1/8、N*V>=1/2、k<=N 下，先平方并支付非负性，再推 `16*mu^2*k<=V`，由正平方根得到 `abs(mu)*sqrt k/sqrt V<=1/4`。它对 k=0 也有效，没有除以 k。
2. **L38–44，`sl_min_one_eight`。** 按 v<=1 分支，从 u<=8v 得 `min(1,u)<=8*min(1,v)`；后一分支用 min<=1。该辅助引理没有将 centered/raw third moment 偷换为相等。
3. **L46–133，公开 `sourceTruncation_lindleyPrefixSurvivalBound`。** 始终固定 `rho=cond nu {|z|<=epsilon/(1+x)}`，与 k、r 无关；原 nu 只要求冻结的 finite2、N*m2=1、mean0、x>=0、0<epsilon<=1/2、原 R<=epsilon^3/8。实际旧 `sourceTruncation_law_data` 给 rho 概率性及 raw 三阶可积；旧 paid_moments 给 `N*abs(mu)<=2R/(epsilon^2*(1+x))` 与 `m3c<=8*m3`；旧 variance_bounds 给实际 V>0 与 N*V>=1/2。N>0 从原归一化推出。由 `2*epsilon<=1+x` 与预算付出 N*abs(mu)<=1/8，因此所有 1<=k<N 的漂移指数<=exp1；没有假设 rho 均值为零。非负 r、V 与严格正分母将 centered 比率界到 8 倍 raw 比率，再用前条 min 界。实际应用第6头后常数为 `8*(2*exp(6+3*1024))*exp1=16*exp(7+3*1024)`。结论逐项等于旧 literal predicate，没有重声明该定义。
4. **L135–168，公开 `sourceTruncation_lindleyRegulator_second_moment`。** 将刚产生的真实 rho survival predicate 和其非负常数实例化到精确已接受的 `sourceTruncation_lindleyRegulator_second_moment_of_survival`。该旧接口在长度 N 的真实 iid joint law 上量化所有 j:Fin N，包含真实 `lindleyRegulator a j` 的平方可积性。其常数 `max 1 (3*C)` 在 C=16*exp(7+3*1024) 下确切化为 `48*exp(7+3*1024)`，分母仍 `sqrt V*sqrt(j.val+1)`，分子仍实际 raw m3。公开结论不再有 survival 前提；首步 j=0、反转、严格事件 disintegration 和 joint-law 独立性沿用已合格消费证明，而非替换成独立副本或重新假定。

## 完整 actual types、定义值与传递公理

两份完整 raw `pp.all=true / pp.maxSteps=10000000 / pp.deepTerms=true / pp.proofs=true` 类型导出均已逐条直接读完，包括所有隐式参数、private 和 compiler generated 声明，没有缩写、因素化或删节读取。类型 JSON SHA256 分别为 `74baa94a9473d24bfb75f1c238f07e37b1ee494647f401b3abe41ccd4eecb5eb`、`fe414751442e8843cdf661649725bf74681675a8723b724b85912240048ef86a`。42 条每条原始类型哈希均自行校验，literal `⋯` 合计0。服务器只读重新解析原 native stdout，确认导出内容逐字、顺序、名称集合与实际 owner map 完全一致。

逐声明覆盖见 `coordination/common-finite-source-survival-full-review-types.json`；保留42个精确名称、actual type SHA256、source-parent 全证明行区间、generated 分类及各自传递公理。30 个生成项已全部审查：条件下非零 numeral/power/product 与 False 的等价、natural cast+1 非零、有限索引正性反证、preimage/Ioi membership 和 nat/rpow 等式；均保留完整类型中的条件，未将其中条件性 False 错读为无条件矛盾。它们的全部生成源证明也在上述 12 个完整显式证明覆盖内。

原 owner-map audit 逐项调用 `Lean.collectAxioms`，选择 `env.getModuleIdxFor?` 返回的实际模块归属，不用 prefix 筛选；明确拒绝任何未冻结 definition。已完整读取审计代码和两份全部42行公理记录。原 axiom JSON SHA256 为 `287239ddec1032ad68e99c3509eb0bb1cf571028a614fd142d0e15d553d7faf9` 与 `480ff90ebf7835658a4e873415addcc7ee6e6b41af4e48e8586c1abd4b082f09`。全部递归公理只含 `propext`、`Classical.choice`、`Quot.sound` 的子集。源码禁止项扫描及完整阅读未见 sorry、admit、新 axiom、unsafe、native_decide。新模块无定义值待审；唯一旧 cdfFourierError 定义及其完整 literal value 已在合格 Berry 审查中复用。

## 原文忠实性、旧合格证据复用及限制

本轮实际完整读了原 `supplement.tex` 的 L1073–1150（BE、真实 Spitzer、非零漂移有限生存及所有端点）、L461–533（固定条件律/矩）、L572–595（regulator目标及 weighted 区别）、L2045–2135（完整条件矩预算）、L2176–2215（个体二阶矩证明），以及 `main.tex` 的 L421–430（原 cutoff）、L491–571（固定条件律、非零可能均值、真实 Lindley 和反转）。原文件 SHA256 分别为 `b99f2ac4d2f39dd39772d98a5702b7a923c2f10f8730a08fc1b4cd6bba4742bd`、`beb00f718487e36de433175c97f1d500cb48e7a92ce5bd5ad5d62bb132122d06`，与冻结 source contract 一致。source-contract 和 proof-route 也完整读取。没有把 source 的 informal asymp 提升为更强 literal 常数；本轮不修改 p54 或其他原 scope repair。

第6头忠实表达原 `M_m=max(0,S1,...,Sm)` 的一般非零漂移闭阈值结论，给出明确而非最优常数，原 m3c/variance 尺度不变。第7头支付源固定条件律的概率义务；第8头支付原个体 `E U_i^2 <= C*m3/(tau*sqrt i)`，Lean i=j.val+1。没有要求原 nu raw 三阶矩，没有条件均值0、atomless、对称性或自由独立性假设。原文 BE/Spitzer 路线为经典方法，保留 Petrov、Spitzer、Janssen–van Leeuwaarden 归属；不作数学新颖性主张。

以下旧证据按 exact source/object 复用，只完整读实际消费的公开/私有接口及 literal 定义，未重复旧全证明、旧 owned types、旧内核或旧 DAG：

- **BerryEsseen**：源 `8bf02df1210d69a2934746987d0022a85166d17c9850fa4fd27656eb88bb2af9`、对象 `d67df1b97eddcde16ee7d9fedc6e6e7e4af11e22e04732a69dbd0b5883b76b57`。独审 MD `01ab66c3d10f4ed72d28ddffa1b56c5de177d32a260e0efc9c7c42e81883ecec`、JSON `e72fcb989c7b0f58eba8bd1aa30a055e03f26c230154ccf6d5b56c9a17e64573`；root qualification `860253b5dad9190421463022a700494e50421eba87333d9c53c2fe6454cfed09` 明确覆盖1950行、119actual types和唯一定义值。本轮读取真正使用的完整 `iid_uncentered_berryEsseen` 接口及其 raw-CDF/drift交互，不将旧119项算入新增42项。
- **SpitzerLaplace**：源 `2faaf41caf7b0025e7171b764b468803688802f0177f02bfa0d4645a7c4890fb`、对象 `86fd91edc877ed88c94de93f109bb92ee01a5b74e36f8eb946714f98766d2f9b`；完整独审 MD `ca4717969ee39b7d1b9003c68f02f53adad40b3132f6f0d4aa9c517a1ae075e5`、JSON `1afc4f8b3d418d2d7be8c54dccfa641c737eff4e92f92eae8204ee855caf5ade`。本轮读取实际 Spitzer 全头、actual endpoint/maximum/payment/G/W literal definitions 与归一化接口，其假设只有实际概率律、正 Laplace尺度和0<s<1。
- **OQ4 LaplaceTail/LaplaceGenerating/FiniteSurvivalLaplace**：读取全部实际消费的 payment 可积性/概率界、CDF到端点界、W/G收敛、W下界、exp reciprocal gap、单点 generating代数界、最大值反单调、闭事件Laplace界全头。服务器 source/object 精确等于 Spitzer 完整独审记录中的已接受依赖绑定；本轮新单点提取补足了旧所有参数消费者不适用的风险。
- **SourceTruncationBridge 与 SourceLindleyRegulatorSecondMoment**：完整读实际 law_data/paid_moments/variance_bounds 全头、原 survival predicate完整literal值、原 unconditional-in-j conditional-on-survival消费全头，以及 prefixSum、maxWithZero、closedUpper、lindleyRegulator literal值。旧二阶矩完整独审 MD `120e65321f4809fe1004e91669af0ef64e3f624dbbe9dc6436befabebf295d50`、JSON `3687b9f2a768694b69892dd953eb55d66746b1970fadaf0b96645059d22236ff`，绑定源 `a0316591ef49be19c0372ce80a87a8eaca4608b1fae6dbf57780e89359fc9310`、对象 `b2b629c25b22fda402fb989bd016d4b1cb607e20a82d68bc308c57c39ca453e3`。Bridge源 `05321c22d1b2ea178fbc116178af345f4186bfce51011c8242b4ccfd2e0dd7d1`、对象 `3a23c563b69b9316b50d14f3b008ad26575d4c547602f4abd13e9c1718295c7a` 也在旧合格证据和本轮只读服务器哈希中一致。joint-law反转、disintegration、首步及 gamma*m2<=2m3 的旧完整证明按该资格复用。

**未覆盖且仍 OPEN：** 能量加权/倾斜 square sums、原 untruncated near-zero survival 的 deletion/concentration 后续、high-regime/growing-y/完整反演与去平滑、最终 C1/C2，以及原 C12/OQ3/OQ4/OQ56 根组。没有以有限恒等式或本轮三个辅助根头宣称整条原根闭合。root 接受时可复用本报告及原源绑定成功回执，除非出现真实数学改动、接口风险或未覆盖证据缺口，无须再重审同一42项或重跑成功源。

审查运行状态：`REVIEW_COMPLETE_RELEASED`；无本审查未完成命令、写入或传输，写权已释放。下一步骤归根协调员：核读本完整报告并资格确认精确两模块，接续原授权的后续源依赖与整合。
