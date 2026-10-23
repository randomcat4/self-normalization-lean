# 一般116有限统一概率界：独立最终审查

STATUS: **CORRECT_FINAL_SOURCE_ACTUAL_INTERFACE_AXIOMS**

精确 Source `ec4b34c5efe5117eabe3cd7fa3b7aa571efd4bdeff6f69914ba91d66e7623606`（95645 bytes，1898行，UTF-8/LF、无BOM）通过本次完整 source-to-statement/proof、全部实际所属类型/透明定义值和递归公理审查。复用同哈希成功服务器 kernel/AX 证据，不重新编译。只关闭冻结的 `finite_adjacent_log_bound`；一般 OQ4、Spectrum、energy 根仍 OPEN，rawleaf 增量0。

## 独立性与输入

独立 reviewer context128，任务 `/root/oq4_finite_final_review_v4`；按派发为 fresh gpt-6.1-sol/xhigh，绝非作者。使用 math-theorem，未使用 math-ultra。只写本报告目录；未改 Source、共享文件或其他所有者文件，未调用服务器、Lean、Git、网络或子代理。未读作者修复总结作为证明，未读其他当前 reviewer 投票。旧完整合格票仅用于精确未变块覆盖复用。机械检查收据中的自述不作为数学推理。

主要精确输入如下；完整输入/输出哈希和全部逐项覆盖见 `receipt.json`、`source-coverage.json`、`actual-coverage.json`。

| 输入 | SHA256 |
|---|---|
| 当前 `general116-finite-source-repair-v4/Source-v4.lean.txt`，亦等于 check-v4/Source | `ec4b34c5efe5117eabe3cd7fa3b7aa571efd4bdeff6f69914ba91d66e7623606` |
| 数学冻结 `frozen-general116-finite-bound-v1.md` | `38222ff582c39adaa9b18ab6880994ab7acbbb719f3eea93cf70fbdba843c09a` |
| 公开声明冻结 | `4fb1c50b4748d14772d8487b5c68b87c35ecb704b2354319aa4c9f6783131bc3` |
| 全78项头/31定义值冻结 | `9b0866f2cf763c5210dc49377fa139aafe285ee2f3487a65443ae9bf99c44a19` |
| 旧完整 Source | `b4500f76bda36edc349d1976a929ec1c885635b089e89622099344e84dbb5db5` |
| 旧完整 qualified report / receipt | `94ff9f5cc116b7a2a7de8832501c1565274bc83d794ff3f5d16cbfb7a72c1384` / `265ae775e00fe2c851d9d74ead03303d3be53f73a2536b9c13d5965debc2bb8b` |
| `owned-interface.txt` | `3e38f2fb4979a8a59718ea2bec503533bbd8cab822d3abefaa2774f8767a8280` |
| `actual-owned.json` | `076158e76d8e795f812137376b61424556a5bf60b3f0f247f70e2ab3a1237e3c` |
| `raw-expressions.json` | `1275e0326e95c854fe45e119a9e3f77327dbba7b351f722c0de7d3792fd07ca1` |
| `audit-native.json` | `4be6beb7ce4d695cbee3626f9d5219e0faace802c9986c5107c1473f8db4294e` |
| 成功 `final-check-receipt.json` | `4905c55399845a1654f09ca4a2bb37413dfbebac659b85a569d692a866fadd28` |
| 实际4814 imports / 新161 Init绑定 | `8759060355bd4fa5bfec8c622694c6449adf59dc47bf48bf0e6feac06816302a` / `0d2167c7d5ed027079f5616471c4e686b94d63b92e2a68411bd8538a59f87b31` |

## 完整 Source 覆盖与声明冻结

本人直接解析旧/当前/冻结文件的原始全文，按名称逐项比较全部78项（31 private defs、46 private theorems、唯一public）。去注释及合并空白后，全部完整声明头和31完整定义值与冻结一致。旧→当前变化恰为下表15个完整 proof body；32个其余 theorem chunk 包括头与完整证明逐字节不变。将47个 proof body各替换同一占位符后，旧/当前其余全部字节相同，故5个imports、namespace、noncomputable section、所有定义、声明次序、作用域、注释及关闭语句无遗漏变化，无新全局helper或概率对象。

32个逐字不变证明的完整覆盖复用上述旧 qualified 完整 Source 票；当前15个变化证明均完整新读，不只看diff。`source-coverage.json`记录所有78项当前/旧完整块哈希和范围。唯一资源选项是 `bDerivative_bound` proof内部的一次 `set_option maxHeartbeats 800000 in`；不改变数学、内核或其他证明选项。全 Source 无 sorry/admit/新增axiom/unsafe/native_decide/partial。

| 完整新审 proof | 当前行 | 核验理由 |
|---|---:|---|
| finite_weighted_geom_identity |154–165|对R归纳；q≠1保证1−q非零；归纳步展开有限和、自然数实嵌入和幂，清分母后纯环恒等式。|
| actual_factorization |493–555|H≥2确保m=H−1≥1；自然减法转实减法合法。lowerModes到全部正奇数r<H的映射单射并满覆盖；有限和拆正/负谱时保留实际parity项。调用真实closedStrip谱公式，N≥1消去zeroMode，最后只用已证normalizer>0作除法。|
| cMode_hasDerivAt |735–785|u′=−u/x；tan(u)与cot(ru)分别求导后相乘，cot导数为ru/(x sin²(ru))正号。x、sin(ru)、cos(u)、cos(ru)均先证非零；得到冻结cDerivative，无失号或漏乘r。|
| cDerivative_bound |786–839|将导数写(u/x)(A−B)，A/B均非负；以tan u≤2u、csc²(ru)≤π²/(4r²u²)、cot(ru)≤1/(ru)、sec²u≤2，得绝对值≤(π²/2+2)/(rx)。乘除均有正分母。|
| bMode_hasDerivAt |840–878|对(cos(rv)/cos v)^N用商法则及自然幂法则。N≥1使(N−1)+1=N；不除以cos(rv)，分母cos(v)>0已证，得到完整冻结bDerivative。|
| bDerivative_bound |879–1009|在r<x保证cos(rv)>0；tan单调与r≥1使对数导数括号非负。上界丢去非负第二项，用sin(rv)≤rv、1/cos v≤√2及旧mode_decay(N−1)。N≥2给N≤2(N−1)，正确把−2γ(N−1)衰减放宽为−γN，系数恰√2π²/4。|
| interpolation_continuous |1095–1151|固定有限支持oddIndices(k+1)，r≤k≤x；端点允许r=x，因为只有cos(rv)作分子。sin(ru)、cos(v)、cos(u)非零先证；每项连续后按有限集归纳求和，闭区间两端完整覆盖。|
| interpolation_hasDerivAt |1184–1208|开区间中r≤k<x，满足全部严格导数域；固定有限集逐项导数后fun_sum，未微分随x改变的截断。|
| cutoffs_spec |1307–1347|K=ceil(4E)+2、T=max(1,log(8S)/(8γ))均只依赖固定正常数。指数界方向正确，exp(−log(8S))合法；K≥2且K≥4E推出E/K²≤1/4。|
| normalizedActual_close |1381–1443|由T≥1及H≥K≥2导出N≥H²≥1。在同一N/H域控制正谱尾≤1/4及负谱绝对值≤1/4，得到|Z−1|≤1/2、Z≥1/2；真实因式分解与normalizer>0推出实际p>0。|
| normalizedActual_adjacent_bound |1444–1505|同一N分别因式分解H=k和k+1；负谱两项独立取绝对值，未忽略parity。E/k²吸收成E·N/k³只用k≤N，正谱消费已审MVT接口，得到(D+2E)N/k³。|
| logA_hasDerivAt |1571–1615|先证a>0、x/sin u/cos u非零；cot u/x求导再取log，得到(1/x)(u/(sin u cos u)−1)，保留除x产生的负项。|
| logRho_hasDerivAt |1616–1633|v′=−v/x，cos复合与log两负号相消，rho>0先证，结果(v/x)tan v。|
| scalar_log_derivative_bounds |1634–1698|R=u/(sin u cos u)非负且≤π/√2；用|R−1|≤R+1，无偷加R≥1，得L/x。tan v≥0且≤2v，给0≤logrho′≤π²/(2x³)。|
| actual_probability_mono |1765–1776|展开固定S2.p，使用已经证明的±1半质量律及有限乘积概率实例；closedStrip逐prefix条件的集合包含推出Measure.real单调，无新可测性/正性/概率假设。|

额外完整核对当前公共消费链 long_time_domain、adjacent_log_decomposition、adjacent_log_upper及public body，确认变化proof与旧未变接口的互动：共同N满足T(k+1)²≤N，同时给H=k、k+1两个概率正性，才进行通常概率log运算；三个log差的上界分别按标量MVT、N倍rho差及2倍Z差相加。L/k吸收进L·N/k³只用k²≤N。最终非负性来自真实事件单调与正概率。未加入N/k³统一正下限、奇偶条件、特殊N=k³、谱假设或新全局helper。

## 自然语义和全部实际接口

完整读数学冻结、公开冻结及所有实际显式表达式，核对唯一public实际类型确为：先固定C>0、自然K≥2、实T≥1，再对全部自然N/k，只以k≥K及N≥T(k+1)²为前提，同时输出p(N,k)>0、p(N,k−1)>0与0≤log差≤C·N/k³。C=finalConst、K=heightCutoff、T=timeCutoff均独立于N/k。实阈值减1没有误作自然数截断减法，两概率时间相同。

实际p是接受S2源的透明定义：固定RademacherCosine.law（1/2质量在+1、1/2质量在−1）的Fin N坐标乘积测度，对closedStrip取Measure.real。本人核对精确绑定的p、law、prefixSum、closedStrip原定义：prefixSum是真实前缀坐标和；closedStrip包含全部j≤N及j=0。无自由概率函数替换或条件概率。S2.p源码hash `1229ec66…`、law源码hash `c0ba478f…` 与当前固定原对象绑定一致。

实际owned集合由environment difference、module ownership与stage2三种捕获完全相等，**187项=77显式private+1public+109生成项；31 definitions+156 theorems，0 owned opaque**。完整逐项读187 actual types（包括109 generated）和31完整defvalues，不以78个文本声明计数替代。31定义值实际索引：2,18,19,32,42,46,55,57,65,66,67,72,75,76,78,90,100,114,128,129,132,140,142,159,167,171,177,179,182,184,186。

完整显式表达式中的重复实例树以可逆文本宏去重后分6个whole-entry批次读完：1–31、32–68、69–103、104–138、139–173、174–187。宏定义全部先读；每字段逆展开机器验证与原始显式表达式合并空白后逐字符相同，不是省略、抽样、截断或改用隐式pretty。`interface-macros.txt`及六个批次保留可恢复内容，`actual-coverage.json`逐名记录type/value/raw哈希与已读状态。

生成项逐项覆盖包括eq_1透明值展开、Nat.AtLeastTwo常量实例、omega算术辅助及完整多态_simp引理；所有局部条件在实际类型中显式出现，未藏入新的目标前提。31值中的oddIndices、自然modeSign/parity、positivePart/negativePart、normalizedActual和全部导数均忠实于冻结，真实p只在normalizedActual透明商中使用。显式Real/Nat及其运算、拓扑、导数实例没有被同名局部关系替换。

全部实际名字LF列表SHA：`27b5e222c9718db6dd15042b5567f6bb4388ad555bd36df09bea5208c49ae282`；109生成名字列表SHA：`f9d7a511e36ad96a6628930e47bc9a483268741ed502cf1068489b7353fe4961`。

## 原始表达式、递归公理与导入信任边界

本人独立结构解析全部187 raw typeExpr及31 raw definitionExpr，共218棵完整表达式；逐节点检查构造器/元数、全部binder及de Bruijn变量范围，常量引用集合与每个对应typeRefs/valueRefs精确相等，显式表达式保留这些引用。由JSON实际字段重建的owned-interface全文与原文件相同，未出现深度省略或未解元变量。未把原始序列化文本误当Lean重编译。

完整解析40225个递归闭包节点与1209385条type/value引用，所有引用均在图中；从全部187 owned根重新可达遍历所得集合恰等于整个闭包。逐owned重算其递归公理集合，并与导出axioms逐项比对。唯一axiom-kind节点为 **propext、Classical.choice、Quot.sound**；无sorryAx、新增axiom、unsafe或partial。36个transitive opaque均valueAvailable=true，遍历包含其值引用。240项目依赖常量按actual module owner归入13个实际模块；所有Shao owner均属22个固定绑定imports或本模块，无未知owner。完整闭包名字排序LF列表SHA：`49324d014acb26f95e432c225bb5f59b172cdfd5bb393b35a872eb294336af84`。

全部4814 actual findOLean路径逐项校验与固定runtime LEAN_PATH模块路径形式一致，且包含闭包所有owner。它们精确等于旧4653模块加161个Init模块；不是把旧header图计数冒充实际导入计数。22个Shao实际alias逐项匹配原source/object哈希和已存在alias身份，22个本地curated源码与绑定sourcehash一致：21个旧root对象，S2为已独立合格且精确保全的原lane对象（不虚称其old_root_receipt_object_bound=true）。未重新审/编译接受的旧模块。

新增161项是**成功检查后的补采样**，逐项包含实际/首选runtime路径、sysroot路径、对象SHA/大小/身份，均为固定Lean sysroot的Init对象；不声称存在161项旧before哈希。其最初导入身份依赖root已确立的固定版本只读toolchain契约。旧4653有既存before/pre/post同表指纹证据，表SHA `2d5f14684f2b140e5fc6181a8615c999088bc4ecd2aeb12b0dad44842b935fcb`。导入olean仍处于该既有固定只读package/toolchain信任边界，本票不是对Lean发行二进制或Mathlib全部源码的重新认证。父明确指认final-check-receipt/additional-runtime-bindings/command/input-bindings为所需补证，本轮已核对；无待补关键项。

## 成功服务器证据及停止

固定Lean `leanprover/lean4:v4.36.0-rc1`，Mathlib `807d3836b165983210ee2ecf3cd28f239436949c`。command绑定精确Source、runtime环境、Lean二进制和manifest；CPU18–21、M8192/j4、标准exclusive nonblock flock，autoImplicit=false、debug.skipKernelTC=false、trustLevel1025。唯一成功v4 target调用exit0，41.23秒、0 error、stderr空、process已reaped、lock已释放；139条warning未当作错误或证明证据。

独立重算 `Source bytes + LF + audit-suffix bytes` 得combined SHA `7bb519ec2ca449998e528709e28f997428bd4c2336174778f497fe72b00e00be`；suffix SHA `7ea2d5d861569e79c907b0377a1506e7bb18f8179a246aadd12ff1657a2a8b82`。与input-bindings、command、result、final-check-receipt一致。suffix完整读完：在Source结束后立即捕获全部实际owned，pp.all大深度导出，types和值引用递归，opaque值显式请求，并拒绝unsafe/partial/非白名单axiom；无按名字漏掉生成项的过滤。成功kernel不代替本票自然语义审查，两层均已闭合。

按用户关机重启指令，当前单元在完整审查自然收束点停止。**USER_REQUESTED_RESTART_CHECKPOINTED；目录写权RELEASED；无pending工具/写入；无本context服务器或Lean任务；不启动后续单元。** 重启后仅由根重新激活所有者；此最终答复不构成持续运行机制。完整报告与receipt读回并核哈希后STOP。
