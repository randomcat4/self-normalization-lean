# unit285 独立完整 SOURCE 审查

STATUS: CORRECT_SOURCE_ONLY

候选 SHA256 4fdb9530538a0e55b1875d1de08d1f94d9981878298346d951daac2a2439c134（11295字节、256 LF）完整对应冻结的两个 theorem，未发现关键证明缺口。审查身份为 /root/oq56_unit285_review，与作者分离；此结论只接受这一版源码的数学推导与陈述忠实性，不是 Lean 编译、内核、公理或全部实际所属项验收。

激活文件 SHA256 98b2f3a5dc2e5a95961d509f96a2e561d43ebe666410aa4b9e33ab3cdb0b128f（13999B）及全部53输入，均在首次报告写入前核验 hash/bytes。实际 runtime ACK 也在首次写入前发送给父实例。首次写入时重新核验了同一53输入，封存前仍须确认它们没有变化。只写全新 source-review-01，没有源码、冻结、其他所有者或共享文件写入。

已完整阅读候选全部256行、两条冻结 HEAD 的25行、两份完整 proof 的218行、原始 p41 的449行、p51 的355行、source-bound plan、冻结环境，以及主要实际调用接口的完整陈述、证明和相关 namespace/variable/typeclass 环境。作者报告是被审材料，不作为正确性理由。SOURCE-COVERAGE.json 为每个源码行给出精确字节片段、行 SHA256 与独立审查义务，并将每一 proof 行恰好归入一个已检查义务；六组件覆盖0至11295字节且无间隙、重叠或隐藏分隔。

T01 的实质是实际二阶矩矩母函数界。绝对界只按 nu-AE 使用，给出 f∈[-B,B] 和 f²∈[0,B²] AE。有限概率法则与 measurability 因而真正保证 f、f² 以及 exp(t f) 可积；没有借用 Bochner 非可积时取零的定义得到伪界。Complex.exp_bound_sq 在 x=0、z=u 的完整原接口，结合实部不超过模，给出 |u|≤1 时 exp(u)≤1+u+u²。AE |tf|≤|t|B≤1 支付逐点估计。多项式各项可积使两次积分相加合法；实际 hmean=0 消去线性项，实际 hsecond 乘非负 t²，最后 1+s≤exp(s)。v 没有被 B² 替换，签名没有隐藏 MGF/Bernstein 合同。

T02 用的是真正的 P=Pi_i nu 和 X_i(x)=f(x_i)。evaluation 的可测性、保测推前等于 nu 及 AE 传递，分别支付坐标可测性、相同分布和范围。iIndepFun_pi 在同一实际 P 上给独立性。每个 exp(zX_i) 的可积性由 AE interval 单独建立，再由独立有限和接口建立 exp(zS) 可积性。mgf_map 的 AE 强可测条件由全局可测的 exp(zf) 支付；mgf_sum 和显式函数和等式得到 mgf(S,P,z)=mgf(f,nu,z)^m。非负 mgf 基数容许自然幂比较，指数恒等式给 exp(z²mv)。不存在未qualified283/284候选模块导入；其目录内的 Mathlib 原始文件只作为固定版本 primary API 来源。没有共享 private Bennett 名称或证明依赖。

q=0 在任何除法前使用概率≤1。B=0 用实际 AE f=0 传递到有限所有坐标，得到 S=0 P-AE；严格事件与非负阈值使其为零测事件。余下 B>0、q>0，a=mv≥0，d=√(aq)+Bq>0，t=q/d>0。源码完整建立 d²≥aq、|t|B≤1、td=q、t²a≤q。最后一个不等式来自 q(aq)≤qd² 并除以正 d²。没有除以 a、v 或 m，故 v=0、card=0 均被同一分支覆盖。有限 Pi 及所用独立有限和接口的原证明显式包含空情形，没有偷加 Nonempty ι。T01 的 t=0 及有符号 t 无分母问题。

上下 Chernoff 分别使用 t≥0、-t≤0 以及两份实际指数可积性。两个指数均为 -2td+t²a≤-q。冻结阈值恰为2d；严格绝对坏事件经 S 的符号分支包含于两条 inclusive 单侧事件之并，有限实测度的单调性和并集上界给2exp(-q)。源码没有把严格零阈值坏事件改成非严格绝对事件。

与原题的关系限定于 p41(14) 所需的一般 actual-variance engine。后续原始交互 consumer 仍须使用同一个实际残差、完整异常向量、f=cA-mA、v=V2、B=2ellR 并保留 p41(9) 的非零条件均值。这里未证明该 consumer，也未证明其渐近简化、Delta、Mills、异常积分或完整物理统计量/SZ/CDF 接口。原 Bernstein consumer、Delta、Mills、anomaly integration、PE-R、PE-L、NR、DC、OQ56 和 root 全部保持 OPEN。经典集中工具的正确使用不构成研究新颖性认证。

39条主要 primary API、11份原文件的完整已读代码、原始行号、环境和精确文件 hash 记于 PRIMARY-API-CONTEXTS.json 与 PRIMARY-API-TRACE.md。固定 mathlib pin 807d3836b165983210ee2ecf3cd28f239436949c 的来源依据是这次绑定的父实例只读记录；本审查独立核验本地文件 bytes/hash，没有另作 Git/网络或服务器来源核验。普通实数环算术、有限和改写、可测性及 tactic 基础设施由四条冻结导入支持；没有声称递归重审整个 Mathlib 或进行实际 axiom audit。

作者的 LOCAL-METADATA-FAILURE-001.json 记录一次本地路径数组组装错误，未声称数学/内核通过；其修复后候选组件、冻结和清单在本审查中重新按实际字节核验。作者原始 ACK 先于写入的顺序来自 exact parent-author-intake 见证与作者的诚实晚写 INPUT-ACK 说明；fresh reviewer 不是该旧事件的现场目击者。本审查自身 ACK 顺序可由本轮工具序列验证。本 reviewer 的首次报告命令组合在 functions.exec 的 JavaScript 解析层失败，未调用 exec_command、未有文件效果；纠正命令字符串后才开始报告写入，该本地失败另行保留。另一次自有 READING-COVERAGE 报告更新引入 CRLF，被封存前编码检查拦截；只修正该报告的换行，精确前后字节 provenance 另行保留，候选与所有绑定输入均未改变。

STATIC.json 中的编码、禁用词、声明数和精确冻结比较只是本地确定性核对。派生数为2 theorem、0 def、25 HEAD LF、218 proof LF、12 PRE LF、1 CLOSE LF；实际生成项/所有者清单、完整 TYPE、所需 VALUE、first original object 和 recursive AX 仍为 null。没有 Lean/AX/compiler/probe/SSH/网络/上传/Git/API/缓存/资源/子实例/Goal/schedule/sidebar操作。显式项目限制覆盖 math-theorem 默认的工具链探测要求。

请求模型/推理为 gpt-6.1-sol/xhigh、fresh context；未暴露的实际模型/backend/effort/input/cachedInput/output/reasoningSubset均为 null。下一验收由父实例安排指定服务器 native，成功后同 first-object 的全部实际 TYPE/FULLVALUE/recursive AX 和独立 FINAL。本 reviewer 不排队、不重试、不等待、不自行恢复；唯一 LAST 释放全部 active/dormant/future writer/execution authority。至多保留需新明确 ACT 和精确服务器证据的 SAME 非写入 FINAL 身份。
