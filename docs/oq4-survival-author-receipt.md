# FiniteSurvivalLaplace 实际复现收据

源码固定；完整目标、作者唯一olean生成、import全部新module-owned常量传递公理审计均exit0。目标与olean日志均为空。本收据不构成独立审查票。

冻结接口：drafts/oq4/frozen-finite-survival-laplace-v1.md。新数学源仅Shao/OQ4/FiniteSurvivalLaplace.lean；未修改任何既审数学源、公共定义、根导入、Git、manifest、锁或共享缓存。Generating依赖源eab53afb...与LaplaceTail源664df6aa...保持只读。

源SHA256：49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb。
olean SHA256：49159bb33819ebe0bf2c654a9d031e7a0f9233b3f9de3f34aca47a4c12ee4413。

实际30新常量=28显式（4定义+24定理）+2生成。按所属moduleidx枚举并逐项#print axioms，30条记录与枚举逐项同名匹配；所有30项完整传递公理集均仅propext/Classical.choice/Quot.sound，禁用源项扫描为空。完整原始日志仅server repro_outputs/oq4-survival/；本机summary.json/declarations.md为curated收据。

冻结目标闭合：

- 真实有限产品Pi下的最大值指数、正部端点指数均有独立可测/可积性与[0,1]界，包含自然长度0；公共maxWithZero包含零时刻，并实际证明a_L(0)=1。A的被积函数可测性在本模块给出，其所有k（含0）的真实可积性直接复用已编译LaplaceTail.iid_integrable_positiveLaplace；真实积分线性证明A=1-b。
- 从原本真实产品的坐标iIndepFun_pi，经固定castSucc注入，得到Pi_{n+1}前n坐标推送精确为Pi_n；公共prefixSum的有限求和直接证明投影前缀恒等式，再得投影maxWithZero不超过原最大值。对真实可积函数作推送积分，实际证明Antitone(a_L)，没有把它作为假设。
- a、b、A三个实际级数分别由已编译Generating的有界几何比较真正Summable。输入只保留全L>0、全0<s<1的原始G=exp(B)；A=1-b与真实对数级数给B=-log(1-s)-W，从而证明等价标准化式，不把标准化式作为额外输入。
- 全k≥1/x实际Pi下普通和CDF误差、C_BE≥0、β≥1，以及上述原始SP输入，取d≥0、L=d+β，真正实例化LaplaceTail/Generating给a_L(m)≤sqrt(2)exp(5+3C_BE)(d+β)/sqrt(m)，所有m≥1。
- 公共closedUpper与H_m≤d精确等价，可测indicator真实可积；逐点支付后真实积分给Pi_m.real(closedUpper d)≤exp(d/L)a_L(m)。d/L≤1再给sqrt(2)exp(6+3C_BE)(d+β)/sqrt(m)。闭边界、原子、d=0、m=1与全零路径均保留。

匿名完整推导见proof.md。无任何矩、中心、方差、密度、格点或有界支持前提；β仅为明确CDF误差参数。没有在生存条件化后假设增量独立，没有复制公共Path/prefixSum/maxWithZero/closedUpper定义。

导入：已编译LaplaceTail、LaplaceGenerating，公共ClosedSurvival、FiniteIID，以及已缓存Mathlib.Algebra.BigOperators.Fin。为避免无必要共同工件，前缀投影直接写固定坐标函数，不引入共同Lindley依赖。没有新增缓存请求或写共享缓存。

工具链Lean v4.36.0-rc1，mathlib 807d3836b165983210ee2ecf3cd28f239436949c。全部Lean仅在指定server，先activate再cd工作树，单进程4核亲和。复现命令：

```sh
set -e
source /root/rivermind-data/shao-lean-20261021/activate.sh
cd /root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4
taskset -c 0-3 lake env lean Shao/OQ4/FiniteSurvivalLaplace.lean
taskset -c 0-3 lake env lean -o .lake/build/lib/lean/Shao/OQ4/FiniteSurvivalLaplace.olean Shao/OQ4/FiniteSurvivalLaplace.lean
taskset -c 0-3 lake env lean repro_outputs/oq4-survival/AuditNamefix.lean
python3 repro_outputs/oq4-survival/summarize-namefix.py
```

复合脚本均set-e，Lean失败显式捕获rc后写server日志/exit再返回。target01–03为定向接口修复历史，原63f候选target04曾独立exit0；后发现与Boundary同名，旧候选已撤回。当前namefixTarget、namefixOlean、全部21模块实际import的namefixAudit均exit0，目标与emit日志为空。一次broker明确operation_may_have_started=false后，按SERVER授权作有界native手动fallback；后续emit/audit脚本首先核对target04.exit=0及固定源SHA，再唯一emit。没有在可能已开始时自动重放操作。

本机生产源及curated交付均UTF8无BOM、LF、单最终LF；原始日志和二进制仅server。父实例报告当前branch feat/oq4-one-sided、head9c4f640c...，作者未操作Git或把未审模块混入现有PR。

范围：只得到ν上侧在明确BE型CDF输入和原始SP输入下的条件有限生存界。BE、SP本身、−ν上侧及最终双侧S、无条件S/AC/O0、B1、K/Kv与完整OQ4均OPEN。不声称独立认证。

命名共存修复记录：旧源63f00181f50ab082e0c1e1695ec5c983191bcf25a01bb901454844fe4316b0b5 → 当前49241958f2ae692b56db5fe0aa021a5e88b0020ac6487ddb463d05efb69518cb。精确变换仅把2处标识符measurableSet_closedUpper替换为measurableSet_closedUpper_laplace（新helper声明与内部引用）。已逐字节等价变换核对，没有其他source改动；匿名proof原始snapshot不变，旧Boundary及其他公共/已审API均未改。

旧63f源备份在server repro_outputs/oq4-survival/FiniteSurvivalLaplace.before-namefix63.lean，本机FiniteSurvivalLaplace-before-namefix.lean；旧summary/Audit/receipt/declarations也留名为before-namefix的历史。旧standalone通过不足以说明全lane共存，已透明撤回旧冻结候选。

新候选先以20个既有OQ4模块imports加精确新Finite源码体，实际运行CoexistSource：exit0、日志0字节。该清单包含server根的全部已接受OQ4模块、PR29的Interval/Laplace、Generating与其余前置叶子，不依赖过期本机library根。随后canonical目标及作者唯一olean重新生成，再由AuditNamefix实际同时import全部21个模块并审计本新模块的全部30owned常量：均exit0。最终独立形式复查应针对492新源；旧数学票可由父审查者决定复用，本作者不签票。
