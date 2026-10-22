# v37 OQ4 独立验收：实际 Brownian 比较 S3

STATUS: CORRECT
CRITICAL_GAPS: NONE
审阅者：/root/v37_oq4_accept；本实例 Lean 运行次数：0。

精确验收 PR147，head 54a2db6cee45504f3bf52b04a51ad1409df4aaec，tree 12346fb25200dec1939e4bc0ecfa4a5697a9c6a4。整个源码直接读取指定远程 worktree 的 git show <head>:Shao/OQ4/RademacherS3Assembly.lean；28173字节，SHA256 097d3a773d48f9d94a2a5b439c00d39f6c87eb9b1c793d3b91dba6066fef369c。v36接受基线是f2a39a09ebd50648bd61d68d7018aa01a9810ea0，对应main 82294da791784f3ac34ca52b96e21ef23f8a5329。已独立核对基线是该head祖先，差集恰为18个新增文件，唯一新增生产源码是本S3。

本结论覆盖原谱S3、原Brownian冻结题、数学冻结、完整匿名证明、精确形式冻结、整个最终Lean源码及全部private/generated/public类型和全部定义值。先完成自身数学与源码审查，随后完整读取旧审阅和机械审计程序，核查证据链。派发和状态中可见历史通过元数据，不作“历史结论零曝光”声明，也未凭CORRECT标签验收。

## 实际概率对象与冻结范围

实际Rademacher律为RademacherCosine.law，即±1各1/2。p(n,h)仍是Measure.pi (fun _:Fin n => law)对原弱事件closedStrip的实值概率；K仍是该律从0出发的原killedMass。finite_identities给出p=K和实际有限谱身份。分子没有按谱主项或自由误差重新定义。

Brownian接口为实际B : ℝ≥0 → Ω → ℝ、概率测度P及hB : ProbabilityTheory.IsBrownianReal B P。分母逐字为BrownianSup.probability B P hB。brownian_object给出可测U、U几乎处处等于sup_{0≤t≤1}|B_t|的路径上确界，且对每个实数阈值s，
b(s)=P.real {ω | U(ω)≤s}=P.real (fullStrip B s)。
该结论量化任意承载实际标准Brownian过程的概率空间，消费同一个实际边际概率；没有自由F/hTail、替代尾分布、缩放或耦合前提。

域保持全部自然n包含0，全部m≥1及弱胞元m≤h<m+1，包含整数端点、小胞元和所有奇偶。全k域条件未弱化。唯一渐近前提为H→∞与N/H²→∞，其中H=m+1、N=(n:ℝ)。没有额外N/h³、DA1/DA2、单调性、特殊子列、全k正时间或概率正性输入。

## 数学与实现核对

| 单元（源码起始行） | 独立核对 |
| --- | --- |
| 22定义（22）、definition_bridges（81） | 与形式冻结的全部定义值和公开头完全相同；A只改名实际S2.B，p/K/D/R、原h、同一n的cast、λ=π²/8、4/π原样保留。 |
| finite_identities（101）、zero_time（123）、small_cells（132） | 全自然时间的实际概率/谱身份和正A保留；n=0时p=K=1、形式x=0、偶m中心项和m=1/m=2异常均未删除。 |
| brownian_object（139）、g_pos（155）、finite_ALG（166） | 实际Brownian事件桥、确定性主项正性、正时间sqrt平方/倒平方、g(h/√N)=G、自然幂对数和振幅对数桥成立。g在0的总化值未当成Brownian零阈值正性。 |
| private scale_domain（227） | H−1≤h<H给h→∞；N/h²≥N/H²；t最终≥1推出N>0、n≥1、√N>0。严格阈值与x²=h²/N给x正侧趋0，无附加尺度。 |
| S3_DOM（318） | 实际S2.Q1给D→1、logD→0及p/K最终正性；已接受的实际Brownian首项与正性沿正侧x给T→1、b/T正性。最终W=T、logT→0，共同合法尾段闭合。 |
| S3_ALG（449） | 在正性尾段精确得到log(p/b)−C=logD−logT，K形式由p=K替换；符号、系数和原h分母正确。 |
| S3_MAIN（553）、S3_MAIN_epsilon（584） | 两个残差对数趋0，经最终精确相等得到原中心化差绝对趋0；ε形式明确K_time≤K_pos≤K_e和合法概率商。 |

匿名证明0–11节已全文逐段核对。原首项等价取误差1/2可导出实际Brownian局部正性；正区间均值定理给|log y|≤2|y−1|，进而logT→0。各阈值通过有限最大值合并，无需序列单调。实现使用已接受实际B2的相同正性输出和log在1的连续性，条件与对象一致，没有增加前提。

精确消去后得到原S3要求的绝对o(1)，没有除以N/h²弱化。原文较强Brownian相对指数O率已与原首项等价区分，当前代码和证明不消费它。可选D/T→1与p/b=exp(C)D/T观察正确，但未断言C→0或未中心化概率比趋1。

## 完整机械证据与绑定

已全文读取全部33个公开原生类型、22个原生定义值和其余13个所属类型，包括private scale_domain和12个实际生成定理。所属集合46项=22定义+11公开定理+1私有帮助定理+12生成定理。全部46项账字段和三份名单均读取。独立后缀按环境差、真实模块归属和stage2三路枚举，不以预期名单过滤额外声明；其实际递归类型与值/证明遍历逻辑已经审查。

只读服务器复核重新哈希全部18个发布文件及16个原始证据工件。原生54,347,502字节审计对象、880,065字节原始Expr对象、完整依赖图、日志和组合检查文件均匹配记录。原生46类型/22定义值逐字及逐哈希等于发布清单。61,160项闭包全部类型/值引用在闭包中；真实项目所属依赖恰为554项、22模块。逐项机器复核全部554行安全性、公理和依赖图一致性：unsafe/partial/axiomkind均0，公理仅propext、Classical.choice、Quot.sound。没有声称人工全文阅读54MB引用图或重新证明所有上游模块。

22组实际运行时源码/olean重新哈希；各源码同时匹配本head和v36接受提交的Git字节。sole olean为1958728字节，SHA256 94adfe9486c0b5b7a9b87d40d8dad0c1f1e186841faeb508727904ee6803b3e6，当前对象仍精确一致。

既有目标机械检查采用Lean4.36.0-rc1、固定mathlib 807d3836b165983210ee2ecf3cd28f239436949c。精确Source在offset0，后接独立审计后缀；trustLevel=1025、skipKernelTC=false、autoImplicit=false。原生检查exit0/13.897293秒；唯一canonical emit exit0/3.422515秒/0错误0警告；父imports-only单元与全50分别exit0/4.170284秒及4.316867秒，目标均46项/22定义、旧107对象不变。这些是已有实际执行证据，本实例没有重跑Lean。

根协调人的gate-result.json（SHA256 848db071f079bd2b4bc85bf4b3a8a8877b8d76633c740cbead484d343a44c2bb，validation_revision=2）已完整解析并核对目标源SHA。v37编译、公理、所属声明、模块覆盖和差异门均PASS；266生产模块、1814公开定理、3011含生成定理、5145所属常量。根门由root统一运行；非OQ4源哈希表未逐项人工审阅。

## 范围与非声明

CORRECT仅认可固定Rademacher实际弱存活概率对实际标准Brownian最大绝对值概率的S3_DOM/S3_ALG/S3_MAIN及ε形式。直接消费者是实际S4，继而实际S5；**S4、S5、strict/coset变体、完整Spectrum和一般OQ4根不因本次验收闭合**，其他原根状态不扩展。raw叶增量与原始来源总分母变化均0。旧冻结/匿名稿的pending为历史记录；当前消费通过精确接受基线与源码/对象绑定确认的正式上游，没有以冻结声明充当证明。

本实例仅写指定审阅MD/JSON。未运行Lean、改源码/缓存/refs、合并、发送其他聊天消息或操作外部CPU0–9/80GiB任务。只读数据复核使用CPU10–13。首次大参数元数据请求在Python执行前因Argument list too long退出，缩减仅传清单后复核成功；没有任何Lean或写入重放。
