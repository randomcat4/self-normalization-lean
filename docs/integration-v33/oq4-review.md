STATUS: CORRECT
SCOPE: PR117 / PR127 exact frozen source acceptance; root aggregate gate remains root-owned.
BASELINE: v32 main13a57f29f0f7487cd8097b2cb03476b2523399ad.
REVIEWER: fresh /root/v33_oq4_accept; 2026-10-22.
ROOT_STATUS: OPEN.

本票接受两个冻结数学范围：有限确定性DA1与真实Pair余谱U1。没有发现阻断其数学／陈述接受的关键缺口。独立性指本票为全新验收上下文；本票确实阅读既有报告及作者收据，不冒称又做了一次盲审或重新机械验证。没有运行Lean、改源码、Git、缓存或进程，只写本MD与JSON。所有新服务器命令CPU18–21；原始Expr、全注册表、完整日志和二进制均未下载。

| PR / exact head | 唯一新生产源码 | SHA256 / bytes | public theorem / public def / owned |
|---|---|---|---|
| 117 / 4db5086c1d4408bbca2ae60026b0326a3ac86b2e | Shao/OQ4/RademacherLatticeShift.lean | 5c5ffa545a9e26ba2a33ebba27ffa64aaa708eaeeea0f56c84aacd8f194aebf7 / 13125 | 9 / 4 / 38 |
| 127 / c340b9f27c497ce0959e54aa49bc41ef055ae959 | Shao/OQ4/RademacherSpectralTail.lean | a29cb9e520aa20e644095f9ac776ccd92f747184ac1d8a121992757a5bf16db0 / 25722 | 8 / 2 / 75 |

合计2生产模块、17显式公开定理、6公开定义、113owned常量；所有定义13、theorem-kind100，其中49生成项。声明数不能当成原始义务数。PR117相对Pair111head3c909bfa只新增15文件，PR127相对PR117新增18文件；包括4个辅助Audit.lean，不是额外生产模块。两个parent到head的全部既有Lean／pins文件分别213、216项均原字节不变。

DA1的冻结文件9cf9dba01aa9582ceb8e4d30af06c4778b8b367b61e61562dfc42c7ffb0e2b56/6067B、匿名证明aefff15a1b80173ee362f58b60448699df70bbc8bc729a44f593a8b4099a6bb8/9818B及完整Source已全文核对。实际Scalar定义H=m+1、a=H⁻¹cot(π/(4H))、rho=cos(π/(2H))、lambda=π²/8与v32相同。源码90–153行从q=(u/sin u)cos u≥cos(π/8)>0和实际SCA1内部推出全域log界；155–199行精确恒等式D=−delta²(3h+2delta)/(h³H²)给|D|≤3/h⁴；202–291行结合实际SCA2并取C=C_rho+3lambda+C_log>0，得到冻结DA1。先取绝对C再遍历全部m≥1、全部m≤h<m+1、所有n:Nat，包括0；delta=H−h、弱左端delta=1、领先系数π²/4、残差符号及n/h⁴+H⁻²均未漂移。没有自由Taylor／log前提、充分大／尺度／奇偶条件。它是原文S4确定性部分的明确全有限参数派生扩展，原始叶增量0，不能宣称已得实际S4概率结论。

U1的冻结文件b220e1ca9f89e5f9a3328131b430fb54b9656e5113b93241adbde1aad627354a/8952B、匿名证明0967cf2d0c0773aef9dd8ec4f8a8054e8480c962892c6f4b217ed6b51c827e3c/11974B及Source565行已全文核对。R确为v32 Pair.lowerModes.erase0的normalizedTerm有限和加zeroMode/(amplitude*rho^n)，不是任意误差函数。固定q=exp(−3π²/2)、C=2/[3(1−q)]>0先于全部m/h/n。系数由tan凸性得到2/r，log(cos u)+u²/2单调性给相同r的精确谱比，r=2k+3的r²−9≥12k与t=n/H²≥1给有限几何和，保留指定π²速率与原阈值H²≤n。中心零谱仅在先证明正时间后消去；m=1、2空尾，n=0的0^0与原Pair定义不变。负主模态epsilon*tan²仍在R之外。最终实际类型与冻结的∃C>0、全部弱胞元、Nat时间及H=m+1一致。实际概率绑定沿用已接受Pair.closedStrip_probability_normalized：固定Rademacher等权Dirac产品律、起点0及closedStrip的Measure.real；U1源码只消费这一真实R的已认证定义。

独立终审与服务器证据可复核。DA1报告drafts/oq4/review/rademacher-lattice-shift-formal-review-v1.md SHA67d3c2b5c70c55d46284c00e76f4b80d00504d7ff70900b341c6db5458621ab4/9516B；receipt54e9c1bab037da00c48888716051bf990d16a75c330de7a7372e962b19b4c561/104389B；manifest985babc58bdda30516c211216e067f1f2566f4608d1bddcbb4f0a0e356d349e0/15173B。其6次FINAL命令均exit0，含完整规范Source无-o。38条记录逐项机器解析，4定义/34theorem，22private，unsafe/partial/activeInstance均0，逐记录公理并集仅propext、Classical.choice、Quot.sound。48项结构检查包括全部type Expr、4个完整定义值、universes、owner与flags；旧1135/121保留，full45为1173/125，source/direct目标38相同。v1将private-wrapper前缀逸出0误写成raw目标前缀逸出0；v2纠正为raw外22、全部private、user外0，保留原件且没有重跑成功Lean。

U1报告drafts/oq4/rademacher-spectral-tail-independent-v1/final-review-report-v1.md SHA2a287099ff6c9774e8ae3f3148d7bee0e28899d1e5d2484dbfdd02e42705d883/23200B；curated receipt067e5be29118823feb3e002cd66325a0a5731fc96aa94743da452c5a6222cc99/53192B；85文件manifest4a655959532500785e647dfaee0fb1c09f639f04a9c52719797fa5f91c5c9ffb/15898B。实际6次有效native加1次Options.setNat元数据API失败；Source无-o一次通过，reviewer emit0。75条记录逐项解析为9定义/66theorem、62private，unsafe/partial/activeInstance均0，传递公理同标准3项。Source/Direct为753/80，expanded OldProject1396/156，Full46为1471/165；窄old45为1173/125，不冒充全项目。原Source→Direct因root/Scope未对齐保持NOT_ALIGNED，另一次registry-only DirectAligned才给限定相等。cotangent.eq_1虽然用户名在FiniteS1下，实际owner是Tail，全部75均保留；killedAction.congr_simp在不同闭包的AllModes/KernelRecurrence owner差异保持，不能跨不同闭包宣称owner恒等。四类raw/user交集分别实测0，非名称前缀假设。

必须收窄历史注册表措辞。本票亲自检查DA1真实Asource wrapper第429–434行（wrapper SHAae00feff2c85ab5327ef9b9228d27156a80098ec7b53cda5fe5e978c54bebd93）与Tail instrument.py149–154/final_instrument.py17：两者只把defaultInstanceExtension.getState的derived classes/priorities和getModuleEntries导出；没有default原始local/state.1域，也没有coe_decl TagAttribute域。它们的六个已采集registry域、真实discrTree及顺序比较可以成立，但“所有default/完整全部注册表”不能外推到这些未采集域，未测不是实测空。这是证据完整性与报告范围限制，不是发现数学反例、非法公理或源码变化；两个目标源码均无instance/attribute注册动作，mandatory陈述／内核／公理接受成立。后继若继续要求完整extension保证，应由修正后的一个标准采集器一次实测这些域，不追溯改写旧报告或为包装重放旧成功检查。

本票CPU18–21只读核对94个已闭合小证据文件共2743287B，全部SHA/bytes/prepost-stat一致；大raw/全闭包仅沿用原收据绑定，未新重算或下载。发布14项核心文件中13项直接匹配原本地镜像；Tail author receipt最初错配到旧private收据，纠正为canonical-author-v1/author-receipt.json后匹配e7f96ac79bce519e019ce473ce41e6cc011fb1351abaa696478b1c683b01195f/83659B，非发布文件漂移。v32服务器receipt449d58e2ebb0e34706bcbea3fae929a20840fa25192c0d51c41708ee1e98b22c/状态PASS绑定215生产模块；PR117的132旧生产源逐项与其相同，PR127的133旧源为同132加本批DA1。原lead两个clone未包含GitHub合并commit对象；一次cat-file查询因此失败，未写入；之后改用既有v32收据作字节锚，不声称在lead clone验证了main提交图。根协调负责新合并图／live PR冻结及aggregate gate，不能拿旧堆叠整树覆盖main。

承重闭合是DA1的确定性取整误差义务及原Spectrum S2内的U1统一实际余谱界。U1直接消费端是complete S2 F1/Q1；DA1未来被DA2及真实S4消费。完整S2仍待该后继本身认证；真实Brownian B/U、标准尺度／可测性／a.s.事件／Measure.real与首项尾、实际S3、DA2及S4、弱S5／CP仍未闭合。原frozen01只承诺首项等价，不允许把原spectrum61强谱相对误差默用作Brownian前提。strict、其他coset、一般BE/SP、K/Kv、E3实际双变量与E4–E6、Spectrum/OQ4根均仍OPEN，无百分比或原根闭合新增。

节奏诊断：当前coordination/status/oq4.md为current158，2026-10-22T14:10:38Z，SHA0e8f3e7ffce858a6c71fba915551b23815713e1f3a7f7a1c39f43f52321ab27c/27108B。current102在03:49:56Z已经记录S2匿名数学CORRECT relative actualU1；U1到09:20Z发布，current137的11:20Z至current158的14:10Z持续generic机制修复，certified增量0、heavyNONE，lifetime contexts从68至85。S2独立工具目录462文件/4592320B，此数是体量指标，不推断每份文件工时。current158及可读最近线程活动均明确：新建文件写入模式已查到，80只作本地v2修复，85静态审查STOP，native执行尚未放行。14:16:49Z自己的只读进程观察Lean/lake=0；未触动外部CPU0–9/80GiB任务。最新线程read_thread虽请求1turn仍返回巨量输出，不能冒称逐字读完整线程；本诊断只用实际读到的最新消息、工具片段及完整current158状态。

CAP-R1 opaque value?默认false导致固定fixture必失败、CAP-R2新sidecar/emit路径缺启动前不存在和独占新建、CAP-R3 AUX缺单链接与运行后源hash，都是具体工具／custody缺口；历史capture缺前置absence/hash、非单射Name可读渲染、默认域遗漏也必须保留，不应把它们叫作纯官僚流程。另一方面，重复阶段放行、逐个微小只读API都新建release/receipt、重复大ledger阅读与多版封包，已使审计工具成为数学交付的关键路径；现有证据支持这一流程瓶颈，而非证明本身失败或算力不足。

根协调具体下一步：给当前三项修复一个有界收束单元；fresh85只审实际差异和必要新控制，随后一次执行固定native资格包及S2最终陈述／完整Source no-o／全部44owner公理检查。由root明确短期cache无写者窗口与CPU18–21单重型租约，并给出通过这些固定条件即可执行、形成可审PR的持续授权；普通可逆服务器检查早已获用户授权，不需要再等待用户“native execution authorization”。当前native暂停的实际原因是lane自己内部的execution=false与三项真实静态缺口，没有证据显示用户权限缺失。root可改变内部调度，不可跳过真实缺口或将历史欠证回填为PASS。不要再为相同旧机制展开新框架、重放旧成功测试或要求另一轮phase0；若工具继续膨胀，用root已有标准核验路径一次补齐明确缺域，保持陈述忠实性／内核／公理门。紧接S2，应兑现root所有的真实Brownian首项接口，避免OQ4再次等共享承重依赖。

本票没有授予子实例执行权限，没有启动上述工作，也没有更改任何既有租约。root最终集成门尚待其记录；本次验收仅为这两个冻结源范围CORRECT。
